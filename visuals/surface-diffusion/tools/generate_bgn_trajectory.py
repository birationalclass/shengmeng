#!/usr/bin/env python3
"""Generate every trajectory used by the interactive BGN surface gallery.

Every frame is produced by the same fully discrete linear BGN scheme shown on
slide 8/38 of ``sp电子科大.pdf``.  On the old polyhedral surface S^m we solve

    <(X^{m+1}-X^m)/dt . n^m, phi>_h - <grad H, grad phi> = 0,
    <H n^m, eta>_h + <grad X^{m+1}, grad eta> = 0.

The PDF's later torus and ellipsoid figures supply two additional initial
geometries for explicitly labeled surface-diffusion experiments.  The PDF's
genus-two Willmore experiment is generated separately by
``generate_willmore_trajectory.py``.  No keyframe morphing or remeshing is
used anywhere.
"""

from __future__ import annotations

import argparse
import json
import math
import struct
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

import numpy as np
from scipy.sparse import bmat, block_diag, csc_matrix, diags
from scipy.sparse.linalg import spsolve


MAGIC = b"BGNPFEM1"
METRIC_NAMES = (
    "surface_area",
    "enclosed_volume",
    "quality_min",
    "quality_p05",
    "quality_mean",
    "energy_defect",
)


@dataclass(frozen=True)
class Case:
    slug: str
    name: str
    short_name: str
    caption: str
    source_note: str
    mesh: Callable[[], tuple[np.ndarray, np.ndarray]]
    steps: int
    dt: float
    camera_distance: float
    camera_yaw: float = -0.72
    camera_pitch: float = 0.34


def signed_volume(points: np.ndarray, cells: np.ndarray) -> float:
    p0 = points[cells[:, 0]]
    p1 = points[cells[:, 1]]
    p2 = points[cells[:, 2]]
    return float(np.sum(np.einsum("ij,ij->i", p0, np.cross(p1, p2))) / 6.0)


def orient_outward(points: np.ndarray, cells: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Give a closed connected mesh positive signed volume and center it."""
    points = np.asarray(points, dtype=np.float64)
    cells = np.asarray(cells, dtype=np.int32)
    if signed_volume(points, cells) < 0:
        cells = cells[:, [0, 2, 1]]
    points = points - np.mean(points, axis=0)
    if signed_volume(points, cells) <= 0:
        raise RuntimeError("could not orient closed mesh outward")
    return points, cells


def cube_surface(subdivisions: int = 10, half_extent: float = 1.0) -> tuple[np.ndarray, np.ndarray]:
    """Return a consistently oriented conforming triangulation of a cube."""
    if subdivisions < 2:
        raise ValueError("subdivisions must be at least 2")
    a = float(half_extent)
    faces = (
        ((a, -a, -a), (0, 2 * a, 0), (0, 0, 2 * a)),
        ((-a, -a, a), (0, 2 * a, 0), (0, 0, -2 * a)),
        ((-a, a, -a), (0, 0, 2 * a), (2 * a, 0, 0)),
        ((-a, -a, -a), (2 * a, 0, 0), (0, 0, 2 * a)),
        ((-a, -a, a), (2 * a, 0, 0), (0, 2 * a, 0)),
        ((-a, -a, -a), (0, 2 * a, 0), (2 * a, 0, 0)),
    )
    vertices: list[np.ndarray] = []
    triangles: list[tuple[int, int, int]] = []
    vertex_index: dict[tuple[int, int, int], int] = {}
    scale = 10**12

    def index_of(point: np.ndarray) -> int:
        key = tuple(np.rint(point * scale).astype(np.int64))
        if key not in vertex_index:
            vertex_index[key] = len(vertices)
            vertices.append(point)
        return vertex_index[key]

    for origin_values, u_values, v_values in faces:
        origin = np.asarray(origin_values, dtype=np.float64)
        u_vector = np.asarray(u_values, dtype=np.float64)
        v_vector = np.asarray(v_values, dtype=np.float64)
        grid = np.empty((subdivisions + 1, subdivisions + 1), dtype=np.int32)
        for i in range(subdivisions + 1):
            for j in range(subdivisions + 1):
                grid[i, j] = index_of(origin + (i / subdivisions) * u_vector + (j / subdivisions) * v_vector)
        for i in range(subdivisions):
            for j in range(subdivisions):
                a0, a1, a2, a3 = int(grid[i, j]), int(grid[i + 1, j]), int(grid[i + 1, j + 1]), int(grid[i, j + 1])
                if (i + j) % 2 == 0:
                    triangles.extend(((a0, a1, a2), (a0, a2, a3)))
                else:
                    triangles.extend(((a0, a1, a3), (a1, a2, a3)))
    return orient_outward(np.asarray(vertices), np.asarray(triangles))


def sphere_topology(
    profile: Callable[[float], tuple[float, float]], latitudes: int, longitudes: int
) -> tuple[np.ndarray, np.ndarray]:
    """Triangulate a closed surface of revolution (axis is x)."""
    vertices = [np.asarray((profile(0.0)[0], 0.0, 0.0), dtype=np.float64)]
    for latitude in range(1, latitudes):
        phi = math.pi * latitude / latitudes
        x, radius = profile(phi)
        for longitude in range(longitudes):
            theta = 2 * math.pi * longitude / longitudes
            vertices.append(np.asarray((x, radius * math.cos(theta), radius * math.sin(theta))))
    vertices.append(np.asarray((profile(math.pi)[0], 0.0, 0.0), dtype=np.float64))
    south = len(vertices) - 1
    triangles: list[tuple[int, int, int]] = []
    first_ring = 1
    for j in range(longitudes):
        triangles.append((0, first_ring + j, first_ring + (j + 1) % longitudes))
    for ring in range(latitudes - 2):
        first = 1 + ring * longitudes
        second = first + longitudes
        for j in range(longitudes):
            jn = (j + 1) % longitudes
            triangles.extend(((first + j, second + j, second + jn), (first + j, second + jn, first + jn)))
    last_ring = 1 + (latitudes - 2) * longitudes
    for j in range(longitudes):
        triangles.append((last_ring + j, south, last_ring + (j + 1) % longitudes))
    return orient_outward(np.asarray(vertices), np.asarray(triangles))


def figure_eight_surface() -> tuple[np.ndarray, np.ndarray]:
    """A smooth two-lobed genus-zero surface with a narrow central neck."""
    def profile(phi: float) -> tuple[float, float]:
        cosine = math.cos(phi)
        radius = math.sin(phi) * (0.30 + 1.25 * cosine * cosine)
        return 2.05 * cosine, radius
    return sphere_topology(profile, latitudes=24, longitudes=28)


def oblate_surface(latitudes: int = 20, longitudes: int = 30) -> tuple[np.ndarray, np.ndarray]:
    def profile(phi: float) -> tuple[float, float]:
        return 1.90 * math.cos(phi), 1.90 * math.sin(phi)
    points, cells = sphere_topology(profile, latitudes=latitudes, longitudes=longitudes)
    # Make y the short axis and keep x/z wide, as in the lecture's oblate case.
    points[:, 1] *= 0.31
    return orient_outward(points, cells)


def torus_surface(major_segments: int = 30, minor_segments: int = 16) -> tuple[np.ndarray, np.ndarray]:
    major_radius, minor_radius = 1.45, 0.56
    vertices = []
    for i in range(major_segments):
        u = 2 * math.pi * i / major_segments
        for j in range(minor_segments):
            v = 2 * math.pi * j / minor_segments
            radial = major_radius + minor_radius * math.cos(v)
            vertices.append((radial * math.cos(u), minor_radius * math.sin(v), radial * math.sin(u)))
    triangles = []
    idx = lambda i, j: (i % major_segments) * minor_segments + (j % minor_segments)
    for i in range(major_segments):
        for j in range(minor_segments):
            triangles.extend(((idx(i, j), idx(i + 1, j), idx(i + 1, j + 1)), (idx(i, j), idx(i + 1, j + 1), idx(i, j + 1))))
    return orient_outward(np.asarray(vertices), np.asarray(triangles))


def rounded_box_sdf(point: np.ndarray, half_core: np.ndarray, radius: float) -> float:
    q = np.abs(point) - half_core
    return float(np.linalg.norm(np.maximum(q, 0.0)) + min(float(np.max(q)), 0.0) - radius)


def chair_field(point: np.ndarray) -> float:
    """Rounded block minus two z-directed cylinders: a genus-two chair/frame."""
    box = rounded_box_sdf(point, np.asarray((2.04, 1.02, 0.48)), 0.20)
    first = math.hypot(point[0] - 0.80, point[1]) - 0.53
    second = math.hypot(point[0] + 0.80, point[1]) - 0.53
    return max(box, -first, -second)


def marching_tetrahedra(
    field: Callable[[np.ndarray], float], bounds: tuple[tuple[float, float], ...], resolution: tuple[int, int, int]
) -> tuple[np.ndarray, np.ndarray]:
    """Extract a closed zero set without a third-party meshing dependency."""
    axes = [np.linspace(low, high, count) for (low, high), count in zip(bounds, resolution)]
    nx, ny, nz = resolution
    grid_points = np.empty((nx, ny, nz, 3), dtype=np.float64)
    values = np.empty((nx, ny, nz), dtype=np.float64)
    for i, x in enumerate(axes[0]):
        for j, y in enumerate(axes[1]):
            for k, z in enumerate(axes[2]):
                point = np.asarray((x, y, z), dtype=np.float64)
                grid_points[i, j, k] = point
                values[i, j, k] = field(point)

    # Six tetrahedra about the body diagonal (0, 6).  The shared diagonal is
    # identical in every cube, making the extraction watertight.
    cube_corners = ((0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1))
    tetrahedra = ((0, 1, 2, 6), (0, 2, 3, 6), (0, 3, 7, 6), (0, 7, 4, 6), (0, 4, 5, 6), (0, 5, 1, 6))
    vertices: list[np.ndarray] = []
    triangles: list[tuple[int, int, int]] = []
    edge_cache: dict[tuple[int, int], int] = {}

    def global_id(i: int, j: int, k: int) -> int:
        return (i * ny + j) * nz + k

    def edge_vertex(first: tuple[int, int, int], second: tuple[int, int, int]) -> int:
        a = global_id(*first)
        b = global_id(*second)
        key = (a, b) if a < b else (b, a)
        if key in edge_cache:
            return edge_cache[key]
        va, vb = values[first], values[second]
        alpha = va / (va - vb)
        point = grid_points[first] + alpha * (grid_points[second] - grid_points[first])
        edge_cache[key] = len(vertices)
        vertices.append(point)
        return edge_cache[key]

    def add_polygon(ids_inside: list[tuple[int, int, int]], ids_outside: list[tuple[int, int, int]]) -> None:
        if len(ids_inside) in (1, 3):
            source = ids_inside[0] if len(ids_inside) == 1 else ids_outside[0]
            targets = ids_outside if len(ids_inside) == 1 else ids_inside
            polygon = [edge_vertex(source, target) for target in targets]
            triangles.append(tuple(polygon))
            return
        # Two inside / two outside gives a quadrilateral.  The deterministic
        # split is internal to one tetrahedron and cannot open a mesh crack.
        a, b = ids_inside
        c, d = ids_outside
        ac, ad, bc, bd = edge_vertex(a, c), edge_vertex(a, d), edge_vertex(b, c), edge_vertex(b, d)
        triangles.extend(((ac, bc, bd), (ac, bd, ad)))

    for i in range(nx - 1):
        for j in range(ny - 1):
            for k in range(nz - 1):
                corners = [(i + dx, j + dy, k + dz) for dx, dy, dz in cube_corners]
                for tetrahedron in tetrahedra:
                    nodes = [corners[index] for index in tetrahedron]
                    inside = [node for node in nodes if values[node] < 0]
                    if not inside or len(inside) == 4:
                        continue
                    outside = [node for node in nodes if values[node] >= 0]
                    add_polygon(inside, outside)

    points = np.asarray(vertices, dtype=np.float64)
    cells = np.asarray(triangles, dtype=np.int32)
    # Local polygon order above is topologically consistent but may vary with
    # inside case.  Orient each face by a finite-difference outward gradient.
    epsilon = 1e-5
    for index, cell in enumerate(cells):
        p0, p1, p2 = points[cell]
        center = (p0 + p1 + p2) / 3.0
        gradient = np.asarray([
            field(center + np.eye(3)[axis] * epsilon) - field(center - np.eye(3)[axis] * epsilon)
            for axis in range(3)
        ]) / (2 * epsilon)
        if np.dot(np.cross(p1 - p0, p2 - p0), gradient) < 0:
            cells[index, 1], cells[index, 2] = cells[index, 2], cells[index, 1]
    return orient_outward(points, cells)


def surface_nets(
    field: Callable[[np.ndarray], float], bounds: tuple[tuple[float, float], ...], resolution: tuple[int, int, int]
) -> tuple[np.ndarray, np.ndarray]:
    """Extract a compact quad-dominant zero set with one vertex per active cell."""
    axes = [np.linspace(low, high, count) for (low, high), count in zip(bounds, resolution)]
    nx, ny, nz = resolution
    points_grid = np.empty((nx, ny, nz, 3), dtype=np.float64)
    values = np.empty((nx, ny, nz), dtype=np.float64)
    for i, x in enumerate(axes[0]):
        for j, y in enumerate(axes[1]):
            for k, z in enumerate(axes[2]):
                point = np.asarray((x, y, z), dtype=np.float64)
                points_grid[i, j, k] = point
                values[i, j, k] = field(point)

    corner_offsets = ((0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1))
    cube_edges = ((0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4), (0, 4), (1, 5), (2, 6), (3, 7))
    cell_vertices: dict[tuple[int, int, int], int] = {}
    vertices: list[np.ndarray] = []
    for i in range(nx - 1):
        for j in range(ny - 1):
            for k in range(nz - 1):
                nodes = [(i + di, j + dj, k + dk) for di, dj, dk in corner_offsets]
                samples = np.asarray([values[node] for node in nodes])
                if np.all(samples < 0) or np.all(samples >= 0):
                    continue
                intersections = []
                for first, second in cube_edges:
                    va, vb = samples[first], samples[second]
                    if (va < 0) == (vb < 0):
                        continue
                    alpha = va / (va - vb)
                    intersections.append(points_grid[nodes[first]] + alpha * (points_grid[nodes[second]] - points_grid[nodes[first]]))
                if intersections:
                    cell_vertices[(i, j, k)] = len(vertices)
                    vertices.append(np.mean(intersections, axis=0))

    quads: list[tuple[int, int, int, int]] = []
    def add_quad(cells_around: tuple[tuple[int, int, int], ...]) -> None:
        if all(cell in cell_vertices for cell in cells_around):
            quads.append(tuple(cell_vertices[cell] for cell in cells_around))

    # Each sign-changing grid edge is dual to one surface quad.
    for i in range(nx - 1):
        for j in range(1, ny - 1):
            for k in range(1, nz - 1):
                if (values[i, j, k] < 0) != (values[i + 1, j, k] < 0):
                    add_quad(((i, j - 1, k - 1), (i, j, k - 1), (i, j, k), (i, j - 1, k)))
    for i in range(1, nx - 1):
        for j in range(ny - 1):
            for k in range(1, nz - 1):
                if (values[i, j, k] < 0) != (values[i, j + 1, k] < 0):
                    add_quad(((i - 1, j, k - 1), (i - 1, j, k), (i, j, k), (i, j, k - 1)))
    for i in range(1, nx - 1):
        for j in range(1, ny - 1):
            for k in range(nz - 1):
                if (values[i, j, k] < 0) != (values[i, j, k + 1] < 0):
                    add_quad(((i - 1, j - 1, k), (i, j - 1, k), (i, j, k), (i - 1, j, k)))

    points = np.asarray(vertices, dtype=np.float64)
    triangles: list[tuple[int, int, int]] = []
    for index, quad in enumerate(quads):
        a, b, c, d = quad
        if index % 2:
            triangles.extend(((a, b, d), (b, c, d)))
        else:
            triangles.extend(((a, b, c), (a, c, d)))
    cells = np.asarray(triangles, dtype=np.int32)
    epsilon = 1e-5
    basis = np.eye(3)
    for index, cell in enumerate(cells):
        p0, p1, p2 = points[cell]
        center = (p0 + p1 + p2) / 3.0
        gradient = np.asarray([field(center + basis[axis] * epsilon) - field(center - basis[axis] * epsilon) for axis in range(3)]) / (2 * epsilon)
        if np.dot(np.cross(p1 - p0, p2 - p0), gradient) < 0:
            cells[index, 1], cells[index, 2] = cells[index, 2], cells[index, 1]
    return orient_outward(points, cells)


def chair_surface() -> tuple[np.ndarray, np.ndarray]:
    return surface_nets(
        chair_field,
        bounds=((-2.38, 2.38), (-1.38, 1.38), (-0.78, 0.78)),
        resolution=(29, 19, 13),
    )


def triangle_geometry(points: np.ndarray, cells: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    p0, p1, p2 = points[cells[:, 0]], points[cells[:, 1]], points[cells[:, 2]]
    orientation = np.cross(p1 - p0, p2 - p0)
    double_area = np.linalg.norm(orientation, axis=1)
    if np.min(double_area) <= 1e-12:
        raise RuntimeError("degenerate triangle encountered")
    return orientation, double_area, 0.5 * double_area


def assemble(points: np.ndarray, cells: np.ndarray) -> tuple[csc_matrix, np.ndarray]:
    vertex_count = points.shape[0]
    orientation, double_area, _ = triangle_geometry(points, cells)
    rows: list[int] = []
    cols: list[int] = []
    data: list[float] = []
    diagonal = np.zeros(vertex_count, dtype=np.float64)
    lumped_normals = np.zeros((vertex_count, 3), dtype=np.float64)
    p = points[cells]
    cot = np.empty((cells.shape[0], 3), dtype=np.float64)
    cot[:, 0] = np.einsum("ij,ij->i", p[:, 1] - p[:, 0], p[:, 2] - p[:, 0]) / double_area
    cot[:, 1] = np.einsum("ij,ij->i", p[:, 2] - p[:, 1], p[:, 0] - p[:, 1]) / double_area
    cot[:, 2] = np.einsum("ij,ij->i", p[:, 0] - p[:, 2], p[:, 1] - p[:, 2]) / double_area
    for local_opposite, (local_i, local_j) in enumerate(((1, 2), (2, 0), (0, 1))):
        weights = 0.5 * cot[:, local_opposite]
        ii, jj = cells[:, local_i], cells[:, local_j]
        rows.extend(ii.tolist()); cols.extend(jj.tolist()); data.extend((-weights).tolist())
        rows.extend(jj.tolist()); cols.extend(ii.tolist()); data.extend((-weights).tolist())
        np.add.at(diagonal, ii, weights); np.add.at(diagonal, jj, weights)
    rows.extend(np.arange(vertex_count).tolist()); cols.extend(np.arange(vertex_count).tolist()); data.extend(diagonal.tolist())
    stiffness = csc_matrix((data, (rows, cols)), shape=(vertex_count, vertex_count))
    contribution = orientation / 6.0
    for local in range(3):
        np.add.at(lumped_normals, cells[:, local], contribution)
    return stiffness, lumped_normals


def surface_area(points: np.ndarray, cells: np.ndarray) -> float:
    return float(np.sum(triangle_geometry(points, cells)[2]))


def triangle_quality(points: np.ndarray, cells: np.ndarray) -> np.ndarray:
    p = points[cells]
    squared_edges = np.sum((p[:, 1] - p[:, 0]) ** 2, axis=1) + np.sum((p[:, 2] - p[:, 1]) ** 2, axis=1) + np.sum((p[:, 0] - p[:, 2]) ** 2, axis=1)
    return (4.0 * np.sqrt(3.0) * triangle_geometry(points, cells)[2]) / squared_edges


def metrics(points: np.ndarray, cells: np.ndarray, energy_defect: float) -> np.ndarray:
    quality = triangle_quality(points, cells)
    return np.asarray((surface_area(points, cells), signed_volume(points, cells), float(np.min(quality)), float(np.percentile(quality, 5)), float(np.mean(quality)), energy_defect), dtype=np.float64)


def bgn_step(points: np.ndarray, cells: np.ndarray, dt: float) -> tuple[np.ndarray, float]:
    vertex_count = points.shape[0]
    stiffness, normals = assemble(points, cells)
    bx, by, bz = (diags(normals[:, axis], format="csc") for axis in range(3))
    coupling_t = bmat([[bx, by, bz]], format="csc")
    coupling = bmat([[bx], [by], [bz]], format="csc")
    stiffness_3 = block_diag((stiffness, stiffness, stiffness), format="csc")
    matrix = bmat([[coupling_t / dt, -stiffness], [stiffness_3, coupling]], format="csc")
    old_vector = np.concatenate((points[:, 0], points[:, 1], points[:, 2]))
    rhs = np.concatenate(((coupling_t @ old_vector) / dt, np.zeros(3 * vertex_count)))
    solution = spsolve(matrix, rhs)
    if not np.all(np.isfinite(solution)):
        raise RuntimeError("non-finite value returned by sparse solve")
    next_points = np.column_stack((solution[:vertex_count], solution[vertex_count:2 * vertex_count], solution[2 * vertex_count:3 * vertex_count]))
    curvature = solution[3 * vertex_count:]
    dissipation = float(curvature @ (stiffness @ curvature))
    defect = surface_area(next_points, cells) - surface_area(points, cells) + dt * dissipation
    return next_points, defect


def topology(cells: np.ndarray, vertex_count: int) -> tuple[int, int]:
    edge_counts: dict[tuple[int, int], int] = {}
    for cell in cells:
        for first, second in ((cell[0], cell[1]), (cell[1], cell[2]), (cell[2], cell[0])):
            edge = (int(min(first, second)), int(max(first, second)))
            edge_counts[edge] = edge_counts.get(edge, 0) + 1
    bad = sum(count != 2 for count in edge_counts.values())
    if bad:
        raise RuntimeError(f"mesh is not closed/manifold: {bad} edges do not have two incident faces")
    euler = vertex_count - len(edge_counts) + len(cells)
    genus = int(round((2 - euler) / 2))
    return euler, genus


def generate(case: Case) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    points, cells = case.mesh()
    euler, genus = topology(cells, len(points))
    print(f"{case.slug}: {len(points)} vertices, {len(cells)} triangles, chi={euler}, genus={genus}", flush=True)
    frames = [points.copy()]
    all_metrics = [metrics(points, cells, 0.0)]
    for step in range(case.steps):
        points, defect = bgn_step(points, cells, case.dt)
        frames.append(points.copy())
        all_metrics.append(metrics(points, cells, defect))
        if (step + 1) % max(1, case.steps // 8) == 0 or step + 1 == case.steps:
            current = all_metrics[-1]
            print(f"  step {step + 1:3d}/{case.steps}: area={current[0]:.9f} volume={current[1]:.9f} qmin={current[2]:.5f} defect={defect:.3e}", flush=True)
    times = np.arange(case.steps + 1, dtype=np.float64) * case.dt
    return cells, times, np.asarray(all_metrics), np.asarray(frames)


def validate(cells: np.ndarray, metrics_array: np.ndarray, frames: np.ndarray, dt: float) -> dict[str, float | int | bool]:
    areas, volumes = metrics_array[:, 0], metrics_array[:, 1]
    defects = metrics_array[1:, 5]
    area_increases = np.diff(areas)
    volume_relative_drift = np.max(np.abs(volumes / volumes[0] - 1.0))
    minimum_double_area = min(float(np.min(triangle_geometry(frame, cells)[1])) for frame in frames)
    euler, genus = topology(cells, frames.shape[1])
    positive_volumes = bool(np.all(volumes > 0))
    result: dict[str, float | int | bool] = {
        "vertex_count": int(frames.shape[1]), "triangle_count": int(cells.shape[0]), "frame_count": int(frames.shape[0]),
        "time_step": float(dt), "final_time": float(dt * (frames.shape[0] - 1)), "euler_characteristic": euler, "genus": genus,
        "initial_surface_area": float(areas[0]), "final_surface_area": float(areas[-1]), "max_area_increase": float(np.max(area_increases)),
        "max_energy_defect": float(np.max(defects)), "initial_volume": float(volumes[0]), "final_volume": float(volumes[-1]),
        "max_relative_volume_drift": float(volume_relative_drift), "minimum_triangle_quality": float(np.min(metrics_array[:, 2])),
        "minimum_double_triangle_area": minimum_double_area, "surface_area_monotone": bool(np.max(area_increases) <= 5e-9),
        "energy_inequality_satisfied": bool(np.max(defects) <= 5e-8), "orientation_preserved": positive_volumes and minimum_double_area > 1e-10,
    }
    if not result["surface_area_monotone"]:
        raise RuntimeError(f"surface area increased: {result['max_area_increase']}")
    if not result["energy_inequality_satisfied"]:
        raise RuntimeError(f"BGN energy inequality failed: {result['max_energy_defect']}")
    if not result["orientation_preserved"]:
        raise RuntimeError("mesh became degenerate or its global orientation changed")
    return result


def write_binary(path: Path, cells: np.ndarray, times: np.ndarray, metrics_array: np.ndarray, frames: np.ndarray, dt: float) -> None:
    header = struct.pack("<8sIIIIIIff", MAGIC, 1, frames.shape[1], cells.shape[0], frames.shape[0], len(METRIC_NAMES), 0, float(dt), float(times[-1]))
    with path.open("wb") as stream:
        stream.write(header)
        stream.write(np.asarray(cells, dtype="<u4").tobytes(order="C"))
        stream.write(np.asarray(times, dtype="<f4").tobytes(order="C"))
        stream.write(np.asarray(metrics_array, dtype="<f4").tobytes(order="C"))
        stream.write(np.asarray(frames, dtype="<f4").tobytes(order="C"))


def cases(density: str = "standard") -> list[Case]:
    fine = density == "fine"
    return [
        Case("cube", "立方体 → 圆润平衡形", "立方体", "讲稿原始动画：棱角被表面扩散逐步抹平。", "PDF 第 9 页 · BGN surface diffusion", (lambda: cube_surface(14)) if fine else cube_surface, 320, 5e-5, 5.5),
        Case("torus", "Clifford 环面 → 环面扩散", "环面", "固定拓扑的亏格 1 曲面，观察内外侧曲率差驱动的网格运动。", "受 PDF 第 36 页 Clifford torus 启发 · 此处重算 BGN surface diffusion", (lambda: torus_surface(42, 22)) if fine else torus_surface, 260, 2e-5, 5.8, -0.74, 0.32),
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=[case.slug for case in cases()] + ["all"], default="all")
    parser.add_argument("--density", choices=["standard", "fine"], default="standard")
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parents[1] / "trajectories")
    args = parser.parse_args()
    available_cases = cases(args.density)
    selected = available_cases if args.case == "all" else [case for case in available_cases if case.slug == args.case]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest_cases = []
    for case in selected:
        cells, times, metrics_array, frames = generate(case)
        diagnostics = validate(cells, metrics_array, frames, case.dt)
        suffix = "-fine" if args.density == "fine" else ""
        binary_path = args.output_dir / f"{case.slug}{suffix}.bin"
        diagnostic_path = args.output_dir / f"{case.slug}{suffix}.json"
        write_binary(binary_path, cells, times, metrics_array, frames, case.dt)
        payload = {
            "scheme": "BGN PFEM for three-dimensional surface diffusion", "equations": ["(3.11a) with explicit old-surface normal", "(3.11b)"],
            "metric_names": list(METRIC_NAMES), "slug": case.slug, "name": case.name, "short_name": case.short_name,
            "caption": case.caption, "source_note": case.source_note, **diagnostics,
        }
        diagnostic_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        web_binary = args.output_dir / f"{case.slug}-web.bin.gz"
        standard_variant = (
            {"trajectory": f"trajectories/{case.slug}-web.bin.gz", "fallbackTrajectory": f"trajectories/{case.slug}.bin", "diagnostics": f"trajectories/{case.slug}.json", "bytes": web_binary.stat().st_size, "compression": "gzip"}
            if web_binary.exists()
            else {"trajectory": f"trajectories/{case.slug}.bin", "diagnostics": f"trajectories/{case.slug}.json", "bytes": binary_path.stat().st_size}
        )
        variants = {"standard": standard_variant}
        refined_binary = args.output_dir / f"{case.slug}-fine.bin"
        refined_diagnostics = args.output_dir / f"{case.slug}-fine.json"
        if args.density == "standard" and refined_binary.exists() and refined_diagnostics.exists():
            variants["fine"] = (
                {"trajectory": f"trajectories/{case.slug}-web.bin.gz", "fallbackTrajectory": f"trajectories/{case.slug}.bin", "diagnostics": f"trajectories/{case.slug}-fine.json", "bytes": web_binary.stat().st_size, "compression": "gzip", "refine": True, "kind": "one-to-four display subdivision"}
                if web_binary.exists()
                else {"trajectory": f"trajectories/{case.slug}-fine.bin", "diagnostics": f"trajectories/{case.slug}-fine.json", "bytes": refined_binary.stat().st_size, "kind": "one-to-four display subdivision"}
            )
        manifest_cases.append({
            "slug": case.slug, "name": case.name, "shortName": case.short_name, "caption": case.caption, "sourceNote": case.source_note,
            "trajectory": standard_variant["trajectory"], "diagnostics": standard_variant["diagnostics"],
            "camera": {"distance": case.camera_distance, "yaw": case.camera_yaw, "pitch": case.camera_pitch},
            "bytes": standard_variant["bytes"], "genus": diagnostics["genus"], "flow": "surface-diffusion", "holdSeconds": 0.55, "playDuration": 12, "variants": variants,
        })
        print(json.dumps(payload, indent=2, ensure_ascii=False), flush=True)
        print(f"wrote {binary_path} ({binary_path.stat().st_size:,} bytes)", flush=True)
    if args.case == "all" and args.density == "standard":
        willmore_binary = args.output_dir / "genus-two.bin"
        willmore_diagnostics = args.output_dir / "genus-two.json"
        if willmore_binary.exists() and willmore_diagnostics.exists():
            genus_two = json.loads(willmore_diagnostics.read_text(encoding="utf-8"))
            willmore_web = args.output_dir / "genus-two-web.bin.gz"
            willmore_web_diagnostics = args.output_dir / "genus-two-web.json"
            willmore_standard = (
                {"trajectory": "trajectories/genus-two-web.bin.gz", "fallbackTrajectory": "trajectories/genus-two.bin", "diagnostics": "trajectories/genus-two-web.json", "bytes": willmore_web.stat().st_size, "compression": "gzip"}
                if willmore_web.exists() and willmore_web_diagnostics.exists()
                else {"trajectory": "trajectories/genus-two.bin", "diagnostics": "trajectories/genus-two.json", "bytes": willmore_binary.stat().st_size}
            )
            willmore_variants = {"standard": willmore_standard}
            willmore_refined = args.output_dir / "genus-two-fine.bin"
            willmore_refined_diagnostics = args.output_dir / "genus-two-fine.json"
            if willmore_refined.exists() and willmore_refined_diagnostics.exists():
                willmore_variants["fine"] = (
                    {"trajectory": "trajectories/genus-two-web.bin.gz", "fallbackTrajectory": "trajectories/genus-two.bin", "diagnostics": "trajectories/genus-two-fine.json", "bytes": willmore_web.stat().st_size, "compression": "gzip", "refine": True, "kind": "one-to-four display subdivision"}
                    if willmore_web.exists()
                    else {"trajectory": "trajectories/genus-two-fine.bin", "diagnostics": "trajectories/genus-two-fine.json", "bytes": willmore_refined.stat().st_size, "kind": "one-to-four display subdivision"}
                )
            manifest_cases.insert(1, {
                "slug": "genus-two", "name": genus_two["name"], "shortName": genus_two["short_name"],
                "caption": genus_two["caption"], "sourceNote": genus_two["source_note"],
                "trajectory": willmore_standard["trajectory"], "diagnostics": willmore_standard["diagnostics"],
                "camera": {"distance": 15.5, "yaw": -0.58, "pitch": 0.36}, "bytes": willmore_standard["bytes"],
                "genus": 2, "flow": "willmore", "holdSeconds": 1.8, "playDuration": 13, "variants": willmore_variants,
            })
        helfrich_binary = args.output_dir / "oblate.bin"
        helfrich_diagnostics = args.output_dir / "oblate.json"
        if helfrich_binary.exists() and helfrich_diagnostics.exists():
            oblate = json.loads(helfrich_diagnostics.read_text(encoding="utf-8"))
            helfrich_web = args.output_dir / "oblate-web.bin.gz"
            helfrich_standard = (
                {"trajectory": "trajectories/oblate-web.bin.gz", "fallbackTrajectory": "trajectories/oblate.bin", "diagnostics": "trajectories/oblate.json", "bytes": helfrich_web.stat().st_size, "compression": "gzip"}
                if helfrich_web.exists()
                else {"trajectory": "trajectories/oblate.bin", "diagnostics": "trajectories/oblate.json", "bytes": helfrich_binary.stat().st_size}
            )
            helfrich_variants = {"standard": helfrich_standard}
            helfrich_refined = args.output_dir / "oblate-fine.bin"
            helfrich_refined_diagnostics = args.output_dir / "oblate-fine.json"
            if helfrich_refined.exists() and helfrich_refined_diagnostics.exists():
                helfrich_variants["fine"] = (
                    {"trajectory": "trajectories/oblate-web.bin.gz", "fallbackTrajectory": "trajectories/oblate.bin", "diagnostics": "trajectories/oblate-fine.json", "bytes": helfrich_web.stat().st_size, "compression": "gzip", "refine": True, "kind": "one-to-four display subdivision"}
                    if helfrich_web.exists()
                    else {"trajectory": "trajectories/oblate-fine.bin", "diagnostics": "trajectories/oblate-fine.json", "bytes": helfrich_refined.stat().st_size, "kind": "one-to-four display subdivision"}
                )
            manifest_cases.append({
                "slug": "oblate", "name": oblate["name"], "shortName": oblate["short_name"],
                "caption": oblate["caption"], "sourceNote": oblate["source_note"],
                "trajectory": helfrich_standard["trajectory"], "diagnostics": helfrich_standard["diagnostics"],
                "camera": {"distance": 10.2, "yaw": -0.62, "pitch": 0.38}, "bytes": helfrich_standard["bytes"],
                "genus": 0, "flow": "helfrich", "holdSeconds": 1.2, "playDuration": 13, "variants": helfrich_variants,
            })
        manifest = {"version": 1, "default": "cube", "cases": manifest_cases}
        (args.output_dir / "manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
