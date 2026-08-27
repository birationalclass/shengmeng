#!/usr/bin/env python3
"""Generate the browser trajectory for the BGN surface-diffusion visualizer.

This is a direct assembly of the fully discrete linear BGN scheme shown on
slide 8/38 of ``sp电子科大.pdf``.  On every old polyhedral surface S^m we solve

    <(X^{m+1}-X^m)/dt . n^m, phi>_h - <grad H, grad phi> = 0,
    <H n^m, eta>_h + <grad X^{m+1}, grad eta> = 0.

Piecewise-linear surface finite elements, the cotangent stiffness matrix, and
the triangle-wise mass-lumped normal coupling are used.  The implicit
tangential motion is therefore part of the solve; there is no remeshing and no
shape interpolation.
"""

from __future__ import annotations

import argparse
import json
import struct
from pathlib import Path

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


def cube_surface(subdivisions: int, half_extent: float = 1.0) -> tuple[np.ndarray, np.ndarray]:
    """Return a consistently oriented conforming triangulation of a cube."""
    if subdivisions < 2:
        raise ValueError("subdivisions must be at least 2")

    a = float(half_extent)
    faces = (
        # origin, u-vector, v-vector; cross(u, v) points outward.
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
                point = origin + (i / subdivisions) * u_vector + (j / subdivisions) * v_vector
                grid[i, j] = index_of(point)

        for i in range(subdivisions):
            for j in range(subdivisions):
                a0 = int(grid[i, j])
                a1 = int(grid[i + 1, j])
                a2 = int(grid[i + 1, j + 1])
                a3 = int(grid[i, j + 1])
                # Alternate the square diagonal to avoid a directional bias.
                if (i + j) % 2 == 0:
                    triangles.extend(((a0, a1, a2), (a0, a2, a3)))
                else:
                    triangles.extend(((a0, a1, a3), (a1, a2, a3)))

    points = np.asarray(vertices, dtype=np.float64)
    cells = np.asarray(triangles, dtype=np.int32)
    signed = signed_volume(points, cells)
    if signed <= 0:
        raise RuntimeError(f"cube orientation is not outward (signed volume {signed})")
    return points, cells


def triangle_geometry(points: np.ndarray, cells: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    p0 = points[cells[:, 0]]
    p1 = points[cells[:, 1]]
    p2 = points[cells[:, 2]]
    orientation = np.cross(p1 - p0, p2 - p0)
    double_area = np.linalg.norm(orientation, axis=1)
    if np.min(double_area) <= 1e-12:
        raise RuntimeError("degenerate triangle encountered")
    return orientation, double_area, 0.5 * double_area


def assemble(points: np.ndarray, cells: np.ndarray) -> tuple[csc_matrix, np.ndarray]:
    """Assemble stiffness S and mass-lumped normal vectors b_i."""
    vertex_count = points.shape[0]
    orientation, double_area, _ = triangle_geometry(points, cells)

    rows: list[int] = []
    cols: list[int] = []
    data: list[float] = []
    diagonal = np.zeros(vertex_count, dtype=np.float64)
    lumped_normals = np.zeros((vertex_count, 3), dtype=np.float64)

    p = points[cells]
    # cot(angle at local vertex k) = dot(edge1, edge2) / |edge1 x edge2|
    cot = np.empty((cells.shape[0], 3), dtype=np.float64)
    cot[:, 0] = np.einsum("ij,ij->i", p[:, 1] - p[:, 0], p[:, 2] - p[:, 0]) / double_area
    cot[:, 1] = np.einsum("ij,ij->i", p[:, 2] - p[:, 1], p[:, 0] - p[:, 1]) / double_area
    cot[:, 2] = np.einsum("ij,ij->i", p[:, 0] - p[:, 2], p[:, 1] - p[:, 2]) / double_area

    # Each cotangent belongs to the edge opposite its angle.
    for local_opposite, (local_i, local_j) in enumerate(((1, 2), (2, 0), (0, 1))):
        weights = 0.5 * cot[:, local_opposite]
        ii = cells[:, local_i]
        jj = cells[:, local_j]
        rows.extend(ii.tolist())
        cols.extend(jj.tolist())
        data.extend((-weights).tolist())
        rows.extend(jj.tolist())
        cols.extend(ii.tolist())
        data.extend((-weights).tolist())
        np.add.at(diagonal, ii, weights)
        np.add.at(diagonal, jj, weights)

    rows.extend(np.arange(vertex_count).tolist())
    cols.extend(np.arange(vertex_count).tolist())
    data.extend(diagonal.tolist())
    stiffness = csc_matrix((data, (rows, cols)), shape=(vertex_count, vertex_count))

    # area/3 * unit normal = orientation/6 on every incident triangle.
    contribution = orientation / 6.0
    for local in range(3):
        np.add.at(lumped_normals, cells[:, local], contribution)
    return stiffness, lumped_normals


def signed_volume(points: np.ndarray, cells: np.ndarray) -> float:
    p0 = points[cells[:, 0]]
    p1 = points[cells[:, 1]]
    p2 = points[cells[:, 2]]
    return float(np.sum(np.einsum("ij,ij->i", p0, np.cross(p1, p2))) / 6.0)


def surface_area(points: np.ndarray, cells: np.ndarray) -> float:
    return float(np.sum(triangle_geometry(points, cells)[2]))


def triangle_quality(points: np.ndarray, cells: np.ndarray) -> np.ndarray:
    p = points[cells]
    squared_edges = (
        np.sum((p[:, 1] - p[:, 0]) ** 2, axis=1)
        + np.sum((p[:, 2] - p[:, 1]) ** 2, axis=1)
        + np.sum((p[:, 0] - p[:, 2]) ** 2, axis=1)
    )
    area = triangle_geometry(points, cells)[2]
    return (4.0 * np.sqrt(3.0) * area) / squared_edges


def metrics(points: np.ndarray, cells: np.ndarray, energy_defect: float) -> np.ndarray:
    quality = triangle_quality(points, cells)
    return np.asarray(
        (
            surface_area(points, cells),
            signed_volume(points, cells),
            float(np.min(quality)),
            float(np.percentile(quality, 5)),
            float(np.mean(quality)),
            float(energy_defect),
        ),
        dtype=np.float64,
    )


def bgn_step(points: np.ndarray, cells: np.ndarray, dt: float) -> tuple[np.ndarray, np.ndarray, float]:
    """Solve one fully discrete BGN surface-diffusion step."""
    vertex_count = points.shape[0]
    stiffness, normals = assemble(points, cells)
    bx = diags(normals[:, 0], format="csc")
    by = diags(normals[:, 1], format="csc")
    bz = diags(normals[:, 2], format="csc")
    coupling_t = bmat([[bx, by, bz]], format="csc")
    coupling = bmat([[bx], [by], [bz]], format="csc")
    stiffness_3 = block_diag((stiffness, stiffness, stiffness), format="csc")
    matrix = bmat(
        [
            [coupling_t / dt, -stiffness],
            [stiffness_3, coupling],
        ],
        format="csc",
    )

    old_vector = np.concatenate((points[:, 0], points[:, 1], points[:, 2]))
    rhs = np.concatenate(((coupling_t @ old_vector) / dt, np.zeros(3 * vertex_count)))
    solution = spsolve(matrix, rhs)
    if not np.all(np.isfinite(solution)):
        raise RuntimeError("non-finite value returned by sparse solve")

    next_points = np.column_stack(
        (
            solution[:vertex_count],
            solution[vertex_count : 2 * vertex_count],
            solution[2 * vertex_count : 3 * vertex_count],
        )
    )
    curvature = solution[3 * vertex_count :]
    dissipation = float(curvature @ (stiffness @ curvature))
    defect = surface_area(next_points, cells) - surface_area(points, cells) + dt * dissipation
    return next_points, curvature, defect


def generate(subdivisions: int, steps: int, dt: float) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    points, cells = cube_surface(subdivisions)
    frames = [points.copy()]
    all_metrics = [metrics(points, cells, 0.0)]
    for step in range(steps):
        points, _, defect = bgn_step(points, cells, dt)
        frames.append(points.copy())
        all_metrics.append(metrics(points, cells, defect))
        if (step + 1) % max(1, steps // 8) == 0 or step + 1 == steps:
            current = all_metrics[-1]
            print(
                f"step {step + 1:3d}/{steps}: area={current[0]:.10f} "
                f"volume={current[1]:.10f} qmin={current[2]:.5f} defect={defect:.3e}",
                flush=True,
            )
    times = np.arange(steps + 1, dtype=np.float64) * dt
    return cells, times, np.asarray(all_metrics), np.asarray(frames)


def validate(cells: np.ndarray, metrics_array: np.ndarray, frames: np.ndarray, dt: float) -> dict[str, float | int | bool]:
    areas = metrics_array[:, 0]
    volumes = metrics_array[:, 1]
    defects = metrics_array[1:, 5]
    area_increases = np.diff(areas)
    volume_relative_drift = np.max(np.abs(volumes / volumes[0] - 1.0))
    centroid = np.mean(frames[-1], axis=0)
    radii = np.linalg.norm(frames[-1] - centroid, axis=1)
    orientation_min = min(
        float(np.min(np.einsum("ij,ij->i", np.cross(
            frame[cells[:, 1]] - frame[cells[:, 0]],
            frame[cells[:, 2]] - frame[cells[:, 0]],
        ), frame[cells[:, 0]] - np.mean(frame, axis=0))))
        for frame in frames
    )
    result: dict[str, float | int | bool] = {
        "vertex_count": int(frames.shape[1]),
        "triangle_count": int(cells.shape[0]),
        "frame_count": int(frames.shape[0]),
        "time_step": float(dt),
        "final_time": float(dt * (frames.shape[0] - 1)),
        "initial_surface_area": float(areas[0]),
        "final_surface_area": float(areas[-1]),
        "max_area_increase": float(np.max(area_increases)),
        "max_energy_defect": float(np.max(defects)),
        "initial_volume": float(volumes[0]),
        "final_volume": float(volumes[-1]),
        "max_relative_volume_drift": float(volume_relative_drift),
        "minimum_triangle_quality": float(np.min(metrics_array[:, 2])),
        "final_radius_coefficient_of_variation": float(np.std(radii) / np.mean(radii)),
        "minimum_outward_orientation_test": float(orientation_min),
        "surface_area_monotone": bool(np.max(area_increases) <= 5e-10),
        "energy_inequality_satisfied": bool(np.max(defects) <= 5e-9),
        "orientation_preserved": bool(orientation_min > 0),
    }
    if not result["surface_area_monotone"]:
        raise RuntimeError(f"surface area increased: {result['max_area_increase']}")
    if not result["energy_inequality_satisfied"]:
        raise RuntimeError(f"BGN energy inequality failed: {result['max_energy_defect']}")
    if not result["orientation_preserved"]:
        raise RuntimeError("triangle orientation inverted")
    return result


def write_binary(path: Path, cells: np.ndarray, times: np.ndarray, metrics_array: np.ndarray, frames: np.ndarray, dt: float) -> None:
    header = struct.pack(
        "<8sIIIIIIff",
        MAGIC,
        1,
        frames.shape[1],
        cells.shape[0],
        frames.shape[0],
        len(METRIC_NAMES),
        0,
        float(dt),
        float(times[-1]),
    )
    with path.open("wb") as stream:
        stream.write(header)
        stream.write(np.asarray(cells, dtype="<u4").tobytes(order="C"))
        stream.write(np.asarray(times, dtype="<f4").tobytes(order="C"))
        stream.write(np.asarray(metrics_array, dtype="<f4").tobytes(order="C"))
        stream.write(np.asarray(frames, dtype="<f4").tobytes(order="C"))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--subdivisions", type=int, default=10)
    parser.add_argument("--steps", type=int, default=320)
    parser.add_argument("--dt", type=float, default=5e-5)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "trajectory.bin")
    args = parser.parse_args()

    cells, times, metrics_array, frames = generate(args.subdivisions, args.steps, args.dt)
    diagnostics = validate(cells, metrics_array, frames, args.dt)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    write_binary(args.output, cells, times, metrics_array, frames, args.dt)

    diagnostics_path = args.output.with_name("trajectory-diagnostics.json")
    diagnostics_payload = {
        "scheme": "BGN PFEM for three-dimensional surface diffusion",
        "equations": ["(3.11a) with explicit old-surface normal", "(3.11b)"],
        "metric_names": list(METRIC_NAMES),
        **diagnostics,
    }
    diagnostics_path.write_text(json.dumps(diagnostics_payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(diagnostics_payload, indent=2))
    print(f"wrote {args.output} ({args.output.stat().st_size:,} bytes)")


if __name__ == "__main__":
    main()
