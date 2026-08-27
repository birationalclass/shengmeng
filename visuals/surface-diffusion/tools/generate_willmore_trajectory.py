#!/usr/bin/env python3
"""Generate the PDF's genus-two relaxed-MDR Willmore trajectory.

This implements the closed-surface, zero-spontaneous-curvature specialization
of the linearly implicit system (4.8)/(5.1) in Zhao, arXiv:2608.07244.  The
initial surface is exactly the paper's boundary of a 7 x 4 x 1 cuboid after
removing two 2 x 2 x 1 through-holes.  Connectivity remains fixed.
"""

from __future__ import annotations

import argparse
import json
import struct
from pathlib import Path

import numpy as np
from scipy.sparse import bmat, block_diag, csc_matrix, diags
from scipy.sparse.linalg import spsolve

from generate_bgn_trajectory import (
    MAGIC,
    orient_outward,
    signed_volume,
    surface_area,
    topology,
    triangle_geometry,
    triangle_quality,
)


def cuboid_with_two_square_holes(
    step: float = 0.5,
    face_phases: tuple[int, int, int, int, int, int] = (0, 0, 0, 0, 0, 0),
) -> tuple[np.ndarray, np.ndarray]:
    """Boundary of a 7x4x1 cuboid minus two 2x2x1 square through-holes."""
    xs = np.arange(-3.5, 3.5 + step * 0.25, step)
    ys = np.arange(-2.0, 2.0 + step * 0.25, step)
    zs = np.arange(-0.5, 0.5 + step * 0.25, step)
    nx, ny, nz = len(xs) - 1, len(ys) - 1, len(zs) - 1
    solid = np.ones((nx, ny, nz), dtype=bool)
    for i in range(nx):
        cx = (xs[i] + xs[i + 1]) / 2
        for j in range(ny):
            cy = (ys[j] + ys[j + 1]) / 2
            if abs(cy) < 1.0 and (abs(cx - 1.5) < 1.0 or abs(cx + 1.5) < 1.0):
                solid[i, j, :] = False

    vertices: list[tuple[float, float, float]] = []
    vertex_index: dict[tuple[int, int, int], int] = {}
    triangles: list[tuple[int, int, int]] = []

    def index_of(node: tuple[int, int, int]) -> int:
        if node not in vertex_index:
            vertex_index[node] = len(vertices)
            vertices.append((float(xs[node[0]]), float(ys[node[1]]), float(zs[node[2]])))
        return vertex_index[node]

    # For each outward coordinate direction: neighbour offset, an ordered
    # face-corner cycle whose right-hand normal points out of the solid cell,
    # and a checkerboard phase.  The phase is configurable so triangulation
    # sensitivity of the non-smooth polyhedral initial surface can be audited
    # without changing its geometry, vertex count, or triangle count.
    faces = (
        ((-1, 0, 0), ((0, 0, 0), (0, 0, 1), (0, 1, 1), (0, 1, 0)), face_phases[0]),
        ((1, 0, 0), ((1, 0, 0), (1, 1, 0), (1, 1, 1), (1, 0, 1)), face_phases[1]),
        ((0, -1, 0), ((0, 0, 0), (1, 0, 0), (1, 0, 1), (0, 0, 1)), face_phases[2]),
        ((0, 1, 0), ((0, 1, 0), (0, 1, 1), (1, 1, 1), (1, 1, 0)), face_phases[3]),
        ((0, 0, -1), ((0, 0, 0), (0, 1, 0), (1, 1, 0), (1, 0, 0)), face_phases[4]),
        ((0, 0, 1), ((0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1)), face_phases[5]),
    )
    for i in range(nx):
        for j in range(ny):
            for k in range(nz):
                if not solid[i, j, k]:
                    continue
                for (di, dj, dk), corners, phase in faces:
                    ni, nj, nk = i + di, j + dj, k + dk
                    neighbour_solid = 0 <= ni < nx and 0 <= nj < ny and 0 <= nk < nz and solid[ni, nj, nk]
                    if neighbour_solid:
                        continue
                    quad = [index_of((i + ci, j + cj, k + ck)) for ci, cj, ck in corners]
                    # Checkerboard diagonal prevents a global directional bias.
                    if (i + j + k + phase) % 2:
                        triangles.extend(((quad[0], quad[1], quad[3]), (quad[1], quad[2], quad[3])))
                    else:
                        triangles.extend(((quad[0], quad[1], quad[2]), (quad[0], quad[2], quad[3])))
    points = np.asarray(vertices)
    cells = np.asarray(triangles)
    return orient_outward(points, cells)


def finite_element_geometry(points: np.ndarray, cells: np.ndarray):
    p = points[cells]
    orientation = np.cross(p[:, 1] - p[:, 0], p[:, 2] - p[:, 0])
    double_area = np.linalg.norm(orientation, axis=1)
    if np.min(double_area) <= 1e-12:
        raise RuntimeError("degenerate triangle")
    normals = orientation / double_area[:, None]
    areas = double_area / 2
    gradients = np.empty((len(cells), 3, 3), dtype=np.float64)
    gradients[:, 0] = np.cross(normals, p[:, 2] - p[:, 1]) / double_area[:, None]
    gradients[:, 1] = np.cross(normals, p[:, 0] - p[:, 2]) / double_area[:, None]
    gradients[:, 2] = np.cross(normals, p[:, 1] - p[:, 0]) / double_area[:, None]
    return areas, normals, gradients


def assemble_operators(points: np.ndarray, cells: np.ndarray, alpha: float):
    vertex_count = len(points)
    areas, normals, gradients = finite_element_geometry(points, cells)
    mass = np.zeros(vertex_count, dtype=np.float64)
    rows: list[int] = []
    cols: list[int] = []
    data: list[float] = []
    for local in range(3):
        np.add.at(mass, cells[:, local], areas / 3)
        for other in range(3):
            values = areas * np.einsum("ij,ij->i", gradients[:, local], gradients[:, other])
            rows.extend(cells[:, local].tolist())
            cols.extend(cells[:, other].tolist())
            data.extend(values.tolist())
    stiffness = csc_matrix((data, (rows, cols)), shape=(vertex_count, vertex_count))
    stiffness_3 = block_diag((stiffness, stiffness, stiffness), format="csc")
    mass_3 = block_diag((diags(mass), diags(mass), diags(mass)), format="csc")

    lumped_normal = np.zeros((vertex_count, 3), dtype=np.float64)
    normal_blocks = np.zeros((vertex_count, 3, 3), dtype=np.float64)
    tangent_blocks = np.zeros((vertex_count, 3, 3), dtype=np.float64)
    eye = np.eye(3)
    weights = areas / 3
    outer = np.einsum("fi,fj->fij", normals, normals)
    tangent = eye[None, :, :] - outer
    for local in range(3):
        np.add.at(lumped_normal, cells[:, local], weights[:, None] * normals)
        np.add.at(normal_blocks, cells[:, local], weights[:, None, None] * outer)
        np.add.at(tangent_blocks, cells[:, local], weights[:, None, None] * tangent)
    size = 3 * vertex_count
    vertices = np.arange(vertex_count)[:, None, None]
    row_indices = np.broadcast_to(vertices + vertex_count * np.arange(3)[None, :, None], normal_blocks.shape).ravel()
    col_indices = np.broadcast_to(vertices + vertex_count * np.arange(3)[None, None, :], normal_blocks.shape).ravel()
    normal_mass = csc_matrix((normal_blocks.ravel(), (row_indices, col_indices)), shape=(size, size))
    tangent_mass = csc_matrix((tangent_blocks.ravel(), (row_indices, col_indices)), shape=(size, size))
    normal_coupling = bmat([[diags(lumped_normal[:, 0]), diags(lumped_normal[:, 1]), diags(lumped_normal[:, 2])]], format="csc")
    relaxed_mdr = tangent_mass + alpha * stiffness_3
    return mass, mass_3, stiffness_3, normal_mass, normal_coupling, relaxed_mdr, areas, normals, gradients


def flatten(points: np.ndarray) -> np.ndarray:
    return np.concatenate((points[:, 0], points[:, 1], points[:, 2]))


def unflatten(vector: np.ndarray, vertex_count: int) -> np.ndarray:
    return np.column_stack((vector[:vertex_count], vector[vertex_count:2 * vertex_count], vector[2 * vertex_count:3 * vertex_count]))


def lower_order_rhs(points: np.ndarray, cells: np.ndarray, curvature: np.ndarray, areas: np.ndarray, normals: np.ndarray, gradients: np.ndarray) -> np.ndarray:
    """Assemble R_h^m(test) for zero spontaneous curvature."""
    vertex_count = len(points)
    result = np.zeros((vertex_count, 3), dtype=np.float64)
    identity = np.eye(3)
    k_values = curvature[cells]
    gradient_k = np.einsum("fla,flb->fab", k_values, gradients)
    divergence_k = np.trace(gradient_k, axis1=1, axis2=2)
    projection = identity[None, :, :] - np.einsum("fi,fj->fij", normals, normals)
    mean_squared_k = np.mean(np.sum(k_values * k_values, axis=2), axis=1)
    deformation = (
        np.einsum("ia,flj->flaij", identity, gradients)
        + np.einsum("fli,ja->flaij", gradients, identity)
    )
    deformed_projection = np.einsum("flaik,fkj->flaij", deformation, projection)
    contraction = np.einsum("fji,flaij->fla", gradient_k, deformed_projection)
    values = (
        divergence_k[:, None, None] * gradients
        - contraction
        + 0.5 * mean_squared_k[:, None, None] * gradients
    )
    for local in range(3):
        np.add.at(result, cells[:, local], areas[:, None] * values[:, local])
    return flatten(result)


def initial_curvature(points: np.ndarray, mass: np.ndarray, stiffness_3: csc_matrix) -> np.ndarray:
    return unflatten(-(stiffness_3 @ flatten(points)) / np.tile(mass, 3), len(points))


def willmore_energy(curvature: np.ndarray, mass: np.ndarray) -> float:
    return float(0.5 * np.sum(mass[:, None] * curvature * curvature))


def willmore_step(points: np.ndarray, cells: np.ndarray, curvature: np.ndarray, dt: float, alpha: float):
    vertex_count = len(points)
    mass, mass_3, stiffness_3, normal_mass, coupling, relaxed_mdr, areas, normals, gradients = assemble_operators(points, cells, alpha)
    rhs_w = lower_order_rhs(points, cells, curvature, areas, normals, gradients)
    rhs_k = (stiffness_3 @ flatten(points)) / dt
    n3, n = 3 * vertex_count, vertex_count
    z33 = csc_matrix((n3, n3)); z3n = csc_matrix((n3, n)); zn3 = csc_matrix((n, n3)); znn = csc_matrix((n, n))
    matrix = bmat([
        [normal_mass, -stiffness_3, z3n, relaxed_mdr],
        [-stiffness_3, -mass_3 / dt, z3n, z33],
        [zn3, zn3, znn, coupling],
        [relaxed_mdr, z33, coupling.T, z33],
    ], format="csc")
    rhs = np.concatenate((rhs_w, rhs_k, np.zeros(n), np.zeros(n3)))
    solution = spsolve(matrix, rhs)
    if not np.all(np.isfinite(solution)):
        raise RuntimeError("Willmore linear system returned a non-finite value")
    velocity = unflatten(solution[:n3], n)
    next_curvature = unflatten(solution[n3:2 * n3], n)
    next_points = points + dt * velocity
    next_points -= np.mean(next_points, axis=0)
    return next_points, next_curvature


def frame_metrics(points: np.ndarray, cells: np.ndarray, curvature: np.ndarray, mass: np.ndarray, energy_delta: float) -> np.ndarray:
    quality = triangle_quality(points, cells)
    return np.asarray((
        willmore_energy(curvature, mass), signed_volume(points, cells), float(np.min(quality)), surface_area(points, cells), float(np.mean(quality)), energy_delta
    ), dtype=np.float64)


def write_binary(path: Path, cells: np.ndarray, times: np.ndarray, metrics: np.ndarray, frames: np.ndarray, dt: float) -> None:
    header = struct.pack("<8sIIIIIIff", MAGIC, 1, frames.shape[1], cells.shape[0], frames.shape[0], 6, 0, float(dt), float(times[-1]))
    with path.open("wb") as stream:
        stream.write(header)
        stream.write(np.asarray(cells, dtype="<u4").tobytes())
        stream.write(np.asarray(times, dtype="<f4").tobytes())
        stream.write(np.asarray(metrics, dtype="<f4").tobytes())
        stream.write(np.asarray(frames, dtype="<f4").tobytes())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=500)
    parser.add_argument("--dt", type=float, default=1e-3)
    parser.add_argument("--alpha", type=float, default=10.0)
    parser.add_argument("--save-every", type=int, default=2)
    parser.add_argument("--mesh-step", type=float, default=0.5)
    parser.add_argument("--face-phases", default="000000")
    parser.add_argument(
        "--startup-steps", type=int, default=20,
        help="number of initial nominal intervals split into smaller substeps",
    )
    parser.add_argument(
        "--startup-factor", type=int, default=4,
        help="substeps per startup interval (the substep is dt/startup-factor)",
    )
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "trajectories" / "genus-two.bin")
    args = parser.parse_args()

    if len(args.face_phases) != 6 or any(bit not in "01" for bit in args.face_phases):
        raise SystemExit("face-phases must contain exactly six binary digits")
    if args.startup_steps < 0 or args.startup_steps > args.steps or args.startup_factor < 1:
        raise SystemExit("startup-steps must lie in [0, steps] and startup-factor must be positive")
    face_phases = tuple(int(bit) for bit in args.face_phases)
    points, cells = cuboid_with_two_square_holes(args.mesh_step, face_phases)
    euler, genus = topology(cells, len(points))
    mass, _, stiffness_3, *_ = assemble_operators(points, cells, args.alpha)
    curvature = initial_curvature(points, mass, stiffness_3)
    frames = [points.copy()]
    metric_rows = [frame_metrics(points, cells, curvature, mass, 0.0)]
    times = [0.0]
    previous_energy = metric_rows[-1][0]
    print(f"genus-two: {len(points)} vertices, {len(cells)} triangles, chi={euler}, genus={genus}", flush=True)
    linear_solve_count = 0
    for step in range(1, args.steps + 1):
        substep_count = args.startup_factor if step <= args.startup_steps else 1
        substep_dt = args.dt / substep_count
        for _ in range(substep_count):
            points, curvature = willmore_step(points, cells, curvature, substep_dt, args.alpha)
            linear_solve_count += 1
        mass, *_ = assemble_operators(points, cells, args.alpha)
        current = frame_metrics(points, cells, curvature, mass, 0.0)
        current[5] = current[0] - previous_energy
        previous_energy = current[0]
        if step % args.save_every == 0 or step == args.steps:
            frames.append(points.copy()); metric_rows.append(current.copy()); times.append(step * args.dt)
        if step % max(1, args.steps // 10) == 0 or step == args.steps:
            print(f"  step {step}/{args.steps}: E={current[0]:.8f} area={current[3]:.8f} volume={current[1]:.8f} qmin={current[2]:.5f}", flush=True)

    frames_array = np.asarray(frames)
    metrics_array = np.asarray(metric_rows)
    energy_increases = np.diff(metrics_array[:, 0])
    minimum_double_area = min(float(np.min(triangle_geometry(frame, cells)[1])) for frame in frames_array)
    edges = np.unique(
        np.sort(np.vstack((cells[:, [0, 1]], cells[:, [1, 2]], cells[:, [2, 0]])), axis=1),
        axis=0,
    )
    edge_to_median_ratios = np.asarray([
        float(np.max(lengths) / np.median(lengths))
        for lengths in (
            np.linalg.norm(frame[edges[:, 0]] - frame[edges[:, 1]], axis=1)
            for frame in frames_array
        )
    ])
    maximum_edge_to_median_ratio = float(np.max(edge_to_median_ratios))
    startup_end_time = args.startup_steps * args.dt
    startup_frame_mask = np.asarray(times) <= startup_end_time + 1e-12
    maximum_startup_edge_to_median_ratio = float(np.max(edge_to_median_ratios[startup_frame_mask]))
    diagnostics = {
        "scheme": "linearly implicit relaxed-MDR PFEM for Willmore flow",
        "source_equations": ["arXiv:2608.07244, equations (4.8) and (5.1)"],
        "slug": "genus-two", "name": "方正双孔框 → 8 字 Willmore 曲面", "short_name": "双孔框 → 8 字",
        "caption": "论文中的 7×4×1 方正双孔框在 relaxed-MDR Willmore 流下先快速圆角，再形成亏格 2 的 8 字曲面。",
        "source_note": "PDF 第 28 页 · relaxed-MDR Willmore flow · α=10 · 前 0.02 四分启动步",
        "vertex_count": len(points), "triangle_count": len(cells), "frame_count": len(frames), "computed_step_count": linear_solve_count,
        "nominal_step_count": args.steps,
        "time_step": args.dt, "saved_step_stride": args.save_every, "final_time": args.steps * args.dt, "alpha": args.alpha,
        "startup_steps": args.startup_steps, "startup_factor": args.startup_factor,
        "startup_time_step": args.dt / args.startup_factor, "startup_end_time": startup_end_time,
        "mesh_step": args.mesh_step,
        "triangulation": "direction-phased checkerboard",
        "face_phases": args.face_phases,
        "euler_characteristic": euler, "genus": genus, "initial_energy": float(metrics_array[0, 0]), "final_energy": float(metrics_array[-1, 0]),
        "max_energy_increase_saved_frames": float(np.max(energy_increases)), "energy_monotone_saved_frames": bool(np.max(energy_increases) <= 1e-7),
        "initial_volume": float(metrics_array[0, 1]), "final_volume": float(metrics_array[-1, 1]),
        "maximum_relative_volume_change": float(np.max(np.abs(metrics_array[:, 1] / metrics_array[0, 1] - 1))),
        "minimum_triangle_quality": float(np.min(metrics_array[:, 2])), "minimum_double_triangle_area": minimum_double_area,
        "maximum_edge_to_median_ratio": maximum_edge_to_median_ratio,
        "maximum_startup_edge_to_median_ratio": maximum_startup_edge_to_median_ratio,
        "orientation_preserved": bool(np.all(metrics_array[:, 1] > 0) and minimum_double_area > 1e-10),
    }
    if not np.all(np.isfinite(frames_array)) or not np.all(np.isfinite(metrics_array)):
        raise RuntimeError("non-finite Willmore trajectory state")
    if euler != -2 or genus != 2:
        raise RuntimeError(f"unexpected topology: chi={euler}, genus={genus}")
    if not diagnostics["energy_monotone_saved_frames"]:
        raise RuntimeError("saved-state Willmore energy is not monotone")
    if not diagnostics["orientation_preserved"] or minimum_double_area <= 1e-6:
        raise RuntimeError("triangle orientation or nondegeneracy check failed")
    if maximum_edge_to_median_ratio >= 2.5:
        raise RuntimeError(
            "mesh-spike guard failed: maximum edge / median edge "
            f"is {maximum_edge_to_median_ratio:.6f}"
        )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    write_binary(args.output, cells, np.asarray(times), metrics_array, frames_array, args.dt * args.save_every)
    args.output.with_suffix(".json").write_text(json.dumps(diagnostics, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(diagnostics, ensure_ascii=False, indent=2), flush=True)
    print(f"wrote {args.output} ({args.output.stat().st_size:,} bytes)", flush=True)


if __name__ == "__main__":
    main()
