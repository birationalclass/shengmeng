#!/usr/bin/env python3
"""Generate the paper's biconcave 4x4x1 ellipsoid Helfrich trajectory.

This is the closed-surface, zero-spontaneous-curvature specialization of
Zhao's fully discrete relaxed-MDR Helfrich system (5.7).  The two global
Lagrange multipliers impose the discrete area- and volume-velocity
constraints.  Connectivity remains fixed for the whole trajectory.  Passing
``--latitudes 33 --longitudes 80`` gives exactly the paper's 2,562 vertices
and 5,120 triangles; the web trajectory uses a lighter mesh so that both
display variants remain practical to download.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.sparse import bmat, csc_matrix
from scipy.sparse.linalg import spsolve

from generate_bgn_trajectory import (
    orient_outward,
    signed_volume,
    sphere_topology,
    surface_area,
    topology,
    triangle_geometry,
    triangle_quality,
)
from generate_willmore_trajectory import (
    assemble_operators,
    flatten,
    initial_curvature,
    lower_order_rhs,
    unflatten,
    willmore_energy,
    write_binary,
)


def oblate_ellipsoid(latitudes: int = 33, longitudes: int = 80) -> tuple[np.ndarray, np.ndarray]:
    """Triangulate a 4x4x1 oblate ellipsoid with the short axis along y."""
    def profile(phi: float) -> tuple[float, float]:
        return 2.0 * np.cos(phi), 2.0 * np.sin(phi)

    points, cells = sphere_topology(profile, latitudes=latitudes, longitudes=longitudes)
    points[:, 1] *= 0.25
    return orient_outward(points, cells)


def helfrich_step(
    points: np.ndarray,
    cells: np.ndarray,
    curvature: np.ndarray,
    dt: float,
    alpha: float,
) -> tuple[np.ndarray, np.ndarray, float, float]:
    """One step of (5.7) with kappa-bar=0 and both global constraints."""
    vertex_count = len(points)
    (
        mass,
        mass_3,
        stiffness_3,
        normal_mass,
        coupling,
        relaxed_mdr,
        areas,
        normals,
        gradients,
    ) = assemble_operators(points, cells, alpha)

    rhs_w = lower_order_rhs(points, cells, curvature, areas, normals, gradients)
    rhs_k = (stiffness_3 @ flatten(points)) / dt
    n3, n = 3 * vertex_count, vertex_count
    z33 = csc_matrix((n3, n3))
    z3n = csc_matrix((n3, n))
    zn3 = csc_matrix((n, n3))
    znn = csc_matrix((n, n))
    base = bmat(
        [
            [normal_mass, -stiffness_3, z3n, relaxed_mdr],
            [-stiffness_3, -mass_3 / dt, z3n, z33],
            [zn3, zn3, znn, coupling],
            [relaxed_mdr, z33, coupling.T, z33],
        ],
        format="csc",
    )

    # coupling.T @ 1 contains the mass-lumped integral of the element normal
    # at every vector-valued nodal basis function: m_i * nu_{h,p}(q_i).
    q_volume_w = np.asarray(coupling.T @ np.ones(n)).reshape(-1)
    lumped_normal = unflatten(q_volume_w, n)
    vertex_normal = lumped_normal / mass[:, None]
    theta_area = np.einsum("ij,ij->i", curvature, vertex_normal)
    q_area_w = flatten(theta_area[:, None] * lumped_normal)

    zero_tail = np.zeros(base.shape[0] - n3)
    q_area = np.concatenate((q_area_w, zero_tail))
    q_volume = np.concatenate((q_volume_w, zero_tail))
    constraints = csc_matrix(np.column_stack((q_area, q_volume)))
    matrix = bmat([[base, constraints], [constraints.T, csc_matrix((2, 2))]], format="csc")
    rhs = np.concatenate((rhs_w, rhs_k, np.zeros(n), np.zeros(n3), np.zeros(2)))
    solution = spsolve(matrix, rhs)
    if not np.all(np.isfinite(solution)):
        raise RuntimeError("Helfrich linear system returned a non-finite value")

    velocity = unflatten(solution[:n3], n)
    next_curvature = unflatten(solution[n3 : 2 * n3], n)
    next_points = points + dt * velocity
    next_points -= np.mean(next_points, axis=0)
    lambda_area, lambda_volume = solution[-2:]
    return next_points, next_curvature, float(lambda_area), float(lambda_volume)


def frame_metrics(
    points: np.ndarray,
    cells: np.ndarray,
    curvature: np.ndarray,
    mass: np.ndarray,
    energy_delta: float,
) -> np.ndarray:
    quality = triangle_quality(points, cells)
    return np.asarray(
        (
            willmore_energy(curvature, mass),
            signed_volume(points, cells),
            float(np.min(quality)),
            surface_area(points, cells),
            float(np.mean(quality)),
            energy_delta,
        ),
        dtype=np.float64,
    )


def generate(steps: int, save_every: int, dt: float, alpha: float, latitudes: int, longitudes: int):
    points, cells = oblate_ellipsoid(latitudes, longitudes)
    euler, genus = topology(cells, len(points))
    if euler != 2 or genus != 0:
        raise RuntimeError("unexpected oblate mesh topology")
    mass, _, stiffness_3, *_ = assemble_operators(points, cells, alpha)
    curvature = initial_curvature(points, mass, stiffness_3)
    initial_area, initial_volume = surface_area(points, cells), signed_volume(points, cells)
    previous_energy = willmore_energy(curvature, mass)
    frames = [points.copy()]
    all_metrics = [frame_metrics(points, cells, curvature, mass, 0.0)]
    times = [0.0]
    multipliers: list[tuple[float, float]] = []
    print(f"oblate-helfrich: {len(points)} vertices, {len(cells)} triangles, chi={euler}, genus={genus}", flush=True)

    for step in range(1, steps + 1):
        points, curvature, lambda_area, lambda_volume = helfrich_step(points, cells, curvature, dt, alpha)
        mass, *_ = assemble_operators(points, cells, alpha)
        energy = willmore_energy(curvature, mass)
        multipliers.append((lambda_area, lambda_volume))
        if step % save_every == 0 or step == steps:
            frames.append(points.copy())
            all_metrics.append(frame_metrics(points, cells, curvature, mass, energy - previous_energy))
            times.append(step * dt)
        previous_energy = energy
        if step % max(1, steps // 8) == 0 or step == steps:
            print(
                f"  step {step}/{steps}: E={energy:.8f} "
                f"eA={(surface_area(points, cells)/initial_area-1):+.3e} "
                f"eV={(signed_volume(points, cells)/initial_volume-1):+.3e} "
                f"qmin={np.min(triangle_quality(points, cells)):.5f}",
                flush=True,
            )
    return cells, np.asarray(times), np.asarray(all_metrics), np.asarray(frames), np.asarray(multipliers)


def validate(cells, times, metrics, frames, multipliers, steps, save_every, dt, alpha, latitudes, longitudes):
    energies, volumes, qualities, areas = metrics[:, 0], metrics[:, 1], metrics[:, 2], metrics[:, 3]
    euler, genus = topology(cells, frames.shape[1])
    initial_orientation = triangle_geometry(frames[0], cells)[0]
    orientation_preserved = True
    minimum_double_area = np.inf
    for frame in frames:
        orientation, double_area, _ = triangle_geometry(frame, cells)
        minimum_double_area = min(minimum_double_area, float(np.min(double_area)))
        orientation_preserved &= bool(np.all(np.einsum("ij,ij->i", orientation, initial_orientation) > 0))
    area_error = np.abs(areas / areas[0] - 1)
    volume_error = np.abs(volumes / volumes[0] - 1)
    return {
        "scheme": "linearly implicit relaxed-MDR PFEM for area- and volume-constrained Helfrich flow",
        "source_equations": ["arXiv:2608.07244, equation (5.7), Example 7"],
        "slug": "oblate",
        "name": "扁椭球 → 双凹红细胞形",
        "short_name": "扁椭球 → 红细胞",
        "caption": "论文中的 4×4×1 扁椭球在保面积、保体积 Helfrich 流下形成双凹平衡形。",
        "source_note": "PDF 第 41 页 · constrained relaxed-MDR Helfrich flow · κ̄=0 · α=10",
        "vertex_count": int(frames.shape[1]),
        "triangle_count": int(len(cells)),
        "frame_count": int(len(frames)),
        "computed_step_count": int(steps),
        "time_step": float(dt),
        "saved_step_stride": int(save_every),
        "final_time": float(times[-1]),
        "alpha": float(alpha),
        "spontaneous_curvature": 0.0,
        "mesh_latitudes": int(latitudes),
        "mesh_longitudes": int(longitudes),
        "euler_characteristic": int(euler),
        "genus": int(genus),
        "initial_energy": float(energies[0]),
        "final_energy": float(energies[-1]),
        "max_energy_increase_saved_frames": float(np.max(np.diff(energies))),
        "energy_monotone_saved_frames": bool(np.all(np.diff(energies) <= 1e-8)),
        "initial_area": float(areas[0]),
        "final_area": float(areas[-1]),
        "maximum_relative_area_change": float(np.max(area_error)),
        "initial_volume": float(volumes[0]),
        "final_volume": float(volumes[-1]),
        "maximum_relative_volume_change": float(np.max(volume_error)),
        "minimum_triangle_quality": float(np.min(qualities)),
        "minimum_double_triangle_area": float(minimum_double_area),
        "orientation_preserved": bool(orientation_preserved),
        "maximum_absolute_area_multiplier": float(np.max(np.abs(multipliers[:, 0]))),
        "maximum_absolute_volume_multiplier": float(np.max(np.abs(multipliers[:, 1]))),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=200)
    parser.add_argument("--save-every", type=int, default=1)
    parser.add_argument("--dt", type=float, default=1e-3)
    parser.add_argument("--alpha", type=float, default=10.0)
    parser.add_argument("--latitudes", type=int, default=20)
    parser.add_argument("--longitudes", type=int, default=30)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent.parent / "trajectories" / "oblate.bin")
    args = parser.parse_args()
    if args.steps <= 0 or args.save_every <= 0 or args.steps % args.save_every:
        raise SystemExit("steps must be positive and divisible by save-every")
    if args.latitudes < 4 or args.longitudes < 8:
        raise SystemExit("mesh resolution is too small")
    cells, times, metrics, frames, multipliers = generate(
        args.steps, args.save_every, args.dt, args.alpha, args.latitudes, args.longitudes
    )
    diagnostics = validate(
        cells, times, metrics, frames, multipliers, args.steps, args.save_every,
        args.dt, args.alpha, args.latitudes, args.longitudes
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    write_binary(args.output, cells, times, metrics, frames, args.dt)
    args.output.with_suffix(".json").write_text(json.dumps(diagnostics, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(diagnostics, ensure_ascii=False, indent=2), flush=True)
    print(f"wrote {args.output} ({args.output.stat().st_size:,} bytes)", flush=True)


if __name__ == "__main__":
    main()
