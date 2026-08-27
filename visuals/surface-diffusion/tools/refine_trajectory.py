#!/usr/bin/env python3
"""Create an exact 1-to-4 display subdivision of a saved PFEM trajectory.

Every original edge gets one shared midpoint at every frame.  The refined
triangles cover exactly the same piecewise-linear surface, so area, volume,
energy and time states are unchanged; only the visible triangulation is
denser.  This is intentionally labeled as display refinement in diagnostics.
"""

from __future__ import annotations

import argparse
import json
import struct
from pathlib import Path

import numpy as np

from generate_bgn_trajectory import MAGIC, triangle_quality


def read_binary(path: Path):
    payload = path.read_bytes()
    header = struct.unpack("<8sIIIIIIff", payload[:40])
    magic, version, vertices, triangles, frames, metrics, reserved, dt, total_time = header
    if magic != MAGIC or version != 1:
        raise RuntimeError("unsupported trajectory")
    offset = 40
    cells = np.frombuffer(payload, dtype="<u4", count=triangles * 3, offset=offset).reshape(triangles, 3).copy(); offset += triangles * 3 * 4
    times = np.frombuffer(payload, dtype="<f4", count=frames, offset=offset).copy(); offset += frames * 4
    metric_rows = np.frombuffer(payload, dtype="<f4", count=frames * metrics, offset=offset).reshape(frames, metrics).copy(); offset += frames * metrics * 4
    positions = np.frombuffer(payload, dtype="<f4", count=frames * vertices * 3, offset=offset).reshape(frames, vertices, 3).copy()
    return reserved, dt, total_time, cells, times, metric_rows, positions


def refine(cells: np.ndarray, frames: np.ndarray):
    edges: dict[tuple[int, int], int] = {}
    refined_cells = []
    for a, b, c in cells:
        mids = []
        for first, second in ((a, b), (b, c), (c, a)):
            key = (int(min(first, second)), int(max(first, second)))
            if key not in edges:
                edges[key] = frames.shape[1] + len(edges)
            mids.append(edges[key])
        ab, bc, ca = mids
        refined_cells.extend(((a, ab, ca), (ab, b, bc), (ca, bc, c), (ab, bc, ca)))
    refined_frames = np.empty((frames.shape[0], frames.shape[1] + len(edges), 3), dtype=np.float32)
    refined_frames[:, :frames.shape[1]] = frames
    for (first, second), index in edges.items():
        refined_frames[:, index] = 0.5 * (frames[:, first] + frames[:, second])
    return np.asarray(refined_cells, dtype=np.uint32), refined_frames


def write_binary(path: Path, reserved: int, dt: float, total_time: float, cells: np.ndarray, times: np.ndarray, metrics: np.ndarray, frames: np.ndarray):
    header = struct.pack("<8sIIIIIIff", MAGIC, 1, frames.shape[1], cells.shape[0], frames.shape[0], metrics.shape[1], reserved, dt, total_time)
    with path.open("wb") as stream:
        stream.write(header); stream.write(np.asarray(cells, dtype="<u4").tobytes()); stream.write(np.asarray(times, dtype="<f4").tobytes()); stream.write(np.asarray(metrics, dtype="<f4").tobytes()); stream.write(np.asarray(frames, dtype="<f4").tobytes())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--frame-stride", type=int, default=1, help="keep every nth saved source frame; the final frame is always kept")
    args = parser.parse_args()
    if args.frame_stride < 1:
        raise SystemExit("frame-stride must be positive")
    reserved, dt, total_time, cells, times, metrics, frames = read_binary(args.input)
    if args.frame_stride > 1:
        selected = np.arange(0, len(frames), args.frame_stride, dtype=np.int64)
        if selected[-1] != len(frames) - 1:
            selected = np.append(selected, len(frames) - 1)
        times, metrics, frames = times[selected], metrics[selected], frames[selected]
    refined_cells, refined_frames = refine(cells, frames)
    for index, frame in enumerate(refined_frames):
        metrics[index, 2] = float(np.min(triangle_quality(frame, refined_cells)))
    write_binary(args.output, reserved, dt, total_time, refined_cells, times, metrics, refined_frames)
    source_diagnostics = args.input.with_suffix(".json")
    diagnostics = json.loads(source_diagnostics.read_text(encoding="utf-8"))
    diagnostics.update({
        "base_vertex_count": diagnostics["vertex_count"], "base_triangle_count": diagnostics["triangle_count"],
        "vertex_count": int(refined_frames.shape[1]), "triangle_count": int(refined_cells.shape[0]),
        "frame_count": int(refined_frames.shape[0]),
        "minimum_triangle_quality": float(np.min(metrics[:, 2])), "display_refinement": "one-to-four shared-edge midpoint subdivision",
        "geometry_identical_to_standard_variant": True,
        "display_frame_stride_from_standard": int(args.frame_stride),
    })
    if "saved_step_stride" in diagnostics:
        diagnostics["saved_step_stride"] = int(diagnostics["saved_step_stride"] * args.frame_stride)
    args.output.with_suffix(".json").write_text(json.dumps(diagnostics, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"input": str(args.input), "output": str(args.output), "vertices": refined_frames.shape[1], "triangles": refined_cells.shape[0], "bytes": args.output.stat().st_size}, ensure_ascii=False))


if __name__ == "__main__":
    main()
