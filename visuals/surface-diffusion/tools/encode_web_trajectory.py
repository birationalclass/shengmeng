#!/usr/bin/env python3
"""Create a lossless, gzip-compressed trajectory optimized for web delivery.

Positions after the first frame are stored as bitwise XORs of consecutive
float32 states.  This is exactly reversible (unlike numeric delta
quantization) and makes gzip substantially more effective.  An optional frame
stride reduces only saved display states; the final state is always retained.
"""

from __future__ import annotations

import argparse
import gzip
import json
import struct
from pathlib import Path

import numpy as np

from generate_bgn_trajectory import MAGIC
from refine_trajectory import read_binary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--frame-stride", type=int, default=1)
    parser.add_argument("--diagnostics-output", type=Path)
    args = parser.parse_args()
    if args.frame_stride < 1:
        raise SystemExit("frame-stride must be positive")

    _, dt, total_time, cells, times, metrics, frames = read_binary(args.input)
    selected = np.arange(0, len(frames), args.frame_stride, dtype=np.int64)
    if selected[-1] != len(frames) - 1:
        selected = np.append(selected, len(frames) - 1)
    times, metrics, frames = times[selected], metrics[selected], frames[selected].copy()

    # Preserve the first frame verbatim and XOR every later float's IEEE-754
    # bit pattern with the corresponding float in the preceding saved frame.
    encoded = frames.view(np.uint32)
    encoded[1:] ^= encoded[:-1].copy()
    header = struct.pack(
        "<8sIIIIIIff", MAGIC, 1, frames.shape[1], cells.shape[0], frames.shape[0],
        metrics.shape[1], 2, float(dt), float(total_time),
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("wb") as raw_stream:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw_stream, compresslevel=9, mtime=0) as stream:
            stream.write(header)
            stream.write(np.asarray(cells, dtype="<u4").tobytes())
            stream.write(np.asarray(times, dtype="<f4").tobytes())
            stream.write(np.asarray(metrics, dtype="<f4").tobytes())
            stream.write(np.asarray(frames, dtype="<f4").tobytes())

    if args.diagnostics_output:
        diagnostics = json.loads(args.input.with_suffix(".json").read_text(encoding="utf-8"))
        diagnostics["frame_count"] = int(len(frames))
        diagnostics["saved_step_stride"] = int(diagnostics.get("saved_step_stride", 1) * args.frame_stride)
        diagnostics["web_encoding"] = "lossless consecutive-frame float32 XOR plus gzip"
        args.diagnostics_output.write_text(json.dumps(diagnostics, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    print(json.dumps({
        "input": str(args.input), "output": str(args.output),
        "frames": int(len(frames)), "bytes": args.output.stat().st_size,
        "frame_stride": int(args.frame_stride), "encoding": "xor-float32+gzip",
    }, ensure_ascii=False))


if __name__ == "__main__":
    main()
