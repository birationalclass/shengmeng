# Linear: mandatory resource safety

- Read `RESOURCE_SAFETY.md` and `resource-policy.json` before running a compiler. The user reported repeated system memory exhaustion on 2026-10-11; machine usability takes priority over proof throughput.
- Use `lean_runner.run_file` for every local Lean compile, proof experiment, type check and axiom audit. Existing `build.py`, `audit.py` and the private compiler use this entry point. Do not launch direct `lean`, parallel `lake build`, unbounded subprocesses, or extra proof agents to bypass it.
- Keep one compiler at a time, 8 GiB job memory, 2 Lean threads, CPU at most 25%, and a 20-minute timeout. Check system RAM/commit headroom. Do not raise limits automatically; optimize/split the proof or audit.
- A busy compiler means skip duplicate heartbeat work. A resource hold means inspect the recorded failure and fix its cause before retrying. Do not remove holds or repeat unchanged failing sources automatically.
- Resource-stopped, crashed or partially compiled jobs are not verified. Preserve saved sources and verification records. Only complete successful compile/type/axiom evidence permits a new mathematical checkpoint or publication.
- Keep the exact original theorem hypotheses, open status and manuscript numbering. These safeguards do not complete Lemmas4.1/4.2 or the main theorem.
- Publish only `birationalclass/shengmeng` main `formalization/linear`; retain existing frozen releases and unrelated changes. No workflow edits or OS-wide settings changes.
- Since 2026-10-14, use the D-drive task staging recorded in `research/d-drive-staging-current.json`: `work/d-drive-staging-20261014/compile-stage`, `tools`, and `publish`. Do not create new C-drive temporary source or full-site publication checkouts. Existing C task directories are historical copies; Windows root files are outside this task. The installed Codex Python runtime may remain on C. Resource limits and `lean_runner.run_file` stay mandatory.
