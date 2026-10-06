# Migration helpers

Used for the before/after runs in `docs/assessment/*-migration-*.md`.

- `jsonl_tee_shim.py`: a pass-through for a JSON Lines service. Point a
  caller's binary setting at it, set `SHIM_REAL` to the real binary and
  `SHIM_LOG` to a file, and every request and response line is recorded
  (`REQ ...` / `RES ...`). Run the same caller once per binary and diff the logs.
- `run_pluto_notebook.jl`: `julia tools/migration/run_pluto_notebook.jl NOTEBOOK.jl`
  runs a Pluto notebook headlessly, in dependency order, and prints how many
  cells errored. (Running a notebook file as a plain script is not equivalent:
  cell order and Pluto's string handling differ.)
