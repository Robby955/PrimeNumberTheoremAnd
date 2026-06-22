#!/usr/bin/env python3
"""Run the local theorem-surface fidelity checker from this worktree."""

from pathlib import Path
import runpy


CHECKER = Path("/Users/robsneiderman/Projects/theorempath/scripts/statement_fidelity_check.py")

if not CHECKER.exists():
    raise SystemExit(f"missing checker: {CHECKER}")

runpy.run_path(str(CHECKER), run_name="__main__")
