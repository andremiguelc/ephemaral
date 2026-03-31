"""Invariant compiler + diagnostic test helpers."""

import subprocess
from datetime import datetime
from pathlib import Path

PROOFS_DIR = Path(__file__).parent.parent              # proofs/
EPHEMARAL_BIN = PROOFS_DIR / ".lake" / "build" / "bin" / "ephemaral"
FIXTURES_DIR = Path(__file__).parent / "fixtures"
SNAPSHOTS_DIR = Path(__file__).parent / "snapshots"


def run_aral_compile(fixture_name: str) -> subprocess.CompletedProcess:
    """Run ephemaral in compile-only mode on a fixture .aral file."""
    fixture_path = FIXTURES_DIR / fixture_name
    assert fixture_path.exists(), f"Fixture not found: {fixture_path}"
    assert EPHEMARAL_BIN.exists(), f"Binary not found: {EPHEMARAL_BIN}. Run: cd proofs && lake build ephemaral"
    return subprocess.run(
        [str(EPHEMARAL_BIN), str(fixture_path)],
        capture_output=True,
        text=True,
        timeout=30,
    )


def compile_fixture(fixture_name: str) -> str:
    """Run ephemaral compile-only on fixture and return stdout. Fails if exit code != 0."""
    result = run_aral_compile(fixture_name)
    assert result.returncode == 0, f"ephemaral compile failed on {fixture_name}:\n{result.stderr}"
    return result.stdout


def run_ephemaral(json_path: Path, aral_path, debug: bool = False) -> subprocess.CompletedProcess:
    """Run ephemaral CLI on a JSON + one or more .aral files.
    aral_path can be a single Path or a list of Paths."""
    assert EPHEMARAL_BIN.exists(), f"Binary not found: {EPHEMARAL_BIN}. Run: cd proofs && lake build ephemaral"
    cmd = [str(EPHEMARAL_BIN)]
    if debug:
        cmd.append("--debug")
    cmd.append(str(json_path))
    if isinstance(aral_path, (list, tuple)):
        cmd.extend(str(p) for p in aral_path)
    else:
        cmd.append(str(aral_path))
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=30,
    )


def write_snapshot(name: str, content: str) -> None:
    """Write a diagnostic snapshot for LLM evaluation.
    Filename includes date+time stamp so we can tell which snapshots are current."""
    SNAPSHOTS_DIR.mkdir(exist_ok=True)
    stamp = datetime.now().strftime("%Y-%m-%d-%H%M")
    (SNAPSHOTS_DIR / f"{name}-{stamp}.txt").write_text(content)
