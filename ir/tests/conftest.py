"""Schema test helpers — loads aral-fn.schema.json for validation."""

import json
from pathlib import Path

IR_DIR = Path(__file__).parent.parent                # ir/
SCHEMA_PATH = IR_DIR / "aral-fn.schema.json"
EXAMPLES_DIR = IR_DIR / "examples"
FIXTURES_DIR = Path(__file__).parent / "fixtures"


def load_schema() -> dict:
    return json.loads(SCHEMA_PATH.read_text())


def load_fixture(name: str) -> dict:
    return json.loads((FIXTURES_DIR / name).read_text())


def load_example(name: str) -> dict:
    return json.loads((EXAMPLES_DIR / name).read_text())
