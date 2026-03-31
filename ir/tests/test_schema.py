"""Layer 2: Schema validation tests — Aral-fn JSON against aral-fn.schema.json."""

import pytest
from jsonschema import validate, ValidationError
from conftest import load_schema, load_fixture, load_example, EXAMPLES_DIR


@pytest.fixture(scope="module")
def schema():
    return load_schema()


# ============================================================
# Valid fixtures
# ============================================================

class TestValidFixtures:
    def test_valid_minimal(self, schema):
        validate(load_fixture("valid_minimal.json"), schema)

    def test_valid_ite(self, schema):
        validate(load_fixture("valid_ite.json"), schema)

    def test_valid_round(self, schema):
        validate(load_fixture("valid_round.json"), schema)

    def test_valid_typed_params(self, schema):
        validate(load_fixture("valid_typed_params.json"), schema)


# ============================================================
# Existing ir/examples/ must all validate
# ============================================================

class TestExistingExamples:
    @pytest.fixture(scope="class")
    def example_files(self):
        return sorted(EXAMPLES_DIR.glob("*.json"))

    def test_examples_exist(self, example_files):
        assert len(example_files) > 0, "No examples found in ir/examples/"

    def test_all_examples_valid(self, schema, example_files):
        for f in example_files:
            data = load_example(f.name)
            validate(data, schema)


# ============================================================
# Invalid fixtures — must raise ValidationError
# ============================================================

class TestInvalidFixtures:
    def test_missing_name(self, schema):
        with pytest.raises(ValidationError, match="'name' is a required property"):
            validate(load_fixture("invalid_no_name.json"), schema)

    def test_missing_assigns(self, schema):
        with pytest.raises(ValidationError, match="'assigns' is a required property"):
            validate(load_fixture("invalid_no_assigns.json"), schema)

    def test_bad_arith_op(self, schema):
        with pytest.raises(ValidationError):
            validate(load_fixture("invalid_bad_op.json"), schema)

    def test_bad_round_mode(self, schema):
        with pytest.raises(ValidationError):
            validate(load_fixture("invalid_bad_mode.json"), schema)

    def test_extra_properties(self, schema):
        with pytest.raises(ValidationError, match="Additional properties are not allowed"):
            validate(load_fixture("invalid_extra_props.json"), schema)

    def test_typed_params_missing_type(self, schema):
        with pytest.raises(ValidationError, match="'type' is a required property"):
            validate(load_fixture("invalid_typed_params_missing_type.json"), schema)
