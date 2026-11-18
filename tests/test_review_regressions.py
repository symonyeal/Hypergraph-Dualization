"""Boundary and annotation defects found in the November source review."""
import pytest

from fka.hypergraph import Hypergraph
from fka.properties import analyse, is_read_once
from fka.transversal import is_dual_oracle


def test_oracle_rejects_different_ground_sets():
    with pytest.raises(ValueError, match="same ground set"):
        is_dual_oracle(Hypergraph.empty(1), Hypergraph.from_sets(2, [[]]))


def test_read_once_requires_a_sperner_family_on_active_support():
    redundant = Hypergraph.from_sets(3, [[0], [0, 1]])
    assert not is_read_once(redundant)
    assert not analyse(redundant, graph_classes=False).read_once
    assert is_read_once(Hypergraph.from_sets(3, [[0], [1]]))


@pytest.mark.parametrize("algorithm,default,alternative", [
    ("fka", "degree_sum", "leftmost"),
    ("fkb", "most_frequent", "degree_sum"),
])
def test_cli_keeps_outputs_for_distinct_split_rules(
    algorithm, default, alternative, tmp_path
):
    from fka.cli import main as fka_main
    from fkb.cli import main as fkb_main

    main = fka_main if algorithm == "fka" else fkb_main
    for rule in (default, alternative):
        assert main(["run", "k3", "--no-annotate", "--out", str(tmp_path),
                     "--split-rule", rule]) == 0
    exports = list(tmp_path.glob("*.json"))
    assert len(exports) == 2
    assert any(alternative in p.stem for p in exports)
