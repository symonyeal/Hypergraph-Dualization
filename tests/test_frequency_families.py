"""Regression for the Witt template used in the composition search."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from frequency_families import substitute, templates  # noqa: E402


def test_witt_template_uses_the_declared_ground_set():
    n, C, D = templates()["w11"]
    assert n == 11
    assert len(C) == 66
    assert C == D
    assert all(e < 1 << n for e in C)
    a, b, ec, ed = substitute((n, C, D), [(0, 0, 1, 1)] * n)
    assert a == b
    assert ec == ed == pytest.approx(5 / 11)
