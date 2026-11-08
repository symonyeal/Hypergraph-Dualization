"""Evidence paths never replace an earlier run, including competing writers."""

import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
import block_probe as bp  # noqa: E402


def test_existing_log_is_preserved(tmp_path, monkeypatch):
    log, out = tmp_path / "run.log", tmp_path / "run.json"
    log.write_text("prior evidence")
    monkeypatch.setattr(sys, "argv", ["block_probe", "gk", "1", "guard", "--out", str(out), "--log", str(log)])
    with pytest.raises(FileExistsError):
        bp.main()
    assert log.read_text() == "prior evidence"
    assert not out.exists()


def test_competing_output_is_preserved(tmp_path, monkeypatch):
    out = tmp_path / "run.json"
    monkeypatch.setattr(sys, "argv", ["block_probe", "gk", "1", "guard", "--out", str(out)])

    def run(*args, **kwargs):
        out.write_text("competing evidence")
        return SimpleNamespace(stdout=json.dumps({"kind": "summary", "n": 8, "delta": 2}) + "\n")

    monkeypatch.setattr(bp.subprocess, "run", run)
    with pytest.raises(FileExistsError):
        bp.main()
    assert out.read_text() == "competing evidence"
