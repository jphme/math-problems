#!/usr/bin/env python3
"""Regression test for flush edges passing a later reflex boundary vertex."""
from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path

import erdos634_exact_search as searcher


BASE = Path(__file__).resolve().parent
WITNESS = BASE / "long_edge_reflex_witness.json"


def point(raw):
    return (F(raw[0]), F(raw[1]))


def cycle(raw):
    return tuple(point(p) for p in raw)


def reconstruct_state(search, data):
    state = searcher.normalize_state((search.target,), translation=False)
    for raw_triangle in data["path"]:
        triangle = cycle(raw_triangle)
        choice = search.choose_corner(state)
        assert choice is not None, "the deterministic search must select a corner"
        component_index, corner_index = choice
        component = state[component_index]
        placements = {
            searcher.normalize_cycle(candidate)
            for candidate in search.enumerate_placements(component, corner_index)
        }
        assert searcher.normalize_cycle(triangle) in placements, (
            "each witness-path tile must be generated at the deterministic corner"
        )
        assert searcher.triangle_contained(triangle, component), (
            "each witness-path tile must lie in the selected component"
        )
        replacement = searcher.subtract_triangle(component, triangle)
        assert replacement is not None, "path subtraction must succeed"
        state = searcher.normalize_state(
            state[:component_index]
            + tuple(replacement)
            + state[component_index + 1:],
            translation=False,
        )
    return state


def main() -> None:
    data = json.loads(WITNESS.read_text())
    search = searcher.ExactTilingSearch(
        (5, 3, 7), (21, 21, 33), 33, progress_every=0
    )

    reconstructed = reconstruct_state(search, data)
    expected = searcher.normalize_state(
        tuple(cycle(component) for component in data["state"]),
        translation=False,
    )
    assert reconstructed == expected, "the witness state must be reachable"

    component = cycle(data["component"])
    triangle = searcher.normalize_cycle(cycle(data["triangle"]))
    corner = point(data["corner"][0])
    placements = {
        searcher.normalize_cycle(t)
        for t in search.enumerate_placements(component, component.index(corner))
    }

    assert searcher.triangle_contained(cycle(data["triangle"]), component)
    assert triangle in placements, "the length-7 flush placement was omitted"
    assert len(placements) == 22
    print("LONG_EDGE_REFLEX_REGRESSION_OK")
    print("reachable depth:", data["depth"])
    print("ray length:", data["ray_length"])
    print("tile-edge length:", data["tile_edge_length"])
    print("placements at corner:", len(placements))


if __name__ == "__main__":
    main()
