#!/usr/bin/env python3
"""Guard: the docbuild sub-project must resolve the same toolchain and Mathlib as the root.

`docbuild/` depends on `../`, so it compiles the project's own sources. If it resolves a
different Mathlib, the site build compiles current sources against a stale Mathlib and fails
on names that do not exist there yet — while ordinary CI stays green, because ordinary CI
never enters `docbuild/`.

That has happened twice across toolchain bumps, so it is checked rather than remembered.

Note on the nested `docbuild/lean-toolchain`: it cannot simply be deleted. `lake update`
regenerates it from the resolved dependency graph, and does so with the correct value. The
stale toolchain and the stale manifest were never two mistakes — both are what a *missing*
`cd docbuild && lake update` looks like. So this guard compares rather than forbids, and the
remedy for every failure below is the same single command.

Run with: python3 scripts/check_docbuild_sync.py
"""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
REMEDY = "Regenerate with: cd docbuild && lake update"


def revs(manifest: pathlib.Path) -> dict[str, str]:
    data = json.loads(manifest.read_text())
    return {p["name"].strip("«»"): p.get("rev") for p in data["packages"]}


def main() -> int:
    root_manifest = ROOT / "lake-manifest.json"
    docbuild_manifest = ROOT / "docbuild" / "lake-manifest.json"
    root_toolchain = ROOT / "lean-toolchain"
    docbuild_toolchain = ROOT / "docbuild" / "lean-toolchain"

    for f in (root_manifest, docbuild_manifest, root_toolchain, docbuild_toolchain):
        if not f.exists():
            print(f"FAIL: {f.relative_to(ROOT)} is missing")
            print(REMEDY)
            return 1

    failures = []

    rt = root_toolchain.read_text().strip()
    dt = docbuild_toolchain.read_text().strip()
    if rt != dt:
        failures.append(f"  toolchain: root {rt!r} vs docbuild {dt!r}")

    root_revs, doc_revs = revs(root_manifest), revs(docbuild_manifest)
    for name, root_rev in root_revs.items():
        doc_rev = doc_revs.get(name)
        if doc_rev is None:
            failures.append(f"  {name}: absent from docbuild manifest (root {root_rev})")
        elif doc_rev != root_rev:
            failures.append(f"  {name}: root {root_rev} vs docbuild {doc_rev}")

    if failures:
        print("FAIL: docbuild is out of sync with the root project:")
        print("\n".join(failures))
        print(REMEDY)
        return 1

    print(
        f"OK: docbuild matches the root project — toolchain {rt}, "
        f"{len(root_revs)} shared packages, Mathlib {root_revs.get('mathlib')}."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
