#!/usr/bin/env python3
"""Hermetic smoke test for the built site. No network access.

Two modes:

* default — checks the freshly built Jekyll output: `_site/index.html` exists and its canonical
  URL is exactly the expected deployment URL. Runs on every trigger, so a PR catches a broken
  `url`/`baseurl` split or malformed Liquid before it reaches the deployment.
* ``--assembled`` — additionally checks the artifacts copied in by the assemble step: the
  blueprint website, the blueprint PDF, and the API documentation index. Master-only, since
  those artifacts are only built there.

Run from the repository root. Exits non-zero on any failure.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SITE = ROOT / "_site"

CANONICAL = "https://cameronfreer.github.io/graphon/"

failures: list[str] = []


def fail(msg: str) -> None:
    failures.append(msg)


def check_homepage() -> None:
    index = SITE / "index.html"
    if not index.is_file():
        fail(f"{index} does not exist — the Jekyll build produced no homepage")
        return

    html = index.read_text(errors="replace")

    m = re.search(r'<link[^>]+rel=["\']canonical["\'][^>]*>', html)
    if m is None:
        fail(f"{index}: no <link rel=\"canonical\"> tag (is jekyll-seo-tag running?)")
        return
    href = re.search(r'href=["\']([^"\']+)["\']', m.group(0))
    if href is None:
        fail(f"{index}: canonical link tag has no href")
        return
    if href.group(1) != CANONICAL:
        fail(
            f"{index}: canonical URL is {href.group(1)!r}, expected {CANONICAL!r}. "
            "A doubled path usually means `url` carries the project path while the Jekyll "
            "invocation also passes --baseurl."
        )


def check_assembled() -> None:
    required = [
        SITE / "blueprint" / "index.html",
        SITE / "blueprint" / "blueprint.pdf",
        SITE / "docs" / "index.html",
    ]
    for path in required:
        if not path.is_file():
            fail(f"{path} missing after the assemble step")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--assembled",
        action="store_true",
        help="also require the blueprint and API-doc artifacts copied in by the assemble step",
    )
    args = parser.parse_args()

    check_homepage()
    if args.assembled:
        check_assembled()

    if failures:
        print("FAIL: built-site smoke test")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("OK: built-site smoke test passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
