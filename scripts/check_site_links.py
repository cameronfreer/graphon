#!/usr/bin/env python3
"""Drift checks for the documentation surfaces.

Cheap, hermetic checks that catch the failure modes the landing pages have actually hit:

1. **Canonical-URL split.** `_config.yml` must carry the origin in `url` and the project path
   in `baseurl`, and the CI Jekyll invocation must not *also* pass `--baseurl` — doing both
   doubles the path and emits canonical URLs like `.../graphon/graphon/`.
2. **Placeholder metadata.** `description` must be a real description, not a byline.
3. **Hardcoded internal links.** Internal links on the homepage must go through Jekyll's
   `relative_url`, so a baseurl change cannot silently break them.
4. **Local link targets.** Repository-relative links in `README.md` must resolve on disk.
5. **Duplicated inventories.** Neither landing page may reintroduce a full module table; the
   inventory belongs to `Graphon.lean` and the API docs.

Run from the repository root. Exits non-zero on any failure.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONFIG = ROOT / "home_page" / "_config.yml"
INDEX = ROOT / "home_page" / "index.md"
LAYOUT = ROOT / "home_page" / "_layouts" / "default.html"
README = ROOT / "README.md"
WORKFLOW = ROOT / ".github" / "workflows" / "build.yml"

# A landing page listing this many `Graphon/*.lean` paths is maintaining a module inventory.
INVENTORY_THRESHOLD = 20

failures: list[str] = []


def fail(msg: str) -> None:
    failures.append(msg)


def yaml_scalar(text: str, key: str) -> str | None:
    m = re.search(rf"^{re.escape(key)}:\s*(.*)$", text, re.MULTILINE)
    if m is None:
        return None
    return m.group(1).strip().strip('"').strip("'")


def check_config() -> None:
    text = CONFIG.read_text()
    url = yaml_scalar(text, "url")
    baseurl = yaml_scalar(text, "baseurl")
    description = yaml_scalar(text, "description")

    if url is None or baseurl is None:
        fail(f"{CONFIG}: both `url` and `baseurl` must be set")
        return
    # `url` is the origin only: no path component beyond the host.
    if re.sub(r"^https?://[^/]+", "", url) != "":
        fail(
            f"{CONFIG}: `url` must be the origin only (got {url!r}); "
            "the project path belongs in `baseurl`"
        )
    if baseurl in ("", "/"):
        fail(f"{CONFIG}: `baseurl` must be the project path, e.g. \"/graphon\"")
    if description is None or len(description) < 25 or "by " == description[:3]:
        fail(
            f"{CONFIG}: `description` is a placeholder ({description!r}); it is the page "
            "subtitle and the SEO description"
        )


def check_workflow() -> None:
    text = WORKFLOW.read_text()
    for line in text.splitlines():
        if "jekyll build" in line and "--baseurl" in line:
            fail(
                f"{WORKFLOW}: the Jekyll invocation passes `--baseurl` while `_config.yml` "
                "already sets it; the path gets doubled"
            )


def check_relative_urls() -> None:
    site_root = "cameronfreer.github.io/graphon"
    for path in (INDEX, LAYOUT):
        text = path.read_text()
        if site_root in text:
            fail(
                f"{path}: hardcodes {site_root!r}; route internal links through "
                "Jekyll's `relative_url` instead"
            )
    layout = LAYOUT.read_text()
    for target in ("blueprint", "docs"):
        if re.search(rf'href="{target}[/"]', layout):
            fail(f"{LAYOUT}: bare href to {target!r}; use `relative_url`")


def check_readme_links() -> None:
    text = README.read_text()
    for target in re.findall(r"\]\((?!https?://|#)([^)\s]+)\)", text):
        if not (ROOT / target).exists():
            fail(f"{README}: link target {target!r} does not exist")


def check_no_inventory() -> None:
    for path in (README, INDEX):
        count = len(set(re.findall(r"Graphon/[A-Za-z0-9_]+\.lean", path.read_text())))
        if count >= INVENTORY_THRESHOLD:
            fail(
                f"{path}: lists {count} modules — landing pages must not duplicate the "
                "module inventory (it belongs to Graphon.lean and the API docs)"
            )


def main() -> int:
    check_config()
    check_workflow()
    check_relative_urls()
    check_readme_links()
    check_no_inventory()

    if failures:
        print("FAIL: documentation drift checks")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("OK: documentation drift checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
