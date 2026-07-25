#!/usr/bin/env python3
"""Drift checks for the documentation surfaces.

Cheap, hermetic checks that catch the failure modes the landing pages have actually hit:

1. **Canonical-URL split.** `_config.yml` must carry exactly the deployment origin in `url` and
   exactly the project path in `baseurl`, and the CI Jekyll invocation must not *also* pass
   `--baseurl` — doing both doubles the path and emits canonical URLs like
   `.../graphon/graphon/`. The values are pinned rather than merely pattern-checked, since a
   well-formed but wrong `baseurl` deploys just as broken as a malformed one.
2. **Placeholder metadata.** `description` must be a real description, not a byline.
3. **Hardcoded internal links.** Internal links on the homepage and in the layout must go
   through Jekyll's `relative_url`, so a baseurl change cannot silently break them. Every
   root-relative or bare-path `href`/`src` in the layout is checked, not a fixed list of
   targets.
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

# The deployment is fixed, so pin the values rather than pattern-matching them.
EXPECTED_URL = "https://cameronfreer.github.io"
EXPECTED_BASEURL = "/graphon"

# Hrefs in the layout that legitimately leave the site or are Liquid-generated.
EXTERNAL_PREFIXES = ("http://", "https://", "//", "#", "mailto:", "{{", "{%")

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

    if url != EXPECTED_URL:
        fail(
            f"{CONFIG}: `url` is {url!r}, expected exactly {EXPECTED_URL!r} "
            "(the origin only — the project path belongs in `baseurl`)"
        )
    if baseurl != EXPECTED_BASEURL:
        fail(
            f"{CONFIG}: `baseurl` is {baseurl!r}, expected exactly {EXPECTED_BASEURL!r} "
            "(leading slash, no trailing slash)"
        )
    if description is None or len(description) < 25 or description.lower().startswith("by "):
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

    # Every internal href/src in the layout must be Liquid-generated, not a bare path.
    layout = LAYOUT.read_text()
    for attr, value in re.findall(r'\b(href|src)=["\']([^"\']*)["\']', layout):
        if value == "" or value.startswith(EXTERNAL_PREFIXES):
            continue
        fail(
            f"{LAYOUT}: bare internal {attr}={value!r}; wrap it as "
            "`{{ '/path' | relative_url }}` so the baseurl is applied"
        )


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
