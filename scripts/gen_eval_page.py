#!/usr/bin/env python3
"""Generate the projection scoreboard, the page of `Eval` verdicts published at linglib.io/eval/.

Every verdict on the page comes from `scripts/eval_page/Export.lean`, which instantiates the
verdict theorems of `Eval` and `Lab` at each theory and each cell and reduces their right-hand
sides with Lean. This script adds what the page shows around them: the experiments' printed
numbers and locators from `Linglib/Data/Experiments/<Paper>.json`, author-year citations from
`references.bib`, and links to each theorem's documentation. It types no verdict by hand.

Usage, from the repository root, once `Lab` is built:

    python3 scripts/gen_eval_page.py --export        # run the Lean export first
    python3 scripts/gen_eval_page.py --out DIR        # write DIR/index.html

The page is self-contained: the data is embedded in the HTML, so the file opens from disk too.
"""

import argparse
import datetime
import html
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXPORT = ROOT / "scripts" / "eval_page" / "Export.lean"
TEMPLATE = ROOT / "scripts" / "eval_page" / "template.html"
DEFAULT_JSON = ROOT / ".lake" / "build" / "eval-page" / "verdicts.json"
DEFAULT_OUT = ROOT / ".lake" / "build" / "eval-page"
DATA = ROOT / "Linglib" / "Data" / "Experiments"

# The datasets the page shows, in order, with the task each experiment set its subjects.
DATASETS = {
    "chemla-schlenker-2012": {
        "paper": "ChemlaSchlenker2012",
        "task": "Which inference subjects endorse more from a sentence with a trigger: the "
                "conditional presupposition or the unconditional one.",
        "tables": ["experiment1Inferences", "experiment4Inferences"],
    },
    "chemla-2009a": {
        "paper": "Chemla2009a",
        "task": "How often subjects endorse the universal inference from a trigger in the scope "
                "of a quantifier over ten students.",
        "tables": ["experiment1Universal"],
    },
}


# ---------------------------------------------------------------- bibliography


def bib_entries(keys):
    """Author-year labels, titles and DOIs of the given `references.bib` keys."""
    text = (ROOT / "references.bib").read_text(encoding="utf-8")
    out = {}
    for key in keys:
        m = re.search(r"@\w+\{" + re.escape(key) + r",(.*?)\n\}", text, re.S)
        if not m:
            continue
        body = m.group(1)

        def field(name):
            f = re.search(r"^\s*" + name + r"\s*=\s*\{", body, re.M)
            if not f:
                return ""
            depth, i = 1, f.end()
            while depth and i < len(body):
                depth += {"{": 1, "}": -1}.get(body[i], 0)
                i += 1
            return re.sub(r"\s+", " ", body[f.end():i - 1]).strip()

        surnames = [a.split(",")[0].strip().strip("{}")
                    for a in field("author").split(" and ") if a.strip()]
        if len(surnames) > 2:
            who = surnames[0] + " et al."
        else:
            who = " & ".join(surnames)
        title = re.sub(r"[{}]", "", field("title"))
        title = re.sub(r"\\emph\s*", "", title)
        out[key] = {"who": who, "year": field("year"), "title": title, "doi": field("doi")}
    return out


CITE = re.compile(r"\[([a-z0-9][a-z0-9-]*-\d{4}[a-z]?)\]('s)?")


def doc_html(doc, bib, base):
    """A docstring as HTML: `[key]` links become author-year citations linked to the
    bibliography, backticks code."""
    doc = " ".join(doc.split())
    parts = []
    pos = 0
    for m in re.finditer(r"`([^`]*)`|" + CITE.pattern, doc):
        parts.append(html.escape(doc[pos:m.start()]))
        if m.group(1) is not None:
            parts.append("<code>" + html.escape(m.group(1)) + "</code>")
        else:
            entry = bib.get(m.group(2))
            if entry:
                poss = "'s" if m.group(3) else ""
                href = html.escape(f"{base}references.html#ref_{m.group(2)}")
                parts.append(f'<a href="{href}">{html.escape(entry["who"])}{poss} '
                             f'({html.escape(entry["year"])})</a>')
            else:
                parts.append(html.escape(m.group(0)))
        pos = m.end()
    parts.append(html.escape(doc[pos:]))
    return "".join(parts)


# ---------------------------------------------------------------- labels


def words(ident):
    return re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+", ident)


def theory_label(ident):
    """`transparencyIncremental` -> "Transparency, incremental"; `limitedSymmetry` -> "Limited
    Symmetry"."""
    ws = words(ident.split(".")[-1])
    if len(ws) > 1 and ws[-1].lower() in ("incremental", "symmetric"):
        return " ".join(w.capitalize() for w in ws[:-1]) + ", " + ws[-1].lower()
    return " ".join(w.capitalize() for w in ws)


def parser_label(ident):
    """`oneStep` -> "One step"."""
    label = " ".join(words(ident)).lower()
    return label[:1].upper() + label[1:]


def short(name):
    return name.split(".")[-1]


def doc_href(decl, base):
    return base + decl["module"].replace(".", "/") + ".html#" + decl["name"]


# ---------------------------------------------------------------- page data


def level_labels(spec):
    return {t["name"]: {lv["name"]: lv["label"] for lv in t["levels"]} for t in spec["types"]}


def build(export, base):
    rows = export["rows"]
    specs = {k: json.loads((DATA / (v["paper"] + ".json")).read_text(encoding="utf-8"))
             for k, v in DATASETS.items()}
    docs = [t["decl"]["doc"] for t in export["theories"]]
    docs += [r[k]["doc"] for r in rows for k in ("theorem", "parser", "graduation") if k in r]
    keys = set(DATASETS) | {m.group(1) for d in docs for m in CITE.finditer(d)}
    bib = bib_entries(sorted(keys))

    def decl(d):
        return {"name": d["name"], "short": short(d["name"]), "href": doc_href(d, base),
                "doc": doc_html(d["doc"], bib, base)}

    theories = [{"id": t["id"], "label": theory_label(t["id"]), "source": t["source"],
                 "decl": decl(t["decl"])} for t in export["theories"]]

    cells = {}
    theorems = {}
    for r in rows:
        if "verdict" in r:
            cells[f"{r['dataset']}|{r['theory']}|{r['cell']}"] = {
                "verdict": r["verdict"], "theorem": decl(r["theorem"])}
            theorems.setdefault(r["theorem"]["name"], decl(r["theorem"]))

    datasets = []

    # Chemla & Schlenker 2012: one column per tested construction and order.
    cs = specs["chemla-schlenker-2012"]
    lab = level_labels(cs)
    tables = {t["name"]: t for t in cs["tables"]}
    means = {}
    for exp, name in (("1", "experiment1Inferences"), ("4", "experiment4Inferences")):
        for row in tables[name]["rows"]:
            means.setdefault((row["construction"], row["order"]), {}).setdefault(exp, {})[
                row["inference"]] = row["mean"]
    groups = []
    for k, klabel in lab["Construction"].items():
        cols = []
        for o, olabel in lab["Order"].items():
            obs = next(r for r in rows if r["dataset"] == "chemla-schlenker-2012"
                       and r.get("cell") == f"{k}.{o}" and "observed" in r)
            m = means.get((klabel, olabel), {})
            cols.append({
                "id": f"{k}.{o}", "label": olabel,
                "observed": (obs["observed"]["args"][0]
                             if isinstance(obs["observed"], dict) else None),
                "means": [{"experiment": e, "conditional": v["conditional"],
                           "unconditional": v["unconditional"]} for e, v in sorted(m.items())],
            })
        groups.append({"label": klabel, "cols": cols})
    obs_thm = next(r["theorem"] for r in rows
                   if r["dataset"] == "chemla-schlenker-2012" and "observed" in r)
    datasets.append({
        "id": "chemla-schlenker-2012", "kind": "cells",
        "cite": bib["chemla-schlenker-2012"], "task": DATASETS["chemla-schlenker-2012"]["task"],
        "locators": [f"Experiment {e}, {tables[n]['locator']}" for e, n in
                     (("1", "experiment1Inferences"), ("4", "experiment4Inferences"))],
        "verified": tables["experiment1Inferences"]["verified"],
        "observedTheorem": decl(obs_thm), "groups": groups,
    })

    # Chemla 2009: one column per parser of the same observation.
    ch = specs["chemla-2009a"]
    det = level_labels(ch)["Determiner"]
    tables = {t["name"]: t for t in ch["tables"]}
    parsers = []
    for r in rows:
        if r["dataset"] == "chemla-2009a" and "parser" in r:
            parsers.append({
                "id": short(r["parser"]["name"]), "label": parser_label(short(r["parser"]["name"])),
                "decl": decl(r["parser"]),
                "stipulations": [det.get(s, s) for s in r["stipulations"]],
                "stipulationsTheorem": decl(r["theorem"]),
            })
    obs = next(r for r in rows if r["dataset"] == "chemla-2009a" and "observed" in r)
    graduation = next(r["graduation"] for r in rows if "graduation" in r)
    datasets.append({
        "id": "chemla-2009a", "kind": "parsers",
        "cite": bib["chemla-2009a"], "task": DATASETS["chemla-2009a"]["task"],
        "locators": [f"Experiment 1, {tables['experiment1Universal']['locator']}"],
        "verified": tables["experiment1Universal"]["verified"],
        "observed": obs["observed"]["args"][0] if isinstance(obs["observed"], dict) else None,
        "rates": tables["experiment1Universal"]["rows"],
        "observedTheorem": decl(obs["theorem"]), "graduation": decl(graduation),
        "groups": [{"label": "parse", "cols": parsers}],
    })

    return {"theories": theories, "datasets": datasets, "cells": cells,
            "theorems": list(theorems.values())}


def git_commit():
    sha = os.environ.get("GITHUB_SHA")
    if not sha:
        try:
            sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                                 text=True, check=True).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            sha = ""
    return sha


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--export", action="store_true", help="run the Lean export first")
    ap.add_argument("--json", type=Path, default=DEFAULT_JSON, help="the Lean export's output")
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT, help="directory for index.html")
    ap.add_argument("--docs-base", default="../docs/",
                    help="URL of the API documentation, relative to the page")
    args = ap.parse_args()

    if args.export:
        env = dict(os.environ, EVAL_PAGE_JSON=str(args.json))
        result = subprocess.run(["lake", "env", "lean", str(EXPORT.relative_to(ROOT))],
                                cwd=ROOT, env=env)
        if result.returncode != 0:
            sys.exit("the Lean export failed")

    page = build(json.loads(args.json.read_text(encoding="utf-8")), args.docs_base)
    sha = git_commit()
    page["commit"] = {"sha": sha, "short": sha[:9],
                      "href": f"https://github.com/linglib-community/linglib/tree/{sha}" if sha
                      else ""}
    page["built"] = datetime.date.today().isoformat()

    data = json.dumps(page, ensure_ascii=False).replace("</", "<\\/")
    out = TEMPLATE.read_text(encoding="utf-8").replace("/*EVAL_DATA*/{}", data)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "index.html").write_text(out, encoding="utf-8")
    n = len(page["cells"])
    print(f"wrote {args.out / 'index.html'}: {len(page['theories'])} theories, {n} verdicts")


if __name__ == "__main__":
    main()
