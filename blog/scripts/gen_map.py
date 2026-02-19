#!/usr/bin/env python3
"""Generate blog/static/js/map-data.js from the Lean import graph.

Scans a curated subset of Lean files, extracts import edges and docstrings,
computes layout positions, and writes a JS data file consumed by map.md.

Usage:
    python blog/scripts/gen_map.py           # generate map-data.js
    python blog/scripts/gen_map.py --check   # validate only (no output)
"""

import json
import re
import sys
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).resolve().parent.parent
PROJECT_ROOT = ROOT.parent
LEAN_DIR = PROJECT_ROOT / "Linglib"
OUT_PATH = ROOT / "static" / "js" / "map-data.js"

# ---------------------------------------------------------------------------
# Configuration: which nodes appear on the map
# ---------------------------------------------------------------------------

ROOTS = {
    "scale":       {"label": "Scale / Lattice",        "c": "#2563eb", "lc": "#dbeafe", "tc": "#1e40af"},
    "closure":     {"label": "Closure / Fixpoint",     "c": "#dc2626", "lc": "#fee2e2", "tc": "#991b1b"},
    "luce":        {"label": "Luce / RationalAction",  "c": "#7c3aed", "lc": "#ede9fe", "tc": "#5b21b6"},
    "proposition": {"label": "Proposition / Intension", "c": "#059669", "lc": "#d1fae5", "tc": "#065f46"},
    "decision":    {"label": "Decision / Partition",   "c": "#d97706", "lc": "#fef3c7", "tc": "#92400e"},
}

# Each node: id, root family, relative path under Linglib/
# For glob nodes (RSAImpl), file_path uses * and we scan the directory.
NODES = [
    # Scale cluster
    {"id": "Scale",        "root": "scale",       "file_path": "Core/Scale.lean"},
    {"id": "Mereology",    "root": "scale",       "file_path": "Core/Mereology.lean"},
    {"id": "MereoDim",     "root": "scale",       "file_path": "Core/MereoDim.lean"},
    {"id": "Path",         "root": "scale",       "file_path": "Core/Path.lean"},
    {"id": "Time",         "root": "scale",       "file_path": "Core/Time.lean"},
    {"id": "DimBridge",    "root": "scale",       "file_path": "Theories/Semantics/Events/DimensionBridge.lean"},
    # Closure cluster
    {"id": "Causation",    "root": "closure",     "file_path": "Core/Causation.lean"},
    {"id": "Sufficiency",  "root": "closure",     "file_path": "Theories/Semantics/Causation/Sufficiency.lean"},
    {"id": "Necessity",    "root": "closure",     "file_path": "Theories/Semantics/Causation/Necessity.lean"},
    {"id": "Implicative",  "root": "closure",     "file_path": "Theories/Semantics/Causation/Implicative.lean"},
    {"id": "Ability",      "root": "closure",     "file_path": "Theories/Semantics/Modality/Ability.lean"},
    {"id": "GradedCaus",   "root": "closure",     "file_path": "Theories/Semantics/Causation/GradedCausation.lean"},
    # Luce cluster
    {"id": "RationalAction", "root": "luce",      "file_path": "Core/RationalAction.lean"},
    {"id": "UtilityTheory",  "root": "luce",      "file_path": "Core/UtilityTheory.lean"},
    {"id": "RSAConfig",      "root": "luce",      "file_path": "Theories/Pragmatics/RSA/Core/Config.lean"},
    {"id": "RSAImpl",        "root": "luce",      "file_path": "Theories/Pragmatics/RSA/Implementations/*"},
    # Proposition cluster
    {"id": "Proposition",    "root": "proposition", "file_path": "Core/Proposition.lean"},
    {"id": "Kleene",         "root": "proposition", "file_path": "Core/Kleene.lean"},
    {"id": "Intension",      "root": "proposition", "file_path": "Core/Intension.lean"},
    {"id": "CommonGround",   "root": "proposition", "file_path": "Core/CommonGround.lean"},
    {"id": "Presupposition", "root": "proposition", "file_path": "Core/Presupposition.lean"},
    {"id": "ModalLogic",     "root": "proposition", "file_path": "Core/ModalLogic.lean"},
    # Decision cluster
    {"id": "QUD",            "root": "decision",  "file_path": "Core/QUD.lean"},
    {"id": "DecisionTheory", "root": "decision",  "file_path": "Core/DecisionTheory.lean"},
    {"id": "Partition",      "root": "decision",  "file_path": "Core/Partition.lean"},
    # Tense (in scale family but positioned separately)
    {"id": "Reichenbach",    "root": "scale",     "file_path": "Core/Reichenbach.lean"},
    {"id": "Tense",          "root": "scale",     "file_path": "Core/Tense.lean"},
]

# Proposed nodes
PROPOSED_NODES = [
    {"id": "CausalClosure",   "root": "closure", "file_path": "Theories/Semantics/Causation/CausalClosure.lean"},
    {"id": "DegreeCausation",  "root": "closure", "file_path": "Theories/Semantics/Causation/DegreeCausation.lean"},
]

# Conceptual edges not derivable from direct imports.
# These are NOT used for tier computation — only for the final edge list.
EXTRA_EDGES = [
    {"f": "RSAConfig", "t": "Proposition", "type": "bridge", "label": "SemanticBackend"},
    {"f": "Partition",  "t": "UtilityTheory", "type": "bridge", "label": "Blackwell ordering"},
    {"f": "Time",       "t": "Ability",       "type": "bridge", "label": "aspect \u2192 actuality"},
]

# Labels for specific auto-extracted edges (keyed by "from->to" in import direction)
EDGE_LABELS = {
    "Time->Tense": "Tense pronoun",
    "Time->Ability": "aspect \u2192 actuality",
    "Sufficiency->RSAImpl": "Beller & Gerstenberg 2025",
    "Necessity->RSAImpl": "Beller & Gerstenberg 2025",
    "Scale->RSAImpl": "Lassiter & Goodman 2017",
}

# Nodes whose tier is manually overridden.
# "bridge" means the node conceptually connects two root families.
TIER_OVERRIDES = {
    "MereoDim":  "bridge",
    "DimBridge": "bridge",
    "Ability":   "bridge",
    "Partition":  "bridge",
    "Tense":     "bridge",
}

# Proposed edge connections
PROPOSED_EDGES = [
    {"f": "CausalClosure",  "t": "Causation",       "type": "proposed"},
    {"f": "Sufficiency",    "t": "DegreeCausation",  "type": "proposed"},
    {"f": "Scale",          "t": "DegreeCausation",  "type": "proposed", "label": "degree \u2192 closure family"},
]

# Cluster geometry: bounding boxes for each root family's background rect
CLUSTERS = {
    "scale":       {"x": 30,  "y": 80,  "w": 280, "h": 340, "label": "SCALE / LATTICE"},
    "closure":     {"x": 345, "y": 80,  "w": 250, "h": 340, "label": "CLOSURE / FIXPOINT"},
    "luce":        {"x": 710, "y": 80,  "w": 270, "h": 340, "label": "LUCE / RATIONAL ACTION"},
    "proposition": {"x": 30,  "y": 490, "w": 330, "h": 260, "label": "PROPOSITION / INTENSION"},
    "decision":    {"x": 410, "y": 490, "w": 240, "h": 170, "label": "DECISION / PARTITION"},
}

# Manual position overrides (nodes outside their cluster's auto-layout)
POSITION_OVERRIDES = {
    "Reichenbach": (310, 530),
    "Tense":       (310, 620),
}

# Manual position overrides for proposed nodes
PROPOSED_POSITION_OVERRIDES = {
    "CausalClosure":  (470, 55),
    "DegreeCausation": (340, 390),
}


# ---------------------------------------------------------------------------
# Import extraction
# ---------------------------------------------------------------------------

IMPORT_RE = re.compile(r"^import\s+Linglib\.(\S+)", re.MULTILINE)


def extract_imports(path: Path) -> list[str]:
    """Extract Linglib import paths from a Lean file."""
    try:
        text = path.read_text(encoding="utf-8")
    except (FileNotFoundError, UnicodeDecodeError):
        return []
    return IMPORT_RE.findall(text)


# ---------------------------------------------------------------------------
# Description extraction
# ---------------------------------------------------------------------------

DOCSTRING_RE = re.compile(r"/-(!\s*|\s*)\n(.*?)(?:\n-/)", re.DOTALL)


def extract_desc(path: Path) -> str:
    """Extract first content sentence from a Lean module docstring.

    Skips heading lines (# ...), empty lines, list items (- ...),
    and @cite references. Returns the first prose sentence, truncated
    to a sentence boundary if over 80 characters.
    """
    try:
        text = path.read_text(encoding="utf-8")
    except (FileNotFoundError, UnicodeDecodeError):
        return ""

    m = DOCSTRING_RE.search(text)
    if not m:
        return ""

    body = m.group(2)
    for line in body.split("\n"):
        line = line.strip()
        if not line or line.startswith("#") or line.startswith("-") or line.startswith("@cite"):
            continue
        # Found a content line — extract first sentence
        # Look for ". " or ".\n" as sentence boundary
        sent_end = re.search(r"\.\s", line)
        if sent_end and sent_end.start() >= 20:
            return line[:sent_end.start() + 1]
        # If no sentence boundary found, truncate at 80 chars on word boundary
        if len(line) > 80:
            trunc = line[:80].rsplit(" ", 1)[0]
            return trunc + "\u2026"
        return line

    return ""


# ---------------------------------------------------------------------------
# Build the import-to-node-ID mapping
# ---------------------------------------------------------------------------

def build_module_to_id(nodes: list[dict]) -> dict[str, str]:
    """Map Lean module paths (dot-separated) to node IDs."""
    result = {}
    for node in nodes:
        fp = node["file_path"]
        if "*" in fp:
            continue
        module = fp.replace("/", ".").removesuffix(".lean")
        result[module] = node["id"]
    return result


# ---------------------------------------------------------------------------
# Edge computation
# ---------------------------------------------------------------------------

def compute_edges(nodes: list[dict], proposed_nodes: list[dict]) -> tuple[list[dict], list[dict]]:
    """Compute edges from import graph + extra edges.

    Returns (regular_edges, proposed_edges). The regular edges include both
    auto-extracted import edges and EXTRA_EDGES.
    """
    all_nodes = nodes + proposed_nodes
    module_to_id = build_module_to_id(all_nodes)
    node_by_id = {n["id"]: n for n in all_nodes}

    edges = []
    seen = set()

    for node in nodes:
        fp = node["file_path"]

        if "*" in fp:
            # Glob node: scan all .lean files in the directory
            dir_path = LEAN_DIR / fp.replace("/*", "")
            if not dir_path.is_dir():
                print(f"WARNING: directory not found for glob node {node['id']}: {dir_path}", file=sys.stderr)
                continue
            all_imports = set()
            for lean_file in dir_path.glob("*.lean"):
                for imp in extract_imports(lean_file):
                    all_imports.add(imp)
            imports = list(all_imports)
        else:
            full_path = LEAN_DIR / fp
            if not full_path.exists():
                print(f"WARNING: file not found for node {node['id']}: {full_path}", file=sys.stderr)
                continue
            imports = extract_imports(full_path)

        for imp in imports:
            target_id = module_to_id.get(imp)
            if target_id and target_id != node["id"]:
                edge_key = (target_id, node["id"])
                if edge_key not in seen:
                    seen.add(edge_key)
                    from_root = node_by_id.get(target_id, {}).get("root", "")
                    to_root = node["root"]
                    edge_type = "bridge" if from_root != to_root else "dep"
                    edge = {"f": target_id, "t": node["id"], "type": edge_type}

                    label_key = f"{target_id}->{node['id']}"
                    if label_key in EDGE_LABELS:
                        edge["label"] = EDGE_LABELS[label_key]

                    edges.append(edge)

    # Add extra conceptual edges (not from imports)
    for extra in EXTRA_EDGES:
        edge_key = (extra["f"], extra["t"])
        if edge_key not in seen:
            seen.add(edge_key)
            edges.append(dict(extra))

    # Proposed edges
    proposed_edges = [dict(pe) for pe in PROPOSED_EDGES]

    return edges, proposed_edges


# ---------------------------------------------------------------------------
# Tier computation
# ---------------------------------------------------------------------------

def compute_tiers(nodes: list[dict], edges: list[dict]) -> dict[str, str]:
    """Compute tier for each node: root, derived, or bridge.

    - TIER_OVERRIDES take precedence (for curated bridge designations)
    - Root: no intra-family incoming dep edges from other map nodes
    - Derived: has intra-family incoming dep edges
    """
    node_ids = {n["id"] for n in nodes}
    node_by_id = {n["id"]: n for n in nodes}

    # Only count intra-family dep edges for root/derived determination.
    # Bridge edges and EXTRA_EDGES don't affect root status.
    has_intra_family_incoming = set()
    for e in edges:
        if e["type"] != "dep":
            continue
        f_node = node_by_id.get(e["f"])
        t_node = node_by_id.get(e["t"])
        if f_node and t_node and f_node["root"] == t_node["root"]:
            has_intra_family_incoming.add(e["t"])

    tiers = {}
    for node in nodes:
        nid = node["id"]
        if nid in TIER_OVERRIDES:
            tiers[nid] = TIER_OVERRIDES[nid]
        elif nid not in has_intra_family_incoming:
            tiers[nid] = "root"
        else:
            tiers[nid] = "derived"

    return tiers


# ---------------------------------------------------------------------------
# Layout computation
# ---------------------------------------------------------------------------

def compute_positions(nodes: list[dict], edges: list[dict]) -> dict[str, tuple[int, int]]:
    """Compute x,y positions for each node using topological depth within clusters."""
    node_by_id = {n["id"]: n for n in nodes}
    positions = {}

    # Group nodes by root family
    by_root = defaultdict(list)
    for n in nodes:
        by_root[n["root"]].append(n["id"])

    # Build intra-family dep graph
    children = defaultdict(list)
    parents = defaultdict(list)
    for e in edges:
        if e["type"] != "dep":
            continue
        f_node = node_by_id.get(e["f"])
        t_node = node_by_id.get(e["t"])
        if f_node and t_node and f_node["root"] == t_node["root"]:
            children[e["f"]].append(e["t"])
            parents[e["t"]].append(e["f"])

    for root_key, node_ids in by_root.items():
        cluster = CLUSTERS.get(root_key)
        if not cluster:
            continue

        family_set = set(node_ids)
        family_roots = [
            nid for nid in node_ids
            if not any(p in family_set for p in parents[nid])
        ]

        # Longest-path depth from roots
        depth = {r: 0 for r in family_roots}
        changed = True
        while changed:
            changed = False
            for nid in node_ids:
                for child in children.get(nid, []):
                    if child in family_set:
                        new_d = depth.get(nid, 0) + 1
                        if child not in depth or new_d > depth[child]:
                            depth[child] = new_d
                            changed = True

        for nid in node_ids:
            if nid not in depth:
                depth[nid] = 0

        # Group by depth, excluding overridden nodes
        by_depth = defaultdict(list)
        for nid in node_ids:
            if nid not in POSITION_OVERRIDES:
                by_depth[depth[nid]].append(nid)

        # Distribute within cluster
        max_depth = max(depth.values()) if depth else 0
        padding = 40
        cx, cy, cw, ch = cluster["x"], cluster["y"], cluster["w"], cluster["h"]
        dy = (ch - 2 * padding) / max(max_depth, 1)

        for d, nids in by_depth.items():
            y = cy + padding + d * dy
            n_at_level = len(nids)
            dx = (cw - 2 * padding) / max(n_at_level + 1, 2)
            for i, nid in enumerate(nids):
                x = cx + padding + (i + 1) * dx
                positions[nid] = (int(x), int(y))

    # Apply position overrides
    for nid, pos in POSITION_OVERRIDES.items():
        positions[nid] = pos

    return positions


# ---------------------------------------------------------------------------
# Display helpers
# ---------------------------------------------------------------------------

def display_file(node: dict) -> str:
    """Convert a node's file_path to a short display string."""
    fp = node["file_path"]
    if "*" in fp:
        return fp.replace("Theories/Pragmatics/", "").replace("Theories/Semantics/", "")
    fp = fp.replace("Theories/Semantics/", "")
    fp = fp.replace("Theories/Pragmatics/", "")
    return fp


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    check_only = "--check" in sys.argv

    all_map_nodes = NODES + PROPOSED_NODES

    # Validate file existence
    warnings = []
    for node in all_map_nodes:
        fp = node["file_path"]
        if "*" in fp:
            dir_path = LEAN_DIR / fp.replace("/*", "")
            if not dir_path.is_dir():
                warnings.append(f"WARNING: directory not found for {node['id']}: {dir_path}")
        else:
            full_path = LEAN_DIR / fp
            if not full_path.exists():
                warnings.append(f"WARNING: file not found for {node['id']}: {full_path}")

    for w in warnings:
        print(w, file=sys.stderr)

    # Compute edges from import graph
    edges, proposed_edges = compute_edges(NODES, PROPOSED_NODES)

    # Compute tiers (root/derived/bridge)
    tiers = compute_tiers(NODES, edges)

    # Compute positions
    positions = compute_positions(NODES, edges)

    # Extract descriptions from docstrings
    descs = {}
    for node in all_map_nodes:
        fp = node["file_path"]
        if "*" in fp:
            dir_path = LEAN_DIR / fp.replace("/*", "")
            count = len(list(dir_path.glob("*.lean"))) if dir_path.is_dir() else 0
            descs[node["id"]] = f"{count} paper implementations"
        else:
            full_path = LEAN_DIR / fp
            desc = extract_desc(full_path)
            descs[node["id"]] = desc if desc else "(no description found)"

    # Build output node arrays
    out_nodes = []
    for node in NODES:
        nid = node["id"]
        x, y = positions.get(nid, (0, 0))
        out_nodes.append({
            "id": nid,
            "root": node["root"],
            "x": x,
            "y": y,
            "tier": tiers.get(nid, "derived"),
            "file": display_file(node),
            "desc": descs.get(nid, ""),
        })

    out_proposed_nodes = []
    for node in PROPOSED_NODES:
        nid = node["id"]
        x, y = PROPOSED_POSITION_OVERRIDES.get(nid, (0, 0))
        out_proposed_nodes.append({
            "id": nid,
            "root": node["root"],
            "x": x,
            "y": y,
            "tier": "proposed",
            "file": display_file(node) + " (proposed)",
            "desc": descs.get(nid, ""),
        })

    # Report
    bridge_count = sum(1 for e in edges if e["type"] == "bridge")
    dep_count = sum(1 for e in edges if e["type"] == "dep")
    print(f"Nodes: {len(out_nodes)} regular + {len(out_proposed_nodes)} proposed")
    print(f"Edges: {dep_count} dep + {bridge_count} bridge + {len(proposed_edges)} proposed")
    print(f"Warnings: {len(warnings)}")

    if check_only:
        sys.exit(1 if warnings else 0)

    # Write output
    data = {
        "ROOTS": ROOTS,
        "N": out_nodes,
        "NP": out_proposed_nodes,
        "E": edges,
        "EP": proposed_edges,
        "CLUSTERS": CLUSTERS,
    }

    js_content = (
        "// Auto-generated by gen_map.py \u2014 do not edit\n"
        f"window.MAP_DATA = {json.dumps(data, indent=2)};\n"
    )

    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(js_content, encoding="utf-8")
    print(f"Wrote {OUT_PATH}")


if __name__ == "__main__":
    main()
