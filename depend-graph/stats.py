#!/usr/bin/env python3
"""
dpd_stats.py
Reads a .dpd file and prints statistics about the proof development.

Usage:
    python3 stats.py graph.dpd
    python3 stats.py graph.dpd --csv stats.csv
"""

import re
import argparse
from collections import defaultdict


# ── parser (same as dpd_file_graph.py) ───────────────────────────────────────

def parse_dpd(path):
    nodes = {}
    edges = []
    with open(path) as f:
        text = f.read()
    for m in re.finditer(
        r'N:\s*(\d+)\s*"([^"]+)"\s*(?:\[([^\]]*)\])?\s*;', text
    ):
        nid  = int(m.group(1))
        name = m.group(2)
        attrs_str = m.group(3) or ""
        attrs = {}
        for a in re.finditer(r'(\w+)="?([^",\]]*)"?', attrs_str):
            attrs[a.group(1)] = a.group(2)
        attrs["name"] = name
        nodes[nid] = attrs
    for m in re.finditer(r'E:\s*(\d+)\s*(\d+)', text):
        edges.append((int(m.group(1)), int(m.group(2))))
    return nodes, edges


def file_of_node(node):
    path = node.get("path", "")
    if not path:
        return node.get("name", "unknown")
    parts = path.strip(".").split(".")
    return parts[-1] if parts else "unknown"


def kind_label(node):
    k = node.get("kind", "")
    p = node.get("prop", "no")
    if k == "cnst":
        return "Theorem/Lemma" if p == "yes" else "Definition"
    if k == "inductive":
        return "Inductive"
    if k == "construct":
        return "Constructor"
    return "Other"


# ── statistics ────────────────────────────────────────────────────────────────

def compute_stats(nodes, edges):
    # per-file counts
    file_nodes   = defaultdict(list)
    for nid, n in nodes.items():
        file_nodes[file_of_node(n)].append(nid)

    # in/out degree
    out_deg = defaultdict(int)
    in_deg  = defaultdict(int)
    for src, dst in edges:
        out_deg[src] += 1
        in_deg[dst]  += 1

    # file-level edges
    file_edge_set = set()
    node_to_file  = {nid: file_of_node(n) for nid, n in nodes.items()}
    for src, dst in edges:
        sf, df = node_to_file.get(src), node_to_file.get(dst)
        if sf and df and sf != df:
            file_edge_set.add((sf, df))

    # kind breakdown
    kind_counts = defaultdict(int)
    for n in nodes.values():
        kind_counts[kind_label(n)] += 1

    # unreferenced nodes (no predecessors)
    referenced = {dst for _, dst in edges}
    unreferenced = [nid for nid in nodes if nid not in referenced]

    # most-used nodes
    top_used = sorted(nodes.keys(), key=lambda nid: in_deg[nid], reverse=True)[:10]

    # most complex nodes (most deps)
    top_complex = sorted(nodes.keys(), key=lambda nid: out_deg[nid], reverse=True)[:10]

    return dict(
        total_nodes   = len(nodes),
        total_edges   = len(edges),
        total_files   = len(file_nodes),
        file_edges    = len(file_edge_set),
        file_nodes    = file_nodes,
        kind_counts   = dict(kind_counts),
        unreferenced  = unreferenced,
        top_used      = top_used,
        top_complex   = top_complex,
        in_deg        = in_deg,
        out_deg       = out_deg,
        nodes         = nodes,
    )


def print_report(s):
    sep = "─" * 60

    print(sep)
    print("  ROCQ PROJECT DEPENDENCY STATISTICS")
    print(sep)
    print(f"  Total nodes (definitions/lemmas): {s['total_nodes']}")
    print(f"  Total edges (dependencies):       {s['total_edges']}")
    print(f"  Source files:                     {s['total_files']}")
    print(f"  File-level dependency edges:      {s['file_edges']}")
    print()

    # kind breakdown
    print("  Object kinds:")
    for kind, cnt in sorted(s["kind_counts"].items(), key=lambda x: -x[1]):
        bar = "█" * (cnt * 30 // max(s["kind_counts"].values()))
        print(f"    {kind:<20} {cnt:>5}  {bar}")
    print()

    # per-file breakdown
    print("  Per-file object counts:")
    file_nodes = s["file_nodes"]
    nodes      = s["nodes"]
    out_deg    = s["out_deg"]
    in_deg     = s["in_deg"]
    max_cnt    = max(len(v) for v in file_nodes.values())

    header = f"    {'File':<28} {'Defs':>5} {'Thms':>5} {'Avg deps':>9}"
    print(header)
    print("    " + "─" * 52)
    for fname in sorted(file_nodes.keys()):
        nids  = file_nodes[fname]
        thms  = sum(1 for nid in nids if s["kind_counts"].get("Theorem/Lemma", 0)
                    and kind_label(nodes[nid]) == "Theorem/Lemma")
        defs  = len(nids)
        avg_d = sum(out_deg[nid] for nid in nids) / defs if defs else 0
        bar   = "·" * (defs * 20 // max_cnt)
        print(f"    {fname:<28} {defs:>5} {thms:>5} {avg_d:>9.1f}  {bar}")
    print()

    # top 10 most used
    print("  Top 10 most referenced objects:")
    for nid in s["top_used"]:
        n    = nodes[nid]
        name = n["name"]
        cnt  = in_deg[nid]
        f    = file_of_node(n)
        print(f"    {name:<40} ({cnt} uses)  [{f}]")
    print()

    # top 10 most complex
    print("  Top 10 objects with most dependencies:")
    for nid in s["top_complex"]:
        n    = nodes[nid]
        name = n["name"]
        cnt  = out_deg[nid]
        f    = file_of_node(n)
        print(f"    {name:<40} ({cnt} deps)  [{f}]")
    print()

    # unreferenced
    ur = s["unreferenced"]
    print(f"  Unreferenced objects (no predecessors): {len(ur)}")
    for nid in ur[:15]:
        n = nodes[nid]
        print(f"    {n['name']}  [{file_of_node(n)}]")
    if len(ur) > 15:
        print(f"    ... and {len(ur) - 15} more")
    print(sep)


def write_csv(s, path):
    import csv
    rows = []
    for nid, n in s["nodes"].items():
        rows.append({
            "id":       nid,
            "name":     n["name"],
            "file":     file_of_node(n),
            "kind":     kind_label(n),
            "in_deg":   s["in_deg"][nid],
            "out_deg":  s["out_deg"][nid],
        })
    rows.sort(key=lambda r: (-r["in_deg"], r["file"], r["name"]))
    with open(path, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["id","name","file","kind","in_deg","out_deg"])
        w.writeheader()
        w.writerows(rows)
    print(f"CSV written to: {path}")

def main():
    ap = argparse.ArgumentParser(description="Statistics for a .dpd dependency file")
    ap.add_argument("dpd_file", help="Input .dpd file")
    ap.add_argument("--csv", metavar="PATH", help="Also write per-node CSV")
    args = ap.parse_args()

    nodes, edges = parse_dpd(args.dpd_file)
    stats = compute_stats(nodes, edges)
    print_report(stats)

    if args.csv:
        write_csv(stats, args.csv)


if __name__ == "__main__":
    main()