"""
stats.py — Print statistics about the VizingThesis Rocq library.
Place in viz/depend-graph/ alongside filter_dpd.py.
Run from anywhere:
    python3 stats.py                  # plain-text summary
    python3 stats.py --latex          # LaTeX tables (paste-ready)
    python3 stats.py --latex --out stats.tex   # write to file
    python3 stats.py --verbose        # also list every named item
"""

import os
import re
import argparse
from pathlib import Path
from collections import defaultdict

SCRIPT_DIR   = Path(__file__).resolve().parent
THEORIES_DIR = SCRIPT_DIR.parent / "theories"

# ── Rocq keyword patterns ──────────────────────────────────────────────────────

# Each entry: (category_label, regex)
# Patterns are matched against stripped lines (comments already removed).
ITEM_PATTERNS = [
    ("Lemma",       re.compile(r'^\s*(?:Lemma|lemma)\s+(\w+)')),
    ("Theorem",     re.compile(r'^\s*(?:Theorem|theorem)\s+(\w+)')),
    ("Corollary",   re.compile(r'^\s*(?:Corollary|corollary)\s+(\w+)')),
    ("Proposition", re.compile(r'^\s*(?:Proposition|proposition)\s+(\w+)')),
    ("Fact",        re.compile(r'^\s*(?:Fact|fact)\s+(\w+)')),
    ("Remark",      re.compile(r'^\s*(?:Remark|remark)\s+(\w+)')),
    ("Example",     re.compile(r'^\s*(?:Example|example)\s+(\w+)')),
    ("Definition",  re.compile(r'^\s*(?:Definition|definition)\s+(\w+)')),
    ("Fixpoint",    re.compile(r'^\s*(?:Fixpoint|fixpoint)\s+(\w+)')),
    ("CoFixpoint",  re.compile(r'^\s*(?:CoFixpoint)\s+(\w+)')),
    ("Inductive",   re.compile(r'^\s*(?:Inductive|inductive)\s+(\w+)')),
    ("CoInductive", re.compile(r'^\s*(?:CoInductive)\s+(\w+)')),
    ("Record",      re.compile(r'^\s*(?:Record|record)\s+(\w+)')),
    ("Structure",   re.compile(r'^\s*(?:Structure)\s+(\w+)')),
    ("Class",       re.compile(r'^\s*(?:Class)\s+(\w+)')),
    ("Instance",    re.compile(r'^\s*(?:Instance)\s+(\w+)')),
    ("Notation",    re.compile(r'^\s*(?:Notation|Reserved Notation)\b')),
    ("Axiom",       re.compile(r'^\s*(?:Axiom|Hypothesis|Parameter|Variable|Assume)\s+(\w+)')),
    ("Tactic",      re.compile(r'^\s*(?:Ltac|Ltac2|Tactic Notation)\s+(\w+)')),
    ("Section",     re.compile(r'^\s*Section\s+(\w+)')),
    ("Module",      re.compile(r'^\s*Module\s+(\w+)')),
]

# Proof markers (between these a "proof" lives)
PROOF_START = re.compile(r'^\s*(?:Proof|proof)\b')
PROOF_END   = re.compile(r'^\s*(?:Qed|Defined|Admitted|Abort|Save)\b')

# Admitted/sorry markers (incomplete proofs)
ADMITTED_RE = re.compile(r'\b(?:Admitted|admit|sorry)\b')

COMMENT_RE  = re.compile(r'\(\*.*?\*\)', re.DOTALL)


def strip_comments(text: str) -> str:
    """Remove (* ... *) comments, including nested ones."""
    result = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i+2] == '(*':
            depth += 1
            i += 2
        elif text[i:i+2] == '*)':
            depth = max(0, depth - 1)
            i += 2
            if depth == 0:
                result.append(' ')
        elif depth == 0:
            result.append(text[i])
            i += 1
        else:
            # preserve newlines inside comments so line counts stay aligned
            if text[i] == '\n':
                result.append('\n')
            i += 1
    return ''.join(result)


def analyze_file(path: Path) -> dict:
    raw = path.read_text(encoding='utf-8', errors='replace')
    raw_lines = raw.splitlines()

    clean = strip_comments(raw)
    clean_lines = clean.splitlines()

    stats = {
        "raw_lines":   len(raw_lines),
        "blank_lines": sum(1 for l in raw_lines if not l.strip()),
        "comment_lines": sum(
            1 for r, c in zip(raw_lines, clean_lines)
            if r.strip() and not c.strip()
        ),
        "items":       defaultdict(list),   # category -> [name, ...]
        "proofs":      0,
        "proof_lines": 0,
        "admitted":    0,
        "uses":        set(),               # Require'd modules
    }

    # Count proofs and their line spans
    in_proof = False
    proof_start_line = 0
    for i, line in enumerate(clean_lines):
        if not in_proof and PROOF_START.match(line):
            in_proof = True
            proof_start_line = i
            stats["proofs"] += 1
        elif in_proof and PROOF_END.match(line):
            stats["proof_lines"] += (i - proof_start_line + 1)
            if ADMITTED_RE.search(line):
                stats["admitted"] += 1
            in_proof = False

    # Count Admitted anywhere (not just at proof end)
    for line in clean_lines:
        if re.search(r'^\s*Admitted\s*\.', line):
            pass  # already counted above
        if re.search(r'\badmit\b|\bsorry\b', line):
            stats["admitted"] += 1

    # Collect named items
    for line in clean_lines:
        for category, pat in ITEM_PATTERNS:
            m = pat.match(line)
            if m:
                name = m.group(1) if m.lastindex else ""
                stats["items"][category].append(name)
                break  # one category per line

    # Collect Require imports
    for line in clean_lines:
        m = re.search(r'\bRequire\s+(?:Import\s+|Export\s+)?(\w[\w.]*)', line)
        if m:
            stats["uses"].add(m.group(1))

    return stats


def collect_library(theories_dir: Path) -> dict:
    files = sorted(theories_dir.glob("*.v"))
    if not files:
        raise FileNotFoundError(f"No .v files found in {theories_dir}")

    library = {}
    for f in files:
        library[f.stem] = analyze_file(f)
    return library


def aggregate(library: dict) -> dict:
    totals = {
        "files":         len(library),
        "raw_lines":     0,
        "blank_lines":   0,
        "comment_lines": 0,
        "code_lines":    0,
        "proofs":        0,
        "proof_lines":   0,
        "admitted":      0,
        "items":         defaultdict(int),
    }
    for stats in library.values():
        totals["raw_lines"]     += stats["raw_lines"]
        totals["blank_lines"]   += stats["blank_lines"]
        totals["comment_lines"] += stats["comment_lines"]
        totals["proofs"]        += stats["proofs"]
        totals["proof_lines"]   += stats["proof_lines"]
        totals["admitted"]      += stats["admitted"]
        code = (stats["raw_lines"]
                - stats["blank_lines"]
                - stats["comment_lines"])
        totals["code_lines"] += code
        for cat, names in stats["items"].items():
            totals["items"][cat] += len(names)
    return totals


# ── Formatting helpers ─────────────────────────────────────────────────────────

PROP_CATEGORIES = {"Lemma", "Theorem", "Corollary", "Proposition", "Fact", "Remark"}
DEF_CATEGORIES  = {"Definition", "Fixpoint", "CoFixpoint"}
TYPE_CATEGORIES = {"Inductive", "CoInductive", "Record", "Structure", "Class"}

def section(title: str):
    print(f"\n{'─' * 50}")
    print(f"  {title}")
    print(f"{'─' * 50}")

def row(label: str, value, width: int = 34):
    print(f"  {label:<{width}} {value}")


def print_summary(totals: dict, library: dict):
    section("VizingThesis Library Statistics")

    row("Source files", totals["files"])
    print()
    row("Total lines",   totals["raw_lines"])
    row("  Blank lines", totals["blank_lines"])
    row("  Comment lines", totals["comment_lines"])
    row("  Code lines",  totals["code_lines"])

    print()
    props = sum(totals["items"].get(c, 0) for c in PROP_CATEGORIES)
    defs  = sum(totals["items"].get(c, 0) for c in DEF_CATEGORIES)
    types = sum(totals["items"].get(c, 0) for c in TYPE_CATEGORIES)

    row("Propositions (lemmas/theorems/…)", props)
    row("  Lemmas",      totals["items"].get("Lemma", 0))
    row("  Theorems",    totals["items"].get("Theorem", 0))
    row("  Corollaries", totals["items"].get("Corollary", 0))
    row("  Propositions",totals["items"].get("Proposition", 0))
    row("  Facts/Remarks",
        totals["items"].get("Fact", 0) + totals["items"].get("Remark", 0))
    print()
    row("Definitions (Def/Fix/CoFix)", defs)
    row("  Definitions", totals["items"].get("Definition", 0))
    row("  Fixpoints",   totals["items"].get("Fixpoint", 0))
    print()
    row("Type definitions (Ind/Rec/…)", types)
    row("  Inductives",  totals["items"].get("Inductive", 0))
    row("  Records",     totals["items"].get("Record", 0))
    row("  Classes",     totals["items"].get("Class", 0))
    row("  Instances",   totals["items"].get("Instance", 0))
    print()
    row("Notations",     totals["items"].get("Notation", 0))
    row("Axioms/Hypotheses", totals["items"].get("Axiom", 0))
    row("Tactics (Ltac)", totals["items"].get("Tactic", 0))
    row("Sections",      totals["items"].get("Section", 0))
    row("Modules",       totals["items"].get("Module", 0))

    print()
    row("Proofs",        totals["proofs"])
    row("  Proof lines", totals["proof_lines"])
    avg = (totals["proof_lines"] / totals["proofs"]) if totals["proofs"] else 0
    row("  Avg proof length (lines)", f"{avg:.1f}")
    row("  Admitted/sorry",    totals["admitted"])


def print_per_file(library: dict):
    section("Per-file Breakdown")
    header = f"  {'File':<22} {'Lines':>6} {'Code':>6} {'Lemmas':>7} {'Defs':>5} {'Ind':>4} {'Proofs':>7} {'Adm':>4}"
    print(header)
    print("  " + "·" * (len(header) - 2))
    for stem, s in library.items():
        code   = s["raw_lines"] - s["blank_lines"] - s["comment_lines"]
        lemmas = sum(len(s["items"].get(c, [])) for c in PROP_CATEGORIES)
        defs   = sum(len(s["items"].get(c, [])) for c in DEF_CATEGORIES)
        inds   = sum(len(s["items"].get(c, [])) for c in TYPE_CATEGORIES)
        print(f"  {stem:<22} {s['raw_lines']:>6} {code:>6} {lemmas:>7} {defs:>5} {inds:>4} {s['proofs']:>7} {s['admitted']:>4}")


def print_verbose(library: dict):
    section("Named Items per File")
    show_cats = list(PROP_CATEGORIES) + list(DEF_CATEGORIES) + list(TYPE_CATEGORIES)
    for stem, s in library.items():
        any_items = any(s["items"].get(c) for c in show_cats)
        if not any_items:
            continue
        print(f"\n  [{stem}]")
        for cat in show_cats:
            names = s["items"].get(cat, [])
            if names:
                for name in names:
                    print(f"    {cat:<14} {name}")


# ── LaTeX output ───────────────────────────────────────────────────────────────

def tex_escape(s: str) -> str:
    """Escape characters that are special in LaTeX."""
    replacements = [
        ('\\', r'\textbackslash{}'),
        ('&',  r'\&'),
        ('%',  r'\%'),
        ('$',  r'\$'),
        ('#',  r'\#'),
        ('{',  r'\{'),
        ('}',  r'\}'),
        ('~',  r'\textasciitilde{}'),
        ('^',  r'\textasciicircum{}'),
        ('_',  r'\_'),
    ]
    for old, new in replacements:
        s = s.replace(old, new)
    return s


# Helper: wrap a table body in the Dissertate-compatible table shell.
# Uses \hline (no booktabs), singlespacing, \sffamily to match the caption
# package settings in Dissertate.cls (labelfont/textfont both sf).
def _table_shell(caption: str, label: str, col_spec: str, header_row: str,
                 body_rows: list[str], footer_row: str | None = None) -> str:
    lines = []
    lines.append(r"\begin{table}[htbp]")
    lines.append(r"  \centering")
    lines.append(f"  \\caption{{{caption}}}")
    lines.append(f"  \\label{{{label}}}")
    lines.append(r"  \begin{spacing}{1.0}")        # singlespacing inside table
    lines.append(r"  \sffamily")                   # match Dissertate caption font
    lines.append(f"  \\begin{{tabular}}{{{col_spec}}}")
    lines.append(r"    \hline")
    lines.append(f"    {header_row} \\\\")
    lines.append(r"    \hline\hline")
    for row in body_rows:
        lines.append(f"    {row} \\\\")
    if footer_row is not None:
        lines.append(r"    \hline")
        lines.append(f"    {footer_row} \\\\")
    lines.append(r"    \hline")
    lines.append(r"  \end{tabular}")
    lines.append(r"  \end{spacing}")
    lines.append(r"\end{table}")
    return "\n".join(lines)


def latex_overview_table(totals: dict, library: dict) -> str:
    """Compact two-column table: one key stat per row, no sub-rows."""
    props = sum(totals["items"].get(c, 0) for c in PROP_CATEGORIES)
    defs  = sum(totals["items"].get(c, 0) for c in DEF_CATEGORIES)
    types = sum(totals["items"].get(c, 0) for c in TYPE_CATEGORIES)
    avg   = (totals["proof_lines"] / totals["proofs"]) if totals["proofs"] else 0

    data = [
        ("Source files",        totals["files"]),
        ("Lines of code",       totals["code_lines"]),
        ("Propositions",        props),
        ("Definitions",         defs),
        ("Type definitions",    types),
        ("Proofs",              totals["proofs"]),
        (r"Avg.\ proof length", f"{avg:.1f}"),
    ]

    header = r"\textsc{Metric} & \textsc{Count}"
    body   = [f"{label} & {value}" for label, value in data]
    return _table_shell(
        caption   = "VizingThesis library overview",
        label     = "tab:library-overview",
        col_spec  = "lr",
        header_row= header,
        body_rows = body,
    )


def latex_summary_table(totals: dict) -> str:
    """Detailed grouped summary table."""
    props = sum(totals["items"].get(c, 0) for c in PROP_CATEGORIES)
    defs  = sum(totals["items"].get(c, 0) for c in DEF_CATEGORIES)
    types = sum(totals["items"].get(c, 0) for c in TYPE_CATEGORIES)
    avg   = (totals["proof_lines"] / totals["proofs"]) if totals["proofs"] else 0

    def r(label, value, indent=False):
        prefix = r"\quad " if indent else ""
        return f"{prefix}{tex_escape(label)} & {value}"

    def section_header(title):
        return rf"\multicolumn{{2}}{{l}}{{\textit{{{title}}}}}"

    body = [
        section_header("Lines of code"),
        r(  "Total lines",     totals["raw_lines"]),
        r(  "Code lines",      totals["code_lines"],    indent=True),
        r(  "Comment lines",   totals["comment_lines"], indent=True),
        r(  "Blank lines",     totals["blank_lines"],   indent=True),
        r"\hline",  # inline rule between sections
        section_header("Propositions"),
        r(  "Total",           props),
        r(  "Lemmas",          totals["items"].get("Lemma", 0),        indent=True),
        r(  "Theorems",        totals["items"].get("Theorem", 0),      indent=True),
        r(  "Corollaries",     totals["items"].get("Corollary", 0),    indent=True),
        r(  "Propositions",    totals["items"].get("Proposition", 0),  indent=True),
        r(  "Facts/Remarks",   totals["items"].get("Fact", 0)
                             + totals["items"].get("Remark", 0),       indent=True),
        r"\hline",
        section_header("Definitions"),
        r(  "Total",           defs),
        r(  "Definition",      totals["items"].get("Definition", 0),   indent=True),
        r(  "Fixpoint",        totals["items"].get("Fixpoint", 0),     indent=True),
        r"\hline",
        section_header("Type definitions"),
        r(  "Total",           types),
        r(  "Inductive",       totals["items"].get("Inductive", 0),    indent=True),
        r(  "Record",          totals["items"].get("Record", 0),       indent=True),
        r(  "Class",           totals["items"].get("Class", 0),        indent=True),
        r(  "Instance",        totals["items"].get("Instance", 0),     indent=True),
        r"\hline",
        section_header("Other"),
        r(  "Notations",       totals["items"].get("Notation", 0)),
        r(  "Axioms",          totals["items"].get("Axiom", 0)),
        r(  "Tactics (Ltac)",  totals["items"].get("Tactic", 0)),
        r"\hline",
        section_header("Proofs"),
        r(  "Total proofs",    totals["proofs"]),
        r(  "Total proof lines", totals["proof_lines"],                indent=True),
        r(  "Avg.\ proof length", f"{avg:.1f}",                        indent=True),
        r(  "Admitted/sorry",  totals["admitted"],                     indent=True),
    ]

    # _table_shell appends \\ to every row, but inline \hline rows must not
    # have \\ — so we post-process: rows that are bare \hline are emitted as-is.
    lines = []
    lines.append(r"\begin{table}[htbp]")
    lines.append(r"  \centering")
    lines.append(r"  \caption{VizingThesis library statistics}")
    lines.append(r"  \label{tab:library-stats}")
    lines.append(r"  \begin{spacing}{1.0}")
    lines.append(r"  \sffamily")
    lines.append(r"  \begin{tabular}{lr}")
    lines.append(r"    \hline")
    lines.append(r"    \textsc{Metric} & \textsc{Count} \\")
    lines.append(r"    \hline\hline")
    for item in body:
        if item == r"\hline":
            lines.append(r"    \hline")
        else:
            lines.append(f"    {item} \\\\")
    lines.append(r"    \hline")
    lines.append(r"  \end{tabular}")
    lines.append(r"  \end{spacing}")
    lines.append(r"\end{table}")
    return "\n".join(lines)


def latex_perfile_table(library: dict) -> str:
    """One row per .v file with a totals footer."""
    col_totals = [0] * 7
    body = []
    for stem, s in library.items():
        code   = s["raw_lines"] - s["blank_lines"] - s["comment_lines"]
        lemmas = sum(len(s["items"].get(c, [])) for c in PROP_CATEGORIES)
        defs   = sum(len(s["items"].get(c, [])) for c in DEF_CATEGORIES)
        inds   = sum(len(s["items"].get(c, [])) for c in TYPE_CATEGORIES)
        vals   = [s["raw_lines"], code, lemmas, defs, inds, s["proofs"], s["admitted"]]
        for i, v in enumerate(vals):
            col_totals[i] += v
        body.append(
            f"\\texttt{{{tex_escape(stem)}}} & "
            + " & ".join(str(v) for v in vals)
        )

    header = (r"\textsc{File} & \textsc{Lines} & \textsc{Code}"
              r" & \textsc{Lemmas} & \textsc{Defs} & \textsc{Ind}"
              r" & \textsc{Proofs} & \textsc{Adm}")
    footer = (r"\textbf{Total} & "
              + " & ".join(f"\\textbf{{{v}}}" for v in col_totals))

    return _table_shell(
        caption    = "Per-file breakdown of the VizingThesis library",
        label      = "tab:library-perfile",
        col_spec   = "lrrrrrrr",
        header_row = header,
        body_rows  = body,
        footer_row = footer,
    )


def render_latex(totals: dict, library: dict) -> str:
    parts = [
        "% Generated by stats.py --- do not edit by hand",
        "% Compatible with Dissertate.cls (no booktabs required).",
        "% Requires \\usepackage{setspace} (already loaded by Dissertate).",
        "",
        "% -- Overview (compact) -----------------------------",
        latex_overview_table(totals, library),
        "",
        "% -- Full summary -----------------------------------",
        latex_summary_table(totals),
        "",
        "% -- Per-file breakdown -----------------------------",
        latex_perfile_table(library),
    ]
    return "\n".join(parts)



def main():
    parser = argparse.ArgumentParser(
        description="Print statistics about the VizingThesis Rocq library.")
    parser.add_argument(
        "--verbose", "-v", action="store_true",
        help="(plain-text mode) Also list every named lemma/definition.")
    parser.add_argument(
        "--latex", "-l", action="store_true",
        help="Output LaTeX tables instead of plain text.")
    parser.add_argument(
        "--out", "-o", metavar="FILE",
        help="Write output to FILE instead of stdout (useful with --latex).")
    parser.add_argument(
        "--dir", default=str(THEORIES_DIR), metavar="DIR",
        help=f"Path to theories directory (default: {THEORIES_DIR})")
    args = parser.parse_args()

    theories = Path(args.dir)
    if not theories.is_dir():
        print(f"Error: theories directory not found: {theories}")
        print("Run from vizing-thesis/depend-graph/ or pass --dir <path>")
        raise SystemExit(1)

    library = collect_library(theories)
    totals  = aggregate(library)

    if args.latex:
        output = render_latex(totals, library)
        if args.out:
            Path(args.out).write_text(output + "\n", encoding="utf-8")
            print(f"Wrote LaTeX to {args.out}")
        else:
            print(output)
    else:
        import sys
        out = open(args.out, "w", encoding="utf-8") if args.out else sys.stdout
        # Redirect print to file if needed
        _print = print
        if args.out:
            import builtins
            def _print(*a, **kw): builtins.print(*a, **kw, file=out)

        print_summary(totals, library)
        print_per_file(library)
        if args.verbose:
            print_verbose(library)
        _print()
        if args.out:
            out.close()
            builtins.print(f"Wrote plain-text stats to {args.out}")


if __name__ == "__main__":
    main()