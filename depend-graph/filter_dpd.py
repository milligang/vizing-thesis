import re
import subprocess
import os

SCRIPT_DIR   = os.path.dirname(os.path.abspath(__file__))
DPD_FILE     = os.path.join(SCRIPT_DIR, "graph.dpd")
FILTERED_DPD = os.path.join(SCRIPT_DIR, "graph_filtered.dpd")
OUT_FILE     = os.path.join(SCRIPT_DIR, "graph_filtered.dot")

EXCLUDE_PATTERNS = [
    r'HB_unnamed_',
    r'__canonical__',
    r'__to__',
    r'^choice_',
]

def should_exclude(name):
    return any(re.search(p, name) for p in EXCLUDE_PATTERNS)

def filter_dpd(input_path, output_path):
    with open(input_path) as f:
        lines = f.readlines()

    excluded_ids = set()

    for line in lines:
        m = re.match(r'^N:\s*(\d+)\s+"([^"]+)"', line)
        if m:
            node_id, name = m.group(1), m.group(2)
            if should_exclude(name):
                excluded_ids.add(node_id)

    print(f"Excluding {len(excluded_ids)} nodes")

    with open(output_path, 'w') as f:
        for line in lines:
            m = re.match(r'^N:\s*(\d+)\s+', line)
            if m and m.group(1) in excluded_ids:
                continue
            m = re.match(r'^E:\s*(\d+)\s+(\d+)', line)
            if m and (m.group(1) in excluded_ids or m.group(2) in excluded_ids):
                continue
            f.write(line)

if __name__ == "__main__":
    filter_dpd(DPD_FILE, FILTERED_DPD)

    # dpd2dot always outputs <name>.dot in the CWD, so run it from SCRIPT_DIR
    subprocess.run(["dpd2dot", "graph_filtered.dpd"], check=True, cwd=SCRIPT_DIR)