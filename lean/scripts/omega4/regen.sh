#!/bin/bash
# Regenerate every generated certificate file of the Ω ≤ 4 proof (run from any directory).
# Needs python3 with mpmath. Check the result with `git status` / `git diff` (expected: no change).
set -e
H=$(cd "$(dirname "$0")" && pwd)
python3 "$H/major1d/gen_lean.py"                  # Palprimes/Major1D/Data.lean
python3 "$H/major2d/gen.py" 2                     # Palprimes/Major2D/B2Data.lean
python3 "$H/major2d/gen.py" 3                     # Palprimes/Major2D/B3Data.lean
python3 "$H/major2d/gen_chunks.py" 650 2          # B2C000 … B2C110, B2Chunks (nodes_b2.json)
python3 "$H/major2d/gen_chunks.py" 600 3          # B3C000 … B3C002, B3Chunks (nodes_b3.json)
python3 "$H/major2d/gen_tabs.py" 2 x split 12     # B2Tab00 … B2Tab10, B2Tab; tablv2.txt
python3 "$H/major2d/gen_tabs.py" 3                # B3Tab; tablv3.txt
# Optional, slow: recompute the node counts used for the chunking
# python3 "$H/major2d/nodes.py" 2; python3 "$H/major2d/nodes.py" 3
