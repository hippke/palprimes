#!/bin/bash
# Usage: scripts/check_item.sh L07   — checks Omega3/Items/L07.lean (theorem Omega3.itemL07 : Omega3.ItemL07).
# Prints PASS or FAIL with the reason. Modelled on lean/omega3/pilot/scripts/check.sh.
X=$1; D=/astro/palindromic-primes/lean/omega3/main; cd $D || exit 2
F=Omega3/Items/$X.lean
[ -n "$X" ] || { echo "usage: scripts/check_item.sh <ID>"; exit 2; }
[ -f "$F" ] || { echo "FAIL: $F missing"; exit 1; }
if [ -f scripts/frozen.sha256 ]; then
  sha256sum -c --quiet scripts/frozen.sha256 || { echo "FAIL: frozen files changed"; exit 1; }
else
  echo "WARNING: scripts/frozen.sha256 missing (statements not frozen yet)"
fi
grep -q "^def Item$X : Prop" Omega3/Statements.lean || { echo "FAIL: no Item$X in Omega3/Statements.lean"; exit 1; }
if grep -n -E '\bsorry\b|\badmit\b|\baxiom\b|native_decide|implemented_by|@\[extern|debug\.|unsafe|opaque|elab_rules|macro_rules|^\s*set_option\s+(debug|trace\.Kernel|kernel)' "$F"; then
  echo "FAIL: forbidden token in $F"; exit 1; fi
head -c 400 "$F" | grep -q 'import Omega3.Statements' || { echo "FAIL: $F must import Omega3.Statements"; exit 1; }
# an item file may import Mathlib, Palprimes, Omega3.Statements and its own helper modules Omega3.Items.<X>_*, never another item
if grep -E '^import Omega3\.Items\.' "$F" | grep -v -E "^import Omega3\.Items\.${X}(_[A-Za-z0-9]+)?\s*$"; then
  echo "FAIL: $F imports another item"; exit 1; fi
if grep -E '^import Omega3\.(Skel|Skeleton|Final)' "$F"; then echo "FAIL: $F imports the skeleton"; exit 1; fi
T=$(mktemp -d /tmp/claude-1000/omega3chk.XXXX 2>/dev/null || mktemp -d); C=$T/Check$X.lean
printf 'import Omega3.Items.%s\nexample : Omega3.Item%s := Omega3.item%s\n#print axioms Omega3.item%s\n' $X $X $X $X > $C
OUT=$(systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 nice -n 10 timeout 3600 lake build Omega3.Items.$X 2>&1); RC=$?
if [ $RC -ne 0 ]; then echo "$OUT" | grep -v 'module system' | tail -40; echo "FAIL: build rc $RC"; exit 1; fi
AX=$(systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 nice -n 10 timeout 1800 lake env lean $C 2>&1); RC=$?
echo "$AX" | grep -v 'module system'
[ $RC -eq 0 ] || { echo "FAIL: check file rc $RC"; exit 1; }
echo "$AX" | grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]\|does not depend on any axioms\|depends on axioms: \[propext\]\|depends on axioms: \[propext, Quot.sound\]\|depends on axioms: \[Classical.choice\]\|depends on axioms: \[propext, Classical.choice\]\|depends on axioms: \[Classical.choice, Quot.sound\]\|depends on axioms: \[Quot.sound\]" || { echo "FAIL: non-standard axioms"; exit 1; }
rm -rf $T
echo "PASS Item$X $(date +%T)"
