/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Selection
import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Phase-head identification on the `SO` carrier

[marcolli-chomsky-berwick-2025] Lemma 1.13.7; [chomsky-2000]. P3b of the
single-carrier program: phase-head identification on `SO`, derived from the
**selection-driven head** (`SO.outerCatC`, #800) — the projecting head's outer
category. Section-free and computable, so concrete phase-head checks `decide`.

Because the head is the *selector* (Lemma 1.13.7), the test is
**convention-independent**: it does not depend on a head-initial/head-final planar
embedding (the carrier is unordered anyway). The structural phase *domain*
(complement Z_ℓ / interior Φ°, MCB Def 1.14.2–3) is section/structure-coupled and
stays out of scope here (P3c/P4).
-/

namespace Minimalist

open RootedTree

/-- **Phase-head test on `SO`** ([marcolli-chomsky-berwick-2025] Lemma 1.13.7):
    is the projecting (selection-driven) head's outer category exactly `c`?
    `none` (≠ `some c`) at exocentric nodes. The carrier-native counterpart of
    `Minimalist.isPhaseHeadOf`.

    Phase-head selectors (call directly): C — `isPhaseHeadOf .C` (linglib default
    per [keine-2020]; the Chomsky v-phase extension is `… .C s || … .v s`); D —
    `isPhaseHeadOf .D` ([citko-2014]); SA — `isPhaseHeadOf .SA`. -/
def SO.isPhaseHeadOf (c : Cat) (s : SO) : Bool := s.outerCatC == some c

@[simp] theorem SO.isPhaseHeadOf_lexLeaf (c : Cat) (tok : LIToken) :
    SO.isPhaseHeadOf c (SO.lexLeaf tok) = (tok.item.outerCat == c) := by
  rw [SO.isPhaseHeadOf, SO.outerCatC_lexLeaf]; rfl

/-! ### `decide` demonstrations

Phase-head checks reduce on concrete `mk`-built trees. A two-leaf clause where the
left head c-selects the right: the selector projects, regardless of which side it
sits on (the carrier is unordered) — so the phase head is the selector. -/

/-- A two-leaf bare node over the given tokens (built planar-first via the DSL;
    `SO.node` is noncomputable). -/
private def clause (head comp : LIToken) : SO :=
  SO.ofPlanar (SO.nodeP (SO.leafP head) (SO.leafP comp))

/-- A C selecting a T projects C: the node is a **C-phase**, not a v-phase. -/
example :
    SO.isPhaseHeadOf .C (clause ⟨.simple .C [.T], 0⟩ ⟨.simple .T [], 1⟩) = true
    ∧ SO.isPhaseHeadOf .v (clause ⟨.simple .C [.T], 0⟩ ⟨.simple .T [], 1⟩) = false := by
  decide

/-- A D selecting an N projects D: the node is a **D-phase** ([citko-2014]). -/
example : SO.isPhaseHeadOf .D (clause ⟨.simple .D [.N], 0⟩ ⟨.simple .N [], 1⟩) = true := by
  decide

/-- **Convention-independence**: swapping the two daughters (the carrier is
    unordered, so the trees are *equal*) leaves the phase head unchanged. -/
example :
    clause ⟨.simple .C [.T], 0⟩ ⟨.simple .T [], 1⟩
      = clause ⟨.simple .T [], 1⟩ ⟨.simple .C [.T], 0⟩ := by decide

end Minimalist
