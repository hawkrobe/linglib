/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Selection
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm
import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Phase theory on the `SO` carrier

[marcolli-chomsky-berwick-2025] §1.14 (Def 1.14.1–1.14.4); [chomsky-2000].

**P3b — phase-head identification**: derived from the **selection-driven head**
(`SO.outerCatC`, #800) — the projecting head's outer category. Because the head is
the *selector* (Lemma 1.13.7), the test is **convention-independent** (the carrier
is unordered anyway).

**P3c-2 — the structural phase domain** (Def 1.14.2–1.14.3), grounded **directly in
MCB** rather than the legacy section-based `phaseComplementZ`/`complementInPlanar`
walk (which carried a `side` parameter and a non-commutative `<|>` fallback — a
section artifact with no place on the unordered carrier). MCB states everything in
terms of **subtrees, containment, and the head's sister** — exactly the invariant,
decidable P2 substrate (`subtrees`/`Acc`/`containsOrEq`/`areSistersIn`/`cCommandsIn`,
#797–798) and the selection head (`selHead`, #800). So the whole phase domain is a
**filter over the already-lifted subterm API** — no section, no `Quot.out`, no fresh
`PermEquiv` proof, and every notion `decide`s.

The keystone identity: the **interior Φ°_ℓ (Def 1.14.3) is the phase head's
c-command domain**, `{T_v ∈ Acc(T) | T_v ⊆ T_{s_ℓ}} = Acc.filter (cCommandsIn …
(lexLeaf ℓ))` — the standard "complement domain = head's c-command domain" falling
out of the formalization.
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

/-! ### The phase domain (MCB Def 1.14.2–1.14.3)

The head function on `SO` is `selHead` (#800); a phase is relative to a tree `T` and
a phase-head leaf `ℓ` (the study supplies *which* leaf, per the per-analysis
discipline — C / C+v / +D / +Voice). Every notion is a filter over the invariant
subterm API (`subtrees`/`Acc`/`containsOrEq`/`areSistersIn`/`cCommandsIn`), so it
`decide`s — no section, no `Quot.out`, no fresh `PermEquiv` proof. -/

/-- **L_Φ(T)** ([marcolli-chomsky-berwick-2025] Def 1.14.3 eq 1.14.1): `ℓ` is a
    **phase head** in `T` when its projection path γ_ℓ is nontrivial — the leaf
    `lexLeaf ℓ` has a mother whose head is still `ℓ` (so γ_ℓ reaches an internal
    vertex). Read off `selHead` at the mother; section-free. -/
def SO.isPhaseHead (T : SO) (ℓ : LIToken) : Prop :=
  ∃ n ∈ T.subtrees, SO.immediatelyContains n (SO.lexLeaf ℓ) ∧ n.selHead = some ℓ

instance (T : SO) (ℓ : LIToken) : Decidable (SO.isPhaseHead T ℓ) :=
  Multiset.decidableExistsMultiset

/-- **Within the maximal projection** `T_v ⊆ T_{v_ℓ}`
    ([marcolli-chomsky-berwick-2025] Def 1.14.3): section-free characterization —
    `T_v` is contained in *some* `ℓ`-headed subtree. The maximal projection `v_ℓ`
    is the largest `ℓ`-headed subtree, so `T_v ⊆ T_{v_ℓ}` iff `T_v` sits inside one
    of them (all `ℓ`-headed vertices lie on γ_ℓ below `v_ℓ`). -/
def SO.withinProjection (T : SO) (ℓ : LIToken) (Tv : SO) : Prop :=
  ∃ p ∈ T.subtrees, p.selHead = some ℓ ∧ SO.containsOrEq p Tv

instance (T : SO) (ℓ : LIToken) (Tv : SO) : Decidable (SO.withinProjection T ℓ Tv) :=
  Multiset.decidableExistsMultiset

/-- **The phase Φ_ℓ** ([marcolli-chomsky-berwick-2025] Def 1.14.3 eq 1.14.2):
    `{T_v ∈ Acc'(T) | T_v ⊆ T_{v_ℓ}}` — all accessible terms within the maximal
    projection (`Acc'(T) = T.subtrees`, including the root). -/
def SO.phase (T : SO) (ℓ : LIToken) : Multiset SO :=
  T.subtrees.filter (fun Tv => SO.withinProjection T ℓ Tv)

/-- **The interior Φ°_ℓ** ([marcolli-chomsky-berwick-2025] Def 1.14.3 eq 1.14.3):
    `{T_v ∈ Acc(T) | T_v ⊆ T_{s_ℓ}}` — the head's sister `T_{s_ℓ}` and all of its
    accessible terms; the part the PIC freezes ("Z is the interior of the phase").

    This **is the phase head's c-command domain**: `T_v ⊆ T_{s_ℓ}` exactly when the
    sister of `ℓ` contains-or-equals `T_v`, i.e. `cCommandsIn T (lexLeaf ℓ) T_v`
    (#798). The textbook "complement domain = head's c-command domain", by
    construction — and `Acc(T) = T.Acc` (non-root). -/
def SO.phaseInterior (T : SO) (ℓ : LIToken) : Multiset SO :=
  T.Acc.filter (fun Tv => SO.cCommandsIn T (SO.lexLeaf ℓ) Tv)

/-- **The edge ∂Φ_ℓ** ([marcolli-chomsky-berwick-2025] Def 1.14.3 eq 1.14.4):
    `{T_v ∈ Acc'(T) | T_v ⊆ T_{v_ℓ} ∧ T_v ⊄ T_{s_ℓ}}` — the phase content not in
    the interior (head, specifiers, modifiers); `= Φ_ℓ` when the complement is
    empty. Computed as `phase ∖ interior`. -/
def SO.phaseEdge (T : SO) (ℓ : LIToken) : Multiset SO :=
  (T.phase ℓ).filter (fun Tv => Tv ∉ T.phaseInterior ℓ)

/-- **Phase Impenetrability Condition**: `goal` is frozen in the phase headed by `ℓ`
    iff it lies in the interior (= the complement domain). True by construction — the
    PIC *is* interior membership ([marcolli-chomsky-berwick-2025] §1.14). -/
def SO.Impenetrable (T : SO) (ℓ : LIToken) (goal : SO) : Prop :=
  goal ∈ T.phaseInterior ℓ

instance (T : SO) (ℓ : LIToken) (goal : SO) : Decidable (SO.Impenetrable T ℓ goal) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-! ### Membership characterizations -/

@[simp] theorem SO.mem_phase {T : SO} {ℓ : LIToken} {Tv : SO} :
    Tv ∈ T.phase ℓ ↔ Tv ∈ T.subtrees ∧ SO.withinProjection T ℓ Tv :=
  Multiset.mem_filter

/-- **The interior is the phase head's (non-root) c-command domain** — the keystone
    identity (MCB Def 1.14.3, "Z is the interior of the phase"). -/
@[simp] theorem SO.mem_phaseInterior {T : SO} {ℓ : LIToken} {Tv : SO} :
    Tv ∈ T.phaseInterior ℓ ↔ Tv ∈ T.Acc ∧ T.cCommandsIn (SO.lexLeaf ℓ) Tv :=
  Multiset.mem_filter

@[simp] theorem SO.mem_phaseEdge {T : SO} {ℓ : LIToken} {Tv : SO} :
    Tv ∈ T.phaseEdge ℓ ↔ Tv ∈ T.phase ℓ ∧ Tv ∉ T.phaseInterior ℓ :=
  Multiset.mem_filter

/-- The PIC freezes exactly the head's (non-root) c-command domain. -/
theorem SO.Impenetrable_iff {T : SO} {ℓ : LIToken} {goal : SO} :
    SO.Impenetrable T ℓ goal ↔ goal ∈ T.Acc ∧ T.cCommandsIn (SO.lexLeaf ℓ) goal :=
  SO.mem_phaseInterior

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

/-! ### `decide` demonstrations — the phase domain

A clause `[C [T V]]`: C selects T, T selects V, so C projects and its sister is the
TP. The phase headed by C freezes everything inside TP (the interior), keeps C
itself at the edge. Both layers tested: a deep term is impenetrable, the head is
not, and the head's projection is detected. -/

private def cTok : LIToken := ⟨.simple .C [.T], 0⟩
private def tTok : LIToken := ⟨.simple .T [.V], 1⟩
private def vTok : LIToken := ⟨.simple .V [], 2⟩

private def cP : SO :=
  SO.ofPlanar (SO.nodeP (SO.leafP cTok) (SO.nodeP (SO.leafP tTok) (SO.leafP vTok)))

/-- C heads a nontrivial phase (it projects over the TP). -/
example : SO.isPhaseHead cP cTok := by decide

/-- The embedded `V` is in C's complement domain — **frozen** by the PIC. -/
example : SO.Impenetrable cP cTok (SO.lexLeaf vTok) := by decide

/-- The phase head `C` is at the **edge** — *not* frozen (it can still probe out). -/
example : ¬ SO.Impenetrable cP cTok (SO.lexLeaf cTok) := by decide

/-- …and `C` sits in the edge, not the interior. -/
example : SO.lexLeaf cTok ∈ cP.phaseEdge cTok := by decide

end Minimalist
