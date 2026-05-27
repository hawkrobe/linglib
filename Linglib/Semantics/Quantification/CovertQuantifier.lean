import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Linglib.Core.Logic.Intensional.Frame
import Linglib.Semantics.Composition.LexEntry

/-!
# Covert Operators: Theory and Compositional Interface

@cite{krifka-etal-1995} @cite{carlson-1977} @cite{guerrini-2026}

Covert operators (Gen, DIST, Hab, DPP) are semantically contentful LF nodes
with no overt realization. This module provides:

1. **Abstract quantifier theory** (`covertQ`, `measure`, `thresholdQ`) —
   domain-polymorphic semantics with eliminability proofs. GEN and HAB
   are both instances.

2. **Montague-typed constructors** (`gen`, `genThreshold`, `dist`, `dpp`,
   `hab`) — `LexEntry` values that compose via FA in `evalTree`.
   These package the theory-layer semantics for tree-based interpretation.

## Usage

```
open Semantics.Quantification.CovertQuantifier (genThreshold dist dpp extendLexicon)

def myLex : Lexicon FyModel :=
  extendLexicon baseLex
    [("Gen",  genThreshold myFrame atoms 2 3),
     ("DIST", dist myFrame atomsOf)]
```
-/

namespace Semantics.Quantification.CovertQuantifier

variable {D : Type}

/-- A covert quantifier: `∀d ∈ domain. restriction(d) → scope(d)`.
GEN instantiates with `D = Situation`, `restriction = normal ∧ restrictor`
(see `traditionalGEN` in `Genericity/Generics.lean`). The "habituality is
genericity" view (@cite{chierchia-1995}, @cite{krifka-etal-1995}) treats
HAB the same way; the Boneh–Doron view (@cite{boneh-doron-2013}) treats
HAB as a structurally distinct existential, not a `covertQ` instance —
see `Studies/BonehDoron2013.lean`. -/
def covertQ (domain : List D) (restriction : D → Bool) (scope : D → Bool) : Bool :=
  domain.all λ d => !restriction d || scope d

/-- Dual formulation: no counterexample exists. -/
def covertQ_dual (domain : List D) (restriction : D → Bool) (scope : D → Bool) : Bool :=
  !domain.any λ d => restriction d && !scope d

/-- The two formulations are equivalent (De Morgan). -/
theorem covertQ_equiv (domain : List D) (restriction : D → Bool) (scope : D → Bool) :
    covertQ domain restriction scope = covertQ_dual domain restriction scope := by
  simp only [covertQ, covertQ_dual, List.all_eq_not_any_not]
  congr 1
  induction domain with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.any_cons]
    rw [ih]
    cases restriction d <;> cases scope d <;> rfl

/-- Measure: proportion of restriction-satisfying cases where scope holds. -/
def measure (domain : List D) (restriction : D → Bool) (scope : D → Bool) : ℚ :=
  let restricted := domain.filter restriction
  let satisfied := restricted.filter scope
  if restricted.length = 0 then 0
  else (satisfied.length : ℚ) / (restricted.length : ℚ)

/-- Threshold-based alternative: measure > θ. -/
def thresholdQ (domain : List D) (restriction : D → Bool)
    (scope : D → Bool) (θ : ℚ) : Bool :=
  measure domain restriction scope > θ

/-- Measure is non-negative. -/
theorem measure_nonneg (domain : List D) (restriction : D → Bool) (scope : D → Bool) :
    measure domain restriction scope ≥ 0 := by
  simp only [measure]
  by_cases h : (domain.filter restriction).length = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

/-- Measure is at most 1 (when restriction domain is non-empty). -/
theorem measure_le_one (domain : List D) (restriction : D → Bool) (scope : D → Bool)
    (hNonEmpty : (domain.filter restriction).length > 0) :
    measure domain restriction scope ≤ 1 := by
  simp only [measure]
  have hPos : (domain.filter restriction).length ≠ 0 := Nat.pos_iff_ne_zero.mp hNonEmpty
  simp only [hPos, ↓reduceIte]
  have hLenLe : (List.filter scope (List.filter restriction domain)).length ≤
                (List.filter restriction domain).length :=
    List.length_filter_le _ _
  have hDenom : (0 : ℚ) < ↑(List.filter restriction domain).length := by
    rw [Nat.cast_pos]; exact hNonEmpty
  calc (↑(List.filter scope (List.filter restriction domain)).length : ℚ) /
         ↑(List.filter restriction domain).length
       ≤ ↑(List.filter restriction domain).length /
         ↑(List.filter restriction domain).length := by
           apply div_le_div_of_nonneg_right
           · exact Nat.cast_le.mpr hLenLe
           · exact le_of_lt hDenom
     _ = 1 := div_self (ne_of_gt hDenom)

/-- Any covert quantifier configuration can be matched by threshold semantics.

    Note: this is a *degeneracy* result — the existential threshold is either -1
    (if Q holds) or 1 (if Q fails). It shows eliminability in principle, not that
    the threshold is informative. The RSA treatment adds substance by making the
    threshold uncertain and pragmatically inferred. -/
theorem reduces_to_threshold (domain : List D)
    (restriction : D → Bool) (scope : D → Bool)
    (hNonEmpty : (domain.filter restriction).length > 0) :
    ∃ θ : ℚ, covertQ domain restriction scope =
             thresholdQ domain restriction scope θ := by
  let m := measure domain restriction scope
  by_cases hQ : covertQ domain restriction scope
  · -- Q = true: pick θ = -1
    use -1
    simp only [thresholdQ, hQ]
    have hNonneg := measure_nonneg domain restriction scope
    symm; rw [decide_eq_true_iff]
    have h : (-1 : ℚ) < 0 := by decide
    linarith
  · -- Q = false: pick θ = 1
    use 1
    simp only [thresholdQ]
    have hLe := measure_le_one domain restriction scope hNonEmpty
    have hNotQ : covertQ domain restriction scope = false := by
      simp only [Bool.eq_false_iff]; exact hQ
    simp only [hNotQ]
    symm; rw [decide_eq_false_iff_not]
    intro hContra; linarith

/-! ### Montague-Typed Constructors -/

section Compositional

open Core.Logic.Intensional
open Semantics.Montague (LexEntry Lexicon)

/-- Gen: `(e→t) → (e→t) → t`. Dyadic generic quantifier.

    `generally` encodes the truth conditions — different theories
    instantiate it differently (threshold, normalcy, probabilistic).
    `traditionalGEN` (in `Generics.lean`) and `thresholdQ` (above)
    are specific instantiations. -/
def gen (F : Frame)
    (generally : (F.Entity → Prop) → (F.Entity → Prop) → Prop)
    : LexEntry F :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, generally⟩

open Classical in
/-- Gen with threshold: true iff ≥ `num/denom` of restrictor-satisfying
    atoms also satisfy scope. Montague-typed counterpart of `thresholdQ`. -/
noncomputable def genThreshold (F : Frame) (atoms : List F.Entity)
    (num denom : Nat) : LexEntry F :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, fun restr scope =>
    let restricted := atoms.filter (fun x => decide (restr x))
    let both := restricted.filter (fun x => decide (scope x))
    denom * both.length ≥ num * restricted.length⟩

/-- DIST: `(e→t) → (e→t)`. Distributive operator.

    `atomsOf x` returns the atomic parts of x — for atomic entities
    it returns `[x]`, for plural/kind entities their parts.
    Montague-typed counterpart of `Distributivity.distMaximal`. -/
def dist (F : Frame) (atomsOf : F.Entity → List F.Entity)
    : LexEntry F :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t), fun P x => ∀ a ∈ atomsOf x, P a⟩

/-- DPP: `(e→t) → (e→t) → t`. Derived Property Predication.

    DPP(P)(Q) = ∃x[P(x) ∧ Q(x)]. An existential type-shift for
    kind-denoting NPs combining with stage-level predicates.
    @cite{guerrini-2026} structure (105b). -/
def dpp (F : Frame) (atoms : List F.Entity) : LexEntry F :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t) ⇒ .t, fun prop pred =>
    ∃ x ∈ atoms, prop x ∧ pred x⟩

/-- Hab: `(e→t) → (e→t)`. Habitual aspectual operator.

    `h` maps a predicate to its habitual counterpart.
    On the Chierchia/Krifka "Hab-is-Gen" view, `h` collapses into the
    universal `covertQ` skeleton above; on the Boneh–Doron view it is a
    distinct existential operator (see
    `Studies/BonehDoron2013.lean`). -/
def hab (F : Frame) (h : (F.Entity → Prop) → (F.Entity → Prop))
    : LexEntry F :=
  ⟨(.e ⇒ .t) ⇒ (.e ⇒ .t), h⟩

/-- EXH: `(s→t) → (s→t)`. Exhaustivity operator (proposition modifier).

    `exhOp` maps a proposition to its exhaustified version — typically
    asserting the prejacent and negating innocently excludable alternatives.
    The canonical computational implementation is `exhIE` from
    `Exhaustification.Innocent` (the Set-spec is `exhIE` in
    `Exhaustification.Operators`). Specific instances are plugged in at
    lexicon construction time with alternatives and world domain baked
    into the closure.

    Unlike Gen/DIST/Hab (which quantify over entities), EXH operates on
    propositions (`s→t`). Both compose via FA in the same tree — the
    Montague type system handles the dispatch:
    - Gen:  `(e→t) → (e→t) → t`  — FA with entity predicates
    - EXH:  `(s→t) → (s→t)`      — FA with propositions -/
def exh (F : Frame) (exhOp : (F.Index → Prop) → (F.Index → Prop))
    : LexEntry F :=
  ⟨(.intens .t) ⇒ (.intens .t), exhOp⟩

/-- Extend a lexicon with named covert operators. -/
def extendLexicon {F : Frame} (base : Lexicon F)
    (ops : List (String × LexEntry F)) : Lexicon F :=
  fun s => match ops.find? (fun p => p.1 == s) with
    | some (_, entry) => some entry
    | none => base s

end Compositional

end Semantics.Quantification.CovertQuantifier
