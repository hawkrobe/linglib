/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Modality.Selectional

/-!
# Selectional `will`-Conditionals
[cariani-santorio-2018]

[cariani-santorio-2018] §5.3.1 lifts the selectional analysis of *will*
to conditionals via Kratzerian restriction: an *if*-clause restricts the
modal parameter `f` to its intersection with the antecedent's truth set.
The restriction rule is paper eq. (21); eq. (20) is the LF of the example
sentence and eq. (23) its informal English gloss.

`⟦if A, will B⟧^{w,s,g} = ⟦will B⟧^{w,s,g[f ↦ g(f) ∩ ‖A‖]}`
                       `= B (s(w, g(f) ∩ ‖A‖))`

The semantic rule lives in §5.3.1; §7 then derives the predicted
compositional CEM and Negation-Swap-in-Conditionals theorems as
*consequences* of this restriction rule combined with selection
single-valuedness.

## What's here

- `restrict`: the Kratzer restriction operation `f ∩ ‖A‖` shared by
  every will-conditional construction in this file.
- `willConditional`: the restrictor analysis applied to the selectional
  `will`. The if-clause intersects the modal parameter.
- `compositional_CEM`: `if A, will B ∨ if A, will ¬B` is valid₂ —
  Compositional CEM for will-conditionals (paper §7). Stalnaker's CEM
  lifted to the future-modal layer.
- `narrow_negation_swap`: `¬ (if A, will B) ↔ (if A, will ¬B)` —
  the narrow-scope reading (paper §7). Negation under the if-clause
  swaps through *will* by `Selectional.negation_swap`.
- `willConditional_collapse`: when `w ∈ f` and `A w`, the conditional
  collapses to its consequent: `will B` reduces to `B w`.
-/

set_option autoImplicit false

namespace Semantics.Conditionals.WillConditional

open _root_.Semantics.Conditionals (SelectionFunction)
open Semantics.Modality.Selectional

variable {W : Type*}

/-- **Kratzer restriction** [cariani-santorio-2018] §5.3.1: the if-clause
    `A` restricts the modal parameter `f` to the alternatives that also
    satisfy `A`, i.e. `f ∩ ‖A‖`. Every will-conditional construction in
    this file feeds the selection function this restricted parameter. -/
def restrict (A : W → Prop) (f : Set W) : Set W :=
  f ∩ {w' | A w'}

/-- **Selectional `will`-conditional** [cariani-santorio-2018]
    §5.3.1: the if-clause `A` Kratzer-`restrict`s the modal parameter
    `f` to `f ∩ ‖A‖` before evaluating the *will*-prejacent `B`. The
    restriction rule is paper eq. (21); eq. (23) is its informal English
    gloss. -/
def willConditional (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willSem s B (restrict A f) w

@[simp] theorem willConditional_def (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    willConditional s A B f w ↔ B (s.sel w (f ∩ {w' | A w'})) := Iff.rfl

/-- **Compositional CEM** [cariani-santorio-2018] §7: for the
    selectional `will`-conditional, the disjunction `(if A, will B) ∨
    (if A, will ¬B)` holds at every point.

    Derived from `Semantics.Conditionals.SelectionFunction.sel_em` applied at the
    restricted parameter `f ∩ ‖A‖`. Will Excluded Middle and
    Compositional CEM share this single structural origin: the
    selected world is single-valued no matter which proposition
    restricts the modal parameter. -/
theorem compositional_CEM (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    willConditional s A B f w ∨
    willConditional s A (fun w' => ¬ B w') f w :=
  s.sel_em B (restrict A f) w

/-- **Compositional CEM** is valid₂ (paper §7): holds at every
    ⟨s, f, w⟩ index. -/
theorem valid2_compositional_CEM (A B : W → Prop) :
    Valid2 (W := W) fun s f w =>
      willConditional s A B f w ∨
      willConditional s A (fun w' => ¬ B w') f w :=
  fun s f w => compositional_CEM s A B f w

/-- **Narrow Negation Swap in Conditionals** [cariani-santorio-2018]
    §7: under the *narrow* reading where negation scopes under the
    if-clause, `¬ (if A, will B) ↔ (if A, will ¬B)`. Derived from
    `Semantics.Conditionals.SelectionFunction.sel_neg_swap` at the restricted parameter
    `f ∩ ‖A‖`; the conditional analogue of the matrix Negation Swap,
    lifted by restrictor-style restriction of the modal parameter. -/
theorem narrow_negation_swap (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    willConditional s A (fun w' => ¬ B w') f w ↔
    ¬ willConditional s A B f w :=
  s.sel_neg_swap B (restrict A f) w

/-- **Narrow Negation Swap** is valid₂. -/
theorem valid2_narrow_negation_swap (A B : W → Prop) :
    Valid2 (W := W) fun s f w =>
      willConditional s A (fun w' => ¬ B w') f w ↔
      ¬ willConditional s A B f w :=
  fun s f w => narrow_negation_swap s A B f w

/-- **Wide Negation Swap in Conditionals** [cariani-santorio-2018]
    §7: under the *wide* reading where negation scopes over the entire
    conditional, `¬ (if A, will B) ↔ (if A, will ¬B)`. In the selectional
    setting this is definitionally the converse of `narrow_negation_swap`:
    selection-function single-valuedness reduces both LF positions to the
    same truth condition `¬ B (s.sel w (f ∩ ‖A‖))`, so C&S derive Wide
    Negation Swap from Narrow plus the matrix Negation Swap (paper §7).
    The wide/narrow collapse is internal to the selectional analysis. -/
theorem wide_negation_swap (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    ¬ willConditional s A B f w ↔
    willConditional s A (fun w' => ¬ B w') f w :=
  (narrow_negation_swap s A B f w).symm

/-- **Wide Negation Swap** is valid₂. -/
theorem valid2_wide_negation_swap (A B : W → Prop) :
    Valid2 (W := W) fun s f w =>
      ¬ willConditional s A B f w ↔
      willConditional s A (fun w' => ¬ B w') f w :=
  fun s f w => wide_negation_swap s A B f w

/-- **Postsemantic CEM for will-conditionals** [cariani-santorio-2018]
    §7: Compositional CEM specialized to the context of utterance —
    `(if A, will B) ∨ (if A, will ¬B)` holds at the contextually-fixed
    `⟨sCtx, fCtx, wCtx⟩`. Under a single selection function the
    postsemantic and compositional readings coincide; the paper
    distinguishes them because the supervaluational generalization
    separates Validity₁ from Validity₂. -/
theorem postsemantic_CEM (A B : W → Prop) (sCtx : SelectionFunction W)
    (fCtx : Set W) (wCtx : W) :
    Valid1 (W := W)
      (fun s f w =>
        willConditional s A B f w ∨
        willConditional s A (fun w' => ¬ B w') f w)
      sCtx fCtx wCtx :=
  valid2_implies_valid1
    (fun s f w => compositional_CEM s A B f w) sCtx fCtx wCtx

/-- **Conditional collapse**: when the evaluation world `w` is in the
    restricted modal parameter `f ∩ ‖A‖` (i.e., both in the original
    base and an A-world itself), the conditional collapses to its
    consequent `B w` by Centering. -/
theorem willConditional_collapse (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) (hw_f : w ∈ f) (hw_A : A w) :
    willConditional s A B f w ↔ B w :=
  unembedded_collapse s B (restrict A f) w ⟨hw_f, hw_A⟩

/-- **Restriction is idempotent under satisfaction**: if `f ⊆ ‖A‖`,
    restricting by `A` is a no-op, so `will A → will A` and
    `if A, will B ↔ will B`.  -/
theorem willConditional_redundant (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) (h_subset : ∀ w' ∈ f, A w') :
    willConditional s A B f w ↔ willSem s B f w := by
  have h_eq : restrict A f = f := by
    ext w'
    exact ⟨fun ⟨hf, _⟩ => hf, fun hf => ⟨hf, h_subset w' hf⟩⟩
  unfold willConditional
  rw [h_eq]

/-! ## The universal-base foil for will-conditionals

The Lewis-style universal-quantifier reading lifts to conditionals the
same way the selectional one does — by Kratzer-restricting the modal
parameter — but evaluates the prejacent *universally* over the restricted
parameter instead of at the single selected world. This is the
conditional image of [cariani-santorio-2018]'s matrix foil
`Selectional.universalWill`. It is the natural-language analogue of
[lewis-1973]'s counterfactual semantics, and it falsifies Compositional
CEM: when the restricted parameter contains both a `B`-world and a
`¬B`-world, neither `(if A, will B)` nor `(if A, will ¬B)` is universally
true. The concrete refutation is `CarianiSantorio2018`'s
`universal_will_conditional_cem_fails`, the will-conditional analogue of
`Stalnaker1981.bizet_cem_fails_universal`. -/

/-- **Universal-base will-conditional** (the foil): the if-clause
    Kratzer-restricts the parameter to `f ∩ ‖A‖`, then *will B* is read
    as universal quantification over that restricted parameter. Unlike
    `willConditional`, this validates neither Compositional CEM nor
    Negation Swap. -/
def universalWillConditional (A B : W → Prop) (f : Set W) (w : W) : Prop :=
  universalWill B (restrict A f) w

/-! ## *Would*-conditionals — the past-tense morphological derivative

[cariani-santorio-2018] §5.3.2 identifies *would* with the past
tense form of *will*. The conditional analogue follows: a *would*-
conditional is just the selectional restrictor applied to *would*,
which by `wouldSem_eq_willSem` is identical to a *will*-conditional.
The morphology shifts the modal parameter; the semantic clause is
unchanged. -/

/-- **Selectional `would`-conditional** [cariani-santorio-2018]
    §5.3.2 + §5.3.1: the *would*-conditional is the selectional
    restrictor applied to *would*, which by the morphological identity
    `wouldSem = willSem` collapses to `willConditional`. -/
def wouldConditional (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willConditional s A B f w

/-- **Past-tense morphology = parameter shift** for conditionals:
    *would*-conditionals and *will*-conditionals share their semantic
    clause (the conditional analogue of `wouldSem_eq_willSem`). Tagged
    `@[simp]` so `wouldConditional` reduces to the canonical
    `willConditional` normal form. -/
@[simp] theorem wouldConditional_eq_willConditional (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) (w : W) :
    wouldConditional s A B f w = willConditional s A B f w := rfl

/-! ## Modal subordination

[cariani-santorio-2018] §5.3.1 models modal subordination in a
discourse "If A, will B. Will C." by *coindexing* the second sentence's
*will* to the same restricted modal-base variable the if-clause
introduces, so both *will*s are interpreted under the antecedent's
supposition `f ∩ ‖A‖` rather than the second starting fresh from `f`.
C&S treat the coindexing as a discourse assumption (following Klecha),
not as something the semantics forces. Under that coindexing the
selection function picks the *same* world for both prejacents, because
`s.sel w (f ∩ ‖A‖)` is single-valued — the discourse analogue of the
single-valuedness behind `compositional_CEM` and `narrow_negation_swap`. -/

/-- **Modally-subordinated will-discourse** [cariani-santorio-2018]
    §5.3.1: the minimal two-*will* instance of C&S's coindexing
    analysis — "If A, will B. Will C." with the second *will*'s modal
    base coindexed to the if-clause's restricted parameter `f ∩ ‖A‖`.
    Holds iff both prejacents hold at the Stalnaker-selected world from
    the restricted parameter. -/
def subordinatedWillDiscourse (s : SelectionFunction W) (A B C : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willConditional s A B f w ∧
  willSem s C (restrict A f) w

/-- **Modal subordination = shared selected world**: the subordinated
    discourse picks the *same* world for both prejacents, because
    `s.sel w (f ∩ ‖A‖)` is single-valued. The discourse therefore
    reduces to a single conjunction `B w' ∧ C w'` evaluated at that
    world `w'`. -/
theorem subordinatedWillDiscourse_eq_conj (s : SelectionFunction W)
    (A B C : W → Prop) (f : Set W) (w : W) :
    subordinatedWillDiscourse s A B C f w ↔
    (B (s.sel w (f ∩ {w' | A w'})) ∧ C (s.sel w (f ∩ {w' | A w'}))) :=
  Iff.rfl

/-- **Subordination coincides with an unrestricted continuation exactly
    when the if-clause does not shift the selected world.** The
    modally-subordinated reading evaluates the continuation *will C* at
    the restricted parameter `f ∩ ‖A‖`, whereas a fresh, non-subordinated
    *will C* would evaluate it at `f`. The two readings agree precisely
    when restricting by `A` leaves the selected world fixed
    (`s.sel w f = s.sel w (f ∩ ‖A‖)`); in general they diverge. -/
theorem subordinated_eq_unrestricted_of_no_shift (s : SelectionFunction W)
    (A B C : W → Prop) (f : Set W) (w : W)
    (h_no_shift : s.sel w f = s.sel w (restrict A f)) :
    subordinatedWillDiscourse s A B C f w ↔
    (willConditional s A B f w ∧ willSem s C f w) := by
  unfold subordinatedWillDiscourse willConditional willSem
  rw [h_no_shift]

end Semantics.Conditionals.WillConditional
