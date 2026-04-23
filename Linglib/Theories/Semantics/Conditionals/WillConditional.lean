import Linglib.Theories.Semantics.Modality.Selectional

/-!
# Selectional `will`-Conditionals
@cite{cariani-santorio-2018}

@cite{cariani-santorio-2018} §5.3.1 (eq. 20) lifts the selectional
analysis of *will* to conditionals via Kratzerian restriction: an
*if*-clause restricts the modal parameter `f` to its intersection with
the antecedent's truth set.

`⟦if A, will B⟧^{w,s,g} = ⟦will B⟧^{w,s,g[f ↦ g(f) ∩ ‖A‖]}`
                       `= B (s(w, g(f) ∩ ‖A‖))`

The semantic rule lives in §5.3.1; §7 then derives the predicted
compositional CEM and Negation-Swap-in-Conditionals theorems as
*consequences* of this restriction rule combined with selection
single-valuedness.

## What's here

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

/-- **Selectional `will`-conditional** @cite{cariani-santorio-2018}
    §5.3.1 (eq. 20): the if-clause `A` Kratzer-restricts the modal
    parameter `f` to `f ∩ ‖A‖` before evaluating the *will*-prejacent
    `B`. (Eq. 22 in the paper is the informal English gloss of this
    rule; eq. 20 is the actual semantic clause.) -/
def willConditional (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willSem s B (f ∩ {w' | A w'}) w

@[simp] theorem willConditional_def (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    willConditional s A B f w ↔ B (s.sel w (f ∩ {w' | A w'})) := Iff.rfl

/-- **Compositional CEM** @cite{cariani-santorio-2018} §7: for the
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
  s.sel_em B (f ∩ {w' | A w'}) w

/-- **Compositional CEM** is valid₂ (paper §7): holds at every
    ⟨s, f, w⟩ index. -/
theorem valid2_compositional_CEM (A B : W → Prop) :
    Valid2 (W := W) fun s f w =>
      willConditional s A B f w ∨
      willConditional s A (fun w' => ¬ B w') f w :=
  fun s f w => compositional_CEM s A B f w

/-- **Narrow Negation Swap in Conditionals** @cite{cariani-santorio-2018}
    §7: under the *narrow* reading where negation scopes under the
    if-clause, `¬ (if A, will B) ↔ (if A, will ¬B)`. Derived from
    `Semantics.Conditionals.SelectionFunction.sel_neg_swap` at the restricted parameter
    `f ∩ ‖A‖`; the conditional analogue of the matrix Negation Swap,
    lifted by restrictor-style restriction of the modal parameter. -/
theorem narrow_negation_swap (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    willConditional s A (fun w' => ¬ B w') f w ↔
    ¬ willConditional s A B f w :=
  s.sel_neg_swap B (f ∩ {w' | A w'}) w

/-- **Narrow Negation Swap** is valid₂. -/
theorem valid2_narrow_negation_swap (A B : W → Prop) :
    Valid2 (W := W) fun s f w =>
      willConditional s A (fun w' => ¬ B w') f w ↔
      ¬ willConditional s A B f w :=
  fun s f w => narrow_negation_swap s A B f w

/-- **Wide Negation Swap in Conditionals** @cite{cariani-santorio-2018}
    §7: under the *wide* reading where negation scopes over the entire
    conditional, `¬ (if A, will B) ↔ (if A, will ¬B)`. Definitionally
    equal to the narrow biconditional in the selectional setting, since
    selection-function single-valuedness collapses the LF-position
    distinction: regardless of where negation attaches, the truth
    condition reduces to `¬ B (s.sel w (f ∩ ‖A‖))`. The paper highlights
    that this collapse is a positive prediction of the selectional
    analysis — universal-base treatments scope-distinguish the two. -/
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

/-- **Postsemantic CEM for will-conditionals** @cite{cariani-santorio-2018}
    §7: Compositional CEM specialized to the context of utterance —
    `(if A, will B) ∨ (if A, will ¬B)` holds at the contextually-fixed
    `⟨sCtx, fCtx, wCtx⟩`. Under a single selection function the
    postsemantic and compositional readings coincide; the paper
    distinguishes them because the supervaluational generalization
    separates Validity₁ from Validity₂. -/
theorem postsemantic_CEM (A B : W → Prop) (sCtx : SelectionFunction W)
    (fCtx : Set W) (wCtx : W) :
    Semantics.Modality.Selectional.Valid1 (W := W)
      (fun s f w =>
        willConditional s A B f w ∨
        willConditional s A (fun w' => ¬ B w') f w)
      sCtx fCtx wCtx :=
  Semantics.Modality.Selectional.valid2_implies_valid1
    (fun s f w => compositional_CEM s A B f w) sCtx fCtx wCtx

/-- **Conditional collapse**: when the evaluation world `w` is in the
    restricted modal parameter `f ∩ ‖A‖` (i.e., both in the original
    base and an A-world itself), the conditional collapses to its
    consequent `B w` by Centering. -/
theorem willConditional_collapse (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) (hw_f : w ∈ f) (hw_A : A w) :
    willConditional s A B f w ↔ B w := by
  unfold willConditional
  exact unembedded_collapse s B (f ∩ {w' | A w'}) w ⟨hw_f, hw_A⟩

/-- **Restriction is idempotent under satisfaction**: if `f ⊆ ‖A‖`,
    restricting by `A` is a no-op, so `will A → will A` and
    `if A, will B ↔ will B`.  -/
theorem willConditional_redundant (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) (h_subset : ∀ w' ∈ f, A w') :
    willConditional s A B f w ↔ willSem s B f w := by
  have h_eq : f ∩ {w' | A w'} = f := by
    ext w'
    exact ⟨fun ⟨hf, _⟩ => hf, fun hf => ⟨hf, h_subset w' hf⟩⟩
  unfold willConditional willSem
  rw [h_eq]

/-! ## *Would*-conditionals — the past-tense morphological derivative

@cite{cariani-santorio-2018} §5.3.2 identifies *would* with the past
tense form of *will*. The conditional analogue follows: a *would*-
conditional is just the selectional restrictor applied to *would*,
which by `wouldSem_eq_willSem` is identical to a *will*-conditional.
The morphology shifts the modal parameter; the semantic clause is
unchanged. -/

/-- **Selectional `would`-conditional** @cite{cariani-santorio-2018}
    §5.3.2 + §5.3.1: the *would*-conditional is the selectional
    restrictor applied to *would*, which by the morphological identity
    `wouldSem = willSem` collapses to `willConditional`. -/
def wouldConditional (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willConditional s A B f w

@[simp] theorem wouldConditional_def (s : SelectionFunction W) (A B : W → Prop)
    (f : Set W) (w : W) :
    wouldConditional s A B f w ↔ B (s.sel w (f ∩ {w' | A w'})) := Iff.rfl

/-- **Past-tense morphology = parameter shift** for conditionals:
    *would*-conditionals and *will*-conditionals share their semantic
    clause. -/
theorem wouldConditional_eq_willConditional (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) (w : W) :
    wouldConditional s A B f w = willConditional s A B f w := rfl

/-! ## Modal subordination

@cite{cariani-santorio-2018} §5.3.1: "If A, will B. Will C." reads with
modal subordination — the second sentence's *will* inherits the first
sentence's restricted parameter `f ∩ ‖A‖` rather than starting fresh
from `f`. The selectional analysis predicts this for free: a discourse
of two will-utterances under a shared restricted parameter is just the
conjunction of two `willSem` calls at that parameter.

The selection function picks the *same* world for both prejacents
because `s.sel w (f ∩ ‖A‖)` is single-valued. This is the discourse
analogue of `compositional_CEM` and `narrow_negation_swap`: structural
single-valuedness, not propositional content, drives the prediction. -/

/-- **Modally-subordinated will-discourse** @cite{cariani-santorio-2018}
    §5.3.1: a two-sentence discourse "If A, will B. Will C." where the
    second *will* inherits the if-clause's restricted parameter
    `f ∩ ‖A‖`. The discourse holds iff both prejacents hold at the
    Stalnaker-selected world from the restricted parameter. -/
def subordinatedWillDiscourse (s : SelectionFunction W) (A B C : W → Prop)
    (f : Set W) (w : W) : Prop :=
  willConditional s A B f w ∧
  willSem s C (f ∩ {w' | A w'}) w

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

/-- **Subordination ≠ unrestricted continuation**: the modally-
    subordinated reading `f ∩ ‖A‖` differs in general from a fresh
    *will* at the original parameter `f`. The two coincide only when
    `s.sel w f = s.sel w (f ∩ ‖A‖)` — i.e. when restricting by `A`
    does not shift the selected world. -/
theorem subordinated_eq_unrestricted_iff (s : SelectionFunction W)
    (A B C : W → Prop) (f : Set W) (w : W)
    (hB : willConditional s A B f w) :
    subordinatedWillDiscourse s A B C f w ↔
    (willConditional s A B f w ∧ C (s.sel w (f ∩ {w' | A w'}))) := by
  unfold subordinatedWillDiscourse willSem
  exact ⟨fun ⟨_, h⟩ => ⟨hB, h⟩, fun ⟨_, h⟩ => ⟨hB, h⟩⟩

end Semantics.Conditionals.WillConditional
