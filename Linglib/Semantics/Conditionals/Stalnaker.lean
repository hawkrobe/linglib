module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Semantics.Mood.Defs
public import Linglib.Semantics.Conditionals.SimilarityOrdering
public import Linglib.Discourse.CommonGround

/-!
# Stalnaker's selection-function conditionals

This file adds to the selection conditional of `Conditionals/SelectionFunction.lean` the
contextual machinery of [stalnaker-1975] and the passage from selection functions back to
similarity orderings.

[stalnaker-1975] argues that the indicative/subjunctive distinction is pragmatic: both moods
share the selection conditional's truth condition, and an indicative requires the selection
function to obey the **pragmatic constraint** (`pragmaticConstraint`), staying inside the context
set when it can, which a subjunctive suspends (`Mood.admissibleSelection`). Within a context the
indicative then agrees with the material conditional (`mem_selectionConditional_of_forall_mem`),
without being identified with it. `SelectionFunction.restrict` restricts a selection function to
a context, obeying the constraint (`pragmaticConstraint_restrict`).

A selection function induces a pairwise preference among worlds; when it is transitive
(`SelectionFunction.isCoherent`) it is a similarity ordering (`coherentSelectionToSimilarity`).

## References

* [stalnaker-1968]
* [stalnaker-1975]
* [stalnaker-1981]
-/

@[expose] public section


namespace Conditional

open Mood (Grammatical)
open _root_.Conditional (SelectionFunction selectionPrefers)
open _root_.Conditional (SimilarityOrdering)

/-! ## Coherent selection ⇒ similarity ordering -/

/-- **Coherent selection functions induce similarity orderings.**

Given a coherent selection function, its pairwise preference relation
is a valid `SimilarityOrdering`: reflexive (from `success`) and
transitive (from coherence). -/
def coherentSelectionToSimilarity {W : Type*} [DecidableEq W]
    (s : SelectionFunction W)
    (h_coherent : s.isCoherent) : SimilarityOrdering W where
  closer w₀ w₁ w₂ := selectionPrefers s w₀ w₁ w₂
  closer_refl w₀ w := by
    show s.sel w₀ {w, w} = w
    have h_eq : ({w, w} : Set W) = {w} := Set.insert_eq_of_mem (Set.mem_singleton w)
    rw [h_eq]
    exact Set.mem_singleton_iff.mp (s.inclusion w₀ {w} ⟨w, Set.mem_singleton w⟩)
  closer_trans := h_coherent
  decClose w₀ w₁ w₂ := by exact inferInstanceAs (Decidable (s.sel w₀ {w₁, w₂} = w₁))

/-! ## The pragmatic constraint ([stalnaker-1975]) -/

/-- **Pragmatic constraint on selection** ([stalnaker-1975] §III).

If the conditional is being evaluated at a context-set world `w`, and
some antecedent-world is also in the context set, then the selected
world must be in the context set. Equivalently: context-set worlds are
closer to each other than to non-context-set worlds whenever a
context-set option is available.

The central new contribution of [stalnaker-1975]: it makes
indicative inference forms behave the way they do, without changing
the semantic clause. -/
def pragmaticConstraint {W : Type*} (s : SelectionFunction W)
    (C : Set W) : Prop :=
  ∀ w (A : Set W), w ∈ C → (∃ w' ∈ A, w' ∈ C) → s.sel w A ∈ C

open Classical in
/-- The restriction of a selection function to a context: at a context world, an antecedent
compatible with the context selects among the context's antecedent-worlds; otherwise
selection is as before. The restriction obeys the pragmatic constraint of [stalnaker-1975]
for the context. -/
noncomputable def SelectionFunction.restrict {W : Type*} (s : SelectionFunction W)
    (C : Set W) : SelectionFunction W where
  sel w A := if w ∈ C ∧ (A ∩ C).Nonempty then s.sel w (A ∩ C) else s.sel w A
  inclusion w A hA := by
    split_ifs with h
    · exact (s.inclusion w (A ∩ C) h.2).1
    · exact s.inclusion w A hA
  centering w A hw := by
    split_ifs with h
    · exact s.centering w (A ∩ C) ⟨hw, h.1⟩
    · exact s.centering w A hw

theorem SelectionFunction.restrict_sel_of_mem {W : Type*} (s : SelectionFunction W) (C : Set W)
    {w : W} {A : Set W} (hw : w ∈ C) (hA : (A ∩ C).Nonempty) :
    (s.restrict C).sel w A = s.sel w (A ∩ C) := by
  simp [SelectionFunction.restrict, hw, hA]

theorem SelectionFunction.restrict_sel_of_notMem {W : Type*} (s : SelectionFunction W)
    (C : Set W) {w : W} (A : Set W) (hw : w ∉ C) : (s.restrict C).sel w A = s.sel w A := by
  simp [SelectionFunction.restrict, hw]

/-- The restriction of a selection function to a context obeys the pragmatic constraint for
that context. -/
theorem pragmaticConstraint_restrict {W : Type*} (s : SelectionFunction W) (C : Set W) :
    pragmaticConstraint (s.restrict C) C := fun w A hw hA ↦ by
  have hAC : (A ∩ C).Nonempty := let ⟨v, hvA, hvC⟩ := hA; ⟨v, hvA, hvC⟩
  rw [SelectionFunction.restrict_sel_of_mem s C hw hAC]
  exact (s.inclusion w (A ∩ C) hAC).2

/-- **Mood-indexed admissibility on selection functions**
([stalnaker-1975]).

Stalnaker's mood distinction lives here, not in the truth-conditional
clause:
- `.indicative` requires the selection function to obey
  `pragmaticConstraint` on the context — the central
  [stalnaker-1975] contribution.
- `.subjunctive` imposes no such constraint; the selection function
  may reach outside the context set, which is precisely what
  subjunctive mood signals.

This makes "indicative vs subjunctive" a property of the
*selection-function / context pairing*, not a separate semantic
operator. -/
def Mood.admissibleSelection {W : Type*} (m : Grammatical) (s : SelectionFunction W)
    (C : Set W) : Prop :=
  match m with
  | .indicative  => pragmaticConstraint s C
  | .subjunctive => True

/-- Indicative admissibility unfolds to the pragmatic constraint. -/
theorem admissibleSelection_indicative {W : Type*} (s : SelectionFunction W)
    (C : Set W) :
    Mood.admissibleSelection .indicative s C = pragmaticConstraint s C := rfl

/-- Subjunctive admissibility imposes no constraint. -/
theorem admissibleSelection_subjunctive {W : Type*} (s : SelectionFunction W)
    (C : Set W) :
    Mood.admissibleSelection .subjunctive s C = True := rfl

/-- **The indicative conditional within a context** ([stalnaker-1975] §IV): at a context world,
for an antecedent compatible with the context and a selection function obeying the pragmatic
constraint, the selection conditional holds whenever the material conditional holds throughout
the context. One direction of the contextually mediated equivalence Stalnaker defends in place of
identifying the indicative with the material conditional. -/
theorem mem_selectionConditional_of_forall_mem {W : Type*} (s : SelectionFunction W)
    {C p q : Set W} {w : W} (hw : w ∈ C) (hopen : ∃ w' ∈ p, w' ∈ C)
    (hC : pragmaticConstraint s C) (himp : ∀ w' ∈ C, w' ∈ p → w' ∈ q) :
    w ∈ selectionConditional s p q := by
  obtain ⟨v, hv, -⟩ := id hopen
  rw [mem_selectionConditional_of_nonempty s ⟨v, hv⟩]
  exact himp _ (hC w p hw hopen) (s.inclusion w p ⟨v, hv⟩)

end Conditional
