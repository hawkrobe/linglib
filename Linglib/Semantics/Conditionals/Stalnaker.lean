import Linglib.Semantics.Conditionals.Basic
import Linglib.Semantics.Conditionals.SelectionFunction
import Linglib.Semantics.Mood.Categories
import Linglib.Core.Order.SimilarityOrdering
import Linglib.Discourse.CommonGround

/-!
# Stalnaker selection-function counterfactuals

[stalnaker-1968] [stalnaker-1975] [stalnaker-1981]

Selection-function-based counterfactual semantics, separated from
`Conditionals/Basic.lean` (which retains material/strict/variably-strict
+ counterexamples). All Stalnaker-flavoured machinery — pragmatic
constraint, mooded conditional, indicative-vs-subjunctive admissibility,
the selection ↔ similarity bridge, and the contextually-mediated
material-conditional reduction — lives here.

## Selection Functions

[stalnaker-1968]'s selection function approach to counterfactuals:
- A selection function `s : W × 𝒫(W) → W` selects THE closest
  antecedent-world
- "If A were, C would be" is true iff C holds at s(w, ⦃A⦄)

Key distinction from [lewis-1973]: Lewis universally quantifies
over closest A-worlds; Stalnaker selects a single A-world (with
supervaluation for ties — see `Conditionals/Counterfactual.lean`).

`SelectionFunction` itself lives in
`Semantics/Conditionals/SelectionFunction.lean` and is shared with
[cariani-santorio-2018]'s selectional *will* (`Semantics/Modality/Selectional.lean`)
and will-conditionals (`Semantics/Conditionals/WillConditional.lean`).

## Selection ↔ Similarity Bridge ([stalnaker-1981])

A selection function `s` determines a pairwise preference:
`w₁ ≤_{w₀} w₂` iff `s(w₀, {w₁, w₂}) = w₁`. This is reflexive (by
`success`) and total (by definition); transitivity requires
`s.isCoherent` — rationalizability by a total preorder. The
`coherentSelectionToSimilarity` constructor turns a coherent `s` into
a `Core.Order.SimilarityOrdering`.

## Stalnakerian indicative/subjunctive split ([stalnaker-1975])

[stalnaker-1975] argues that the indicative/subjunctive
distinction is *pragmatic*, not semantic: both have the same
selection-based truth condition. Indicatives require the selection
function to obey the **pragmatic constraint** (stay inside the context
set when possible); subjunctives signal that the constraint is
suspended.

The previous identification `indicativeConditional := materialImp`
was inaccurate per [stalnaker-1975] §IV. We now derive the
equivalence within an appropriate context (the
`*_eq_material_within_context` theorems below) rather than stipulate it.
-/

namespace Semantics.Conditionals

open CommonGround (ContextSet)
open Semantics.Mood (Grammatical)
open _root_.Semantics.Conditionals (SelectionFunction selectionPrefers)
open Core.Order (SimilarityOrdering)

/-! ## Coherent selection ⇒ similarity ordering -/

/-- **Coherent selection functions induce similarity orderings.**

Given a coherent selection function, its pairwise preference relation
is a valid `SimilarityOrdering`: reflexive (from `success`) and
transitive (from coherence). -/
def coherentSelectionToSimilarity {W : Type*} [DecidableEq W]
    (s : SelectionFunction W)
    (h_coherent : s.isCoherent) : SimilarityOrdering W where
  atCenter w₀ :=
    Preorder.ofLE (fun w₁ w₂ => selectionPrefers s w₀ w₁ w₂)
      (fun w => by
        show s.sel w₀ {w, w} = w
        have h_eq : ({w, w} : Set W) = {w} := Set.insert_eq_of_mem (Set.mem_singleton w)
        rw [h_eq]
        have h_ne : ({w} : Set W).Nonempty := ⟨w, Set.mem_singleton w⟩
        have h_in := s.inclusion w₀ {w} h_ne
        exact Set.mem_singleton_iff.mp h_in)
      (fun w₁ w₂ w₃ => h_coherent w₀ w₁ w₂ w₃)
  decClose w₀ w₁ w₂ := by exact inferInstanceAs (Decidable (s.sel w₀ {w₁, w₂} = w₁))

/-! ## Stalnakerian mood machinery

The bare selection-conditional clause `selectionConditional` and its
decidability instance now live in `SelectionFunction.lean` — the
[stalnaker-1968] substrate shared with the counterfactual reading
(`Counterfactual.stalnakerCounterfactual`). This section adds the
[stalnaker-1975] indicative refinements on top of that shared clause. -/

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
    (C : ContextSet W) : Prop :=
  ∀ w (A : Set W), C w → (∃ w' ∈ A, C w') → C (s.sel w A)

/-- **Mooded conditional** ([stalnaker-1975]): the truth-conditional
clause is `selectionConditional` regardless of grammatical mood. The mood
index `m` is metadata at the call site; the *semantic* mood difference
is captured by which selection functions are admissible (see
`admissibleSelection`).

Single source of truth: indicative and subjunctive conditionals do not
have distinct semantic clauses. -/
def moodedConditional {W : Type*} (_m : Grammatical) (s : SelectionFunction W)
    (p q : W → Prop) : W → Prop :=
  selectionConditional s p q

/-- `moodedConditional` is decidable when its consequent is. -/
instance moodedConditional_decidable {W : Type*} (m : Grammatical)
    (s : SelectionFunction W) (p q : W → Prop) [DecidablePred q] (w : W) :
    Decidable (moodedConditional m s p q w) :=
  inferInstanceAs (Decidable (selectionConditional s p q w))

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
    (C : ContextSet W) : Prop :=
  match m with
  | .indicative  => pragmaticConstraint s C
  | .subjunctive => True

/-- Indicative admissibility unfolds to the pragmatic constraint. -/
theorem admissibleSelection_indicative {W : Type*} (s : SelectionFunction W)
    (C : ContextSet W) :
    Mood.admissibleSelection .indicative s C = pragmaticConstraint s C := rfl

/-- Subjunctive admissibility imposes no constraint. -/
theorem admissibleSelection_subjunctive {W : Type*} (s : SelectionFunction W)
    (C : ContextSet W) :
    Mood.admissibleSelection .subjunctive s C = True := rfl

/-- **Mood is irrelevant to the truth-conditional clause**
([stalnaker-1975]). For any grammatical mood, the mooded
conditional reduces to the bare selection conditional. -/
theorem moodedConditional_eq_selectionConditional {W : Type*} (m : Grammatical)
    (s : SelectionFunction W) (p q : W → Prop) :
    moodedConditional m s p q = selectionConditional s p q := rfl

/-- **Selection conditional ≡ material within an appropriate context**
([stalnaker-1975] §IV).

In any context `C` evaluated at a context-set world `w`, given that the
antecedent is open in `C`, the selection function obeys the pragmatic
constraint, and the material conditional holds throughout `C`, the
selection conditional is true. The contextually-mediated equivalence
Stalnaker defends in place of the semantic identification.

Specialised to `.indicative` mood, this is the Stalnakerian claim that
indicative conditionals reduce to the material conditional within an
appropriate context.

Hypotheses encode the "appropriate context" conditions:
- `hC_w`: `w` is in the context set;
- `h_open_p`: some context-set world satisfies `p` (antecedent is open);
- `h_constraint`: `s` obeys the pragmatic constraint relative to `C`;
- `h_C_imp`: in the context, the material conditional holds. -/
theorem selectionConditional_eq_material_within_context {W : Type*}
    (s : SelectionFunction W) (C : ContextSet W) (p q : W → Prop) (w : W)
    (hC_w : C w)
    (h_open_p : ∃ w' ∈ {w' | p w'}, C w')
    (h_constraint : pragmaticConstraint s C)
    (h_C_imp : ∀ w', C w' → p w' → q w') :
    selectionConditional s p q w := by
  unfold selectionConditional
  have h_nonempty : ({w' | p w'} : Set W).Nonempty := by
    obtain ⟨w', hw'_p, _⟩ := h_open_p
    exact ⟨w', hw'_p⟩
  have h_sel_C : C (s.sel w {w' | p w'}) :=
    h_constraint w {w' | p w'} hC_w h_open_p
  have h_sel_p : p (s.sel w {w' | p w'}) :=
    s.inclusion w {w' | p w'} h_nonempty
  exact h_C_imp _ h_sel_C h_sel_p

/-- **Indicative-mood specialisation**: when the mood is indicative and
the selection function is admissible, the mooded conditional reduces
to the material conditional within the context. -/
theorem moodedConditional_indicative_eq_material_within_context {W : Type*}
    (s : SelectionFunction W) (C : ContextSet W) (p q : W → Prop) (w : W)
    (hC_w : C w)
    (h_open_p : ∃ w' ∈ {w' | p w'}, C w')
    (h_admissible : Mood.admissibleSelection .indicative s C)
    (h_C_imp : ∀ w', C w' → p w' → q w') :
    moodedConditional .indicative s p q w :=
  selectionConditional_eq_material_within_context s C p q w hC_w h_open_p
    h_admissible h_C_imp

end Semantics.Conditionals
