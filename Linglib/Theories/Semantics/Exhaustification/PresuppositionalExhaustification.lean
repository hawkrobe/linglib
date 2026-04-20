import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Exhaustification.Operators

/-!
# Presuppositional Exhaustification (pex)
@cite{delpinal-bassi-sauerland-2024} @cite{bassi-delpinal-sauerland-2021}

Formalization of @cite{delpinal-bassi-sauerland-2024} "Free choice and
presuppositional exhaustification" Semantics & Pragmatics 17, Article 3: 1–52.

## Core idea

Standard exhaustification (**exh**) produces flat, fully assertive output:
it asserts the prejacent plus negated IE alternatives plus II alternatives.
**pex** splits this output into two dimensions:

- **asserts**: only the prejacent φ
- **presupposes**: (i) the negation of each IE alternative, and
  (ii) a *homogeneity presupposition* — that all II alternatives have the
  same truth value

This structuring is the mirror image of **only**: *only* presupposes its
prejacent and asserts the negation of alternatives.

## Why it matters

The assertive/presuppositional split lets pex derive:
1. Free choice for ◇∨ from local application
2. Double prohibition for ¬◇∨ from negation over pex's assertive component
3. Negative FC for ¬□∧ analogously
4. Correct predictions for embedded FC puzzles (under negative factives,
   in disjunctions, under quantifiers) via standard presupposition
   projection and filtering

Standard **exh** cannot solve these embedded puzzles because its output is
flat — negation, factives, and filtering operators cannot distinguish
assertive from presuppositional content.

## Architecture

`pexIEII` takes the same IE/II computation from `Operators.lean` and
produces a `PrProp World` — a Prop-based partial proposition with separate
assertive and presuppositional components. This directly integrates with
the presupposition projection infrastructure in `Core.Semantics.Presupposition`.

This file contains only the abstract pex theory (parameterized by an
arbitrary `World` type and abstract `ALT`, `φ`). The concrete worked
example over `FCWorld` (the five-world toy from @cite{bar-lev-fox-2020}) and
all consequences specific to that example — `pexFC`, `pex_fc`,
`pex_double_prohibition`, the negative-FC isomorphism, and the embedding
puzzles from §3–§5 — live in the study file
`Phenomena/Modality/Studies/DelPinalBassiSauerland2024.lean`.
-/

namespace Exhaustification.Presuppositional

open Exhaustification
open Core.Presupposition (PrProp)

variable {World : Type*}

-- ============================================================================
-- SECTION 2: Homogeneity
-- ============================================================================

/-!
## Homogeneity

A set of propositions is **homogeneous** at a world `w` when all members
agree on their truth value at `w`: either all true or all false.

This captures the presupposition triggered by pex for II alternatives.
For FC: the II alternatives are ◇p and ◇q, so homogeneity gives ◇p ↔ ◇q.
-/

/-- Homogeneity: all propositions in a set have the same truth value.
    For the empty set, homogeneity holds vacuously. -/
def homogeneous (S : Set (Set World)) (w : World) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, (α w ↔ β w)

/-- Homogeneity over a two-element set is biconditional. -/
theorem homogeneous_pair (p q : Set World) (w : World) :
    homogeneous {p, q} w ↔ (p w ↔ q w) := by
  constructor
  · intro h
    exact h p (Set.mem_insert _ _) q (Set.mem_insert_of_mem _ rfl)
  · intro hiff α hα β hβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
      first | exact Iff.rfl | exact hiff | exact hiff.symm

/-- Homogeneity + at-least-one-holds → all hold. -/
theorem homogeneous_and_exists_imp_all (S : Set (Set World)) (w : World)
    (hHomog : homogeneous S w) (α : Set World) (hα : α ∈ S) (ha : α w) :
    ∀ β ∈ S, β w :=
  fun β hβ => (hHomog α hα β hβ).mp ha

-- ============================================================================
-- SECTION 3: pex^{IE+II}
-- ============================================================================

/-!
## pex^{IE+II}: Presuppositional Exhaustification

Definition (9) from the paper. For a structure φ of propositional type
and a local context c:

⟦pex^{IE+II}(φ)⟧:
  a. **asserts**: ⟦φ⟧
  b. **presupposes**:
     (i) ⋀{¬⟦ψ⟧ : ψ ∈ IE(φ) ∧ ⟦ψ⟧ ∈ Rₓ}
     (ii) homogeneity over relevant II alternatives

We treat Rₓ (the relevance predicate) as a parameter; for basic cases
all alternatives are relevant.
-/

/-- **pex^{IE+II}**: Presuppositional exhaustification with IE and II.

    Unlike `exhIEII` which returns `Set World` (flat, fully assertive),
    `pexIEII` returns `PrProp World` (assertive + presuppositional).

    - **assertion** = φ (the prejacent)
    - **presupposition** = (negation of relevant IE alternatives) ∧
                           (homogeneity of relevant II alternatives) -/
def pexIEII (ALT : Set (Set World)) (φ : Set World)
    (Rc : Set (Set World)) : PrProp World where
  assertion := φ
  presup := fun w =>
    -- (i) all relevant IE alternatives are false
    (∀ ψ, isInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → ¬ψ w) ∧
    -- (ii) relevant II alternatives are homogeneous
    homogeneous {α ∈ II ALT φ | α ∈ Rc} w

/-- pex with all alternatives relevant (the default case). -/
def pexIEII_full (ALT : Set (Set World)) (φ : Set World) : PrProp World :=
  pexIEII ALT φ ALT

-- ============================================================================
-- SECTION 4: Basic Properties
-- ============================================================================

/-- pex asserts the prejacent. -/
theorem pex_assertion_eq (ALT : Set (Set World)) (φ : Set World)
    (Rc : Set (Set World)) :
    (pexIEII ALT φ Rc).assertion = φ := rfl

/-- The overall meaning of pex (presupposition ∧ assertion) entails φ. -/
theorem pex_holds_entails_prejacent (ALT : Set (Set World)) (φ : Set World)
    (Rc : Set (Set World)) (w : World)
    (h : (pexIEII ALT φ Rc).holds w) : φ w :=
  h.2

/-- Negation applies only to the assertive component; presupposition projects. -/
theorem pex_neg_assertion (ALT : Set (Set World)) (φ : Set World)
    (Rc : Set (Set World)) :
    ((pexIEII ALT φ Rc).neg).assertion = fun w => ¬φ w := rfl

/-- Negation preserves the presupposition (projection from under negation). -/
theorem pex_neg_presup (ALT : Set (Set World)) (φ : Set World)
    (Rc : Set (Set World)) :
    ((pexIEII ALT φ Rc).neg).presup = (pexIEII ALT φ Rc).presup := rfl

-- ============================================================================
-- SECTION 5: Negative FC entailment (abstract)
-- ============================================================================

/-!
## Negative Free Choice (abstract entailment)

For ¬□(p ∧ q)-sentences:
- φ = ¬□(p ∧ q)
- The pex output presupposes ¬□p ↔ ¬□q

Combined with ¬□(p ∧ q), this entails ¬□p ∧ ¬□q.

This result is stated as a pure entailment theorem: the interaction
of the assertion ¬□(p ∧ q) and homogeneity ¬□p ↔ ¬□q suffices for
negative FC, regardless of how IE/II are computed.
-/

/-- Negative FC entailment: ¬□(p ∧ q) + homogeneity(¬□p, ¬□q) → ¬□p ∧ ¬□q.

    This is the paper's (19a):
    ⟦pex^{IE+II}[¬□[T ∧ B]]⟧ = (¬□T ∨ ¬□B)_{¬□T↔¬□B} ⊨ ¬□T ∧ ¬□B -/
theorem negative_fc_entailment {W : Type*}
    (boxP boxQ : Set W) (w : W)
    (hassert : ¬(boxP w ∧ boxQ w))
    (hhomog : (¬boxP w) ↔ (¬boxQ w)) :
    ¬boxP w ∧ ¬boxQ w := by
  -- hassert: ¬(□p ∧ □q), i.e., ¬□p ∨ ¬□q
  -- hhomog: ¬□p ↔ ¬□q
  -- From ¬(□p ∧ □q): at least one of ¬□p, ¬□q holds
  -- By homogeneity: both hold
  constructor
  · intro hP
    -- □p holds → ¬(¬□p) → ¬(¬□q) by homogeneity → □q → □p ∧ □q → contradiction
    exact hassert ⟨hP, by_contra fun hNQ => absurd (hhomog.mpr hNQ) (not_not.mpr hP)⟩
  · intro hQ
    exact hassert ⟨by_contra fun hNP => absurd (hhomog.mp hNP) (not_not.mpr hQ), hQ⟩

-- ============================================================================
-- SECTION 6: Equivalence with exhIEII for Basic Cases (§2.1)
-- ============================================================================

/-!
## Equivalence for Non-FC Cases

For basic (non-FC) scalar sentences, pex^{IE+II} and exh^{IE+II} predict
the same overall entailments. When II is empty (no innocent inclusion),
pex reduces to asserting φ and presupposing ¬IE — matching pex^{IE}.

This is the paper's (11a): ⟦pex^{IE+II}(∃)⟧ = ⟦pex^{IE}(∃)⟧ = ∃_{¬∀}
-/

/-- For basic scalar sentences (where II ∩ Rc is empty), pex's presupposition
    reduces to just the negated IE alternatives (homogeneity is vacuous). -/
theorem pex_basic_scalar (ALT : Set (Set World)) (φ : Set World)
    (Rc : Set (Set World))
    (hII_empty : ∀ α, α ∈ II ALT φ → α ∈ Rc → False) (w : World) :
    (pexIEII ALT φ Rc).presup w ↔
      (∀ ψ, isInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → ¬ψ w) := by
  simp only [pexIEII]
  constructor
  · exact fun ⟨hIE, _⟩ => hIE
  · intro hIE
    exact ⟨hIE, fun α ⟨hα_II, hα_Rc⟩ => absurd hα_Rc (fun h => hII_empty α hα_II h)⟩

-- ============================================================================
-- SECTION 7: Comparison with exhIEII (structural note)
-- ============================================================================

/-!
## Structural Difference: pex vs exh

The key structural difference:

  **exh^{IE+II}(φ)** = φ ∧ ¬IE ∧ II                (flat, fully assertive)
  **pex^{IE+II}(φ)** = φ_{¬IE ∧ homog(II)}          (structured)

For FC (φ = ◇(p∨q)):
  exh: ◇(p∨q) ∧ ◇p ∧ ◇q ∧ ¬◇(p∧q)
  pex: asserts ◇(p∨q), presupposes (◇p ↔ ◇q) ∧ ¬◇(p∧q)

The overall entailments are the same (both entail ◇p ∧ ◇q), but the
at-issue structure differs. This difference is what allows pex to solve
the embedded FC puzzles that exh cannot.

For the concrete worked example over `FCWorld` and the embedded FC
puzzles, see `Phenomena/Modality/Studies/DelPinalBassiSauerland2024.lean`.
-/

end Exhaustification.Presuppositional
