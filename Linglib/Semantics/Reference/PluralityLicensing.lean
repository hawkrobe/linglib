import Linglib.Semantics.Dynamic.PPCDRT.Anaphora

/-!
# Plurality Licensing for Anaphors
[rakosi-2019]

The split between **morphosyntactic** and **semantic** plurality licensing
of anaphors. [rakosi-2019] demonstrates that Hungarian reciprocals
(*egymás*) tolerate morphosyntactically singular antecedents (quantified
NPs, singular coordinate DPs, collective nouns) while reflexives
(*maga/maguk*) require morphosyntactic plurality (plural noun head + plural
verb agreement + plural anaphor form).

The distinction is derivable from the formal semantics:

- **Reflexive binding** (=) operates via φ-feature agreement. The anaphor
  must match the morphosyntactic features of its antecedent and the verb.
  Agreement is a syntactic mechanism → morphosyntactic plurality required.
- **Reciprocity** (R) requires per-state distinctness, presupposing
  multiple individuals in the denotation. This is a semantic requirement:
  the antecedent must *denote* a plurality, but need not *bear plural
  morphology*.

## Anchoring

Substrate originating with [rakosi-2019]; consumed by
`Studies/Rakosi2019.lean` (the paper formalisation) and
`Fragments/Hungarian/Reciprocals.lean` (the per-language data file). Two
consumers cross the linglib substrate-promotion threshold; sits in
`Reference/` rather than directly in either consumer to preserve the
Fragments → Substrate dependency arrow (Fragments may not import
Studies).

This file does not depend on H&D 2020 or DH 2024 — only on the PPCDRT
substrate that defines `bindingCond`, `reciprocityCond`,
`groupIdentityCond`.
-/

namespace Semantics.Reference.PluralityLicensing

open PPCDRT
open Core

universe u

variable {E : Type u}

-- ════════════════════════════════════════════════════════════════
-- § 1: Plurality Requirement Type
-- ════════════════════════════════════════════════════════════════

/-- What kind of plurality an anaphor requires from its antecedent.

    [rakosi-2019]: Hungarian reciprocals tolerate morphosyntactically
    singular antecedents while reflexives do not. The distinction is
    derivable from the formal semantics:

    - **Reflexive binding** (=) operates via φ-feature agreement → requires
      morphosyntactic plurality.
    - **Reciprocity** (R) requires per-state distinctness in the denotation
      → semantic plurality suffices. -/
inductive PluralityRequirement where
  /-- Requires plural morphology on the antecedent + plural verb agreement
      + plural anaphor form. Characteristic of reflexive anaphors. -/
  | morphosyntactic
  /-- Requires only that the antecedent denote multiple individuals.
      Syntactic number features are irrelevant. Characteristic of
      reciprocal anaphors. -/
  | semantic
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Anaphor → Requirement Map
-- ════════════════════════════════════════════════════════════════

/-- The plurality requirement for each anaphor type, derived from the
    underlying anaphoric relation:
    - Reflexives use binding (=) → φ-agreement → morphosyntactic.
    - Reciprocals use reciprocity (R) → semantic distinctness → semantic. -/
def anaphorPluralityReq (isReciprocal : Bool) : PluralityRequirement :=
  if isReciprocal then .semantic else .morphosyntactic

/-- Whether an antecedent satisfies the plurality requirement. -/
def satisfiesPluralityReq (req : PluralityRequirement)
    (syntacticPl semanticPl : Bool) : Bool :=
  match req with
  | .morphosyntactic => syntacticPl
  | .semantic        => semanticPl

-- ════════════════════════════════════════════════════════════════
-- § 3: Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Reciprocals are licensed by semantic plurality alone. -/
theorem recip_licensed_by_semantic_plurality (semanticPl : Bool)
    (h : semanticPl = true) :
    satisfiesPluralityReq (anaphorPluralityReq true) false semanticPl = true := by
  simp only [satisfiesPluralityReq, anaphorPluralityReq, if_true, h]

/-- Reflexives require morphosyntactic plurality: semantic plurality alone
    is insufficient. -/
theorem refl_needs_morphosyntactic_plurality :
    satisfiesPluralityReq (anaphorPluralityReq false) false true = false := rfl

/-- When an antecedent IS morphosyntactically plural, both anaphor types
    are licensed (morphosyntactic plurality implies semantic). -/
theorem morphosyntactic_pl_licenses_both :
    satisfiesPluralityReq (anaphorPluralityReq false) true true = true ∧
    satisfiesPluralityReq (anaphorPluralityReq true) true true = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: Connection to PPCDRT Reciprocity
-- ════════════════════════════════════════════════════════════════

/-- Reciprocity in PPCDRT — restricted to states where both drefs are
    *defined* — forces at least two distinct individuals in the value
    range. The distinctness clause of `reciprocityCond` says that whenever
    `s uAnaph = some d_a` and `s uAnt = some d_b`, `d_a ≠ d_b`; so any
    jointly-defined witness produces a pair of distinct values.

    Partiality means we can't derive the existence of *some* jointly-defined
    state from `S.IsNonempty` alone — the anaphor and antecedent could each
    be defined on disjoint subsets of `S` (or nowhere), leaving the
    distinctness clause vacuously true. The strengthened hypothesis
    `hdef : ∃ s ∈ S, (s uAnaph).isSome ∧ (s uAnt).isSome` is the natural
    one for the linguistic case (a discourse referent introduced by a
    reciprocal forces its antecedent to be jointly defined at some state
    — paper eq 41 makes this explicit through the `∂(∪u = ∪𝒜(u))`
    presupposition combined with the existential extension `[u]`).

    This is the formal-semantic justification for `.semantic` plurality
    licensing of reciprocals: when the meaning is *non-vacuously* satisfied,
    the denotation is forced to contain plurality, regardless of whether
    the antecedent bears plural morphology. -/
theorem reciprocity_implies_multiple_individuals (uAnaph uAnt : Nat)
    (S : PluralAssign E) (Δ : Set Nat)
    (hdef : ∃ s ∈ S, (s uAnaph).isSome ∧ (s uAnt).isSome)
    (h : reciprocityCond uAnaph uAnt S Δ) :
    ∃ (a b : E), a ≠ b := by
  obtain ⟨g, hgS, hAnaph, hAnt⟩ := hdef
  obtain ⟨da, hda⟩ := Option.isSome_iff_exists.mp hAnaph
  obtain ⟨db, hdb⟩ := Option.isSome_iff_exists.mp hAnt
  exact ⟨da, db, h.2 g hgS da db hda hdb⟩

/-- Binding (`bindingCond`) is compatible with a singleton state where
    both drefs are mapped to the same value — there is no distinctness
    requirement, so the antecedent can be a single individual. This is
    why reflexive binding does NOT impose a semantic plurality
    requirement. -/
theorem binding_compatible_with_singleton (e : E) (uAnaph uAnt : Nat) :
    bindingCond uAnaph uAnt
      (PluralAssign.singleton (PartialAssign.update (PartialAssign.update PartialAssign.empty uAnaph e) uAnt e)) ∅ := by
  intro g hg
  simp only [PluralAssign.singleton, Membership.mem] at hg
  subst hg
  by_cases h : uAnaph = uAnt
  · subst h; rfl
  · simp [PartialAssign.update_at, h]

end Semantics.Reference.PluralityLicensing
