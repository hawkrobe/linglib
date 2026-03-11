import Linglib.Theories.Semantics.Supervaluation.Basic
import Linglib.Core.Logic.Truth3
import Linglib.Core.Logic.Consequence
import Linglib.Core.Logic.ThreeValuedLogic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Tolerant, Classical, Strict (TCS)
@cite{cobreros-etal-2012}

@cite{cobreros-etal-2012} "Tolerant, Classical, Strict."
*Journal of Philosophical Logic* 41:347–385.

## Overview

A similarity-based semantics for vague predicates that derives three
notions of truth from a single model:

- **Classical (c)**: standard satisfaction M ⊨c P(a) iff a ∈ I(P)
- **Tolerant (t)**: M ⊨t P(a) iff ∃d ~_P a, d ∈ I(P)
- **Strict (s)**: M ⊨s P(a) iff ∀d ~_P a, d ∈ I(P)

The tolerance relation ~_P is reflexive and symmetric (but not
transitive) — an indifference relation for predicate P.

## Key Results

- **Extension hierarchy**: strict ⊆ classical ⊆ tolerant (Lemma 1)
- **Tolerance is t-valid**: ∀x∀y(P(x) ∧ x~_Py → P(y)) (Fact 2)
- **Two-step tolerance**: ∀x∀y∀z(P(x) ∧ x~_Py ∧ y~_Pz → P(z)) (Fact 3)
- **Borderline contradictions**: borderline cases tolerantly satisfy P ∧ ¬P
- **LP/K3 correspondence**: t-consequence = LP-consequence,
  s-consequence = K3-consequence (Theorem 3)

## Connection to Supervaluation

Strict truth for an atomic predicate at individual a is supervaluation
over the tolerance neighborhood of a: `superTrue (I(P) ·) {d | d ~_P a}`.
Tolerant truth is the existential dual (sub-truth). This makes TCS a
*localized* supervaluation — each individual gets its own specification
space determined by its similarity neighborhood.

Unlike standard supervaluationism, TCS **allows** borderline
contradictions: P ∧ ¬P is tolerantly true for borderline cases.
In supervaluationism, P ∧ ¬P is super-false even when P is borderline
(penumbral connection). This difference traces to TCS negation:
tolerant ¬φ = not strictly φ (weaker than not classically φ).

## Architecture

This file provides the core TCS framework. It connects to
`Supervaluation/Basic.lean` by showing that strict/tolerant truth
instantiate `superTrue` over tolerance neighborhoods.
-/

namespace Semantics.Supervaluation.TCS

open Core.Duality (Truth3)
open Semantics.Supervaluation (SpecSpace superTrue superTrue_true_iff
  superTrue_false_iff superTrue_indet_iff)

-- ════════════════════════════════════════════════════
-- § 1. T-Models
-- ════════════════════════════════════════════════════

/-- A T-model: a classical model equipped with tolerance (indifference)
    relations per predicate. Each ~_P is reflexive and symmetric but
    possibly non-transitive — capturing "looks the same" for predicate P.

    Definition 4 of @cite{cobreros-etal-2012}. The non-transitivity of
    ~_P is what makes vagueness possible: a can look like b and b can
    look like c, but a need not look like c. -/
structure TModel (D Pred : Type*) where
  /-- Classical interpretation: I(P) ∈ {0,1}^D -/
  interp : Pred → D → Bool
  /-- Tolerance relation ~_P per predicate -/
  sim : Pred → D → D → Bool
  /-- Reflexivity: every individual is similar to itself -/
  sim_refl : ∀ P d, sim P d d = true
  /-- Symmetry: similarity is undirected -/
  sim_symm : ∀ P d₁ d₂, sim P d₁ d₂ = true → sim P d₂ d₁ = true

-- ════════════════════════════════════════════════════
-- § 2. Atomic Satisfaction
-- ════════════════════════════════════════════════════

variable {D Pred : Type*} [Fintype D] [DecidableEq D]

/-- Tolerant atomic satisfaction: M ⊨t P(a) iff some P-similar
    individual classically satisfies P. Definition 9, t-atomic. -/
def tolerantAtom (M : TModel D Pred) (P : Pred) (a : D) : Bool :=
  decide (∃ d : D, M.sim P a d = true ∧ M.interp P d = true)

/-- Strict atomic satisfaction: M ⊨s P(a) iff every P-similar
    individual classically satisfies P. Definition 9, s-atomic. -/
def strictAtom (M : TModel D Pred) (P : Pred) (a : D) : Bool :=
  decide (∀ d : D, M.sim P a d = true → M.interp P d = true)

-- ════════════════════════════════════════════════════
-- § 3. Extension Hierarchy (Lemma 1, atomic)
-- ════════════════════════════════════════════════════

omit [DecidableEq D] in
/-- Strict ⟹ classical: if P holds for all similar individuals,
    it holds for a itself (by reflexivity of ~_P). -/
theorem strict_implies_classical (M : TModel D Pred) (P : Pred) (a : D)
    (hs : strictAtom M P a = true) :
    M.interp P a = true := by
  rw [strictAtom, decide_eq_true_eq] at hs
  exact hs a (M.sim_refl P a)

omit [DecidableEq D] in
/-- Classical ⟹ tolerant: if a classically satisfies P, then a
    itself witnesses tolerant satisfaction (by reflexivity of ~_P). -/
theorem classical_implies_tolerant (M : TModel D Pred) (P : Pred) (a : D)
    (hc : M.interp P a = true) :
    tolerantAtom M P a = true := by
  rw [tolerantAtom, decide_eq_true_eq]
  exact ⟨a, M.sim_refl P a, hc⟩

omit [DecidableEq D] in
/-- Strict ⟹ tolerant (transitive from above). -/
theorem strict_implies_tolerant (M : TModel D Pred) (P : Pred) (a : D)
    (hs : strictAtom M P a = true) :
    tolerantAtom M P a = true :=
  classical_implies_tolerant M P a (strict_implies_classical M P a hs)

-- ════════════════════════════════════════════════════
-- § 4. Tolerance Principle (Facts 2–3)
-- ════════════════════════════════════════════════════

omit [DecidableEq D] in
/-- Strict P at a, plus a ~_P b, gives classical P at b. The strict
    extension is closed under similarity. -/
theorem strict_sim_classical (M : TModel D Pred) (P : Pred) (a b : D)
    (hs : strictAtom M P a = true) (hsim : M.sim P a b = true) :
    M.interp P b = true := by
  rw [strictAtom, decide_eq_true_eq] at hs
  exact hs b hsim

omit [DecidableEq D] in
/-- **One-step tolerance** (Fact 2): if a is strictly P and a ~_P b,
    then b is tolerantly P. This is the tolerance principle
    ∀x∀y(P(x) ∧ x~_Py → P(y)) being t-valid: the premises hold
    strictly, the conclusion holds tolerantly.

    Proof: strict(a) + sim(a,b) → classical(b) → tolerant(b). -/
theorem tolerance_one_step (M : TModel D Pred) (P : Pred) (a b : D)
    (hs : strictAtom M P a = true) (hsim : M.sim P a b = true) :
    tolerantAtom M P b = true :=
  classical_implies_tolerant M P b (strict_sim_classical M P a b hs hsim)

omit [DecidableEq D] in
/-- **Two-step tolerance** (Fact 3): tolerance propagates across
    two similarity steps. If strictly P(a), a ~_P b, b ~_P c, then
    tolerantly P(c). Two steps is the maximum: the third step can
    fail because ~_P is non-transitive.

    Proof: strict(a) + sim(a,b) → classical(b). Then b witnesses
    tolerant(c) via sim(c,b) (by symmetry). -/
theorem tolerance_two_step (M : TModel D Pred) (P : Pred) (a b c : D)
    (hs : strictAtom M P a = true)
    (hab : M.sim P a b = true) (hbc : M.sim P b c = true) :
    tolerantAtom M P c = true := by
  rw [tolerantAtom, decide_eq_true_eq]
  exact ⟨b, M.sim_symm P b c hbc, strict_sim_classical M P a b hs hab⟩

-- ════════════════════════════════════════════════════
-- § 5. Borderline Cases (Definition 10)
-- ════════════════════════════════════════════════════

/-- An individual is borderline-P if it is in the tolerant extension
    but not the strict extension. Equivalently: tolerantly P AND
    tolerantly ¬P (since tolerant ¬P = not strictly P). -/
def isBorderline (M : TModel D Pred) (P : Pred) (a : D) : Bool :=
  tolerantAtom M P a && !strictAtom M P a

omit [DecidableEq D] in
/-- Borderline ↔ witnesses exist on both sides: some P-similar
    individual is classically P, and some is classically not-P. -/
theorem borderline_iff_both_witnesses (M : TModel D Pred) (P : Pred) (a : D) :
    isBorderline M P a = true ↔
    (∃ d, M.sim P a d = true ∧ M.interp P d = true) ∧
    (∃ d, M.sim P a d = true ∧ M.interp P d = false) := by
  simp only [isBorderline, Bool.and_eq_true, Bool.not_eq_true',
    tolerantAtom, strictAtom, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨d, hsd, hpd⟩, hns⟩
    push_neg at hns
    obtain ⟨e, hse, hne⟩ := hns
    refine ⟨⟨d, hsd, hpd⟩, ⟨e, hse, ?_⟩⟩
    cases hv : M.interp P e
    · rfl
    · exact absurd hv hne
  · rintro ⟨⟨d, hsd, hpd⟩, ⟨e, hse, hne⟩⟩
    refine ⟨⟨d, hsd, hpd⟩, ?_⟩
    push_neg; exact ⟨e, hse, by simp [hne]⟩

-- ════════════════════════════════════════════════════
-- § 6. Tolerant Contradictions
-- ════════════════════════════════════════════════════

omit [DecidableEq D] in
/-- Borderline cases satisfy tolerant contradictions: tolerantly P
    AND not strictly P (= tolerantly ¬P). Unlike supervaluationism
    where P ∧ ¬P is super-false even for borderline cases, TCS
    allows borderline contradictions because tolerant negation only
    requires strict truth to fail. -/
theorem borderline_tolerant_contradiction (M : TModel D Pred) (P : Pred) (a : D)
    (hb : isBorderline M P a = true) :
    tolerantAtom M P a = true ∧ strictAtom M P a = false := by
  simp only [isBorderline, Bool.and_eq_true, Bool.not_eq_true'] at hb
  exact hb

-- ════════════════════════════════════════════════════
-- § 7. Bridge: TCS ↔ Supervaluation
-- ════════════════════════════════════════════════════

/-- The tolerance neighborhood of a under P: the set of individuals
    P-similar to a. This is a `SpecSpace` because ~_P is reflexive
    (a is always in its own neighborhood).

    This makes TCS a *localized* supervaluation: each individual
    gets its own specification space. -/
def toleranceSpace (M : TModel D Pred) (P : Pred) (a : D) : SpecSpace D where
  admissible := Finset.univ.filter (fun d => M.sim P a d)
  nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, M.sim_refl P a⟩⟩

omit [DecidableEq D] in
/-- **Strict truth = super-truth** over the tolerance neighborhood.
    An individual strictly satisfies P iff P is true at ALL
    specification points (P-similar individuals) in its tolerance
    space. This is the central architectural connection to
    `Supervaluation/Basic.lean`. -/
theorem strict_iff_superTrue (M : TModel D Pred) (P : Pred) (a : D) :
    strictAtom M P a = true ↔
    superTrue (M.interp P) (toleranceSpace M P a) = Truth3.true := by
  rw [strictAtom, decide_eq_true_eq, superTrue_true_iff]
  constructor
  · intro h d hd; exact h d (Finset.mem_filter.mp hd).2
  · intro h d hd; exact h d (Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩)

omit [DecidableEq D] in
/-- **¬Tolerant = super-false** over the tolerance neighborhood.
    An individual is not tolerantly P iff P is false at ALL
    specification points in its tolerance space. -/
theorem not_tolerant_iff_superFalse (M : TModel D Pred) (P : Pred) (a : D) :
    tolerantAtom M P a = false ↔
    superTrue (M.interp P) (toleranceSpace M P a) = Truth3.false := by
  rw [tolerantAtom, decide_eq_false_iff_not, superTrue_false_iff]
  push_neg
  constructor
  · intro h d hd
    have hsim := (Finset.mem_filter.mp hd).2
    have := h d hsim
    cases hv : M.interp P d <;> simp_all
  · intro h d hd
    have := h d (Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩)
    simp_all

omit [DecidableEq D] in
/-- **Borderline = indefinite** under supervaluation. An individual
    is borderline-P in TCS iff P is indefinite (neither super-true
    nor super-false) over its tolerance space.

    This connects TCS to @cite{fine-1975}'s supervaluationism:
    borderline cases are exactly the cases where the tolerance
    neighborhood disagrees — some similar individuals satisfy P,
    others don't. -/
theorem borderline_iff_superTrue_indet (M : TModel D Pred) (P : Pred) (a : D) :
    isBorderline M P a = true ↔
    superTrue (M.interp P) (toleranceSpace M P a) = Truth3.indet := by
  rw [borderline_iff_both_witnesses, superTrue_indet_iff]
  constructor
  · rintro ⟨⟨d, hsd, hpd⟩, ⟨e, hse, hne⟩⟩
    exact ⟨⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hsd⟩, hpd⟩,
           ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, hse⟩, hne⟩⟩
  · rintro ⟨⟨d, hd, hpd⟩, ⟨e, he, hne⟩⟩
    exact ⟨⟨d, (Finset.mem_filter.mp hd).2, hpd⟩,
           ⟨e, (Finset.mem_filter.mp he).2, hne⟩⟩

-- ════════════════════════════════════════════════════
-- § 8. Formula Language and Compositional Satisfaction
-- ════════════════════════════════════════════════════

/-- Propositional TCS formulas with ground atomic predications.
    No quantifiers — the key results (hierarchy, tolerance,
    borderline contradictions) are visible at this level. -/
inductive TCSFormula (Pred D : Type*) where
  | atom : Pred → D → TCSFormula Pred D
  | neg : TCSFormula Pred D → TCSFormula Pred D
  | conj : TCSFormula Pred D → TCSFormula Pred D → TCSFormula Pred D

/-- Satisfaction mode: tolerant, classical, or strict. -/
inductive SatMode | tolerant | classical | strict
  deriving DecidableEq, Repr

/-- Dual mode: negation swaps t ↔ s and leaves c fixed.
    This encodes the mutual recursion of Definition 9:
    tolerant negation checks strict failure, strict negation
    checks tolerant failure. -/
def SatMode.dual : SatMode → SatMode
  | .tolerant => .strict
  | .strict => .tolerant
  | .classical => .classical

/-- Three-valued satisfaction (Definition 9). The mutual recursion
    between t and s through negation is encoded via `SatMode.dual`. -/
def sat (M : TModel D Pred) : SatMode → TCSFormula Pred D → Bool
  | .classical, .atom P a => M.interp P a
  | .tolerant, .atom P a => tolerantAtom M P a
  | .strict, .atom P a => strictAtom M P a
  | m, .neg φ => !sat M m.dual φ
  | m, .conj φ ψ => sat M m φ && sat M m ψ

-- ════════════════════════════════════════════════════
-- § 9. Full Hierarchy (Lemma 1)
-- ════════════════════════════════════════════════════

private lemma bool_contra_neg {a b : Bool}
    (h : a = true → b = true) : !b = true → !a = true := by
  cases a <;> cases b <;> simp_all

omit [DecidableEq D] in
/-- **Lemma 1** (full formula level): for any formula φ,
    strict satisfaction implies classical, and classical implies
    tolerant. The negation case uses contrapositive of the other
    direction — this is why both directions must be proved together. -/
theorem sat_hierarchy (M : TModel D Pred) (φ : TCSFormula Pred D) :
    (sat M .strict φ = true → sat M .classical φ = true) ∧
    (sat M .classical φ = true → sat M .tolerant φ = true) := by
  induction φ with
  | atom P a =>
    exact ⟨strict_implies_classical M P a, classical_implies_tolerant M P a⟩
  | neg ψ ih =>
    refine ⟨?_, ?_⟩
    · -- s(¬ψ) → c(¬ψ): contrapositive of c(ψ) → t(ψ)
      cases hc : sat M .classical ψ <;> cases ht : sat M .tolerant ψ <;>
        simp_all [sat, SatMode.dual]
    · -- c(¬ψ) → t(¬ψ): contrapositive of s(ψ) → c(ψ)
      cases hs : sat M .strict ψ <;> cases hc : sat M .classical ψ <;>
        simp_all [sat, SatMode.dual]
  | conj ψ χ ihψ ihχ =>
    simp only [sat, Bool.and_eq_true]
    exact ⟨fun ⟨h1, h2⟩ => ⟨ihψ.1 h1, ihχ.1 h2⟩,
           fun ⟨h1, h2⟩ => ⟨ihψ.2 h1, ihχ.2 h2⟩⟩

omit [DecidableEq D] in
theorem sat_strict_implies_classical (M : TModel D Pred)
    (φ : TCSFormula Pred D) :
    sat M .strict φ = true → sat M .classical φ = true :=
  (sat_hierarchy M φ).1

omit [DecidableEq D] in
theorem sat_classical_implies_tolerant (M : TModel D Pred)
    (φ : TCSFormula Pred D) :
    sat M .classical φ = true → sat M .tolerant φ = true :=
  (sat_hierarchy M φ).2

-- ════════════════════════════════════════════════════
-- § 10. Duality (Remark 1)
-- ════════════════════════════════════════════════════

omit [DecidableEq D] in
/-- **Remark 1**: tolerant and strict are duals. M ⊨t φ iff M ⊭s ¬φ,
    and M ⊨s φ iff M ⊭t ¬φ. This falls out of the definition:
    sat .tolerant (neg φ) = !(sat .strict φ). -/
theorem tolerant_strict_duality (M : TModel D Pred) (φ : TCSFormula Pred D) :
    sat M .tolerant φ = !sat M .strict (.neg φ) := by
  simp [sat, SatMode.dual, Bool.not_not]

omit [DecidableEq D] in
/-- Dual direction: M ⊨s φ iff M ⊭t ¬φ. -/
theorem strict_tolerant_duality (M : TModel D Pred) (φ : TCSFormula Pred D) :
    sat M .strict φ = !sat M .tolerant (.neg φ) := by
  simp [sat, SatMode.dual, Bool.not_not]

-- ════════════════════════════════════════════════════
-- § 11. Concrete Example: 4-Element Sorites Model
-- ════════════════════════════════════════════════════

/-! The paper's running example (p. 354–355): four individuals
    a, b, c, d in a chain of pairwise similarities.
    I(P) = {a, b}: a and b are classically tall.
    a ~_P b ~_P c ~_P d (chain), nothing else beyond reflexivity.

    Predictions:
    - Strict extension: {a} (only a has ALL neighbors classically P)
    - Classical extension: {a, b}
    - Tolerant extension: {a, b, c} (c has neighbor b who is P)
    - Borderline: {b, c}
    - b and c tolerantly satisfy P ∧ ¬P -/

section Example

inductive Elt | a | b | c | d
  deriving Repr, DecidableEq, BEq

instance : Fintype Elt where
  elems := {.a, .b, .c, .d}
  complete x := by cases x <;> simp

inductive VPred | tall
  deriving Repr, DecidableEq

def soritesModel : TModel Elt VPred where
  interp
    | .tall, .a => true | .tall, .b => true
    | .tall, .c => false | .tall, .d => false
  sim
    | .tall, .a, .a => true | .tall, .a, .b => true
    | .tall, .b, .a => true | .tall, .b, .b => true | .tall, .b, .c => true
    | .tall, .c, .b => true | .tall, .c, .c => true | .tall, .c, .d => true
    | .tall, .d, .c => true | .tall, .d, .d => true
    | _, _, _ => false
  sim_refl P x := by cases P; cases x <;> rfl
  sim_symm P x₁ x₂ h := by cases P; cases x₁ <;> cases x₂ <;> simp_all

-- Extension verification

theorem strict_extension :
    strictAtom soritesModel .tall .a = true ∧
    strictAtom soritesModel .tall .b = false ∧
    strictAtom soritesModel .tall .c = false ∧
    strictAtom soritesModel .tall .d = false := by native_decide

theorem classical_extension :
    soritesModel.interp .tall .a = true ∧
    soritesModel.interp .tall .b = true ∧
    soritesModel.interp .tall .c = false ∧
    soritesModel.interp .tall .d = false := by decide

theorem tolerant_extension :
    tolerantAtom soritesModel .tall .a = true ∧
    tolerantAtom soritesModel .tall .b = true ∧
    tolerantAtom soritesModel .tall .c = true ∧
    tolerantAtom soritesModel .tall .d = false := by native_decide

-- Borderline cases: b and c

theorem b_is_borderline :
    isBorderline soritesModel .tall .b = true := by native_decide

theorem c_is_borderline :
    isBorderline soritesModel .tall .c = true := by native_decide

theorem a_not_borderline :
    isBorderline soritesModel .tall .a = false := by native_decide

theorem d_not_borderline :
    isBorderline soritesModel .tall .d = false := by native_decide

-- Tolerant contradictions at borderline cases

theorem b_tolerant_contradiction :
    sat soritesModel .tolerant
      (.conj (.atom .tall .b) (.neg (.atom .tall .b))) = true := by
  native_decide

theorem c_tolerant_contradiction :
    sat soritesModel .tolerant
      (.conj (.atom .tall .c) (.neg (.atom .tall .c))) = true := by
  native_decide

-- Non-borderline cases do NOT satisfy tolerant contradictions

theorem a_no_tolerant_contradiction :
    sat soritesModel .tolerant
      (.conj (.atom .tall .a) (.neg (.atom .tall .a))) = false := by
  native_decide

theorem d_no_tolerant_contradiction :
    sat soritesModel .tolerant
      (.conj (.atom .tall .d) (.neg (.atom .tall .d))) = false := by
  native_decide

-- Classical contradictions are always classically false

theorem classical_contradiction_false (x : Elt) :
    sat soritesModel .classical
      (.conj (.atom .tall x) (.neg (.atom .tall x))) = false := by
  cases x <;> native_decide

-- Non-transitivity: a ~_P b and b ~_P c but a ≁_P c

theorem sim_non_transitive :
    soritesModel.sim .tall .a .b = true ∧
    soritesModel.sim .tall .b .c = true ∧
    soritesModel.sim .tall .a .c = false := by decide

-- Tolerance propagation: a is strictly tall, c is tolerantly tall
-- (two steps along the chain), but d is NOT tolerantly tall
-- (three steps would be needed)

theorem tolerance_reaches_c :
    strictAtom soritesModel .tall .a = true ∧
    tolerantAtom soritesModel .tall .c = true ∧
    tolerantAtom soritesModel .tall .d = false := by native_decide

end Example

-- ════════════════════════════════════════════════════
-- § 12. Nine Consequence Relations (Definition 17)
-- ════════════════════════════════════════════════════

/-! @cite{cobreros-etal-2012} §3: from three notions of satisfaction
    {s, c, t} we obtain nine consequence relations ⊨ᵐⁿ by varying
    the standard for premises (m) and conclusions (n). -/

/-- Lift Boolean satisfaction to Prop for use with `MixedConsequence`. -/
def satProp (M : TModel D Pred) (mode : SatMode) (φ : TCSFormula Pred D) : Prop :=
  sat M mode φ = true

open Core.Logic.Consequence (MixedConsequence SatImplies)

/-- The nine TCS consequence relations as instances of `MixedConsequence`. -/
def tcsConsequence [Fintype D] [DecidableEq D]
    (m n : SatMode) (Γ : List (TCSFormula Pred D)) (φ : TCSFormula Pred D) : Prop :=
  MixedConsequence (satProp (D := D) (Pred := Pred)) m n Γ φ

-- ════════════════════════════════════════════════════
-- § 13. Strength Ordering (Lemma 7)
-- ════════════════════════════════════════════════════

omit [DecidableEq D] in
/-- Strict satisfaction implies classical. -/
theorem satImplies_strict_classical :
    SatImplies (satProp (D := D) (Pred := Pred)) SatMode.strict SatMode.classical :=
  fun M φ h => sat_strict_implies_classical M φ h

omit [DecidableEq D] in
/-- Classical satisfaction implies tolerant. -/
theorem satImplies_classical_tolerant :
    SatImplies (satProp (D := D) (Pred := Pred)) SatMode.classical SatMode.tolerant :=
  fun M φ h => sat_classical_implies_tolerant M φ h

omit [DecidableEq D] in
/-- Strict satisfaction implies tolerant (transitive). -/
theorem satImplies_strict_tolerant :
    SatImplies (satProp (D := D) (Pred := Pred)) SatMode.strict SatMode.tolerant :=
  SatImplies.trans satImplies_strict_classical satImplies_classical_tolerant

-- ════════════════════════════════════════════════════
-- § 14. Identity Models and Mode Collapse
-- ════════════════════════════════════════════════════

/-- An **identity T-model**: similarity is the identity relation.
    In such models, tolerant = classical = strict for all formulas,
    since the only element similar to a is a itself.

    This is the key construction in @cite{cobreros-etal-2012} Lemma 2:
    every C-model can be expanded to a T-model where all three notions
    of satisfaction coincide. -/
def identityModel (interp : Pred → D → Bool) : TModel D Pred where
  interp := interp
  sim _ d₁ d₂ := decide (d₁ = d₂)
  sim_refl _ d := by simp
  sim_symm _ d₁ d₂ h := by simp [decide_eq_true_eq] at *; exact h.symm

/-- In an identity model, tolerant satisfaction equals classical. -/
theorem identityModel_tolerant_eq_classical (interp : Pred → D → Bool)
    (P : Pred) (a : D) :
    tolerantAtom (identityModel interp) P a = interp P a := by
  simp only [tolerantAtom, identityModel, decide_eq_true_eq]
  cases hv : interp P a <;> simp [hv]

/-- In an identity model, strict satisfaction equals classical. -/
theorem identityModel_strict_eq_classical (interp : Pred → D → Bool)
    (P : Pred) (a : D) :
    strictAtom (identityModel interp) P a = interp P a := by
  simp only [strictAtom, identityModel, decide_eq_true_eq]
  cases hv : interp P a <;> simp [hv]

/-- **All modes agree in an identity model** (Lemma 2).
    For any formula, satisfaction under all three modes coincides. -/
theorem identityModel_modes_agree (interp : Pred → D → Bool)
    (mode : SatMode) (φ : TCSFormula Pred D) :
    sat (identityModel interp) mode φ =
    sat (identityModel interp) .classical φ := by
  induction φ generalizing mode with
  | atom P a =>
    cases mode with
    | classical => rfl
    | tolerant => exact identityModel_tolerant_eq_classical interp P a
    | strict => exact identityModel_strict_eq_classical interp P a
  | neg ψ ih =>
    simp only [sat]; congr 1; exact ih mode.dual
  | conj ψ χ ihψ ihχ =>
    simp only [sat]; exact congr (congrArg _ (ihψ mode)) (ihχ mode)

-- ════════════════════════════════════════════════════
-- § 15. Collapse Theorem (Lemma 8)
-- ════════════════════════════════════════════════════

/-- **Lemma 8**: cc = sc = ct = st. All four relations coincide.

    Proof strategy:
    - cc ⊆ sc ⊆ st (by premise/conclusion monotonicity)
    - cc ⊆ ct ⊆ st (by premise/conclusion monotonicity)
    - st ⊆ cc (by identity model argument: every cc-counterexample
      gives an st-counterexample via the identity model)

    Hence all four are equal. We prove st ⊆ cc; the rest follow
    from monotonicity. -/
theorem st_implies_cc
    {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (hst : tcsConsequence (D := D) (Pred := Pred) .strict .tolerant Γ φ) :
    tcsConsequence .classical .classical Γ φ := by
  intro M hprem
  -- Construct identity model from M's interpretation
  let M' := identityModel (D := D) (Pred := Pred) M.interp
  -- In M', all modes agree with classical
  have hagree : ∀ (mode : SatMode) (ψ : TCSFormula Pred D),
      sat M' mode ψ = sat M' .classical ψ :=
    identityModel_modes_agree M.interp
  -- M' has the same classical interpretation as M
  have hsame : ∀ ψ : TCSFormula Pred D,
      sat M .classical ψ = sat M' .classical ψ := by
    intro ψ; induction ψ with
    | atom P a => rfl
    | neg ψ ih => simp [sat, SatMode.dual, ih]
    | conj ψ χ ihψ ihχ => simp [sat, ihψ, ihχ]
  -- Premises hold strictly in M' (since strict = classical in M')
  have hprem' : ∀ γ ∈ Γ, satProp M' .strict γ := fun γ hγ => by
    rw [satProp, hagree .strict γ, ← hsame γ]
    exact hprem γ hγ
  -- Conclusion holds tolerantly in M' (by st-consequence)
  have hconc' := hst M' hprem'
  -- Tolerant = classical in M'
  rw [satProp, hagree .tolerant φ, ← hsame φ] at hconc'
  exact hconc'

/-- cc ⊆ st (by monotonicity). -/
theorem cc_implies_st
    {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D}
    (hcc : tcsConsequence (D := D) (Pred := Pred) .classical .classical Γ φ) :
    tcsConsequence .strict .tolerant Γ φ :=
  Core.Logic.Consequence.mixed_monotone
    satImplies_strict_classical satImplies_classical_tolerant hcc

/-- **cc = st**: the four mixed consequence relations coincide. -/
theorem cc_iff_st
    {Γ : List (TCSFormula Pred D)} {φ : TCSFormula Pred D} :
    tcsConsequence (D := D) (Pred := Pred) .classical .classical Γ φ ↔
    tcsConsequence .strict .tolerant Γ φ :=
  ⟨cc_implies_st, st_implies_cc⟩

-- ════════════════════════════════════════════════════
-- § 16. Duality of TCS Satisfaction
-- ════════════════════════════════════════════════════

open Core.Logic.Consequence (SatDuality IsSelfDual)

/-- The dual mode involution: d(d(m)) = m. -/
theorem dual_invol (m : SatMode) : m.dual.dual = m := by
  cases m <;> rfl

omit [DecidableEq D] in
/-- **Satisfaction-level duality**: M ⊨ᵐ ¬φ iff M ⊭^{d(m)} φ.
    Negation swaps the satisfaction mode via the dual operation.

    Note: TCSFormula.neg is NOT an involution (¬¬φ ≠ φ syntactically),
    so the abstract `SatDuality` structure from Consequence.lean
    does not apply. Instead we prove the key property directly. -/
theorem sat_neg_swap (M : TModel D Pred) (m : SatMode) (φ : TCSFormula Pred D) :
    sat M m (.neg φ) = !sat M m.dual φ := by
  simp [sat]

/-- **st is self-dual**: d(t) = s and d(s) = t. Self-dual
    consequence relations satisfy the deduction theorem
    (Lemma 10 of @cite{cobreros-etal-2012}). -/
theorem st_self_dual : IsSelfDual SatMode.dual .strict .tolerant := rfl

/-- **cc is self-dual**: d(c) = c. -/
theorem cc_self_dual : IsSelfDual SatMode.dual .classical .classical := rfl

-- ════════════════════════════════════════════════════
-- § 17. LP/K3 Correspondence (Theorem 3)
-- ════════════════════════════════════════════════════

private theorem Bool.ne_false_eq_true {b : Bool} (h : b ≠ false) : b = true := by
  cases b <;> simp at h ⊢

private theorem Bool.ne_true_eq_false {b : Bool} (h : b ≠ true) : b = false := by
  cases b <;> simp at h ⊢

open Core.Duality (Truth3)
open Core.Logic.ThreeValuedLogic (isLPDesignated isK3Designated
  lp_neg_iff_not_k3 k3_neg_iff_not_lp lp_meet k3_meet)

/-- Construct a three-valued interpretation from a T-model.
    Each atom (P, a) gets:
    - `Truth3.true` if strictly P(a) (all similar individuals satisfy P)
    - `Truth3.false` if not tolerantly P(a) (no similar individual satisfies P)
    - `Truth3.indet` otherwise (borderline: some similar individuals do, others don't)

    This is the construction in Lemma 4 of @cite{cobreros-etal-2012}. -/
def toMV (M : TModel D Pred) : Pred → D → Truth3 :=
  fun P a =>
    if strictAtom M P a then Truth3.true
    else if tolerantAtom M P a then Truth3.indet
    else Truth3.false

/-- Three-valued evaluation of TCS formulas using Strong Kleene
    connectives, parameterized by a three-valued atom valuation. -/
def mvEvalTCS (v : Pred → D → Truth3) : TCSFormula Pred D → Truth3
  | .atom P a => v P a
  | .neg φ => Truth3.neg (mvEvalTCS v φ)
  | .conj φ ψ => Truth3.meet (mvEvalTCS v φ) (mvEvalTCS v ψ)

omit [DecidableEq D] in
/-- The three-valued interpretation correctly classifies atoms:
    `toMV` produces `Truth3.true` exactly when strict, `Truth3.false`
    exactly when not tolerant, and `Truth3.indet` for borderline. -/
theorem toMV_true_iff (M : TModel D Pred) (P : Pred) (a : D) :
    toMV M P a = Truth3.true ↔ strictAtom M P a = true := by
  simp [toMV]; split <;> simp_all

omit [DecidableEq D] in
theorem toMV_false_iff (M : TModel D Pred) (P : Pred) (a : D) :
    toMV M P a = Truth3.false ↔ tolerantAtom M P a = false := by
  unfold toMV
  constructor
  · intro h
    by_contra ht
    have ht' := Bool.ne_false_eq_true ht
    have hs : strictAtom M P a = false := by
      by_contra hsc; simp [Bool.ne_false_eq_true hsc] at h
    simp [hs, ht'] at h
  · intro h
    have hns : strictAtom M P a = false := by
      by_contra hc
      have := strict_implies_tolerant M _ a (Bool.ne_false_eq_true hc)
      rw [h] at this; cases this
    simp [hns, h]

omit [DecidableEq D] in
/-- **Correspondence at the formula level** (Theorem 3).

    For any T-model M and formula φ:
    - M ⊨ᵗ φ iff `mvEvalTCS (toMV M) φ` is LP-designated
    - M ⊨ˢ φ iff `mvEvalTCS (toMV M) φ` is K3-designated

    This establishes that t-satisfaction = LP-satisfaction and
    s-satisfaction = K3-satisfaction via the `toMV` translation. -/
theorem tcs_lp_k3_correspondence (M : TModel D Pred)
    (φ : TCSFormula Pred D) :
    (sat M .tolerant φ = true ↔ isLPDesignated (mvEvalTCS (toMV M) φ)) ∧
    (sat M .strict φ = true ↔ isK3Designated (mvEvalTCS (toMV M) φ)) := by
  induction φ with
  | atom P a =>
    constructor
    · -- tolerant ↔ LP-designated (non-false)
      unfold sat mvEvalTCS
      constructor
      · intro h hf
        have := (toMV_false_iff M P a).mp hf
        rw [h] at this; cases this
      · intro h
        by_contra hc
        exact h ((toMV_false_iff M P a).mpr (Bool.ne_true_eq_false hc))
    · -- strict ↔ K3-designated (= true)
      unfold sat mvEvalTCS isK3Designated
      exact (toMV_true_iff M P a).symm
  | neg ψ ih =>
    obtain ⟨iht, ihs⟩ := ih
    -- Key: sat M m (.neg ψ) = !sat M m.dual ψ  (by sat definition)
    have neg_t : sat M .tolerant (.neg ψ) = !sat M .strict ψ := by simp [sat, SatMode.dual]
    have neg_s : sat M .strict (.neg ψ) = !sat M .tolerant ψ := by simp [sat, SatMode.dual]
    constructor
    · -- tolerant (neg ψ) ↔ LP(neg eval)
      unfold mvEvalTCS
      rw [lp_neg_iff_not_k3]
      constructor
      · intro h hk3
        rw [neg_t] at h
        exact absurd (ihs.mpr hk3) (by cases sat M .strict ψ <;> simp_all)
      · intro h
        rw [neg_t]
        cases hv : sat M .strict ψ <;> simp
        exact absurd (ihs.mp hv) h
    · -- strict (neg ψ) ↔ K3(neg eval)
      unfold mvEvalTCS
      rw [k3_neg_iff_not_lp]
      constructor
      · intro h hlp
        rw [neg_s] at h
        exact absurd (iht.mpr hlp) (by cases sat M .tolerant ψ <;> simp_all)
      · intro h
        rw [neg_s]
        cases hv : sat M .tolerant ψ <;> simp
        exact absurd (iht.mp hv) h
  | conj ψ χ ihψ ihχ =>
    obtain ⟨ihtψ, ihsψ⟩ := ihψ
    obtain ⟨ihtχ, ihsχ⟩ := ihχ
    have hsat_conj : ∀ m, sat M m (.conj ψ χ) = (sat M m ψ && sat M m χ) :=
      fun _ => by simp [sat]
    constructor
    · -- tolerant conj ↔ LP meet
      unfold mvEvalTCS
      rw [lp_meet]
      constructor
      · intro h
        rw [hsat_conj] at h; simp [Bool.and_eq_true] at h
        exact ⟨ihtψ.mp h.1, ihtχ.mp h.2⟩
      · intro ⟨h1, h2⟩
        rw [hsat_conj]; simp [Bool.and_eq_true]
        exact ⟨ihtψ.mpr h1, ihtχ.mpr h2⟩
    · -- strict conj ↔ K3 meet
      unfold mvEvalTCS
      rw [k3_meet]
      constructor
      · intro h
        rw [hsat_conj] at h; simp [Bool.and_eq_true] at h
        exact ⟨ihsψ.mp h.1, ihsχ.mp h.2⟩
      · intro ⟨h1, h2⟩
        rw [hsat_conj]; simp [Bool.and_eq_true]
        exact ⟨ihsψ.mpr h1, ihsχ.mpr h2⟩

omit [DecidableEq D] in
/-- **Theorem 3, t-direction**: tolerant satisfaction = LP-satisfaction. -/
theorem tolerant_iff_lp (M : TModel D Pred) (φ : TCSFormula Pred D) :
    sat M .tolerant φ = true ↔ isLPDesignated (mvEvalTCS (toMV M) φ) :=
  (tcs_lp_k3_correspondence M φ).1

omit [DecidableEq D] in
/-- **Theorem 3, s-direction**: strict satisfaction = K3-satisfaction. -/
theorem strict_iff_k3 (M : TModel D Pred) (φ : TCSFormula Pred D) :
    sat M .strict φ = true ↔ isK3Designated (mvEvalTCS (toMV M) φ) :=
  (tcs_lp_k3_correspondence M φ).2

-- ════════════════════════════════════════════════════
-- § 18. Sorites Resolution via st-consequence (§3.6)
-- ════════════════════════════════════════════════════

/-! The sorites paradox is resolved by st-consequence:

    **Version 1**: Pa₁, a₁Iₚa₂, a₂Iₚa₃, ..., aₙ₋₁Iₚaₙ ⊨ˢᵗ Paₙ

    This is st-INVALID. The premises require strict truth (all
    similar individuals satisfy P), but in the sorites model,
    the first premise Pa₁ is strictly true while the similarity
    premises create a chain. The conclusion Paₙ fails tolerantly.

    Each individual step IS st-valid: Pa, aIₚb ⊨ˢᵗ Pb.
    But st-consequence is non-transitive, so chaining fails.

    We demonstrate this on the concrete 4-element model from § 11. -/

section Sorites

/-- Tolerance steps in the sorites model: each adjacent pair
    has the tolerant-conclusion step valid (the similar individual
    is tolerantly P), but the strict-premise step only works for a.

    a: strictly tall, b: tolerantly tall (but not strictly),
    c: tolerantly tall (but not classically), d: not tolerantly tall. -/
theorem sorites_satisfaction_profile :
    sat soritesModel .strict (.atom .tall .a) = true ∧
    sat soritesModel .classical (.atom .tall .b) = true ∧
    sat soritesModel .tolerant (.atom .tall .c) = true ∧
    sat soritesModel .tolerant (.atom .tall .d) = false := by
  native_decide

/-- **Non-transitivity of st-consequence.** Even though each step
    a→b and b→c holds individually in `soritesModel`, the chain
    a→d fails: d is NOT tolerantly tall.

    In the 4-element sorites model:
    - a is strictly tall, b is tolerantly tall (step a→b valid)
    - b is classically tall, c is tolerantly tall (step b→c valid)
    - But d is NOT tolerantly tall (chain breaks)

    This demonstrates that st-consequence is non-transitive
    (Footnote 14 of @cite{cobreros-etal-2012}). -/
theorem st_nontransitive :
    -- a is strictly tall
    sat soritesModel .strict (.atom .tall .a) = true ∧
    -- b is tolerantly tall
    sat soritesModel .tolerant (.atom .tall .b) = true ∧
    -- c is tolerantly tall
    sat soritesModel .tolerant (.atom .tall .c) = true ∧
    -- But d is NOT tolerantly tall (chain breaks)
    sat soritesModel .tolerant (.atom .tall .d) = false := by
  native_decide

/-- The sorites argument a₁ → a₂ → a₃ → a₄ is st-invalid: we
    cannot derive tolerant Pa₄ from strict Pa₁ plus the full
    similarity chain, because the chain exceeds the two-step
    tolerance limit. -/
theorem sorites_chain_invalid :
    ¬tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [.atom .tall .a] (.atom .tall .d) := by
  intro h
  have hprem : sat soritesModel .strict (.atom .tall .a) = true := by native_decide
  have hd := h soritesModel (fun γ hγ => by simp at hγ; subst hγ; exact hprem)
  -- But d is not tolerantly tall in soritesModel
  have hfalse : sat soritesModel .tolerant (.atom .tall .d) = false := by native_decide
  exact absurd hd (by simp [satProp, hfalse])

end Sorites

-- ════════════════════════════════════════════════════
-- § 19. Strength Lattice Summary
-- ════════════════════════════════════════════════════

/-! The nine consequence relations on the restricted vocabulary
    (propositional formulas — no identity or similarity predicates)
    collapse to six distinct relations, ordered by strength:

    ```
        cc = sc = ct = st        (classical)
         /              \
       ss               tt
        \              /
       cs              tc
         \            /
            ts         (empty)
    ```

    - **cc = st**: classical consequence (four collapse)
    - **ss**: K3-consequence (strict-to-strict)
    - **tt**: LP-consequence (tolerant-to-tolerant)
    - **cs**: strictly weaker than ss
    - **tc**: strictly weaker than tt
    - **ts**: the empty relation (Lemma 9: nothing follows)

    Key properties of st (the recommended relation):
    - Validates tolerance (the principle ∀xy(Px ∧ xIᵨy → Py))
    - Satisfies the deduction theorem
    - Has modus ponens
    - Is non-transitive (blocks sorites chaining)
-/

end Semantics.Supervaluation.TCS
