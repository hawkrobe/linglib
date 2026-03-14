/-
# Plural Distributivity and Non-Maximality

Formalizes the independence of distributivity and maximality,
following Križ & @cite{kriz-spector-2021} and @cite{haslinger-etal-2025}.

## Insight

Distributivity (predicate applies to each atom) and maximality
(no exceptions allowed) are orthogonal semantic properties.
The tolerance relation ⪯ (which pluralities count as "similar enough")
is a contextual parameter—essentially a QUD on the plurality domain.

## Connection to QUD Infrastructure

A tolerance relation induces a partition on pluralities:
- Identity tolerance → exact QUD (every distinction matters)
- Coarser tolerance → coarser QUD (some exceptions irrelevant)

This parallels how QUDs partition propositions in `Core/QUD.lean`.

-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Linglib.Core.Discourse.QUD
import Linglib.Core.Logic.Truth3
import Linglib.Theories.Semantics.Supervaluation.Basic

namespace Semantics.Lexical.Plural.Distributivity

variable {Atom W : Type*} [DecidableEq Atom]

-- Tolerance Relations (Križ & @cite{kriz-spector-2021}, Definition 14)

/--
A tolerance relation determines which sub-pluralities count as
"similar enough" to the whole for current conversational purposes.

Formally: ⪯ is reflexive and respects mereological structure.
-/
structure Tolerance (Atom : Type*) [DecidableEq Atom] where
  /-- y ⪯ x: y is similar enough to x -/
  rel : Finset Atom → Finset Atom → Bool
  /-- Reflexivity -/
  refl : ∀ x, rel x x = true
  /-- Tolerance implies part-of -/
  sub : ∀ x y, rel x y = true → x ⊆ y

namespace Tolerance

/-- Identity: only x ⪯ x (forces maximal reading) -/
def identity : Tolerance Atom where
  rel x y := x == y
  refl x := beq_self_eq_true x
  sub x y h := by simp only [beq_iff_eq] at h; exact h ▸ Finset.Subset.refl x

/-- Full: any part is tolerant (allows existential reading) -/
def full : Tolerance Atom where
  rel x y := decide (x ⊆ y)
  refl x := by simp
  sub x y h := by simp only [decide_eq_true_iff] at h; exact h

end Tolerance

-- Distributivity Operators

/--
Maximal distributive: ⟦each P⟧(x) = ∀a ∈ x. P(a)

This is the semantics of English "each", German "jeder".
-/
def distMaximal (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Bool :=
  decide (∀ a ∈ x, P a w = true)

/--
Tolerant distributive: ⟦each* P⟧^⪯(x) = ∃z. z ⪯ x ∧ ∀a ∈ z. P(a)

This is the semantics of German "jeweils" (for non-max speakers).
-/
def distTolerant (P : Atom → W → Bool) (tol : Tolerance Atom)
    (x : Finset Atom) (w : W) : Bool :=
  decide (∃ z ∈ x.powerset, tol.rel z x = true ∧ ∀ a ∈ z, P a w = true)

-- Key Theorems

/-- Maximal distributive = tolerant distributive with identity tolerance -/
theorem distMaximal_eq_identity (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    distMaximal P x w = distTolerant P Tolerance.identity x w := by
  simp only [distMaximal, distTolerant, Tolerance.identity, decide_eq_decide]
  constructor
  · intro h
    exact ⟨x, Finset.mem_powerset.mpr (Finset.Subset.refl x), beq_self_eq_true x, h⟩
  · intro ⟨z, _, hz_eq, hz_all⟩
    simp only [beq_iff_eq] at hz_eq
    exact hz_eq ▸ hz_all

omit [DecidableEq Atom] in
/-- Maximal distributive forces all atoms to satisfy P -/
theorem distMaximal_forces_all (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    distMaximal P x w = true → ∀ a ∈ x, P a w = true := by
  simp only [distMaximal, decide_eq_true_iff]
  exact id

/-- Tolerant distributive with full tolerance allows exceptions -/
theorem distTolerant_allows_exceptions (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) (a : Atom) (ha : a ∈ x) (hPa : P a w = true) :
    distTolerant P Tolerance.full x w = true := by
  simp only [distTolerant, decide_eq_true_iff]
  refine ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha), ?_, ?_⟩
  · simp only [Tolerance.full, Finset.singleton_subset_iff, decide_eq_true_iff]; exact ha
  · simp [hPa]

-- Križ & @cite{kriz-spector-2021}: Full Formalization

/-!
## The Križ & @cite{kriz-spector-2021} Account
@cite{kriz-spector-2021}

The K&S theory explains both homogeneity and non-maximality through:

1. Candidate interpretations: For "the Xs are P", generate propositions
   {∀a∈z. P(a) | z ⊆ X} for all sub-pluralities z.

2. Trivalent semantics:
   - TRUE at w: all candidates true at w
   - FALSE at w: all candidates false at w
   - GAP: some true, some false

3. Homogeneity: The gap is symmetric under negation. This explains why
   "the Xs are P" (quasi-universal) and "the Xs aren't P" (quasi-existential)
   have the same undefined region.

4. Non-maximality: QUD-based relevance filtering reduces the candidate set,
   allowing sentences to be judged true even when not all candidates hold.
-/

section KrizSpector

variable {Atom W : Type*} [DecidableEq Atom]

-- Part 1: Basic Predicates on Pluralities

/-- All atoms in x satisfy P at w -/
def allSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Bool :=
  decide (∀ a ∈ x, P a w = true)

/-- Some atom in x satisfies P at w -/
def someSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Bool :=
  decide (∃ a ∈ x, P a w = true)

/-- No atom in x satisfies P at w -/
def noneSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Bool :=
  decide (∀ a ∈ x, P a w = false)

-- Part 2: Trivalent Truth Values (Core.Duality.Truth3)

open Core.Duality (Truth3)
open Semantics.Supervaluation (SpecSpace superTrue)

/--
The trivalent truth value for plural predication "the Xs are P".

- TRUE: all atoms satisfy P
- FALSE: no atoms satisfy P
- GAP: some but not all satisfy P

This is the core of @cite{kriz-spector-2021} Section 2, instantiated
as a supervaluation over the atoms of the plurality: each atom is a
"specification point", and predication is super-true iff the predicate
holds at all of them.
-/
def pluralTruthValue (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Truth3 :=
  if h : x.Nonempty then
    superTrue (fun a => P a w) ⟨x, h⟩
  else .true  -- empty plurality: vacuously true

/-- pluralTruthValue is .true iff allSatisfy holds -/
@[simp]
theorem pluralTruthValue_eq_true_iff (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .true ↔ allSatisfy P x w = true := by
  unfold pluralTruthValue superTrue allSatisfy
  simp only [decide_eq_true_eq]
  split_ifs <;> simp_all

/-- pluralTruthValue is .false iff noneSatisfy holds (and not allSatisfy) -/
@[simp]
theorem pluralTruthValue_eq_false_iff (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .false ↔ allSatisfy P x w = false ∧ noneSatisfy P x w = true := by
  unfold pluralTruthValue superTrue allSatisfy noneSatisfy
  simp only [decide_eq_true_eq]
  split_ifs <;> simp_all

/-- pluralTruthValue is .gap iff neither all nor none satisfy -/
@[simp]
theorem pluralTruthValue_eq_gap_iff (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .gap ↔ allSatisfy P x w = false ∧ noneSatisfy P x w = false := by
  unfold pluralTruthValue superTrue allSatisfy noneSatisfy
  simp only [decide_eq_true_eq]
  split_ifs <;> simp_all

/-- If all satisfy P, then none satisfy ¬P -/
theorem allSatisfy_imp_noneSatisfy_neg (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    allSatisfy P x w = true → noneSatisfy (λ a w => !P a w) x w = true := by
  simp only [allSatisfy, noneSatisfy, decide_eq_true_eq, Bool.not_eq_false']
  intro h a ha
  exact h a ha

/-- If none satisfy P, then all satisfy ¬P -/
theorem noneSatisfy_imp_allSatisfy_neg (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    noneSatisfy P x w = true → allSatisfy (λ a w => !P a w) x w = true := by
  simp only [allSatisfy, noneSatisfy, decide_eq_true_eq, Bool.not_eq_true']
  intro h a ha
  exact h a ha

/-- If not all satisfy ¬P, then not none satisfy P -/
theorem not_allSatisfy_neg_imp_not_noneSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    allSatisfy (λ a w => !P a w) x w = false → noneSatisfy P x w = false := by
  intro h
  unfold allSatisfy at h
  unfold noneSatisfy
  simp only [decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true'] at h
  push_neg at h
  simp only [decide_eq_false_iff_not, decide_eq_true_eq]
  push_neg
  obtain ⟨a, ha, hPa⟩ := h
  refine ⟨a, ha, ?_⟩
  -- hPa : !(P a w) ≠ true means !(P a w) = false means P a w = true
  cases hP : P a w <;> simp_all

/-- If not none satisfy ¬P, then not all satisfy P -/
theorem not_noneSatisfy_neg_imp_not_allSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    noneSatisfy (λ a w => !P a w) x w = false → allSatisfy P x w = false := by
  intro h
  unfold noneSatisfy at h
  unfold allSatisfy
  simp only [decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_false'] at h
  push_neg at h
  simp only [decide_eq_false_iff_not, decide_eq_true_eq]
  push_neg
  obtain ⟨a, ha, hPa⟩ := h
  refine ⟨a, ha, ?_⟩
  -- hPa : !(P a w) ≠ false means !(P a w) = true means P a w = false
  cases hP : P a w <;> simp_all

-- Part 3: The Homogeneity Theorem

/-- The gap condition: some but not all atoms satisfy P -/
def inGap (P : Atom → W → Bool) (x : Finset Atom) (w : W) : Prop :=
  (∃ a ∈ x, P a w = true) ∧ (∃ a ∈ x, P a w = false)

/--
Homogeneity Theorem (Križ & @cite{kriz-spector-2021}, Section 2.1).

The gap is symmetric under negation: a world is in the gap for P
iff it's in the gap for ¬P.

This explains why:
- "The Xs are P" is undefined when some but not all Xs are P
- "The Xs aren't P" is ALSO undefined in exactly those worlds

Proof: The gap for P is {∃a.P(a) ∧ ∃a.¬P(a)}.
       The gap for ¬P is {∃a.¬P(a) ∧ ∃a.¬¬P(a)} = {∃a.¬P(a) ∧ ∃a.P(a)}.
       These are identical.
-/
theorem homogeneity_gap_symmetric (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    inGap P x w ↔ inGap (λ a w => !P a w) x w := by
  simp only [inGap, Bool.not_eq_true', Bool.not_eq_false']
  constructor <;> (intro ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩; exact ⟨⟨b, hb, hPb⟩, ⟨a, ha, hPa⟩⟩)

/--
Corollary: pluralTruthValue is gap iff negated version is gap.
-/
theorem pluralTruthValue_gap_iff_neg_gap (P : Atom → W → Bool) (x : Finset Atom) (w : W)
    (_hne : x.Nonempty) :
    pluralTruthValue P x w = .gap ↔ pluralTruthValue (λ a w => !P a w) x w = .gap := by
  rw [pluralTruthValue_eq_gap_iff, pluralTruthValue_eq_gap_iff]
  simp only [allSatisfy, noneSatisfy, decide_eq_false_iff_not,
             Bool.not_eq_true', Bool.not_eq_false']
  exact And.comm

/--
Homogeneity Polarity Theorem: Truth and falsity swap under negation.

If "the Xs are P" is TRUE, then "the Xs are ¬P" is FALSE, and vice versa.

Note: Requires x to be nonempty. For empty x, both `allSatisfy P` and `allSatisfy ¬P`
are vacuously true, so the theorem doesn't hold.
-/
theorem pluralTruthValue_neg (P : Atom → W → Bool) (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    pluralTruthValue (λ a w => !P a w) x w =
    match pluralTruthValue P x w with
    | .true => .false
    | .false => .true
    | .indet => .indet := by
  cases h : pluralTruthValue P x w
  -- Case .true → .false: allSatisfy P ⇒ noneSatisfy ¬P, not allSatisfy ¬P
  · rw [pluralTruthValue_eq_true_iff] at h
    rw [pluralTruthValue_eq_false_iff]
    refine ⟨?_, allSatisfy_imp_noneSatisfy_neg P x w h⟩
    simp only [allSatisfy, decide_eq_true_eq, Bool.not_eq_true'] at h
    simp only [allSatisfy, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
               not_forall, exists_prop]
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, by simp [h a ha]⟩
  -- Case .false → .true: noneSatisfy P ⇒ allSatisfy ¬P
  · rw [pluralTruthValue_eq_false_iff] at h
    rw [pluralTruthValue_eq_true_iff]
    exact noneSatisfy_imp_allSatisfy_neg P x w h.2
  -- Case .gap → .gap: witnesses on both sides
  · rw [pluralTruthValue_eq_gap_iff] at h
    rw [pluralTruthValue_eq_gap_iff]
    obtain ⟨hNotAll, hNotNone⟩ := h
    simp only [allSatisfy, decide_eq_false_iff_not, decide_eq_true_eq] at hNotAll
    push_neg at hNotAll
    obtain ⟨a, ha, hPa⟩ := hNotAll
    simp only [noneSatisfy, decide_eq_false_iff_not, decide_eq_true_eq] at hNotNone
    push_neg at hNotNone
    obtain ⟨b, hb, hPb⟩ := hNotNone
    exact ⟨by simp only [allSatisfy, decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true',
                          not_forall, exists_prop]; exact ⟨b, hb, by simp [hPb]⟩,
           by simp only [noneSatisfy, decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_false',
                          not_forall, exists_prop]; exact ⟨a, ha, by simp [hPa]⟩⟩

end KrizSpector

-- The Independence Result

/-- Classification by [±distributive] × [±maximal] -/
inductive DistMaxClass where
  | distMax       -- each, jeder: +dist, +max
  | distNonMax    -- jeweils: +dist, -max
  | nonDistMax    -- all: -dist, +max
  | nonDistNonMax -- the Xs: -dist, -max
  deriving DecidableEq, Repr

/-- All four classes are instantiated by the formal operators -/
def classifyOperator (forcesDistributivity : Bool) (usesTolerance : Bool)
    : DistMaxClass :=
  match forcesDistributivity, usesTolerance with
  | true, false => .distMax
  | true, true => .distNonMax
  | false, false => .nonDistMax
  | false, true => .nonDistNonMax

end Semantics.Lexical.Plural.Distributivity
