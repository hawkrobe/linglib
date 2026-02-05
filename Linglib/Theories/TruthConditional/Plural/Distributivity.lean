/-
# Plural Distributivity and Non-Maximality

Formalizes the independence of distributivity and maximality,
following Križ & Spector (2021) and Haslinger et al. (2025).

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

## References

- Križ & Spector (2021). Interpreting plural predication. L&P.
- Haslinger, Rosina, Schmitt & Wurm (2025). On the relation between
  distributivity and maximality. S&P 18.
- Link (1983). The logical analysis of plurals and mass terms.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Linglib.Theories.Core.QUD

namespace TruthConditional.Plural.Distributivity

variable {Atom W : Type*} [DecidableEq Atom]

-- Tolerance Relations (Križ & Spector 2021, Definition 14)

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

-- Križ & Spector (2021): Full Formalization

/-!
## The Križ & Spector (2021) Account

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

-- Part 2: Trivalent Truth Values

/-- Trivalent truth value for homogeneous predicates -/
inductive TruthValue where
  | true   -- All candidates true
  | false  -- All candidates false
  | gap    -- Some true, some false (undefined)
  deriving DecidableEq, Repr

/--
The trivalent truth value for plural predication "the Xs are P".

- TRUE: all atoms satisfy P
- FALSE: no atoms satisfy P
- GAP: some but not all satisfy P

This is the core of K&S (2021) Section 2.
-/
def pluralTruthValue (P : Atom → W → Bool) (x : Finset Atom) (w : W) : TruthValue :=
  if allSatisfy P x w then .true
  else if noneSatisfy P x w then .false
  else .gap

/-- pluralTruthValue is .true iff allSatisfy holds -/
@[simp]
theorem pluralTruthValue_eq_true_iff (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .true ↔ allSatisfy P x w = true := by
  simp only [pluralTruthValue]
  split_ifs with h <;> simp_all

/-- pluralTruthValue is .false iff noneSatisfy holds (and not allSatisfy) -/
@[simp]
theorem pluralTruthValue_eq_false_iff (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .false ↔ allSatisfy P x w = false ∧ noneSatisfy P x w = true := by
  simp only [pluralTruthValue]
  split_ifs with h1 h2 <;> simp_all

/-- pluralTruthValue is .gap iff neither all nor none satisfy -/
@[simp]
theorem pluralTruthValue_eq_gap_iff (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .gap ↔ allSatisfy P x w = false ∧ noneSatisfy P x w = false := by
  simp only [pluralTruthValue]
  split_ifs with h1 h2 <;> simp_all

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
Homogeneity Theorem (Križ & Spector 2021, Section 2.1).

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
  unfold pluralTruthValue allSatisfy noneSatisfy
  simp only [decide_eq_true_eq, Bool.not_eq_true', Bool.not_eq_false', Bool.not_not]
  constructor <;> (intro h; split_ifs at h ⊢ <;> first | rfl | contradiction | omega)

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
    | .gap => .gap := by
  -- Case split on the value of pluralTruthValue P x w
  cases h : pluralTruthValue P x w
  -- Case .true: allSatisfy P holds, so noneSatisfy ¬P holds, giving .false
  · rw [pluralTruthValue_eq_true_iff] at h
    have hNone := allSatisfy_imp_noneSatisfy_neg P x w h
    -- Need to show allSatisfy ¬P = false
    have hNotAll : allSatisfy (λ a w => !P a w) x w = false := by
      simp only [allSatisfy, decide_eq_true_eq, Bool.not_eq_true'] at h
      simp only [allSatisfy, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
                 not_forall, exists_prop]
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, by simp [h a ha]⟩
    simp only [pluralTruthValue, hNotAll, Bool.false_eq_true, ↓reduceIte, hNone, ite_false]
  -- Case .false: noneSatisfy P holds, so allSatisfy ¬P holds, giving .true
  · rw [pluralTruthValue_eq_false_iff] at h
    have hAll := noneSatisfy_imp_allSatisfy_neg P x w h.2
    simp only [pluralTruthValue, hAll, ↓reduceIte]
  -- Case .gap: neither all nor none, so gap for ¬P too
  · rw [pluralTruthValue_eq_gap_iff] at h
    obtain ⟨hNotAll, hNotNone⟩ := h
    -- From hNotAll (allSatisfy P = false), get witness where P is false
    simp only [allSatisfy, decide_eq_false_iff_not, decide_eq_true_eq] at hNotAll
    push_neg at hNotAll
    obtain ⟨a, ha, hPa⟩ := hNotAll
    -- From hNotNone (noneSatisfy P = false), get witness where P is true
    simp only [noneSatisfy, decide_eq_false_iff_not, decide_eq_true_eq] at hNotNone
    push_neg at hNotNone
    obtain ⟨b, hb, hPb⟩ := hNotNone
    -- Now show allSatisfy ¬P = false and noneSatisfy ¬P = false
    have h1 : allSatisfy (λ a w => !P a w) x w = false := by
      simp only [allSatisfy, decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_true',
                 not_forall, exists_prop]
      exact ⟨b, hb, by simp [hPb]⟩
    have h2 : noneSatisfy (λ a w => !P a w) x w = false := by
      simp only [noneSatisfy, decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_false',
                 not_forall, exists_prop]
      exact ⟨a, ha, by simp [hPa]⟩
    simp only [pluralTruthValue, h1, h2, Bool.false_eq_true, ↓reduceIte, ite_false]

-- Part 4: Candidate Interpretations

/-- Decidable proposition type -/
abbrev BProp (W : Type*) := W → Bool

/--
The candidate proposition for sub-plurality z: "P holds of all atoms in z".
-/
def candidateProp (P : Atom → W → Bool) (z : Finset Atom) : BProp W :=
  λ w => decide (∀ a ∈ z, P a w = true)

/--
Full candidate set: all sub-plurality propositions.

This is the set S from K&S (2021) before relevance filtering.
-/
def fullCandidateSet (P : Atom → W → Bool) (x : Finset Atom) : Set (BProp W) :=
  { candidateProp P z | z ∈ x.powerset }

/--
Candidate set parameterized by tolerance.

With identity tolerance: only the maximal candidate.
With full tolerance: all sub-plurality candidates.
-/
def candidateSet (P : Atom → W → Bool) (tol : Tolerance Atom)
    (x : Finset Atom) : Set (BProp W) :=
  { p | ∃ z ∈ x.powerset, tol.rel z x = true ∧ p = candidateProp P z }

-- Part 5: Truth on All Readings

/-- All candidates in the set are true at w -/
def trueOnAll (candidates : Set (BProp W)) (w : W) : Prop :=
  ∀ p ∈ candidates, p w = true

/-- All candidates in the set are false at w -/
def falseOnAll (candidates : Set (BProp W)) (w : W) : Prop :=
  ∀ p ∈ candidates, p w = false

/-- Some candidates true, some false (the gap) -/
def gapOnCandidates (candidates : Set (BProp W)) (w : W) : Prop :=
  (∃ p ∈ candidates, p w = true) ∧ (∃ p ∈ candidates, p w = false)

-- Part 6: Key Correspondence Theorems

/--
Theorem: The maximal candidate is exactly distMaximal.
-/
theorem candidateProp_x_eq_distMaximal (P : Atom → W → Bool) (x : Finset Atom) :
    candidateProp P x = distMaximal P x := by
  rfl

/--
Theorem: With identity tolerance, the candidate set is a singleton
containing only the maximal candidate.
-/
theorem identity_candidateSet_eq_singleton (P : Atom → W → Bool) (x : Finset Atom) :
    candidateSet P Tolerance.identity x = {candidateProp P x} := by
  ext p
  simp only [candidateSet, Set.mem_setOf_eq, Set.mem_singleton_iff,
             Finset.mem_powerset, Tolerance.identity, beq_iff_eq]
  constructor
  · intro ⟨z, _, hz_eq, hp⟩
    rw [← hz_eq, hp]
  · intro hp
    exact ⟨x, Finset.Subset.refl x, rfl, hp⟩

/--
Theorem: With full tolerance, the candidate set is exactly fullCandidateSet.
-/
theorem full_candidateSet_eq_full (P : Atom → W → Bool) (x : Finset Atom) :
    candidateSet P Tolerance.full x = fullCandidateSet P x := by
  ext p
  simp only [candidateSet, fullCandidateSet, Set.mem_setOf_eq, Finset.mem_powerset,
             Tolerance.full, decide_eq_true_iff]
  constructor
  · intro ⟨z, hz_mem, _, hp⟩
    exact ⟨z, hz_mem, hp.symm⟩
  · intro ⟨z, hz_mem, hp⟩
    exact ⟨z, hz_mem, hz_mem, hp.symm⟩

/--
Theorem: trueOnAll for the full candidate set iff all atoms satisfy P.

This connects the candidate framework to the simple universal condition.
-/
theorem trueOnAll_full_iff_allSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    trueOnAll (fullCandidateSet P x) w ↔ allSatisfy P x w = true := by
  constructor
  · -- (→): If all candidates true, then all atoms satisfy P
    intro h
    simp only [allSatisfy, decide_eq_true_eq]
    intro a ha
    -- The singleton {a} is in fullCandidateSet
    have hsing : candidateProp P {a} ∈ fullCandidateSet P x := by
      simp only [fullCandidateSet, Set.mem_setOf_eq, Finset.mem_powerset]
      exact ⟨{a}, Finset.singleton_subset_iff.mpr ha, rfl⟩
    have := h (candidateProp P {a}) hsing
    simp only [candidateProp, decide_eq_true_eq, Finset.mem_singleton, forall_eq] at this
    exact this
  · -- (←): If all atoms satisfy P, then all candidates are true
    intro h p hp
    simp only [fullCandidateSet, Set.mem_setOf_eq, Finset.mem_powerset] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    simp only [candidateProp, decide_eq_true_eq]
    intro a ha
    simp only [allSatisfy, decide_eq_true_eq] at h
    exact h a (hz ha)

/--
Theorem: falseOnAll for full candidates iff no atom satisfies P.

Known issue: This theorem is currently unprovable because `fullCandidateSet`
includes the empty sub-plurality `∅`, and `candidateProp P ∅ w = true` vacuously
for all w. Therefore `falseOnAll (fullCandidateSet P x) w` is always `False`.

TODO: Fix `fullCandidateSet` to exclude empty sub-pluralities (which have no
linguistic interpretation). Then the proof follows by:
- (→): Singleton candidates {a} false → each P(a) fails.
- (←): No P(a) holds → for any nonempty z ⊆ x, some atom in z fails P.
-/
theorem falseOnAll_full_iff_noneSatisfy (P : Atom → W → Bool) (x : Finset Atom) (w : W)
    (hne : x.Nonempty) :
    falseOnAll (fullCandidateSet P x) w ↔ noneSatisfy P x w = true := by
  sorry

/--
Main Theorem: The trivalent semantics matches the candidate interpretation framework.

pluralTruthValue P x w equals:
- .true iff trueOnAll (fullCandidateSet P x) w
- .false iff falseOnAll (fullCandidateSet P x) w
- .gap iff gapOnCandidates (fullCandidateSet P x) w

This is the central correspondence theorem of K&S (2021), showing that the
simple trivalent semantics (based on all/some/none) coincides with the more
sophisticated "truth on all readings" approach.

Known issue: The `.false` and `.gap` cases are blocked by the same empty
candidate issue as `falseOnAll_full_iff_noneSatisfy`: `fullCandidateSet` includes
`candidateProp P ∅` which is vacuously true, so `falseOnAll` is always `False`
and `gapOnCandidates` is trivially satisfied on the true-witness side.

TODO: Fix `fullCandidateSet` to exclude empty sub-pluralities, then prove:
- TRUE: via `trueOnAll_full_iff_allSatisfy` + `pluralTruthValue_eq_true_iff`
- FALSE: via corrected `falseOnAll_full_iff_noneSatisfy` + `pluralTruthValue_eq_false_iff`
- GAP: singleton witnesses for both true and false candidates
-/
theorem pluralTruthValue_eq_candidateSemantics (P : Atom → W → Bool) (x : Finset Atom) (w : W)
    (hne : x.Nonempty) :
    (pluralTruthValue P x w = .true ↔ trueOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .false ↔ falseOnAll (fullCandidateSet P x) w) ∧
    (pluralTruthValue P x w = .gap ↔ gapOnCandidates (fullCandidateSet P x) w) := by
  sorry

end KrizSpector

-- Strong Relevance and QUD Filtering

section StrongRelevance

variable [Fintype W] [DecidableEq W]

/--
Strong relevance: a proposition aligns with a QUD's partition.

A proposition p is strongly relevant to QUD q iff p respects the partition:
if two worlds are q-equivalent, then p has the same truth value at both.

This is the key filtering mechanism from K&S (2021) Section 3.
-/
def isStronglyRelevantProp (q : QUD W) (p : BProp W) : Prop :=
  ∀ w1 w2 : W, q.sameAnswer w1 w2 = true → p w1 = p w2

/-- Decidable version -/
noncomputable def isStronglyRelevant (q : QUD W) (p : BProp W) : Bool :=
  (Fintype.elems : Finset W).toList.all λ w1 =>
    (Fintype.elems : Finset W).toList.all λ w2 =>
      !q.sameAnswer w1 w2 || (p w1 == p w2)

/-- Filter candidate set to strongly relevant propositions -/
def stronglyRelevantSet (q : QUD W) (candidates : Set (BProp W)) : Set (BProp W) :=
  { p ∈ candidates | isStronglyRelevantProp q p }

/--
Theorem: With exact QUD, all propositions are strongly relevant.

The exact QUD distinguishes all worlds, so every proposition trivially
respects the partition.
-/
theorem exact_all_relevant [LawfulBEq W] (p : BProp W) :
    isStronglyRelevantProp (QUD.exact (M := W)) p := by
  intro w1 w2 h
  simp only [QUD.exact, beq_iff_eq] at h
  exact congrArg p h

/--
Corollary: With exact QUD, the filtered set equals the original set.
-/
theorem exact_stronglyRelevantSet_eq [LawfulBEq W] (candidates : Set (BProp W)) :
    stronglyRelevantSet (QUD.exact (M := W)) candidates = candidates := by
  ext p
  simp only [stronglyRelevantSet, Set.mem_sep_iff]
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, exact_all_relevant p⟩

/--
Theorem: With trivial QUD, only constant propositions are strongly relevant.
-/
theorem trivial_relevant_iff_constant (p : BProp W) :
    isStronglyRelevantProp (QUD.trivial (M := W)) p ↔ (∀ w1 w2 : W, p w1 = p w2) := by
  simp only [isStronglyRelevantProp, QUD.trivial]
  constructor
  · intro h w1 w2; exact h w1 w2 trivial
  · intro h _ _ _; exact h _ _

/--
Non-Maximality Theorem: With a coarse QUD that groups "all P" with "almost all P",
the maximal candidate may not be strongly relevant, allowing non-maximal readings.

This is the formal content of K&S (2021) Section 3's relevance filtering.

Proof idea:
- If q groups w_all (where all satisfy P) with w_almost (where not all satisfy),
  then candidateProp P x has different values at these QUD-equivalent worlds.
- But strong relevance requires same values at QUD-equivalent worlds.
- Contradiction.

The proof is by contradiction: strong relevance + QUD equivalence forces the
maximal candidate to agree on w_all and w_almost, but allSatisfy gives
different values.
-/
theorem nonMaximality_from_coarse_qud (P : Atom → W → Bool) (x : Finset Atom)
    (q : QUD W) (w_all w_almost : W)
    (h_equiv : q.sameAnswer w_all w_almost = true)
    (h_all : allSatisfy P x w_all = true)
    (h_not_all : allSatisfy P x w_almost = false) :
    ¬isStronglyRelevantProp q (candidateProp P x) := by
  intro hsr
  have heq := hsr w_all w_almost h_equiv
  -- candidateProp P x w = allSatisfy P x w (definitionally)
  change allSatisfy P x w_all = allSatisfy P x w_almost at heq
  rw [h_all, h_not_all] at heq
  exact absurd heq (by decide)

end StrongRelevance

-- Correspondence Theorems

section Correspondence

variable [Fintype W] [DecidableEq W]

/--
With identity tolerance, the only tolerant sub-plurality is x itself.

This is because z ⪯ x under identity tolerance iff z = x.
-/
theorem identity_tolerant_iff_eq (x z : Finset Atom) :
    Tolerance.identity.rel z x = true ↔ z = x := by
  simp only [Tolerance.identity, beq_iff_eq]

/--
Identity tolerance candidate set contains exactly the maximal proposition.

NOTE: This is a variant of identity_candidateSet_eq_singleton,
stating it in terms of the explicit proposition form.
-/
theorem identity_candidateSet_singleton' (P : Atom → W → Bool) (x : Finset Atom) :
    candidateSet P Tolerance.identity x =
    {λ w => decide (∀ a ∈ x, P a w = true)} := by
  -- This follows from identity_candidateSet_eq_singleton + candidateProp definition
  rw [identity_candidateSet_eq_singleton]
  rfl

/--
Strong relevance (propositional version): respects QUD partition.
-/
theorem stronglyRelevant_iff (q : QUD W) (p : BProp W) :
    isStronglyRelevantProp q p ↔ ∀ w1 w2, q.sameAnswer w1 w2 = true → p w1 = p w2 := by
  rfl

/--
With exact QUD, all propositions are strongly relevant.

The exact QUD distinguishes all worlds, so every proposition aligns with it.
-/
theorem exact_all_stronglyRelevant [LawfulBEq W] (p : BProp W) :
    isStronglyRelevantProp (QUD.exact (M := W)) p := by
  intro w1 w2 h
  simp only [QUD.exact, beq_iff_eq] at h
  exact congrArg p h

/--
With trivial QUD, only constant propositions are strongly relevant.

The trivial QUD groups all worlds together, so a proposition is relevant
iff it has the same value at all worlds.
-/
theorem trivial_stronglyRelevant_iff (p : BProp W) :
    isStronglyRelevantProp (QUD.trivial (M := W)) p ↔ (∀ w1 w2 : W, p w1 = p w2) := by
  simp only [isStronglyRelevantProp, QUD.trivial]
  constructor
  · intro h w1 w2
    exact h w1 w2 trivial
  · intro h _ _ _
    exact h _ _

/--
Key Theorem: The maximal proposition is always strongly relevant to exact QUD.

This shows the connection between `distMaximal` and the truth-on-all-readings
approach: under the exact QUD, the maximal candidate is always relevant.
-/
theorem maximal_relevant_to_exact [LawfulBEq W] (P : Atom → W → Bool) (x : Finset Atom) :
    isStronglyRelevantProp (QUD.exact (M := W))
      (λ w => decide (∀ a ∈ x, P a w = true)) :=
  exact_all_stronglyRelevant _

/--
Correspondence Theorem: distMaximal characterizes truth on the maximal candidate.

The algebraic operator `distMaximal` equals the truth value of the unique candidate
generated by identity tolerance. This connects the operator-based approach
to the pragmatic truth-on-all-readings approach of Križ & Spector (2021).
-/
theorem distMaximal_eq_maximal_candidate (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    distMaximal P x w = (λ w => decide (∀ a ∈ x, P a w = true)) w := by
  rfl

/--
Correspondence Theorem: distTolerant with full tolerance is always true.

With full tolerance, any sub-plurality (including the empty set) is tolerant,
so distTolerant is true as long as x is in the powerset of itself (always true).
The empty set vacuously satisfies the predicate.
-/
theorem distTolerant_full_always_true (P : Atom → W → Bool) (x : Finset Atom) (w : W) :
    distTolerant P Tolerance.full x w = true := by
  simp only [distTolerant, Tolerance.full, decide_eq_true_iff]
  refine ⟨∅, Finset.empty_mem_powerset x, ?_, ?_⟩
  · simp only [Finset.empty_subset, decide_true]
  · intro a ha; simp at ha

/--
Correspondence Theorem: distTolerant unfolds to existence of tolerant witness.

This connects the operator to the candidate interpretation framework.
-/
theorem distTolerant_iff_exists_tolerant (P : Atom → W → Bool) (tol : Tolerance Atom)
    (x : Finset Atom) (w : W) :
    distTolerant P tol x w = true ↔
    ∃ z ∈ x.powerset, tol.rel z x = true ∧ (∀ a ∈ z, P a w = true) := by
  simp only [distTolerant, decide_eq_true_iff]

end Correspondence

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

end TruthConditional.Plural.Distributivity
