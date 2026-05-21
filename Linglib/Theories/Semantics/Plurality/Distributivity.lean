import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Linglib.Theories.Semantics.Questions.Partition.QUD
import Linglib.Theories.Semantics.Questions.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Core.Logic.Truth3
import Linglib.Core.Logic.Duality

/-!
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

namespace Semantics.Plurality.Distributivity

variable {Atom W : Type*} [DecidableEq Atom]

-- Tolerance Relations (Križ & @cite{kriz-spector-2021}, the tolerance-on-
-- plural-info-states relation introduced in their non-maximality section)

/--
A tolerance relation determines which sub-pluralities count as
"similar enough" to the whole for current conversational purposes.

Formally: ⪯ is reflexive and respects mereological structure.
-/
structure Tolerance (Atom : Type*) [DecidableEq Atom] where
  /-- y ⪯ x: y is similar enough to x -/
  rel : Finset Atom → Finset Atom → Prop
  /-- Decidability of the tolerance relation. -/
  decRel : ∀ x y, Decidable (rel x y)
  /-- Reflexivity -/
  refl : ∀ x, rel x x
  /-- Tolerance implies part-of -/
  sub : ∀ x y, rel x y → x ⊆ y

/-- Per-`Tolerance` decidability instance for the relation. -/
instance Tolerance.instDecidableRel {Atom : Type*} [DecidableEq Atom]
    (tol : Tolerance Atom) (x y : Finset Atom) : Decidable (tol.rel x y) :=
  tol.decRel x y

namespace Tolerance

/-- Identity: only x ⪯ x (forces maximal reading) -/
def identity : Tolerance Atom where
  rel x y := x = y
  decRel x y := decEq x y
  refl _ := rfl
  sub x y h := h ▸ Finset.Subset.refl x

/-- Trivial: any part is tolerated (allows existential reading).
    @cite{kriz-spector-2021} call this the *trivial* tolerance — the
    relation is just sub-pluralityhood, with no further restriction. -/
def trivial : Tolerance Atom where
  rel x y := x ⊆ y
  decRel x y := Finset.decidableDforallFinset
  refl _ := Finset.Subset.refl _
  sub _ _ h := h

end Tolerance

-- Distributivity Operators

/--
Maximal distributive: ⟦each P⟧(x) = ∀a ∈ x. P(a)

This is the semantics of English "each", German "jeder".
-/
def distMaximal (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ x, P a w

instance distMaximal.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (distMaximal P x w) := by unfold distMaximal; infer_instance

/--
Tolerant distributive: ⟦each* P⟧^⪯(x) = ∃z. z ⪯ x ∧ z ≠ ∅ ∧ ∀a ∈ z. P(a)

This is the semantics of German "jeweils" (for non-max speakers).
The nonemptiness constraint prevents the empty set from vacuously
witnessing truth (∀a ∈ ∅, P a w is trivially true).
-/
def distTolerant (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (tol : Tolerance Atom) (x : Finset Atom) (w : W) : Prop :=
  ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x ∧ ∀ a ∈ z, P a w

instance distTolerant.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (tol : Tolerance Atom)
    (x : Finset Atom) (w : W) :
    Decidable (distTolerant P tol x w) := by unfold distTolerant; infer_instance

-- Key Theorems

/-- Maximal distributive ↔ tolerant distributive with identity tolerance
    (on nonempty pluralities). -/
theorem distMaximal_iff_identity (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W)
    (hne : x.Nonempty) :
    distMaximal P x w ↔ distTolerant P Tolerance.identity x w := by
  unfold distMaximal distTolerant
  refine ⟨fun h => ?_, fun ⟨z, _, _, hz_eq, hz_all⟩ => ?_⟩
  · exact ⟨x, Finset.mem_powerset.mpr (Finset.Subset.refl x), hne,
      show (x : Finset Atom) = x from rfl, h⟩
  · simp only [Tolerance.identity] at hz_eq
    exact hz_eq ▸ hz_all

/-- Maximal distributive forces all atoms to satisfy P -/
theorem distMaximal_forces_all (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) :
    distMaximal P x w → ∀ a ∈ x, P a w := id

/-- Tolerant distributive with trivial tolerance allows exceptions -/
theorem distTolerant_allows_exceptions (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) (a : Atom) (ha : a ∈ x) (hPa : P a w) :
    distTolerant P Tolerance.trivial x w := by
  refine ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
          ⟨a, Finset.mem_singleton.mpr rfl⟩, ?_, ?_⟩
  · exact Finset.singleton_subset_iff.mpr ha
  · intro b hb; rw [Finset.mem_singleton.mp hb]; exact hPa

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
def allSatisfy (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ x, P a w

instance allSatisfy.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (allSatisfy P x w) := by unfold allSatisfy; infer_instance

/-- Some atom in x satisfies P at w -/
def someSatisfy (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∃ a ∈ x, P a w

instance someSatisfy.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (someSatisfy P x w) := by unfold someSatisfy; infer_instance

/-- No atom in x satisfies P at w -/
def noneSatisfy (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  ∀ a ∈ x, ¬ P a w

instance noneSatisfy.instDecidable (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (noneSatisfy P x w) := by unfold noneSatisfy; infer_instance

-- Part 2: Trivalent Truth Values (Core.Duality.Truth3)

open Core.Duality (Truth3)

/--
The trivalent truth value for plural predication "the Xs are P".

- TRUE: all atoms satisfy P (vacuously on `∅`)
- FALSE: nonempty plurality with no atoms satisfying P
- GAP: witnesses on both sides

This is the core of @cite{kriz-spector-2021} Section 2: predication
on a plurality is super-true iff the predicate holds at every atom,
super-false iff it fails at every atom, gap otherwise. The
@cite{van-fraassen-1966} supervaluation framing (each atom as a
"specification point", per `Semantics.Supervaluation.superTrue`) is
documented by `Semantics.Supervaluation.superTrue_eq_dist`. -/
@[reducible] def pluralTruthValue (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) : Truth3 :=
  Core.Duality.dist x (fun a => P a w)

/-- pluralTruthValue is .true iff allSatisfy holds -/
@[simp]
theorem pluralTruthValue_eq_true_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .true ↔ allSatisfy P x w :=
  Core.Duality.dist_eq_true_iff x _

/-- pluralTruthValue is .false iff noneSatisfy holds (and x is nonempty) -/
@[simp]
theorem pluralTruthValue_eq_false_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .false ↔ x.Nonempty ∧ noneSatisfy P x w :=
  Core.Duality.dist_eq_false_iff x _

/-- pluralTruthValue is .indet iff witnesses on both sides exist -/
@[simp]
theorem pluralTruthValue_eq_gap_iff (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    pluralTruthValue P x w = .indet ↔
    (∃ a ∈ x, P a w) ∧ (∃ a ∈ x, ¬ P a w) :=
  Core.Duality.dist_eq_indet_iff x _

/-- If all satisfy P, then none satisfy ¬P -/
theorem allSatisfy_imp_noneSatisfy_neg (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allSatisfy P x w → noneSatisfy (fun a w => ¬ P a w) x w := by
  intro h a ha hPa; exact hPa (h a ha)

/-- If none satisfy P, then all satisfy ¬P -/
theorem noneSatisfy_imp_allSatisfy_neg (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    noneSatisfy P x w → allSatisfy (fun a w => ¬ P a w) x w := id

-- Part 3: The Homogeneity Theorem

/-- The gap condition: some but not all atoms satisfy P -/
def inGap (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  (∃ a ∈ x, P a w) ∧ (∃ a ∈ x, ¬ P a w)

/--
Homogeneity Theorem (Križ & @cite{kriz-spector-2021}, Section 2.1).

The gap is symmetric under negation: a world is in the gap for P
iff it's in the gap for ¬P.

This explains why:
- "The Xs are P" is undefined when some but not all Xs are P
- "The Xs aren't P" is ALSO undefined in exactly those worlds

Proof: The gap for P is {∃a.P(a) ∧ ∃a.¬P(a)}.
       The gap for ¬P is {∃a.¬P(a) ∧ ∃a.¬¬P(a)} = {∃a.¬P(a) ∧ ∃a.P(a)}.
       These are identical (in classical logic; uses Decidable on P).
-/
theorem homogeneity_gap_symmetric (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    inGap P x w ↔ inGap (fun a w => ¬ P a w) x w := by
  unfold inGap
  refine ⟨fun ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩ => ?_,
          fun ⟨⟨a, ha, hnPa⟩, ⟨b, hb, hnnPb⟩⟩ => ?_⟩
  · exact ⟨⟨b, hb, hPb⟩, ⟨a, ha, fun hnPa => hnPa hPa⟩⟩
  · refine ⟨⟨b, hb, ?_⟩, ⟨a, ha, hnPa⟩⟩
    by_contra hPb; exact hnnPb hPb

/--
Corollary: pluralTruthValue is gap iff negated version is gap.
-/
theorem pluralTruthValue_gap_iff_neg_gap (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) (_hne : x.Nonempty) :
    pluralTruthValue P x w = .indet ↔
    pluralTruthValue (fun a w => ¬ P a w) x w = .indet := by
  rw [pluralTruthValue_eq_gap_iff, pluralTruthValue_eq_gap_iff]
  refine ⟨fun ⟨⟨a, ha, hPa⟩, ⟨b, hb, hnPb⟩⟩ => ?_,
          fun ⟨⟨a, ha, hnPa⟩, ⟨b, hb, hnnPb⟩⟩ => ?_⟩
  · exact ⟨⟨b, hb, hnPb⟩, ⟨a, ha, fun hnPa => hnPa hPa⟩⟩
  · refine ⟨⟨b, hb, ?_⟩, ⟨a, ha, hnPa⟩⟩
    by_contra hPb; exact hnnPb hPb

/--
Homogeneity Polarity Theorem: Truth and falsity swap under negation.

If "the Xs are P" is TRUE, then "the Xs are ¬P" is FALSE, and vice versa.

Note: Requires x to be nonempty. For empty x, both `allSatisfy P` and
`allSatisfy ¬P` are vacuously true, so the theorem doesn't hold.
-/
theorem pluralTruthValue_neg (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) (hne : x.Nonempty) :
    pluralTruthValue (fun a w => ¬ P a w) x w =
    match pluralTruthValue P x w with
    | .true => .false
    | .false => .true
    | .indet => .indet := by
  cases h : pluralTruthValue P x w
  · -- Case .true → .false
    rw [pluralTruthValue_eq_true_iff] at h
    rw [pluralTruthValue_eq_false_iff]
    exact ⟨hne, fun a ha hnPa => hnPa (h a ha)⟩
  · -- Case .false → .true
    rw [pluralTruthValue_eq_false_iff] at h
    rw [pluralTruthValue_eq_true_iff]
    intro a ha hPa; exact h.2 a ha hPa
  · -- Case .indet → .indet
    rw [pluralTruthValue_eq_gap_iff] at h
    rw [pluralTruthValue_eq_gap_iff]
    obtain ⟨⟨a, ha, hPa⟩, ⟨b, hb, hnPb⟩⟩ := h
    exact ⟨⟨b, hb, hnPb⟩, ⟨a, ha, fun hnPa => hnPa hPa⟩⟩

end KrizSpector

-- Atom Vacuity

/--
On singletons, `distMaximal` reduces to the predicate itself.

This is WHY `each`/`jeder` forces maximality: when it distributes P to individual
atoms, the result is just P(a) — there's no plurality for tolerance to weaken.
@cite{haslinger-etal-2025} §2.3, the argument below the four-way classification.
-/
theorem distMaximal_singleton {Atom : Type*} {W : Type*}
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (a : Atom) (w : W) :
    distMaximal P {a} w ↔ P a w := by
  unfold distMaximal
  simp

/--
On pairs, `distMaximal` reduces to conjunction of individual checks.

This is the two-atom instance of Link's distributive inference
(`distr_atom_part` in Link1983.lean): for a distributive P, checking
`*P` on a two-atom plurality {a, b} reduces to P(a) ∧ P(b).

When `a = b`, `{a, b} = {a}` (Finset dedup) and the result
degenerates to `P a w` (= `P a w ∧ P a w` by `and_self`).
-/
theorem distMaximal_pair (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (a b : Atom) (w : W) :
    distMaximal P {a, b} w ↔ P a w ∧ P b w := by
  unfold distMaximal
  simp [and_comm]

/--
**Atom Vacuity Theorem (general).**

On singletons, `distTolerant` reduces to the predicate itself for ANY
tolerance relation — not just identity tolerance.

This is because {a} has exactly one nonempty subset (itself), and
`tol.refl` guarantees `tol.rel {a} {a}` holds. The tolerance parameter
literally has nothing to vary over.
-/
theorem distTolerant_singleton {Atom : Type*} [DecidableEq Atom] {W : Type*}
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (tol : Tolerance Atom) (a : Atom) (w : W) :
    distTolerant P tol {a} w ↔ P a w := by
  unfold distTolerant
  refine ⟨fun ⟨z, hz_mem, hz_ne, _, hz_all⟩ => ?_, fun hPa => ?_⟩
  · obtain ⟨b, hb⟩ := hz_ne
    have hba : b = a := Finset.mem_singleton.mp (Finset.mem_powerset.mp hz_mem hb)
    have hPb : P b w := hz_all b hb
    exact hba ▸ hPb
  · exact ⟨{a}, Finset.mem_powerset.mpr (Finset.Subset.refl _),
           ⟨a, Finset.mem_singleton.mpr rfl⟩, tol.refl {a},
           fun b hb => by rw [Finset.mem_singleton.mp hb]; exact hPa⟩

/--
Corollary: on singletons, all tolerance relations agree.
-/
theorem distTolerant_singleton_independent {Atom : Type*} [DecidableEq Atom] {W : Type*}
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (tol₁ tol₂ : Tolerance Atom) (a : Atom) (w : W) :
    distTolerant P tol₁ {a} w ↔ distTolerant P tol₂ {a} w := by
  rw [distTolerant_singleton, distTolerant_singleton]

/-- Special case: identity tolerance on singletons. -/
theorem distTolerant_identity_singleton (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (a : Atom) (w : W) :
    distTolerant P Tolerance.identity {a} w ↔ P a w :=
  distTolerant_singleton P Tolerance.identity a w

-- The Independence Result

/--
Classification by [±distributive] × [±maximal].

@cite{haslinger-etal-2025} present a four-cell typology in which the
two properties are argued to be orthogonal: all four cells are
attested or predicted.
-/
structure DistMaxClass where
  /-- Does this operator force the predicate to apply to each atom separately? -/
  isDistributive : Bool
  /-- Does this operator block exception tolerance (force all atoms to satisfy P)? -/
  isMaximal : Bool
  deriving DecidableEq, Repr, BEq

/-- each, jeder (DP and distance): +dist, +max -/
def DistMaxClass.distMax : DistMaxClass := ⟨true, true⟩
/-- jeweils: +dist, -max -/
def DistMaxClass.distNonMax : DistMaxClass := ⟨true, false⟩
/-- all/alle: -dist, +max -/
def DistMaxClass.nonDistMax : DistMaxClass := ⟨false, true⟩
/-- definite plurals: -dist, -max -/
def DistMaxClass.nonDistNonMax : DistMaxClass := ⟨false, false⟩

/--
Hypothetical exception-tolerant DP quantifier.
@cite{haslinger-etal-2025} flag this as a typology cell predicted
possible by the Križ & @cite{kriz-spector-2021} framework but not
attested in any known language. The non-attestation is a typological
puzzle — the formal tools for non-maximality (tolerance relations)
don't inherently block DP-internal quantifiers from using them.

⟦[jeder* P] Q⟧^≤ = λw.∃z[z ≤ ⊕P ∧ ∀y[y ∈ AT ∧ y ⊑ z → ⟦Q⟧^≤(w)(y)]]
-/
def distTolerantQuant (restrictor scope : Atom → W → Prop)
    [∀ a w, Decidable (restrictor a w)] [∀ a w, Decidable (scope a w)]
    (tol : Tolerance Atom) (x : Finset Atom) (w : W) : Prop :=
  ∃ z ∈ x.powerset, z.Nonempty ∧ tol.rel z x ∧
    (∀ a ∈ z, restrictor a w) ∧ (∀ a ∈ z, scope a w)

end Semantics.Plurality.Distributivity
