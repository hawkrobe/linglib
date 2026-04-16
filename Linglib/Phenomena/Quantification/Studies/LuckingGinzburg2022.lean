import Linglib.Theories.Semantics.TypeTheoretic.Quantification
import Linglib.Theories.Semantics.Quantification.Quantifier
import Linglib.Core.Logic.Quantification.NumberTree
import Mathlib.Data.Finset.Powerset

/-!
# Referential Transparency Theory
@cite{lucking-ginzburg-2022} @cite{barwise-cooper-1981} @cite{cooper-2023}

@cite{lucking-ginzburg-2022} propose *Referential Transparency Theory* (RTT),
replacing GQT's set-of-sets denotations for quantified noun phrases (QNPs)
with **sets of ordered set bipartitions**. A bipartition ⟨refset, compset⟩
partitions the head noun's extension into a reference set and complement set;
the union is the maxset. Quantifier words act as "sieves" on bipartitions via
a **descriptive quantifier condition** (q-cond), and a **quantifier perspective**
(q-persp) gates anaphora accessibility.

## Core contributions formalized

1. **Ordered set bipartitions** as QNP denotations (§2.3, (15))
2. **Descriptive quantifier conditions** as cardinality relations (§4.2)
3. **Quantifier perspective** *derived* from bipartition structure (§4.3, (47))
4. **few/a few contrast**: same q-cond, different q-persp via refind (§4.3, (46))
5. **Anti-predication**: VP predicates on refset, ¬VP on compset (§4.5)
6. **Structural conservativity**: by construction (§1.3)
7. **Complexity reduction**: 2^(k+1) − 1 vs GQT's 2^(T(k)) (§4.8)
8. **Bridges**: RTT refsets = Cooper witness sets; compset predictions match

## Thread map

- **Ordered set bipartitions**: defined here (`BP`)
- **Witness sets**: `Theories.Semantics.TypeTheoretic.Quantification` —
  `WitnessSet`, `IsExistW`, `AnaphoraRef`, `anaphoraAvailable`
- **GQT properties**: `Theories.Semantics.Quantification.Quantifier` —
  `PropGQ`, `PConservative`
- **Conservative count**: `Core.Quantification.conservativeQuantifierCount`
- **Dog example**: reuses `DogWorld` from TTR Ch. 7
-/

namespace Phenomena.Quantification.Studies.LuckingGinzburg2022

open Semantics.TypeTheoretic
open Core.Quantification

-- ============================================================================
-- §1. Ordered Set Bipartitions (§2.3, (15))
-- ============================================================================

/-! ### §1. Ordered set bipartitions

An ordered set bipartition of a set s is a pair ⟨refset, compset⟩ of disjoint
subsets whose union is s. The ordering matters: ⟨A, B⟩ ≠ ⟨B, A⟩ in general.
These replace GQT's subset-of-powerset denotations. -/

variable {α : Type} [DecidableEq α]

/-- An ordered set bipartition: a pair of Finsets.
    §2.3, (15): ⟨refset, compset⟩ where refset ∩ compset = ∅
    and refset ∪ compset = maxset (the head noun's extension).
    Disjointness and union are verified extrinsically to enable `decide`. -/
structure BP (α : Type) where
  refset : Finset α
  compset : Finset α
  deriving DecidableEq

/-- The maxset (union of refset and compset). -/
def BP.maxset (b : BP α) : Finset α := b.refset ∪ b.compset

/-- All ordered set bipartitions of S: for each R ⊆ S, form ⟨R, S \ R⟩. -/
def allBP (S : Finset α) : Finset (BP α) :=
  S.powerset.map ⟨λ R => ⟨R, S \ R⟩, λ a b h => by
    simp [BP.mk.injEq] at h; exact h.1⟩

/-- The number of bipartitions of S equals 2^|S|.
    Each element independently goes to refset or compset. -/
theorem allBP_card (S : Finset α) : (allBP S).card = 2 ^ S.card := by
  simp [allBP, Finset.card_map, Finset.card_powerset]

/-- Every bipartition in allBP has maxset = S. -/
theorem allBP_maxset (S : Finset α) (b : BP α) (h : b ∈ allBP S) :
    b.maxset = S := by
  simp [allBP, Finset.mem_map] at h
  obtain ⟨R, hR, rfl⟩ := h
  exact Finset.union_sdiff_of_subset hR

/-- Refset of every bipartition in allBP is a subset of S. -/
theorem allBP_refset_sub (S : Finset α) (b : BP α) (h : b ∈ allBP S) :
    b.refset ⊆ S := by
  simp [allBP, Finset.mem_map] at h
  obtain ⟨R, hR, rfl⟩ := h
  exact hR

-- ============================================================================
-- §2. Descriptive Quantifier Conditions (§4.2)
-- ============================================================================

/-! ### §2. Descriptive quantifier conditions

A q-cond is a relation on |refset| and |compset|. Since RTT q-conds depend
only on cardinalities (@cite{lucking-ginzburg-2022} §4.2), this is
`ℕ → ℕ → Bool` — quantity invariance by construction. -/

/-- A descriptive quantifier condition: a decidable relation on
    the cardinalities of refset and compset.
    §4.2: the quantifier word's semantic contribution. -/
abbrev QCond := ℕ → ℕ → Bool

/-- q-cond for *every*: |compset| = 0 (equivalently, |refset| = |maxset|).
    §4.7, (58). -/
def every_qcond : QCond := λ _r c => c == 0

/-- q-cond for *no*: |refset| = 0 (all elements in compset). -/
def no_qcond : QCond := λ r _c => r == 0

/-- q-cond for *some*: |refset| ≥ 1 (at least one witness). -/
def some_qcond : QCond := λ r _c => decide (r ≥ 1)

/-- q-cond for *most*: |refset| > |compset|.
    §4.2: proportional, refset is the majority. -/
def most_qcond : QCond := λ r c => decide (r > c)

/-- q-cond for *few*: |refset| < |compset|.
    §4.3, (46): refset is the minority. The paper uses |refset| ≪ |compset|
    with a contextual threshold; we simplify to strict less-than. -/
def few_qcond : QCond := λ r c => decide (r < c)

/-- q-cond for *many*: |refset| > θ (absolute threshold).
    §4.2, (39): evaluated against contextual standard. -/
def many_qcond (θ : ℕ) : QCond := λ r _c => decide (r > θ)

/-- Sieve: filter bipartitions by a quantifier condition.
    §2.3: quantifiers act as sieves on bipartition sets. -/
def sieve (qc : QCond) (bps : Finset (BP α)) : Finset (BP α) :=
  bps.filter (λ b => qc b.refset.card b.compset.card)

-- ============================================================================
-- §3. Quantifier Perspective & Refind (§4.3)
-- ============================================================================

/-! ### §3. Quantifier perspective (q-persp)

The q-persp feature is *derived* from the bipartition denotation (§4.3, (47)).
It tracks whether the bipartition with an empty refset — ⟨∅, maxset⟩ —
is included in the quantifier's denotation. If so, the compset is accessible
for anaphoric reference.

The key empirical prediction: *few* and *a few* share the same q-cond
(|refset| < |compset|) but differ in q-persp because *a few* includes a
**refind** — an individual member of refset (§4.3, (46)). The refind forces
refset ≠ ∅, excluding ⟨∅, maxset⟩ and blocking compset anaphora. -/

/-- Quantifier perspective, derived from bipartition denotation.
    §4.3, (47)–(48): gates anaphoric accessibility of compset. -/
inductive QPerspective where
  /-- The empty-refset bipartition ⟨∅, maxset⟩ IS in the denotation.
      Compset is available for anaphora. -/
  | refsetEmpty
  /-- The empty-refset bipartition is NOT in the denotation.
      Compset is not available. -/
  | refsetNonempty
  deriving DecidableEq, Repr

/-- Derive q-persp from a sieved set of bipartitions.
    §4.3, (47): check whether ⟨∅, _⟩ survives the sieve.

    The paper also has a third value "none" for degenerate cases
    like *every* (sole bipartition ⟨maxset, ∅⟩), but this is functionally
    equivalent to `refsetNonempty` — compset not available in either case. -/
def deriveQPersp (bps : Finset (BP α)) : QPerspective :=
  if decide (∃ b ∈ bps, b.refset = ∅) then .refsetEmpty
  else .refsetNonempty

/-- Compset is available for anaphora iff q-persp = refsetEmpty.
    §4.3, (47b). -/
def QPerspective.compsetAvailable : QPerspective → Bool
  | .refsetEmpty => true
  | .refsetNonempty => false

/-- Refind filter: exclude bipartitions with empty refset.
    §4.3, (46): *a few* includes a refind (an individual from refset),
    which requires refset ≠ ∅. This excludes ⟨∅, maxset⟩, changing
    q-persp from `refsetEmpty` to `refsetNonempty`. -/
def refindFilter (bps : Finset (BP α)) : Finset (BP α) :=
  bps.filter (λ b => decide (b.refset.card > 0))

-- ============================================================================
-- §4. Structural Derivation of Compset Anaphora
-- ============================================================================

/-! ### §4. Deriving compset anaphora from bipartition structure

The paper's central contribution: compset anaphora availability is *derived*
from the bipartition denotation via q-persp, not stipulated per quantifier.
This section proves per-quantifier q-persp derivations on a concrete domain
and shows that the few/a few contrast follows structurally.

Note: the full @cite{cooper-2023} Ch. 7 anaphora table also depends on
referentiality (refset in dgb-params vs q-params) and plurality — distinctions
orthogonal to RTT's q-persp mechanism. RTT's novel prediction is specifically
about **compset accessibility**, which we derive here. -/

open Semantics.TypeTheoretic (DogWorld)

/-- Bool version of `isDog` for decidable sieving. -/
def isDogB : DogWorld → Bool
  | .fido => true | .rex => true | .spot => true | .luna => false

/-- Bool version of `doesBark`. -/
def doesBarkB : DogWorld → Bool
  | .fido => true | .rex => false | .spot => true | .luna => false

/-- The set of dogs (3 entities). -/
def dogs : Finset DogWorld := Finset.univ.filter (fun x => isDogB x)

theorem dogs_eq : dogs = {.fido, .rex, .spot} := by decide

/-- 2^3 = 8 bipartitions of the dog set. -/
theorem dog_bipartitions_card : (allBP dogs).card = 8 := by decide

-- Per-quantifier q-persp derivations

/-- *Every*: sole bipartition ⟨dogs, ∅⟩ has refset = dogs ≠ ∅.
    Q-persp = refsetNonempty. Compset not available (compset = ∅). -/
theorem every_dog_qpersp :
    deriveQPersp (sieve every_qcond (allBP dogs)) = .refsetNonempty := by
  decide

/-- *No*: sole bipartition ⟨∅, dogs⟩ has refset = ∅.
    Q-persp = refsetEmpty. Compset available — but for *no*,
    compset = maxset, so it collapses with maxset anaphora. -/
theorem no_dog_qpersp :
    deriveQPersp (sieve no_qcond (allBP dogs)) = .refsetEmpty := by decide

/-- *Some*: ⟨∅, _⟩ excluded by |refset| ≥ 1.
    Q-persp = refsetNonempty. -/
theorem some_dog_qpersp :
    deriveQPersp (sieve some_qcond (allBP dogs)) = .refsetNonempty := by
  decide

/-- *Most*: ⟨∅, _⟩ excluded by |refset| > |compset|.
    Q-persp = refsetNonempty. -/
theorem most_dog_qpersp :
    deriveQPersp (sieve most_qcond (allBP dogs)) = .refsetNonempty := by
  decide

/-- *Few*: ⟨∅, dogs⟩ included (0 < 3). Q-persp = refsetEmpty.
    Compset IS available.
    "Few dogs barked. They [= non-barking dogs] slept through." -/
theorem few_dog_qpersp :
    deriveQPersp (sieve few_qcond (allBP dogs)) = .refsetEmpty := by decide

/-- *A few*: same q-cond as *few*, but refind excludes ⟨∅, dogs⟩.
    Q-persp = refsetNonempty. Compset NOT available.
    "#They [= non-barking dogs] slept through." -/
theorem aFew_dog_qpersp :
    deriveQPersp (refindFilter (sieve few_qcond (allBP dogs))) =
      .refsetNonempty := by decide

-- The few / a few contrast: the paper's key empirical result, derived structurally

/-- Compset available for *few* (derived from q-persp). -/
theorem few_compset_available :
    (deriveQPersp (sieve few_qcond (allBP dogs))).compsetAvailable = true := by
  decide

/-- Compset NOT available for *a few* (derived: refind changes q-persp). -/
theorem aFew_compset_not_available :
    (deriveQPersp (refindFilter (sieve few_qcond (allBP dogs)))).compsetAvailable
      = false := by decide

/-- This matches @cite{cooper-2023} Ch. 7: `.compset ∈ anaphoraAvailable .few`
    but `.compset ∉ anaphoraAvailable .aFew`. -/
theorem few_aFew_matches_cooper :
    (AnaphoraRef.compset ∈ anaphoraAvailable .few) ∧
    (AnaphoraRef.compset ∉ anaphoraAvailable .aFew) := by
  exact ⟨by decide, by decide⟩

-- ============================================================================
-- §5. Witness-Set Bridge
-- ============================================================================

/-! ### §5. RTT refsets are Cooper witness sets

@cite{cooper-2023} Ch. 7 defines `WitnessSet P X` as X ⊆ extension of P.
RTT's refsets satisfy this by construction: every bipartition in `allBP S`
has `refset ⊆ S`. When S = fullExtFinset P, this is exactly `WitnessSet P`. -/

/-- Every RTT bipartition's refset is a Cooper witness set.
    Bridges RTT's bipartition denotations to the witness-set framework
    of @cite{cooper-2023} Ch. 7. -/
theorem bp_refset_is_witnessSet [Fintype α] (P : α → Prop) [DecidablePred P]
    (b : BP α) (h : b ∈ allBP (fullExtFinset P)) :
    WitnessSet P b.refset :=
  ⟨fun a ha => (Finset.mem_filter.mp (allBP_refset_sub _ b h ha)).2⟩

/-- The dogs Finset equals Cooper's fullExtFinset isDog. -/
theorem dogs_eq_fullExt : dogs = fullExtFinset isDog := by decide

-- ============================================================================
-- §6. Conservativity & Complexity
-- ============================================================================

/-! ### §6. Structural conservativity and complexity reduction

RTT's bipartitions partition only the *restrictor* (head noun extension).
Conservativity is guaranteed by construction: the scope set never appears
independently. §1.3, §4.8. -/

/-- Convert a QCond (bipartition sieve) to a classical PropGQ.
    The QNP ⟨q-cond, N⟩ applied to VP = Q is true iff some bipartition
    survives the sieve such that all refset members satisfy Q. -/
def qcondToGQ (qc : QCond) [Fintype α] (N : α → Prop) [DecidablePred N]
    (Q : α → Prop) : Prop :=
  ∃ b ∈ allBP (Finset.univ.filter N),
    qc b.refset.card b.compset.card = true ∧ ∀ a ∈ b.refset, Q a

/-- Conservativity holds for any QCond by construction.
    Every `a ∈ b.refset` satisfies N (since `b.refset ⊆ filter N`),
    so replacing Q with `N ∧ Q` doesn't change truth.
    @cite{lucking-ginzburg-2022} §1.3 @cite{barwise-cooper-1981} -/
theorem qcond_conservative [Fintype α] (qc : QCond) (N Q : α → Prop)
    [DecidablePred N] :
    qcondToGQ qc N Q ↔ qcondToGQ qc N (fun x => N x ∧ Q x) := by
  constructor
  · rintro ⟨b, hmem, hqc, hQ⟩
    refine ⟨b, hmem, hqc, fun a ha => ?_⟩
    have haN : N a := by
      have hSub := allBP_refset_sub _ b hmem
      have := Finset.mem_filter.mp (hSub ha)
      exact this.2
    exact ⟨haN, hQ a ha⟩
  · rintro ⟨b, hmem, hqc, hNQ⟩
    exact ⟨b, hmem, hqc, fun a ha => (hNQ a ha).2⟩

/-- RTT quantifier count: for a head noun extension of size k,
    there are 2^(k+1) − 1 possible QNP denotations (non-empty subsets
    of the 2^k bipartitions). §4.8. -/
def rttQuantifierCount (k : ℕ) : ℕ := 2 ^ (k + 1) - 1

#guard rttQuantifierCount 2 == 7
#guard rttQuantifierCount 3 == 15

/-- RTT's quantifier space is strictly smaller than GQT's conservative
    count (@cite{van-benthem-1984}).
    For n=2: RTT gives 7 vs GQT's 64. -/
theorem rtt_fewer_than_conservative_2 :
    rttQuantifierCount 2 < conservativeQuantifierCount 2 := by decide

theorem rtt_fewer_than_conservative_3 :
    rttQuantifierCount 3 < conservativeQuantifierCount 3 := by decide

theorem rtt_fewer_than_conservative_4 :
    rttQuantifierCount 4 < conservativeQuantifierCount 4 := by decide

-- ============================================================================
-- §7. Anti-predication (§4.5)
-- ============================================================================

/-! ### §7. Anti-predication

A VP simultaneously predicates positively on refset members (the "nucl")
and negatively on compset members (the "anti-nucl"). This two-headed
predication is specific to RTT and absent from standard GQT. §4.5, Figure 5:
the declarative plural head-subject rule has both `nucl` and `anti-nucl`. -/

/-- Anti-predication: the VP holds for all refset members and fails
    for all compset members. -/
def antiPredication (VP : α → Bool) (b : BP α) : Prop :=
  (∀ a ∈ b.refset, VP a = true) ∧ (∀ a ∈ b.compset, VP a = false)

omit [DecidableEq α] in
/-- Anti-predication implies the VP holds for every refset member. -/
theorem antiPred_refset (VP : α → Bool) (b : BP α)
    (h : antiPredication VP b) (a : α) (ha : a ∈ b.refset) :
    VP a = true := h.1 a ha

omit [DecidableEq α] in
/-- Anti-predication implies the VP fails for every compset member. -/
theorem antiPred_compset (VP : α → Bool) (b : BP α)
    (h : antiPredication VP b) (a : α) (ha : a ∈ b.compset) :
    VP a = false := h.2 a ha

/-- Truth conditions for "every N VP" via RTT:
    ∃ b in the sieved set with anti-predication ↔ ∀ a ∈ S, VP a = true.
    The unique bipartition ⟨S, ∅⟩ makes anti-predication equivalent to
    the VP holding on all of S (anti-nucl on ∅ is vacuous). -/
theorem every_truth_conditions (S : Finset α) (VP : α → Bool) :
    (∃ b ∈ sieve every_qcond (allBP S), antiPredication VP b) ↔
    (∀ a ∈ S, VP a = true) := by
  constructor
  · -- Forward: the unique surviving bipartition has refset = R where S ⊆ R,
    -- so anti-predication on R implies the VP holds on all of S
    rintro ⟨b, hb, hanti⟩
    have hmem := (Finset.mem_filter.mp hb).1
    have hqc := (Finset.mem_filter.mp hb).2
    rw [allBP, Finset.mem_map] at hmem
    obtain ⟨R, hR, rfl⟩ := hmem
    rw [Finset.mem_powerset] at hR
    simp only [every_qcond, beq_iff_eq] at hqc
    have hcomp : S \ R = ∅ := Finset.card_eq_zero.mp hqc
    -- Every a ∈ S must be in R (since S \ R = ∅), so anti-predication applies
    intro a haS
    apply hanti.1
    by_contra h
    exact absurd (hcomp ▸ Finset.mem_sdiff.mpr ⟨haS, h⟩) (by simp)
  · -- Backward: construct ⟨S, S \ S⟩ = ⟨S, ∅⟩
    intro hall
    have hsdiff : S \ S = (∅ : Finset α) := by simp
    refine ⟨⟨S, S \ S⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩, hall, fun a ha => ?_⟩
    · rw [allBP, Finset.mem_map]
      exact ⟨S, Finset.mem_powerset.mpr (Finset.Subset.refl S), rfl⟩
    · simp [every_qcond]
    · rw [hsdiff] at ha; simp at ha

-- ============================================================================
-- §8. Sieve Cardinalities
-- ============================================================================

/-! ### §8. Sieve cardinalities

Concrete verification that the q-cond sieves produce expected counts. -/

theorem every_dog_sieve_card :
    (sieve every_qcond (allBP dogs)).card = 1 := by decide

theorem no_dog_sieve_card :
    (sieve no_qcond (allBP dogs)).card = 1 := by decide

/-- 4 few-bipartitions: ⟨∅, dogs⟩ plus 3 singletons. -/
theorem few_dog_sieve_card :
    (sieve few_qcond (allBP dogs)).card = 4 := by decide

/-- Refind removes the empty-refset bipartition, leaving 3. -/
theorem aFew_dog_sieve_card :
    (refindFilter (sieve few_qcond (allBP dogs))).card = 3 := by decide

end Phenomena.Quantification.Studies.LuckingGinzburg2022
