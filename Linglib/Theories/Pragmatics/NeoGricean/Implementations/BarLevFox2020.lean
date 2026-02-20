/-
# Innocent Inclusion and Free Choice

Formalization of Bar-Lev & Fox (2020) "Free choice, simplification, and Innocent Inclusion"
Natural Language Semantics 28:175-223.

## The Key Innovation

Standard Innocent Exclusion (IE) yields exclusive-or for simple disjunction but
fails to derive free choice. Bar-Lev & Fox add Innocent Inclusion (II):

**IE**: Exclude alternatives that can be false in ALL maximal consistent sets
**II**: Include alternatives that can be true in ALL maximal consistent sets (after IE)

## Why II Derives Free Choice

The key is closure under conjunction:
- Simple disjunction `{a ∨ b, a, b, a ∧ b}` IS closed under ∧ → exclusive-or
- FC disjunction `{◇(a ∨ b), ◇a, ◇b, ◇(a ∧ b)}` is NOT closed → free choice

When ALT is not closed under conjunction, II can assign TRUE to alternatives
that IE cannot assign FALSE to.

## References

- Bar-Lev & Fox (2020). Free choice, simplification, and Innocent Inclusion. NLS 28:175-223.
- Fox (2007). Free choice and the theory of scalar implicatures.
- Spector (2016). Comparing exhaustivity operators.
-/

import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Basic

namespace NeoGricean.FreeChoice

open NeoGricean.Exhaustivity

-- SECTION 1: Free Choice Setup

/-!
## Free Choice Configuration

To derive free choice, we need:
- φ = ◇(a ∨ b) (the prejacent)
- ALT = {◇(a ∨ b), ◇a, ◇b, ◇(a ∧ b)} (the alternatives)

Key observation: This ALT is NOT closed under conjunction!
- ◇a ∧ ◇b is NOT in ALT (it's not equivalent to any member)

This non-closure is what allows II to derive free choice.
-/

/-- Possible worlds for free choice (whether each disjunct is permitted).

    The `separatelyAB` world is crucial: it represents an epistemic state where
    a and b are each individually permitted but not jointly — i.e., some
    accessible world has a (not b) and some has b (not a), but no single
    accessible world has both. This distinguishes ◇a ∧ ◇b from ◇(a ∧ b)
    and is what makes free choice derivable via II. -/
inductive FCWorld where
  | neither : FCWorld       -- Neither a nor b permitted
  | onlyA : FCWorld         -- Only a permitted
  | onlyB : FCWorld         -- Only b permitted
  | both : FCWorld          -- Both jointly permitted (◇(a ∧ b))
  | separatelyAB : FCWorld  -- Each individually permitted, not jointly (◇a ∧ ◇b ∧ ¬◇(a∧b))
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Proposition: a is permitted -/
def permA : Prop' FCWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => False
  | .both => True
  | .separatelyAB => True

/-- Proposition: b is permitted -/
def permB : Prop' FCWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => True
  | .both => True
  | .separatelyAB => True

/-- Proposition: a ∨ b is permitted (◇(a ∨ b)) -/
def permAorB : Prop' FCWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => True
  | .both => True
  | .separatelyAB => True

/-- Proposition: a ∧ b is permitted (◇(a ∧ b)) -/
def permAandB : Prop' FCWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True
  | .separatelyAB => False  -- individually permitted ≠ jointly permitted

/-- The free choice alternative set: {◇(a ∨ b), ◇a, ◇b, ◇(a ∧ b)} -/
def fcALT : Set (Prop' FCWorld) :=
  {permAorB, permA, permB, permAandB}

/-- The prejacent: ◇(a ∨ b) -/
def fcPrejacent : Prop' FCWorld := permAorB

-- SECTION 4: Non-Closure Under Conjunction

/-!
## The Key Structural Property

**Theorem (Non-closure)**: fcALT is NOT closed under conjunction.

Specifically: permA ∧ permB (= ◇a ∧ ◇b) is not in fcALT.

This is the structural property that distinguishes FC alternatives from
simple disjunction alternatives and enables the free choice inference.

For simple disjunction:
- ALT = {a ∨ b, a, b, a ∧ b}
- a ∧ b IS in ALT
- Closed under conjunction

For FC disjunction:
- ALT = {◇(a ∨ b), ◇a, ◇b, ◇(a ∧ b)}
- ◇a ∧ ◇b is NOT in ALT (it's different from ◇(a ∧ b)!)
- NOT closed under conjunction
-/

/-- The free choice alternatives are NOT closed under conjunction in the
    relevant sense: the conjunction of two alternatives is not equivalent
    to any single alternative in the general case.

    In modal logic: ◇a ∧ ◇b ⊭ ◇(a ∧ b) (there are worlds where both are
    individually possible but their conjunction is not).
-/
theorem fc_not_closed_general :
    ¬(∀ (X : Set (Prop' FCWorld)), X ⊆ fcALT → (⋀ X) ∈ fcALT) := by
  intro h
  have hX : ({permA, permB} : Set (Prop' FCWorld)) ⊆ fcALT := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with rfl | rfl <;> simp
  have hconj := h {permA, permB} hX
  simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hconj
  rcases hconj with heq | heq | heq | heq
  · -- ⋀{permA, permB} = permAorB: at onlyA, permB false so conjunction false
    have : ¬(⋀ ({permA, permB} : Set _)) .onlyA :=
      fun hc => hc permB (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · -- ⋀{permA, permB} = permA: at onlyA, permB false so conjunction false
    have : ¬(⋀ ({permA, permB} : Set _)) .onlyA :=
      fun hc => hc permB (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · -- ⋀{permA, permB} = permB: at onlyB, permA false so conjunction false
    have : ¬(⋀ ({permA, permB} : Set _)) .onlyB :=
      fun hc => hc permA (Set.mem_insert_iff.mpr (Or.inl rfl))
    rw [heq] at this; exact this trivial
  · -- ⋀{permA, permB} = permAandB: at separatelyAB, both individually True
    have : (⋀ ({permA, permB} : Set _)) .separatelyAB := by
      intro φ hφ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
      rcases hφ with rfl | rfl <;> trivial
    rw [heq] at this; exact this

-- SECTION 5: IE Analysis for Free Choice

/-!
## IE Computation for Free Choice

For φ = ◇(a ∨ b) and ALT = {◇(a ∨ b), ◇a, ◇b, ◇(a ∧ b)}:

**IE Analysis**:
- ◇(a ∧ b) is innocently excludable (can be consistently negated)
- ◇a is NOT innocently excludable (negating it contradicts φ at some worlds)
- ◇b is NOT innocently excludable (negating it contradicts φ at some worlds)

Result: IE = {◇(a ∧ b)}

This is where standard exhaustivity stops: Exh^{IE}(◇(a ∨ b)) = ◇(a ∨ b) ∧ ¬◇(a ∧ b)
which does NOT entail ◇a ∧ ◇b.
-/

-- SECTION 6: II Analysis for Free Choice

/-!
## II Computation for Free Choice

After IE excludes ◇(a ∧ b), II considers which remaining alternatives
can be consistently assigned TRUE.

**II Analysis**:
Given φ = ◇(a ∨ b) and IE = {◇(a ∧ b)}:

Consider the constraint set: {◇(a ∨ b), ¬◇(a ∧ b)}
- This is consistent with ◇a (witness: onlyA world)
- This is consistent with ◇b (witness: onlyB world)
- Both ◇a and ◇b appear in EVERY maximal II-compatible set

Therefore: II = {◇a, ◇b}

**Result**: Exh^{IE+II}(◇(a ∨ b)) = ◇(a ∨ b) ∧ ¬◇(a ∧ b) ∧ ◇a ∧ ◇b

This is FREE CHOICE!
-/

-- SECTION 7: Free Choice Theorem

/-!
## Main Result: Free Choice Derivation

**Theorem**: Exh^{IE+II}(◇(a ∨ b)) ⊢ ◇a ∧ ◇b

The exhaustified meaning of "you may have a or b" entails
"you may have a AND you may have b".
-/

/-- Helper: The finite alternative set fcALT. -/
private theorem fcALT_finite : Set.Finite fcALT :=
  Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _)))

/-- Helper: fcPrejacent is satisfiable. -/
private theorem fcPrejacent_sat : ∃ w, fcPrejacent w := ⟨.onlyA, trivial⟩

/-- Helper: permAorB is NOT innocently excludable.
    ∼permAorB contradicts fcPrejacent (= permAorB) in any consistent set. -/
private theorem permAorB_not_ie :
    ¬isInnocentlyExcludable fcALT fcPrejacent permAorB := by
  intro ⟨_, hIE⟩
  obtain ⟨E, hMC⟩ := exists_MCset fcALT fcPrejacent fcALT_finite fcPrejacent_sat
  obtain ⟨u, hu⟩ := hMC.1.2.2
  exact hu (∼permAorB) (hIE E hMC) (hu fcPrejacent hMC.1.1)

/-- Helper: fcPrejacent ∧ ¬permA ∧ ¬permB is inconsistent. -/
private theorem perm_cover : ∀ u, fcPrejacent u → ¬permA u → ¬permB u → False :=
  fun u => by cases u <;> simp [fcPrejacent, permAorB, permA, permB]

/-- Helper: An MC-set that omits ∼permA. -/
private theorem mc_set_without_neg_permA :
    isMCSet fcALT fcPrejacent {fcPrejacent, ∼permB, ∼permAandB} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl
      · left; rfl
      · right; exact ⟨permB, by simp [fcALT], rfl⟩
      · right; exact ⟨permAandB, by simp [fcALT], rfl⟩
    · exact ⟨.onlyA, fun ψ hψ => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
        rcases hψ with rfl | rfl | rfl
        · exact trivial
        · exact id
        · exact id⟩
  · intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · -- ∼permAorB contradicts fcPrejacent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (∼permAorB) hψ' (hu fcPrejacent (hsub (Set.mem_insert _ _)))
      · -- ∼permA + ∼permB + fcPrejacent is inconsistent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact perm_cover u
          (hu fcPrejacent (hsub (Set.mem_insert _ _)))
          (hu (∼permA) hψ')
          (hu (∼permB) (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-- Helper: An MC-set that omits ∼permB. -/
private theorem mc_set_without_neg_permB :
    isMCSet fcALT fcPrejacent {fcPrejacent, ∼permA, ∼permAandB} := by
  constructor
  · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
    · intro ψ hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl
      · left; rfl
      · right; exact ⟨permA, by simp [fcALT], rfl⟩
      · right; exact ⟨permAandB, by simp [fcALT], rfl⟩
    · exact ⟨.onlyB, fun ψ hψ => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
        rcases hψ with rfl | rfl | rfl
        · exact trivial
        · exact id
        · exact id⟩
  · intro E' hE' hsub ψ hψ'
    rcases hE'.2.1 ψ hψ' with rfl | ⟨a, ha, rfl⟩
    · exact Set.mem_insert _ _
    · simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (∼permAorB) hψ' (hu fcPrejacent (hsub (Set.mem_insert _ _)))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · -- ∼permB + ∼permA + fcPrejacent is inconsistent
        exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact perm_cover u
          (hu fcPrejacent (hsub (Set.mem_insert _ _)))
          (hu (∼permA) (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
          (hu (∼permB) hψ')
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-- Helper: permA is NOT innocently excludable. -/
private theorem permA_not_ie :
    ¬isInnocentlyExcludable fcALT fcPrejacent permA := by
  intro ⟨_, hIE⟩
  have hNotIn : ∼permA ∉ ({fcPrejacent, ∼permB, ∼permAandB} : Set (Prop' FCWorld)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => Eq.mp (congrFun h .neither) id,
           fun h => Eq.mpr (congrFun h .onlyA) id trivial,
           fun h => Eq.mpr (congrFun h .onlyA) id trivial⟩
  exact hNotIn (hIE _ mc_set_without_neg_permA)

/-- Helper: permB is NOT innocently excludable. -/
private theorem permB_not_ie :
    ¬isInnocentlyExcludable fcALT fcPrejacent permB := by
  intro ⟨_, hIE⟩
  have hNotIn : ∼permB ∉ ({fcPrejacent, ∼permA, ∼permAandB} : Set (Prop' FCWorld)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => Eq.mp (congrFun h .neither) id,
           fun h => Eq.mp (congrFun h .onlyA) id trivial,
           fun h => Eq.mpr (congrFun h .onlyB) id trivial⟩
  exact hNotIn (hIE _ mc_set_without_neg_permB)

/-- Helper: dispatch IE-excludability at .separatelyAB. For any IE-excludable q,
    (∼q) .separatelyAB holds. -/
private theorem ie_neg_at_separatelyAB (q : Prop' FCWorld)
    (hqIE : isInnocentlyExcludable fcALT fcPrejacent q) : (∼q) FCWorld.separatelyAB := by
  have hq_in := hqIE.1
  simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hq_in
  rcases hq_in with rfl | rfl | rfl | rfl
  · exact absurd hqIE permAorB_not_ie
  · exact absurd hqIE permA_not_ie
  · exact absurd hqIE permB_not_ie
  · exact id  -- (∼permAandB) .separatelyAB = ¬False

/-- Helper: For any II-compatible R, adding a target alternative that holds at
    .separatelyAB and is implied by permAandB preserves II-compatibility. -/
private theorem extend_II_with_target
    (target : Prop' FCWorld)
    (htarget_alt : target ∈ fcALT)
    (htarget_sep : target FCWorld.separatelyAB)
    (hAandB_implies : ∀ u, permAandB u → target u)
    (R : Set (Prop' FCWorld))
    (hRcompat : isIICompatible fcALT fcPrejacent R) (_hNotIn : target ∉ R) :
    isIICompatible fcALT fcPrejacent (R ∪ {target}) := by
  constructor
  · intro x hx
    rcases hx with hxR | hxT
    · exact hRcompat.1 hxR
    · rw [Set.mem_singleton_iff.mp hxT]; exact htarget_alt
  · obtain ⟨u₀, hu₀⟩ := hRcompat.2
    by_cases htarg : target u₀
    · exact ⟨u₀, fun ψ hψ => by
        rcases hψ with hψ_left | hψ_right
        · exact hu₀ ψ (Set.mem_union_left _ hψ_left)
        · rcases hψ_right with hψR | hψT
          · exact hu₀ ψ (Set.mem_union_right _ hψR)
          · rw [Set.mem_singleton_iff.mp hψT]; exact htarg⟩
    · -- ¬target u₀: use .separatelyAB as witness
      refine ⟨.separatelyAB, fun ψ hψ => ?_⟩
      rcases hψ with hψ_left | hψ_right
      · rcases hψ_left with hψ_φ | hψ_ie
        · rw [Set.mem_singleton_iff.mp hψ_φ]; exact trivial
        · obtain ⟨q, hqIE, rfl⟩ := hψ_ie
          exact ie_neg_at_separatelyAB q hqIE
      · rcases hψ_right with hψR | hψT
        · -- ψ ∈ R ⊆ fcALT: all members except permAandB hold at .separatelyAB
          have hψ_fcALT := hRcompat.1 hψR
          simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ_fcALT
          rcases hψ_fcALT with rfl | rfl | rfl | rfl
          · exact trivial  -- permAorB .separatelyAB
          · exact trivial  -- permA .separatelyAB
          · exact trivial  -- permB .separatelyAB
          · -- permAandB ∈ R: hAandB_implies gives target u₀, contradicting ¬target u₀
            exact absurd (hAandB_implies u₀ (hu₀ permAandB (Set.mem_union_right _ hψR))) htarg
        · rw [Set.mem_singleton_iff.mp hψT]; exact htarget_sep

/-- Helper: a target alternative in fcALT that holds at .separatelyAB and is
    implied by permAandB is innocently includable. -/
private theorem target_in_II
    (target : Prop' FCWorld)
    (htarget_alt : target ∈ fcALT)
    (htarget_sep : target FCWorld.separatelyAB)
    (hAandB_implies : ∀ u, permAandB u → target u) :
    isInnocentlyIncludable fcALT fcPrejacent target := by
  constructor
  · exact htarget_alt
  · intro R ⟨hRcompat, hRmax⟩
    by_contra hNotIn
    have hext := extend_II_with_target target htarget_alt htarget_sep hAandB_implies
      R hRcompat hNotIn
    exact hNotIn (hRmax (R ∪ {target}) hext Set.subset_union_left
      (Set.mem_union_right R rfl))

/-- The free choice inference: exhaustified ◇(a ∨ b) entails ◇a -/
theorem fc_entails_permA :
    ∀ w, exhIEII fcALT fcPrejacent w → permA w := by
  intro w ⟨_, _, hII⟩
  exact hII permA (target_in_II permA (by simp [fcALT]) trivial
    (fun u h => by cases u <;> simp_all [permAandB, permA]))

/-- The free choice inference: exhaustified ◇(a ∨ b) entails ◇b -/
theorem fc_entails_permB :
    ∀ w, exhIEII fcALT fcPrejacent w → permB w := by
  intro w ⟨_, _, hII⟩
  exact hII permB (target_in_II permB (by simp [fcALT]) trivial
    (fun u h => by cases u <;> simp_all [permAandB, permB]))

/-- Main Free Choice Theorem: Exh^{IE+II}(◇(a ∨ b)) ⊢ ◇a ∧ ◇b -/
theorem free_choice :
    ∀ w, exhIEII fcALT fcPrejacent w → permA w ∧ permB w := by
  intro w hw
  exact ⟨fc_entails_permA w hw, fc_entails_permB w hw⟩

-- SECTION 8: Contrast with Simple Disjunction

/-!
## Why Simple Disjunction Doesn't Get Free Choice

For comparison, simple disjunction:
- φ = a ∨ b
- ALT = {a ∨ b, a, b, a ∧ b}

This ALT IS closed under conjunction (a ∧ b is already there).

**IE Analysis**: IE = {a, b, a ∧ b} (all proper alternatives excludable)
**II Analysis**: II = ∅ (nothing can be consistently included after IE)

Result: Exh^{IE+II}(a ∨ b) = (a ∨ b) ∧ ¬a ∧ ¬b ∧ ¬(a ∧ b) = ⊥

This is inconsistent! So Exh cannot apply to simple disjunction
(motivating embedded exhaustification in complex sentences).

The contrast:
- ◇(a ∨ b): FC alternatives not closed → free choice
- a ∨ b: Alternatives closed → exclusive-or (or inconsistency)
-/

/-- Simple disjunction worlds -/
inductive DisjWorld where
  | neither : DisjWorld
  | onlyA : DisjWorld
  | onlyB : DisjWorld
  | both : DisjWorld
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Proposition a -/
def propA : Prop' DisjWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => False
  | .both => True

/-- Proposition b -/
def propB : Prop' DisjWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => True
  | .both => True

/-- Proposition a ∨ b -/
def propAorB : Prop' DisjWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => True
  | .both => True

/-- Proposition a ∧ b -/
def propAandB : Prop' DisjWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True

/-- Simple disjunction alternatives: {a ∨ b, a, b, a ∧ b} -/
def simpleALT : Set (Prop' DisjWorld) :=
  {propAorB, propA, propB, propAandB}

/-- Simple disjunction IS closed under conjunction (a ∧ b ∈ ALT) -/
theorem simple_has_conjunction :
    propAandB ∈ simpleALT := by
  simp [simpleALT]

/-- For simple disjunction, exhaustification yields exclusive-or
    (or inconsistency without embedded Exh) -/
theorem simple_exclusive_or :
    ∀ w, exhIE simpleALT propAorB w →
      (propA w ∧ ¬propB w) ∨ (propB w ∧ ¬propA w) ∨ (propA w ∧ propB w) := by
  intro w hExh
  -- exhIE requires all IE members to hold at w, including φ
  -- Since propAorB ∈ IE (it's in every MC-set as the prejacent), propAorB w
  cases w
  · -- neither: propAorB is false, so exhIE is vacuously inconsistent here
    -- φ ∈ IE ALT φ (the prejacent is in every MC-set by compatibility)
    -- propAorB .neither is definitionally False
    exact (hExh propAorB (λ E hE_mc => hE_mc.1.1)).elim
  · -- onlyA
    left; simp [propA, propB]
  · -- onlyB
    right; left; simp [propA, propB]
  · -- both
    right; right; simp [propA, propB]

-- Summary

/-!
## Summary

### Definitions
- `II`: Innocently Includable alternatives (those in every MI-set)
- `exhIEII`: Combined exhaustivity operator Exh^{IE+II}
- `isInnocentlyIncludable`: Predicate for II membership

### Results
- `free_choice`: Exh^{IE+II}(◇(a ∨ b)) ⊢ ◇a ∧ ◇b
- `fc_not_closed_general`: FC alternatives not closed under ∧
- `simple_has_conjunction`: Simple disjunction alternatives ARE closed

### Theoretical Insight
The structural difference between FC and simple disjunction is
**closure under conjunction**:
- Closed → exclusive-or (standard scalar implicature)
- Not closed → free choice (via Innocent Inclusion)

### References
- Bar-Lev & Fox (2020). Free choice, simplification, and Innocent Inclusion.
- Fox (2007). Free choice and the theory of scalar implicatures.
- Spector (2016). Comparing exhaustivity operators.
-/

end NeoGricean.FreeChoice
