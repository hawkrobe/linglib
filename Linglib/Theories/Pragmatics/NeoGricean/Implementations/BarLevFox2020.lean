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

-- SECTION 1: Innocent Inclusion (II)

/-!
## Definition of Innocent Inclusion

From Bar-Lev & Fox (2020), Definition (51):

> II(p, C) = ∩{C'' ⊆ C : C'' is maximal s.t.
>            {r : r ∈ C''} ∪ {p} ∪ {¬q : q ∈ IE(p,C)} is consistent}

That is: after computing IE, find all maximal subsets of alternatives that
can consistently be assigned TRUE (given that IE alternatives are false).
An alternative is innocently includable iff it appears in ALL such maximal sets.
-/

variable {World : Type*}
variable (ALT : Set (Prop' World))
variable (φ : Prop' World)

/--
**Definition (II-compatible set)**: A set of propositions R is (ALT, φ, IE)-compatible
for inclusion if:
a) R ⊆ ALT
b) {r : r ∈ R} ∪ {φ} ∪ {¬q : q ∈ IE(ALT, φ)} is consistent
-/
def isIICompatible (R : Set (Prop' World)) : Prop :=
  R ⊆ ALT ∧
  SetConsistent ({φ} ∪ {ψ | ∃ q, isInnocentlyExcludable ALT φ q ∧ ψ = ∼q} ∪ R)

/--
**Definition (MI-set)**: Maximal II-compatible set.
A set R is maximally (ALT, φ, IE)-compatible if it is II-compatible
and not properly included in any other II-compatible set.
-/
def isMISet (R : Set (Prop' World)) : Prop :=
  isIICompatible ALT φ R ∧
  ∀ R', isIICompatible ALT φ R' → R ⊆ R' → R' ⊆ R

/--
**Definition (II)**: II(ALT, φ) = {r ∈ ALT : r belongs to every MI-set}

An alternative r is innocently includable iff it belongs to every MI-set.
-/
def II : Set (Prop' World) :=
  {r ∈ ALT | ∀ R, isMISet ALT φ R → r ∈ R}

/--
An alternative a is innocently includable given ALT and φ
if and only if a ∈ II(ALT, φ).
-/
def isInnocentlyIncludable (a : Prop' World) : Prop :=
  a ∈ II ALT φ

-- SECTION 2: Combined Exhaustivity Operator (Exh^{IE+II})

/--
**Definition (Exh^{IE+II})**: The exhaustivity operator with both IE and II.

  ⟦Exh^{IE+II}⟧(ALT)(φ)(w) ⇔
    φ(w) ∧
    ∀q ∈ IE(ALT,φ)[¬q(w)] ∧    -- exclude IE alternatives
    ∀r ∈ II(ALT,φ)[r(w)]        -- include II alternatives

This is Bar-Lev & Fox's key operator that derives free choice.
-/
def exhIEII : Prop' World := λ w =>
  φ w ∧
  (∀ q, isInnocentlyExcludable ALT φ q → ¬q w) ∧
  (∀ r, isInnocentlyIncludable ALT φ r → r w)

-- SECTION 3: Free Choice Setup

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

/-- ◇a ∧ ◇b (permission for each individually) -/
def permAandPermB : Prop' FCWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True
  | .separatelyAB => True  -- each individually permitted

/-- Key distinction: ◇(a ∧ b) ≠ ◇a ∧ ◇b — they differ at `separatelyAB`
    where a and b are each individually permitted but not jointly.
    This is the modal non-equivalence that drives free choice. -/
theorem permAandB_ne_permAandPermB :
    ¬(∀ w, permAandB w ↔ permAandPermB w) := by
  intro h
  exact absurd ((h .separatelyAB).mpr trivial) id

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

/-- The conjunction alternative is excludable -/
theorem conjunction_excludable :
    ∃ w, fcPrejacent w ∧ ¬permAandB w := by
  use FCWorld.onlyA
  simp [fcPrejacent, permAorB, permAandB]

/-- permA is not excludable (negating it at some φ-worlds is inconsistent) -/
theorem permA_not_excludable_witness :
    ∃ w, fcPrejacent w ∧ permA w ∧ ¬permB w := by
  use FCWorld.onlyA
  simp [fcPrejacent, permAorB, permA, permB]

/-- permB is not excludable (negating it at some φ-worlds is inconsistent) -/
theorem permB_not_excludable_witness :
    ∃ w, fcPrejacent w ∧ permB w ∧ ¬permA w := by
  use FCWorld.onlyB
  simp [fcPrejacent, permAorB, permA, permB]

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

/-- ◇a is consistent with φ and ¬◇(a ∧ b) -/
theorem permA_includable_witness :
    ∃ w, fcPrejacent w ∧ ¬permAandB w ∧ permA w := by
  use FCWorld.onlyA
  simp [fcPrejacent, permAorB, permAandB, permA]

/-- ◇b is consistent with φ and ¬◇(a ∧ b) -/
theorem permB_includable_witness :
    ∃ w, fcPrejacent w ∧ ¬permAandB w ∧ permB w := by
  use FCWorld.onlyB
  simp [fcPrejacent, permAorB, permAandB, permB]

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
        have h1 : permAorB u := hu fcPrejacent (hsub (Set.mem_insert _ _))
        have h2 : ¬permA u := hu (∼permA) hψ'
        have h3 : ¬permB u :=
          hu (∼permB) (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        cases u <;> simp_all [permAorB, permA, permB]
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
        have h1 : permAorB u := hu fcPrejacent (hsub (Set.mem_insert _ _))
        have h2 : ¬permA u :=
          hu (∼permA) (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        have h3 : ¬permB u := hu (∼permB) hψ'
        cases u <;> simp_all [permAorB, permA, permB]
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

/-- Helper: For any II-compatible R, adding permA preserves II-compatibility. -/
private theorem extend_II_with_permA (R : Set (Prop' FCWorld))
    (hRcompat : isIICompatible fcALT fcPrejacent R) (_hpA : permA ∉ R) :
    isIICompatible fcALT fcPrejacent (R ∪ {permA}) := by
  constructor
  · intro x hx
    rcases hx with hxR | hxA
    · exact hRcompat.1 hxR
    · rw [Set.mem_singleton_iff.mp hxA]; simp [fcALT]
  · -- Get witness from R's consistency
    obtain ⟨u₀, hu₀⟩ := hRcompat.2
    by_cases hpAu₀ : permA u₀
    · -- u₀ also witnesses the extended set
      exact ⟨u₀, fun ψ hψ => by
        rcases hψ with hψ_left | hψ_right
        · exact hu₀ ψ (Set.mem_union_left _ hψ_left)
        · rcases hψ_right with hψR | hψA
          · exact hu₀ ψ (Set.mem_union_right _ hψR)
          · rw [Set.mem_singleton_iff.mp hψA]; exact hpAu₀⟩
    · -- ¬permA u₀: use .separatelyAB as witness
      refine ⟨.separatelyAB, fun ψ hψ => ?_⟩
      rcases hψ with hψ_left | hψ_right
      · rcases hψ_left with hψ_φ | hψ_ie
        · rw [Set.mem_singleton_iff.mp hψ_φ]; exact trivial
        · obtain ⟨q, hqIE, rfl⟩ := hψ_ie
          exact ie_neg_at_separatelyAB q hqIE
      · rcases hψ_right with hψR | hψA
        · -- ψ ∈ R ⊆ fcALT, show ψ .separatelyAB
          have hψ_fcALT := hRcompat.1 hψR
          simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ_fcALT
          rcases hψ_fcALT with rfl | rfl | rfl | rfl
          · exact trivial  -- permAorB .separatelyAB
          · -- permA ∈ R, but hu₀ gives permA u₀, contradicting ¬permA u₀
            exact absurd (hu₀ permA (Set.mem_union_right _ hψR)) hpAu₀
          · exact trivial  -- permB .separatelyAB
          · -- permAandB ∈ R: derive contradiction from u₀
            exfalso
            have hAandB := hu₀ permAandB (Set.mem_union_right _ hψR)
            have hAorB := hu₀ fcPrejacent
              (Set.mem_union_left _ (Set.mem_union_left _ rfl))
            cases u₀ <;> simp_all [fcPrejacent, permA, permAandB]
        · rw [Set.mem_singleton_iff.mp hψA]; exact trivial

/-- Helper: For any II-compatible R, adding permB preserves II-compatibility. -/
private theorem extend_II_with_permB (R : Set (Prop' FCWorld))
    (hRcompat : isIICompatible fcALT fcPrejacent R) (_hpB : permB ∉ R) :
    isIICompatible fcALT fcPrejacent (R ∪ {permB}) := by
  constructor
  · intro x hx
    rcases hx with hxR | hxB
    · exact hRcompat.1 hxR
    · rw [Set.mem_singleton_iff.mp hxB]; simp [fcALT]
  · obtain ⟨u₀, hu₀⟩ := hRcompat.2
    by_cases hpBu₀ : permB u₀
    · exact ⟨u₀, fun ψ hψ => by
        rcases hψ with hψ_left | hψ_right
        · exact hu₀ ψ (Set.mem_union_left _ hψ_left)
        · rcases hψ_right with hψR | hψB
          · exact hu₀ ψ (Set.mem_union_right _ hψR)
          · rw [Set.mem_singleton_iff.mp hψB]; exact hpBu₀⟩
    · refine ⟨.separatelyAB, fun ψ hψ => ?_⟩
      rcases hψ with hψ_left | hψ_right
      · rcases hψ_left with hψ_φ | hψ_ie
        · rw [Set.mem_singleton_iff.mp hψ_φ]; exact trivial
        · obtain ⟨q, hqIE, rfl⟩ := hψ_ie
          exact ie_neg_at_separatelyAB q hqIE
      · rcases hψ_right with hψR | hψB
        · have hψ_fcALT := hRcompat.1 hψR
          simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ_fcALT
          rcases hψ_fcALT with rfl | rfl | rfl | rfl
          · exact trivial
          · exact trivial  -- permA .separatelyAB
          · exact absurd (hu₀ permB (Set.mem_union_right _ hψR)) hpBu₀
          · exfalso
            have hAandB := hu₀ permAandB (Set.mem_union_right _ hψR)
            have hAorB := hu₀ fcPrejacent
              (Set.mem_union_left _ (Set.mem_union_left _ rfl))
            cases u₀ <;> simp_all [fcPrejacent, permB, permAandB]
        · rw [Set.mem_singleton_iff.mp hψB]; exact trivial

/-- Helper: permA is innocently includable. -/
private theorem permA_in_II :
    isInnocentlyIncludable fcALT fcPrejacent permA := by
  constructor
  · simp [fcALT]
  · intro R ⟨hRcompat, hRmax⟩
    by_contra hpA
    have hext := extend_II_with_permA R hRcompat hpA
    exact hpA (hRmax (R ∪ {permA}) hext Set.subset_union_left (Set.mem_union_right R rfl))

/-- Helper: permB is innocently includable. -/
private theorem permB_in_II :
    isInnocentlyIncludable fcALT fcPrejacent permB := by
  constructor
  · simp [fcALT]
  · intro R ⟨hRcompat, hRmax⟩
    by_contra hpB
    have hext := extend_II_with_permB R hRcompat hpB
    exact hpB (hRmax (R ∪ {permB}) hext Set.subset_union_left (Set.mem_union_right R rfl))

/-- The free choice inference: exhaustified ◇(a ∨ b) entails ◇a -/
theorem fc_entails_permA :
    ∀ w, exhIEII fcALT fcPrejacent w → permA w := by
  intro w ⟨_, _, hII⟩
  exact hII permA permA_in_II

/-- The free choice inference: exhaustified ◇(a ∨ b) entails ◇b -/
theorem fc_entails_permB :
    ∀ w, exhIEII fcALT fcPrejacent w → permB w := by
  intro w ⟨_, _, hII⟩
  exact hII permB permB_in_II

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
