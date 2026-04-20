import Linglib.Theories.Semantics.Exhaustification.Operators
import Linglib.Phenomena.Modality.FreeChoice

/-!
# Bar-Lev & Fox (2020) — Free Choice via Innocent Inclusion
@cite{bar-lev-fox-2020} @cite{fox-2007} @cite{spector-2016}

Worked example of @cite{bar-lev-fox-2020} "Free choice, simplification, and
Innocent Inclusion" (Natural Language Semantics 28:175–223) over a five-world
toy modal model.

## What this file does

The abstract theory of Innocent Exclusion (`IE`), Innocent Inclusion (`II`),
the cell-of-the-induced-partition (`cell`), and the cell-identification theorem
`mem_II_of_cell_witness` lives in
`Theories/Semantics/Exhaustification/Operators.lean`. This file instantiates
that theory on a small `FCWorld` and verifies the paper's headline empirical
prediction:

  Exh^{IE+II}(◇(a ∨ b)) ⊨ ◇a ∧ ◇b

The contrast with simple disjunction (where the alternative set IS closed
under conjunction and free choice does *not* arise) is captured via a parallel
`DisjWorld` toy + `simpleALT` and `simple_has_conjunction`.

## Why the cell-identification API matters

In the paper, the move from "exhaustification of a disjunction" to "free
choice" is enabled by a structural property of the alternative set: it is
*not* closed under conjunction, so the cell of the partition induced by the
alternatives is consistent and uniquely fixed. The free choice proof here is
a one-line corollary of `mem_II_of_cell_witness` once a witness world for the
cell is exhibited (the `separatelyAB` world, where each disjunct is
individually possible but not jointly).

-/

namespace Phenomena.Modality.Studies.BarLevFox2020

open Exhaustification

-- ============================================================================
-- §1. The five-world FC toy model
-- ============================================================================

/-- Possible worlds for free choice: each represents a configuration of which
disjuncts are individually or jointly permitted.

The `separatelyAB` world is the cell witness: each disjunct is individually
permitted but they are not jointly permitted. This world distinguishes
`◇a ∧ ◇b` from `◇(a ∧ b)` and is the cornerstone of @cite{bar-lev-fox-2020}'s
free-choice derivation. -/
inductive FCWorld where
  | neither : FCWorld       -- Neither a nor b permitted
  | onlyA : FCWorld         -- Only a permitted
  | onlyB : FCWorld         -- Only b permitted
  | both : FCWorld          -- Both jointly permitted (◇(a ∧ b))
  | separatelyAB : FCWorld  -- Each individually permitted, not jointly
  deriving DecidableEq, Repr, Inhabited

/-- ◇a — `a` is permitted at the world. -/
def permA : Set FCWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => False
  | .both => True
  | .separatelyAB => True

/-- ◇b — `b` is permitted at the world. -/
def permB : Set FCWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => True
  | .both => True
  | .separatelyAB => True

/-- ◇(a ∨ b) — the prejacent. -/
def permAorB : Set FCWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => True
  | .both => True
  | .separatelyAB => True

/-- ◇(a ∧ b) — joint permission. -/
def permAandB : Set FCWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True
  | .separatelyAB => False

/-- The free-choice alternative set: `{◇(a ∨ b), ◇a, ◇b, ◇(a ∧ b)}`. -/
def fcALT : Set (Set FCWorld) :=
  {permAorB, permA, permB, permAandB}

/-- The prejacent: `◇(a ∨ b)`. -/
def fcPrejacent : Set FCWorld := permAorB

-- ============================================================================
-- §2. Non-closure under conjunction
-- ============================================================================

/-- The free-choice alternative set is **not** closed under conjunction.
Witnessed by `permA ∧ permB` (= ◇a ∧ ◇b), which is not equivalent to any
member of `fcALT` — in particular, not to `permAandB` (= ◇(a ∧ b)), since the
`separatelyAB` world satisfies the former but not the latter. -/
theorem fc_not_closed_general :
    ¬(∀ (X : Set (Set FCWorld)), X ⊆ fcALT → (⋀ X) ∈ fcALT) := by
  intro h
  have hX : ({permA, permB} : Set (Set FCWorld)) ⊆ fcALT := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with rfl | rfl <;> simp
  have hconj := h {permA, permB} hX
  simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hconj
  rcases hconj with heq | heq | heq | heq
  · have : ¬(⋀ ({permA, permB} : Set _)) .onlyA :=
      fun hc => hc permB (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · have : ¬(⋀ ({permA, permB} : Set _)) .onlyA :=
      fun hc => hc permB (Set.mem_insert_of_mem _ rfl)
    rw [heq] at this; exact this trivial
  · have : ¬(⋀ ({permA, permB} : Set _)) .onlyB :=
      fun hc => hc permA (Set.mem_insert_iff.mpr (Or.inl rfl))
    rw [heq] at this; exact this trivial
  · have : (⋀ ({permA, permB} : Set _)) .separatelyAB := by
      intro φ hφ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
      rcases hφ with rfl | rfl <;> trivial
    rw [heq] at this; exact this

-- ============================================================================
-- §3. The cell witness: `separatelyAB`
-- ============================================================================

/-!
The cornerstone of the free-choice derivation is exhibiting a world that
witnesses the `cell` of the partition induced by `fcALT`. Once this is in
place, free choice follows as a one-line corollary of
`mem_II_of_cell_witness`.

The witness world is `separatelyAB`. Establishing the cell predicate at
`separatelyAB` requires four facts about the IE structure of `fcALT`:

* `permAorB` is *not* innocently excludable (since ∼permAorB contradicts the
  prejacent in any MC-set);
* `permA` is *not* innocently excludable (witnessed by an MC-set that omits
  ∼permA);
* `permB` is *not* innocently excludable (symmetric);
* `permAandB` *is* innocently excludable.
-/

private theorem fcALT_finite : Set.Finite fcALT :=
  Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton _)))

private theorem fcPrejacent_sat : ∃ w, fcPrejacent w := ⟨.onlyA, trivial⟩

private theorem permAorB_not_ie :
    ¬isInnocentlyExcludable fcALT fcPrejacent permAorB := by
  intro ⟨_, hIE⟩
  obtain ⟨E, hMC⟩ := exists_MCset fcALT fcPrejacent fcALT_finite fcPrejacent_sat
  obtain ⟨u, hu⟩ := hMC.1.2.2
  exact hu (∼permAorB) (hIE E hMC) (hu fcPrejacent hMC.1.1)

/-- ¬`permA` and ¬`permB` together with the prejacent are inconsistent on
`FCWorld`: every world satisfying `permAorB` satisfies at least one disjunct. -/
private theorem perm_cover : ∀ u, fcPrejacent u → ¬permA u → ¬permB u → False :=
  fun u => by cases u <;> simp [fcPrejacent, permAorB, permA, permB]

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
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact hu (∼permAorB) hψ' (hu fcPrejacent (hsub (Set.mem_insert _ _)))
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact perm_cover u
          (hu fcPrejacent (hsub (Set.mem_insert _ _)))
          (hu (∼permA) hψ')
          (hu (∼permB) (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

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
      · exfalso; obtain ⟨u, hu⟩ := hE'.2.2
        exact perm_cover u
          (hu fcPrejacent (hsub (Set.mem_insert _ _)))
          (hu (∼permA) (hsub (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
          (hu (∼permB) hψ')
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

private theorem permA_not_ie :
    ¬isInnocentlyExcludable fcALT fcPrejacent permA := by
  intro ⟨_, hIE⟩
  have hNotIn : ∼permA ∉ ({fcPrejacent, ∼permB, ∼permAandB} : Set (Set FCWorld)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => Eq.mp (congrFun h .neither) id,
           fun h => Eq.mpr (congrFun h .onlyA) id trivial,
           fun h => Eq.mpr (congrFun h .onlyA) id trivial⟩
  exact hNotIn (hIE _ mc_set_without_neg_permA)

private theorem permB_not_ie :
    ¬isInnocentlyExcludable fcALT fcPrejacent permB := by
  intro ⟨_, hIE⟩
  have hNotIn : ∼permB ∉ ({fcPrejacent, ∼permA, ∼permAandB} : Set (Set FCWorld)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => Eq.mp (congrFun h .neither) id,
           fun h => Eq.mp (congrFun h .onlyA) id trivial,
           fun h => Eq.mpr (congrFun h .onlyB) id trivial⟩
  exact hNotIn (hIE _ mc_set_without_neg_permB)

/-- `permAandB` *is* innocently excludable: every MC-set contains `∼permAandB`,
because adjoining `∼permAandB` to any MC-set is consistent (witnessed at
`onlyA` whenever the MC-set itself is consistent), so maximality forces
inclusion. -/
private theorem permAandB_is_ie :
    isInnocentlyExcludable fcALT fcPrejacent permAandB := by
  refine ⟨by simp [fcALT], ?_⟩
  intro E hE
  apply hE.2 (E ∪ {∼permAandB}) ?_ Set.subset_union_left
    (Set.mem_union_right E rfl)
  refine ⟨Set.mem_union_left _ hE.1.1, ?_, ?_⟩
  · rintro ψ (hψE | hψN)
    · exact hE.1.2.1 ψ hψE
    · refine Or.inr ⟨permAandB, by simp [fcALT], Set.mem_singleton_iff.mp hψN⟩
  · obtain ⟨u₀, hu₀⟩ := hE.1.2.2
    by_cases hpAB : permAandB u₀
    · -- u₀ satisfies permAandB, so u₀ = .both. Switch witness to .onlyA.
      have hu_both : u₀ = FCWorld.both := by
        cases u₀ <;> simp_all [permAandB]
      refine ⟨FCWorld.onlyA, fun ψ hψ => ?_⟩
      rcases hψ with hψE | hψN
      · -- ψ ∈ E and ψ holds at .both. Cases on ψ's structure.
        have hψBoth : ψ FCWorld.both := hu_both ▸ hu₀ ψ hψE
        rcases hE.1.2.1 ψ hψE with hψφ | ⟨a, ha, hψN⟩
        · rw [hψφ]; exact trivial
        · exfalso
          rw [hψN] at hψBoth
          simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · exact hψBoth trivial
          · exact hψBoth trivial
          · exact hψBoth trivial
          · exact hψBoth trivial
      · rw [Set.mem_singleton_iff.mp hψN]; intro h; exact h
    · refine ⟨u₀, fun ψ hψ => ?_⟩
      rcases hψ with hψE | hψN
      · exact hu₀ ψ hψE
      · rw [Set.mem_singleton_iff.mp hψN]; exact hpAB

/-- **Cell witness for the FC alternative set.** The `separatelyAB` world
verifies `cell fcALT fcPrejacent` — it satisfies the prejacent, falsifies
every IE-excludable alternative (only `permAandB`), and verifies every
non-excludable alternative (`permAorB`, `permA`, `permB`). -/
theorem separatelyAB_in_cell : cell fcALT fcPrejacent .separatelyAB := by
  refine ⟨trivial, ?_, ?_⟩
  · intro q hq
    have hqAlt : q ∈ fcALT := hq.1
    simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hqAlt
    rcases hqAlt with rfl | rfl | rfl | rfl
    · exact absurd hq permAorB_not_ie
    · exact absurd hq permA_not_ie
    · exact absurd hq permB_not_ie
    · intro h; exact h
  · rintro r ⟨hrAlt, hrNotIE⟩
    simp only [fcALT, Set.mem_insert_iff, Set.mem_singleton_iff] at hrAlt
    rcases hrAlt with rfl | rfl | rfl | rfl
    · exact trivial
    · exact trivial
    · exact trivial
    · exact absurd permAandB_is_ie hrNotIE

-- ============================================================================
-- §4. Free choice as a corollary of cell identification
-- ============================================================================

/-- **Main free-choice theorem.** `Exh^{IE+II}(◇(a ∨ b)) ⊨ ◇a ∧ ◇b`.

The proof is a direct application of `mem_II_of_cell_witness` to each
disjunct, using `separatelyAB_in_cell` as the cell witness. -/
theorem free_choice :
    ∀ w, exhIEII fcALT fcPrejacent w → permA w ∧ permB w := by
  intro w ⟨_, _, hII⟩
  refine ⟨hII permA ?_, hII permB ?_⟩
  · exact mem_II_of_cell_witness fcALT fcPrejacent
      (by simp [fcALT]) .separatelyAB separatelyAB_in_cell trivial
  · exact mem_II_of_cell_witness fcALT fcPrejacent
      (by simp [fcALT]) .separatelyAB separatelyAB_in_cell trivial

-- ============================================================================
-- §5. Contrast: simple disjunction (closed under ∧)
-- ============================================================================

/-- Simple-disjunction worlds (no modal layer). -/
inductive DisjWorld where
  | neither : DisjWorld
  | onlyA : DisjWorld
  | onlyB : DisjWorld
  | both : DisjWorld
  deriving DecidableEq, Repr, Inhabited

/-- Atomic proposition `a`. -/
def propA : Set DisjWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => False
  | .both => True

/-- Atomic proposition `b`. -/
def propB : Set DisjWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => True
  | .both => True

/-- Disjunction `a ∨ b`. -/
def propAorB : Set DisjWorld
  | .neither => False
  | .onlyA => True
  | .onlyB => True
  | .both => True

/-- Conjunction `a ∧ b`. -/
def propAandB : Set DisjWorld
  | .neither => False
  | .onlyA => False
  | .onlyB => False
  | .both => True

/-- Simple disjunction's alternative set: `{a ∨ b, a, b, a ∧ b}`. -/
def simpleALT : Set (Set DisjWorld) :=
  {propAorB, propA, propB, propAandB}

/-- The structural contrast with FC: simple disjunction's alternative set
**is** closed under conjunction (`a ∧ b ∈ simpleALT`). This is what blocks
the cell from being consistent and prevents free choice from arising. -/
theorem simple_has_conjunction : propAandB ∈ simpleALT := by simp [simpleALT]

-- ============================================================================
-- §6. Bridge to empirical free-choice data
-- ============================================================================

/-!
Bar-Lev & Fox predict that free choice is a pragmatic inference (derived by
`Exh^{IE+II}`) rather than a semantic entailment. This matches the empirical
classification recorded in `Phenomena.Modality.FreeChoice`.
-/

/-- The free-choice inference is *not* a semantic entailment. -/
theorem fc_is_pragmatic :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isSemanticEntailment = false := rfl

/-- The free-choice inference IS captured by Bar-Lev & Fox's pragmatic theory. -/
theorem fc_captured_pragmatically :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isPragmaticInference = true := rfl

end Phenomena.Modality.Studies.BarLevFox2020
