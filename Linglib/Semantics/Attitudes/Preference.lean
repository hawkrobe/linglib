module

public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Data.Set.Lattice.Bounded
public import Linglib.Core.Order.Minimals

/-!
# Preference structures

A preference structure, in the sense of Condoravdi and Lauer, is a set of propositions with a
strict ranking by importance. *Want* relates an agent to the maximal elements of the structure
its context supplies. A structure is consistent with an information state when any family of its
preferences that the information rules out jointly contains a strictly ranked pair, and realistic
when each preference is compatible with the information. Consistency entails realism and makes
the maximal preferences jointly realizable. The maximal preferences also order worlds, as an
ordering source does for Kratzer.

## Main definitions

* `PreferenceStructure`, with `maxElts`, `Consistent` and `Realistic`.
* `PreferenceStructure.maxPreorder`, `PreferenceStructure.best`: the world order of the maximal
  preferences and its best worlds.
* `PreferenceStructure.discrete`: the unranked structure on a set of preferences.

## Main statements

* `PreferenceStructure.Consistent.realistic`: consistency entails realism.
* `PreferenceStructure.Consistent.inter_sInter_maxElts_nonempty`: the maximal preferences of a
  consistent structure are jointly compatible with the information.
* `PreferenceStructure.consistent_of_realistic_of_isChain`: a realistic chain is consistent.

## Implementation notes

The ranking is a strict order on all of `Set W`, of which only its restriction to the preferences
is observed.

## References

* [condoravdi-lauer-2011]
* [condoravdi-lauer-2012]
* [condoravdi-lauer-2016]
* [lauer-2013]
* [kratzer-1981]
-/

@[expose] public section

variable {W : Type*}

/-- A preference structure is a set of propositions `prefs` with a strict ranking `prec`, where
`prec p q` reads "`q` is strictly preferred to `p`". The ranking is a relation on all of `Set W`,
and only its restriction to `prefs` is ever observed. -/
structure PreferenceStructure (W : Type*) where
  /-- The propositions the agent has preferences over. -/
  prefs : Set (Set W)
  /-- The strict ranking. `prec p q` reads "q is strictly preferred
      to p". -/
  prec : Set W → Set W → Prop
  /-- The strict-partial-order axioms, packaged as a mathlib typeclass. -/
  isStrictOrder : IsStrictOrder (Set W) prec

namespace PreferenceStructure

variable (P : PreferenceStructure W)

instance : IsStrictOrder (Set W) P.prec := P.isStrictOrder

/-- The maximal elements of the preference structure are the preferences with nothing in `prefs`
strictly above them. -/
def maxElts : Set (Set W) :=
  {p ∈ P.prefs | ∀ q ∈ P.prefs, ¬ P.prec p q}

@[simp] theorem mem_maxElts {φ : Set W} :
    φ ∈ P.maxElts ↔ φ ∈ P.prefs ∧ ∀ q ∈ P.prefs, ¬ P.prec φ q :=
  Iff.rfl

theorem maxElts_subset_prefs : P.maxElts ⊆ P.prefs := fun _ h ↦ h.1

/-- A preference structure is consistent with respect to an information state `B` when any subfamily
of preferences whose joint realization is incompatible with `B` contains a strictly ranked pair. -/
def Consistent (B : Set W) : Prop :=
  ∀ X ⊆ P.prefs, B ∩ ⋂₀ X = ∅ → ∃ p ∈ X, ∃ q ∈ X, P.prec p q

/-- A preference structure is realistic with respect to an information state when every preference
is compatible with it. -/
def Realistic (B : Set W) : Prop :=
  ∀ p ∈ P.prefs, p ∩ B ≠ ∅

section Consistent

variable {P} {B : Set W}

/-- Realism follows from consistency via the singleton-`X` case combined
    with irreflexivity. -/
theorem Consistent.realistic (hC : P.Consistent B) : P.Realistic B := by
  intro p hp hpB
  obtain ⟨_, rfl, _, rfl, hqr⟩ := hC {p} (Set.singleton_subset_iff.2 hp)
    (by rw [Set.sInter_singleton, Set.inter_comm]; exact hpB)
  exact irrefl_of P.prec _ hqr

/-- A consistent structure has a nonempty information state, as the empty subfamily shows. -/
theorem Consistent.nonempty (hC : P.Consistent B) : B.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h ↦
    let ⟨_, hp, _⟩ := hC ∅ (Set.empty_subset _) (by rw [Set.sInter_empty, Set.inter_univ]; exact h)
    hp

/-- A preference incompatible with a maximal one is ranked strictly below it. -/
theorem Consistent.prec_of_mem_maxElts (hC : P.Consistent B) {p q : Set W} (hp : p ∈ P.maxElts)
    (hq : q ∈ P.prefs) (h : B ∩ (p ∩ q) = ∅) : P.prec q p := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hC {p, q}
    (Set.insert_subset hp.1 (Set.singleton_subset_iff.2 hq)) (by rwa [Set.sInter_pair])
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  exacts [absurd hxy (irrefl_of P.prec _), absurd hxy (hp.2 _ hq), hxy,
    absurd hxy (irrefl_of P.prec _)]

/-- The maximal preferences of a consistent structure are jointly belief-compatible. -/
theorem Consistent.inter_sInter_maxElts_nonempty (hC : P.Consistent B) :
    (B ∩ ⋂₀ P.maxElts).Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h ↦
    let ⟨_, hp, _, hq, hpq⟩ := hC _ P.maxElts_subset_prefs h
    hp.2 _ hq.1 hpq

/-- Two maximal preferences of a consistent structure are jointly belief-compatible, which blocks
conflicting desires. -/
theorem Consistent.inter_inter_nonempty_of_mem_maxElts (hC : P.Consistent B) {φ ψ : Set W}
    (hφ : φ ∈ P.maxElts) (hψ : ψ ∈ P.maxElts) : (B ∩ (φ ∩ ψ)).Nonempty :=
  hC.inter_sInter_maxElts_nonempty.mono <| Set.inter_subset_inter_right _ <|
    Set.subset_inter (Set.sInter_subset_of_mem hφ) (Set.sInter_subset_of_mem hψ)

/-- A chain of realistic preferences is consistent. -/
theorem consistent_of_realistic_of_isChain (hR : P.Realistic B) (hc : IsChain P.prec P.prefs)
    (hB : B.Nonempty) : P.Consistent B := by
  intro X hX hXB
  by_contra h
  have hs : X.Subsingleton := fun p hp q hq ↦
    by_contra fun hne ↦ (hc (hX hp) (hX hq) hne).elim (fun hpq ↦ h ⟨p, hp, q, hq, hpq⟩)
      (fun hqp ↦ h ⟨q, hq, p, hp, hqp⟩)
  rcases hs.eq_empty_or_singleton with rfl | ⟨p, rfl⟩
  · rw [Set.sInter_empty, Set.inter_univ] at hXB
    exact hB.ne_empty hXB
  · rw [Set.sInter_singleton, Set.inter_comm] at hXB
    exact hR p (hX (Set.mem_singleton p)) hXB

end Consistent

/-! ### The world preorder induced by maximal preferences -/

/-- The world preorder induced by the maximal preferences ranks `w` below `v` when `w` verifies
every maximal preference that `v` verifies. It is the ordering-source construction with `maxElts` as
the source. -/
@[reducible] def maxPreorder : Preorder W := Preorder.ofCriteria (· ∈ ·) P.maxElts

theorem maxPreorder_le_iff {w v : W} :
    P.maxPreorder.le w v ↔ ∀ p ∈ P.maxElts, v ∈ p → w ∈ p :=
  Iff.rfl

/-- The worlds of `F` that best realize the maximal preferences. -/
def best (F : Set W) : Set W := P.maxPreorder.minimals F

/-- When some world of `F` realizes every maximal preference, the best worlds of `F` are
    exactly those. -/
theorem best_eq_of_nonempty {F : Set W} (h : (F ∩ ⋂₀ P.maxElts).Nonempty) :
    P.best F = F ∩ ⋂₀ P.maxElts :=
  Preorder.minimals_ofCriteria_eq h

/-! ### Unranked preferences -/

/-- The discrete structure has the preferences `S` and no ranking, so every preference is maximal.
-/
def discrete (S : Set (Set W)) : PreferenceStructure W where
  prefs := S
  prec _ _ := False
  isStrictOrder := { irrefl := fun _ h ↦ h, trans := fun _ _ _ h _ ↦ h }

@[simp] theorem maxElts_discrete (S : Set (Set W)) : (discrete S).maxElts = S :=
  Set.ext fun _ ↦ ⟨And.left, fun h ↦ ⟨h, fun _ _ h ↦ h⟩⟩

/-- Unranked preferences are consistent when jointly belief-compatible. -/
theorem consistent_discrete {S : Set (Set W)} {B : Set W} (h : (B ∩ ⋂₀ S).Nonempty) :
    (discrete S).Consistent B := fun _ hX hXB ↦
  absurd hXB (h.mono (Set.inter_subset_inter_right _ (Set.sInter_subset_sInter hX))).ne_empty

/-- The structure with the single preference `p`. -/
abbrev single (p : Set W) : PreferenceStructure W := discrete {p}

@[simp] theorem maxElts_single (p : Set W) : (single p).maxElts = {p} := maxElts_discrete _

theorem consistent_single {p B : Set W} (h : (p ∩ B).Nonempty) : (single p).Consistent B :=
  consistent_discrete (by rwa [Set.sInter_singleton, Set.inter_comm])

end PreferenceStructure
