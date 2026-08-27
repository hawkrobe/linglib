import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Linglib.Logic.Modal.Basic

/-!
# Domain alternatives of a modalized existential

This file defines the modal profile of an existential claim `∃ x ∈ D, Q x` evaluated under
a Kripke accessibility relation, and the subdomain alternatives whose exhaustification
strengthens it. `FreeChoice` holds when every member of the domain is a witness in some
accessible world and `ModalVariation` when the witnesses vary across the accessible worlds;
`subdomainAlternatives` lists the subdomains an item competes with — every nonempty proper subdomain
for a domain widener, the singletons for an anti-singleton item — and `AntiExhaustivity S`
is the negation of the pre-exhaustified alternative for `S`: if `S` is possible, so is the
rest of the domain. Negating the pre-exhaustified singleton alternatives yields Modal
Variation and negating all proper ones yields Free Choice.

## Main definitions

* `claim`, `witnesses` — the existential over a subdomain and its
  witnesses at a world.
* `FreeChoice`, `ModalVariation`, `Uniqueness` — the modal
  components.
* `subdomainAlternatives` — the singleton or proper subdomain alternatives.
* `AntiExhaustivity` — the negated pre-exhaustified alternative.

## References

* [kratzer-shimoyama-2002]
* [alonso-ovalle-menendez-benito-2010]
* [chierchia-2013]
-/

namespace Exhaustification

open ModalLogic

variable {W E : Type*} (R : W → W → Prop) (w : W) (D : Finset E) (Q : W → E → Prop)

/-- The existential claim over the subdomain `S`: some member of `S` is a witness. -/
def claim (S : Finset E) (v : W) : Prop := ∃ x ∈ S, Q v x

/-- Free Choice: every member of the domain is a witness in some accessible world. -/
def FreeChoice : Prop := ∀ x ∈ D, ◇[R] (Q · x) w

section Witnesses

variable [∀ v, DecidablePred (Q v)]

/-- The witnesses of the existential claim at `v`. -/
def witnesses (v : W) : Finset E := D.filter (Q v ·)

/-- Modal Variation: the witnesses vary across the accessible worlds. -/
def ModalVariation : Prop := ∃ v, R w v ∧ ∃ v', R w v' ∧ witnesses D Q v ≠ witnesses D Q v'

/-- Uniqueness: at most one witness in each accessible world. -/
def Uniqueness : Prop := □[R] (fun v => (witnesses D Q v).card ≤ 1) w

theorem claim_iff_witnesses_nonempty (v : W) :
    claim Q D v ↔ (witnesses D Q v).Nonempty := by
  simp [claim, witnesses, Finset.Nonempty]

/-- Two distinct possibilities give Modal Variation under uniqueness. -/
theorem modalVariation_of_two (hU : Uniqueness R w D Q) {a b : E} (ha : a ∈ D) (hb : b ∈ D)
    (hab : a ≠ b) (pa : ◇[R] (Q · a) w) (pb : ◇[R] (Q · b) w) : ModalVariation R w D Q := by
  obtain ⟨v, hv, hqa⟩ := pa
  obtain ⟨v', hv', hqb⟩ := pb
  refine ⟨v, hv, v', hv', fun h => ?_⟩
  have hb' : b ∈ witnesses D Q v := h ▸ Finset.mem_filter.2 ⟨hb, hqb⟩
  exact hab (Finset.card_le_one.1 (hU v hv) a (Finset.mem_filter.2 ⟨ha, hqa⟩) b hb')

/-- Under uniqueness, Free Choice on a domain with two members entails Modal Variation. -/
theorem modalVariation_of_freeChoice (hU : Uniqueness R w D Q) (hD : 1 < D.card)
    (h : FreeChoice R w D Q) : ModalVariation R w D Q :=
  let ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hD
  modalVariation_of_two R w D Q hU ha hb hab (h a ha) (h b hb)

/-- Modal Variation fails when no accessible world has a witness. -/
theorem not_modalVariation_of_box_empty (h : □[R] (fun v => witnesses D Q v = ∅) w) :
    ¬ ModalVariation R w D Q :=
  fun ⟨v, hv, v', hv', hne⟩ => hne ((h v hv).trans (h v' hv').symm)

end Witnesses

/-! ### Subdomain alternatives -/

/-- Which subdomains of the domain an item competes with. -/
inductive Subdomains
  /-- Every nonempty proper subdomain, for a domain widener. -/
  | proper
  /-- The singleton subdomains, for an anti-singleton item. -/
  | singletons
  deriving DecidableEq

variable [DecidableEq E]

/-- The subdomain alternatives of `D`. -/
def subdomainAlternatives : Subdomains → Finset E → Finset (Finset E)
  | .singletons, D => D.image ({·})
  | .proper, D => D.powerset.filter fun S => S.Nonempty ∧ S ≠ D

/-- The singleton alternatives are among the proper ones. -/
theorem subdomainAlternatives_singletons_subset (hD : 1 < D.card) :
    subdomainAlternatives .singletons D ⊆ subdomainAlternatives .proper D := by
  intro S hS
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hS
  refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 ha),
    Finset.singleton_nonempty a, fun h => ?_⟩
  simp [← h] at hD

/-- The negated pre-exhaustified alternative for `S`: if `S` is possible, so is the rest
of the domain. -/
def AntiExhaustivity (S : Finset E) : Prop :=
  ◇[R] (claim Q S) w → ◇[R] (claim Q (D \ S)) w

/-- Under a possibility modal the claim entails one of its singleton alternatives. -/
theorem exists_singleton_of_diamond (h : ◇[R] (claim Q D) w) :
    ∃ S ∈ subdomainAlternatives .singletons D, ◇[R] (claim Q S) w :=
  let ⟨v, hv, a, ha, hqa⟩ := h
  ⟨{a}, Finset.mem_image_of_mem _ ha, v, hv, a, Finset.mem_singleton_self a, hqa⟩

/-- Negating the pre-exhaustified singleton alternatives makes at least two members
possibilities. -/
theorem two_of_singletons (h : ◇[R] (claim Q D) w)
    (hs : ∀ S ∈ subdomainAlternatives .singletons D, AntiExhaustivity R w D Q S) :
    ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ ◇[R] (Q · a) w ∧ ◇[R] (Q · b) w := by
  obtain ⟨v, hv, a, ha, hqa⟩ := h
  obtain ⟨v', hv', b, hb, hqb⟩ :=
    hs {a} (Finset.mem_image_of_mem _ ha) ⟨v, hv, a, Finset.mem_singleton_self a, hqa⟩
  obtain ⟨hbD, hba⟩ := Finset.mem_sdiff.1 hb
  exact ⟨a, ha, b, hbD, fun h => hba (h ▸ Finset.mem_singleton_self a), ⟨v, hv, hqa⟩,
    ⟨v', hv', hqb⟩⟩

/-- Under uniqueness, negating the pre-exhaustified singleton alternatives yields Modal
Variation. -/
theorem modalVariation_of_singletons [∀ v, DecidablePred (Q v)] (hU : Uniqueness R w D Q)
    (h : ◇[R] (claim Q D) w)
    (hs : ∀ S ∈ subdomainAlternatives .singletons D, AntiExhaustivity R w D Q S) :
    ModalVariation R w D Q :=
  let ⟨_, ha, _, hb, hab, pa, pb⟩ := two_of_singletons R w D Q h hs
  modalVariation_of_two R w D Q hU ha hb hab pa pb

/-- Under a necessity modal, a true claim whose singleton alternatives are all false shows
Modal Variation. -/
theorem modalVariation_of_box [∀ v, DecidablePred (Q v)] (hw : ∃ v, R w v)
    (h : □[R] (claim Q D) w)
    (hc : ∀ S ∈ subdomainAlternatives .singletons D, ¬ □[R] (claim Q S) w) :
    ModalVariation R w D Q := by
  obtain ⟨v, hv⟩ := hw
  obtain ⟨a, ha, hqa⟩ := h v hv
  have := hc {a} (Finset.mem_image_of_mem _ ha)
  simp only [box, claim, Finset.mem_singleton, exists_eq_left, not_forall] at this
  obtain ⟨v', hv', hna⟩ := this
  exact ⟨v, hv, v', hv', fun h =>
    hna (Finset.mem_filter.1 (h ▸ Finset.mem_filter.2 ⟨ha, hqa⟩ : a ∈ witnesses D Q v')).2⟩

/-- Negating every pre-exhaustified proper alternative yields Free Choice. -/
theorem freeChoice_of_proper (h : ◇[R] (claim Q D) w)
    (hs : ∀ S ∈ subdomainAlternatives .proper D, AntiExhaustivity R w D Q S) :
    FreeChoice R w D Q := by
  intro a ha
  by_contra hna
  obtain ⟨v, hv, x, hx, hqx⟩ := h
  have hxa : x ≠ a := fun h => hna ⟨v, hv, h ▸ hqx⟩
  have hS : D.erase a ∈ subdomainAlternatives .proper D := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.erase_subset a D),
      ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩⟩, fun h => ?_⟩
    exact Finset.notMem_erase a D (by rw [h]; exact ha)
  obtain ⟨v', hv', y, hy, hqy⟩ := hs _ hS ⟨v, hv, x, Finset.mem_erase.2 ⟨hxa, hx⟩, hqx⟩
  obtain ⟨-, hy'⟩ := Finset.mem_sdiff.1 hy
  have : y = a := by
    by_contra hya
    exact hy' (Finset.mem_erase.2 ⟨hya, (Finset.mem_sdiff.1 hy).1⟩)
  exact hna ⟨v', hv', this ▸ hqy⟩

/-! ### Decidability -/

section Decidable

variable [Fintype W] [DecidableRel R] [∀ v, DecidablePred (Q v)]

instance (S : Finset E) (v : W) : Decidable (claim Q S v) :=
  inferInstanceAs (Decidable (∃ x ∈ S, _))

instance : Decidable (FreeChoice R w D Q) := inferInstanceAs (Decidable (∀ x ∈ D, _))

instance [DecidableEq W] : Decidable (ModalVariation R w D Q) :=
  inferInstanceAs (Decidable (∃ v, R w v ∧ ∃ v', R w v' ∧ _ ≠ _))

instance : Decidable (Uniqueness R w D Q) := inferInstanceAs (Decidable (□[R] _ w))

instance (S : Finset E) : Decidable (AntiExhaustivity R w D Q S) :=
  inferInstanceAs (Decidable (_ → _))

end Decidable

end Exhaustification
