module

public import Linglib.Logic.Aristotelian.Morphism
public import Linglib.Logic.Aristotelian.Partition
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Bitstring semantics of a fragment

Every element of the Boolean closure of a fragment `φ : ι → α` is the join of the parts of the
partition `φ` induces that lie below it. Sending an element to the set of those parts is therefore
an order isomorphism from the closure onto the powerset of the parts. Demey and Smessaert write
the set as a bitstring with one bit per part, and the isomorphism carries the fragment to an
Aristotelian diagram of bitstrings. Two fragments have isomorphic closures iff their partitions
have the same number of parts.

## Main definitions

* `Aristotelian.bitstring`: the isomorphism from the closure onto the powerset of the parts.
* `Aristotelian.AristotelianIso.bitstring`: the fragment and its bitstrings are Aristotelian
  isomorphic.

## Main results

* `Aristotelian.anchor_le_or_le_compl`: an anchor lies below each element of the closure or
  below its complement.
* `Aristotelian.card_closure`: the closure of a fragment whose partition has `n` parts has `2 ^ n`
  elements.
* `Aristotelian.isAtom_iff_mem_parts`: the atoms of the closure are the parts.
* `Aristotelian.nonempty_orderIso_closure_iff`: two fragments have isomorphic closures iff their
  partitions have equally many parts.

## Implementation notes

Demey and Smessaert number the parts and write the set of parts below an element as a string of
bits; `bitstring` keeps the set. Their Lemma 9, that the bitstring of a part has a single bit
set, appears as `isAtom_iff_mem_parts`, since the atoms of a powerset are its singletons. Their
Theorem 2 follows from Theorem 1 through the Boolean-to-Aristotelian lemma; here it is proved
directly from `bitstring`.

## References

* [demey-smessaert-2018]
* [demey-smessaert-2024]
-/

@[expose] public section

namespace Aristotelian

open Finset BooleanSubalgebra

variable {α ι : Type*} [BooleanAlgebra α] [Fintype ι] {φ : ι → α}

theorem anchor_mem_closure (σ : ι → Bool) : anchor φ σ ∈ closure (Set.range φ) :=
  inf_induction top_mem (fun _ h _ h' ↦ inf_mem h h') fun i _ ↦ by
    have h := subset_closure (s := Set.range φ) ⟨i, rfl⟩
    split
    exacts [h, compl_mem h]

/-- An anchor lies below each element of the closure or below its complement
([demey-smessaert-2018] Lemma 6). -/
theorem anchor_le_or_le_compl {ψ : α} (hψ : ψ ∈ closure (Set.range φ)) (σ : ι → Bool) :
    anchor φ σ ≤ ψ ∨ anchor φ σ ≤ ψᶜ := by
  induction hψ using closure_bot_sup_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    cases hσ : σ i
    exacts [.inr (anchor_le_compl_of_false hσ), .inl (anchor_le_of_true hσ)]
  | bot => exact .inr (by simp)
  | sup x _ y _ ihx ihy =>
    rcases ihx with hx | hx
    · exact .inl (hx.trans le_sup_left)
    rcases ihy with hy | hy
    · exact .inl (hy.trans le_sup_right)
    · exact .inr (compl_sup (a := x) ▸ le_inf hx hy)
  | compl x _ ih => exact ih.symm.imp id fun h ↦ (compl_compl x).symm ▸ h

variable [DecidableEq ι] [DecidableEq α]

theorem le_or_disjoint_of_mem_parts {ψ a : α} (hψ : ψ ∈ closure (Set.range φ))
    (ha : a ∈ (partition φ).parts) : a ≤ ψ ∨ Disjoint a ψ := by
  obtain ⟨-, σ, rfl⟩ := mem_partition_parts.1 ha
  exact (anchor_le_or_le_compl hψ σ).imp_right le_compl_iff_disjoint_right.1

/-- An element of the closure lies below `ψ₂` iff every part below it does, since it is the join
of the parts below it ([demey-smessaert-2018] Lemma 7). -/
theorem le_iff_forall_mem_parts {ψ₁ ψ₂ : α} (h₁ : ψ₁ ∈ closure (Set.range φ)) :
    ψ₁ ≤ ψ₂ ↔ ∀ a ∈ (partition φ).parts, a ≤ ψ₁ → a ≤ ψ₂ := by
  refine ⟨fun h a _ ha ↦ ha.trans h, fun h ↦ ?_⟩
  have hsup : (partition φ).parts.sup (· ⊓ ψ₁) = ψ₁ := by
    rw [← sup_inf_distrib_right]
    exact (congrArg (· ⊓ ψ₁) (partition φ).sup_parts).trans (top_inf_eq ψ₁)
  rw [← hsup]
  refine Finset.sup_le fun a ha ↦ ?_
  rcases le_or_disjoint_of_mem_parts h₁ ha with hle | hdis
  · exact inf_le_left.trans (h a ha hle)
  · simp [hdis.eq_bot]

theorem mem_closure_of_mem_parts {a : α} (ha : a ∈ (partition φ).parts) :
    a ∈ closure (Set.range φ) := by
  obtain ⟨-, σ, rfl⟩ := mem_partition_parts.1 ha
  exact anchor_mem_closure σ

variable (φ) in
/-- The bitstring of an element of the closure is the set of parts below it. This is an order
isomorphism onto the powerset of the parts ([demey-smessaert-2018] Theorem 1,
[demey-smessaert-2024] Definition 4). -/
noncomputable def bitstring : closure (Set.range φ) ≃o Set (partition φ).parts :=
  .ofSurjective
    (OrderEmbedding.ofMapLEIff (fun ψ ↦ {a | a.1 ≤ ψ.1}) fun ψ₁ ψ₂ ↦ by
      rw [Subtype.mk_le_mk, le_iff_forall_mem_parts ψ₁.2]
      exact ⟨fun h a ha ↦ h (a := ⟨a, ha⟩), fun h a ↦ h a.1 a.2⟩)
    fun S ↦ by
      classical
      refine ⟨⟨(univ.filter (· ∈ S)).sup Subtype.val, sup_induction bot_mem
        (fun _ h _ h' ↦ sup_mem h h') fun a _ ↦ mem_closure_of_mem_parts a.2⟩, ?_⟩
      ext a
      refine ⟨fun h ↦ by_contra fun haS ↦ (partition φ).ne_bot a.2 ?_,
        fun h ↦ le_sup (by simpa using h)⟩
      refine le_bot_iff.1 ((le_inf le_rfl h).trans_eq ?_)
      rw [sup_inf_distrib_left]
      refine (Finset.sup_eq_bot_iff _ _).2 fun b hb ↦
        ((partition φ).disjoint a.2 b.2 fun hab ↦ ?_).eq_bot
      exact haS (Subtype.ext hab ▸ by simpa using hb)

@[simp] theorem mem_bitstring {ψ : closure (Set.range φ)} {a : (partition φ).parts} :
    a ∈ bitstring φ ψ ↔ a.1 ≤ ψ.1 :=
  .rfl

variable (φ) in
/-- The closure of a fragment has `2 ^ n` elements, where `n` is the number of parts of its
partition ([demey-smessaert-2018] Theorem 1). -/
theorem card_closure : Nat.card (closure (Set.range φ)) = 2 ^ #(partition φ).parts := by
  rw [Nat.card_congr (bitstring φ).toEquiv, Nat.card_eq_fintype_card, Fintype.card_set,
    Fintype.card_coe]

/-- The atoms of the closure are the parts ([demey-smessaert-2018] Lemma 9). -/
theorem isAtom_iff_mem_parts {ψ : closure (Set.range φ)} : IsAtom ψ ↔ ψ.1 ∈ (partition φ).parts
    where
  mp h := by
    obtain ⟨a, ha, haψ, ha0⟩ : ∃ a ∈ (partition φ).parts, a ≤ ψ.1 ∧ a ≠ ⊥ := by
      by_contra! hcon
      exact h.1 (Subtype.ext (le_bot_iff.1 ((le_iff_forall_mem_parts ψ.2).2 fun a ha h ↦
        (hcon a ha h).le)))
    have hb : (⟨a, mem_closure_of_mem_parts ha⟩ : closure (Set.range φ)) ≠ ⊥ :=
      fun h0 ↦ ha0 (congrArg Subtype.val h0)
    exact congrArg Subtype.val ((h.le_iff_eq hb).1 haψ) ▸ ha
  mpr h := ⟨fun h0 ↦ (partition φ).ne_bot h (congrArg Subtype.val h0), fun χ hχ ↦ by
    rcases le_or_disjoint_of_mem_parts χ.2 h with hle | hdis
    · exact absurd hle (not_le_of_gt hχ)
    · exact Subtype.ext (disjoint_self.1 (hdis.mono_left hχ.le))⟩

variable (φ) in
/-- The bitstrings of the elements of a fragment form an Aristotelian diagram isomorphic to it
([demey-smessaert-2018] Theorem 2). -/
noncomputable def AristotelianIso.bitstring :
    AristotelianIso φ fun i ↦ Aristotelian.bitstring φ (corner φ i) where
  toEquiv := .refl ι
  map_disjoint i j := (BooleanSubalgebra.disjoint_coe (a := corner φ i) (b := corner φ j)).trans
    (disjoint_map_orderIso_iff (Aristotelian.bitstring φ)).symm
  map_codisjoint i j :=
    (BooleanSubalgebra.codisjoint_coe (a := corner φ i) (b := corner φ j)).trans
      (codisjoint_map_orderIso_iff (Aristotelian.bitstring φ)).symm
  map_lt i j := (Subtype.coe_lt_coe (x := corner φ i) (y := corner φ j)).trans
    (Aristotelian.bitstring φ).lt_iff_lt.symm

variable {ι' α' : Type*} [BooleanAlgebra α'] [Fintype ι'] [DecidableEq ι'] [DecidableEq α']
  (ψ : ι' → α')

variable (φ) in
/-- Two fragments have order-isomorphic closures iff their partitions have equally many parts
([demey-smessaert-2024], on Givant and Halmos's classification of finite Boolean algebras). -/
theorem nonempty_orderIso_closure_iff :
    Nonempty (closure (Set.range φ) ≃o closure (Set.range ψ)) ↔
      #(partition φ).parts = #(partition ψ).parts where
  mp := fun ⟨e⟩ ↦ Nat.pow_right_injective le_rfl <| show 2 ^ _ = 2 ^ _ by
    rw [← card_closure, ← card_closure]; exact Nat.card_congr e.toEquiv
  mpr h := ⟨(bitstring φ).trans <| (Fintype.equivOfCardEq <| by
    rwa [Fintype.card_coe, Fintype.card_coe]).toOrderIsoSet.trans (bitstring ψ).symm⟩

end Aristotelian
