/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.List.Factors
import Linglib.Phonology.Autosegmental.NormalForm

/-!
# Factors and banned-subgraph grammars

[jardine-2017]'s connected-subgraph embedding in position coordinates: a factor
occurs at per-tier offsets when its tier words are windows of the host's and its
links transport shifted. Banned-subgraph grammars ([jardine-2016-diss] Ch. 5)
are lists of forbidden factors.

## Main definitions

* `AR.IsFactorAt`, `AR.FactorEmbeds`: factor occurrence at given offsets, and
  its existential closure.
* `AR.Free`: avoidance of every factor of a banned-subgraph grammar.

## Main results

* `AR.factorEmbeds_iff_bounded`: embedding is a bounded search over offsets.
* `AR.factorEmbeds_iff_infix_of_link_free`: for link-free factors, embedding is
  independent per-tier infix occurrence — [jardine-2019]'s link-free fragment.
-/

namespace Autosegmental

variable {ι : Type*} {τ : ι → Type*}
variable (F X : TieredAR ι τ) [Finite F.obj.V] [Finite X.obj.V]

namespace AR

/-- `F` occurs in `X` at per-tier offsets `o`. -/
structure IsFactorAt (o : ι → ℕ) : Prop where
  /-- Each tier word of `F` is the window of `X`'s at the tier's offset. -/
  window : ∀ i p, p < F.tierLength i → (X.tierWord i)[p + o i]? = (F.tierWord i)[p]?
  /-- Links transport by the offsets. -/
  link_map : ∀ i j p q, F.link i j p q → X.link i j (p + o i) (q + o j)

/-- `F` subgraph-embeds in `X` when some offsets place it as a factor
    ([jardine-2017]'s connected-subgraph embedding). -/
def FactorEmbeds : Prop := ∃ o : ι → ℕ, F.IsFactorAt X o

/-- `X` avoids every forbidden factor of a banned-subgraph grammar
    ([jardine-2016-diss] Ch. 5's `L^NL_G`). -/
def Free (B : List {F : TieredAR ι τ // Finite F.obj.V}) : Prop :=
  ∀ F ∈ B, haveI := F.property; ¬ F.val.FactorEmbeds X

variable {F X} {o : ι → ℕ}

/-- On a tier where the factor is nonempty, the window equations force the offset
    in bounds. -/
theorem IsFactorAt.offset_le (h : F.IsFactorAt X o) {i : ι} (hi : F.tierLength i ≠ 0) :
    o i ≤ X.tierLength i := by
  have hb : 0 < (F.tierWord i).length := by simpa using Nat.pos_of_ne_zero hi
  have h0 := (h.window i 0 (Nat.pos_of_ne_zero hi)).trans
    (List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩)
  have := (List.getElem?_eq_some_iff.mp h0).1
  simp only [length_tierWord] at this
  omega

/-- Offsets clamp to the host's tier lengths; the clamp only moves offsets on
    tiers where the factor is empty. -/
theorem IsFactorAt.clamp (h : F.IsFactorAt X o) :
    F.IsFactorAt X fun i => min (o i) (X.tierLength i) where
  window i p hp := by
    show (X.tierWord i)[p + min (o i) (X.tierLength i)]? = (F.tierWord i)[p]?
    rw [Nat.min_eq_left (h.offset_le (i := i) (by omega))]
    exact h.window i p hp
  link_map i j p q hl := by
    obtain ⟨hpF, hqF, -⟩ := id hl
    show X.link i j (p + min (o i) (X.tierLength i)) (q + min (o j) (X.tierLength j))
    rw [Nat.min_eq_left (h.offset_le (i := i) (by omega)),
      Nat.min_eq_left (h.offset_le (i := j) (by omega))]
    exact h.link_map i j p q hl

/-- `FactorEmbeds` is a bounded search over offsets. -/
theorem factorEmbeds_iff_bounded :
    F.FactorEmbeds X ↔
      ∃ o : ι → ℕ, (∀ i, o i ≤ X.tierLength i) ∧ F.IsFactorAt X o :=
  ⟨fun ⟨_, h⟩ => ⟨_, fun _ => min_le_right _ _, h.clamp⟩, fun ⟨o, _, h⟩ => ⟨o, h⟩⟩

/-- For a link-free factor, embedding reduces to independent per-tier infix
    occurrences ([jardine-2019]'s link-free fragment). -/
theorem factorEmbeds_iff_infix_of_link_free (hF : ∀ i j p q, ¬ F.link i j p q) :
    F.FactorEmbeds X ↔ ∀ i, F.tierWord i <:+: X.tierWord i := by
  constructor
  · rintro ⟨o, hw, -⟩ i
    exact (List.isInfix_iff_exists_offset _ _).mpr
      ⟨o i, fun p hp => hw i p (by simpa using hp)⟩
  · intro h
    choose o ho using fun i => (List.isInfix_iff_exists_offset _ _).mp (h i)
    exact ⟨o, fun i p hp => ho i p (by simpa using hp),
      fun i j p q hl => absurd hl (hF i j p q)⟩

end AR

end Autosegmental
