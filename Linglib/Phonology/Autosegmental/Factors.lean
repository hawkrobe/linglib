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
variable (F X : AR (Sigma.fst : ((i : ι) × τ i) → ι))

/-- `F` occurs in `X` at per-tier offsets `o`: each tier word of `F` is the
    window of `X`'s at `o i`, and `F`'s links transport shifted. -/
def AR.IsFactorAt [Finite F.obj.V] [Finite X.obj.V] (o : ι → ℕ) : Prop :=
  (∀ i p, p < F.tierLength i → (X.tierWord i)[p + o i]? = (F.tierWord i)[p]?) ∧
    ∀ i j p q, F.link i j p q → X.link i j (p + o i) (q + o j)

/-- `F` subgraph-embeds in `X` when some offsets place it as a factor
    ([jardine-2017]'s connected-subgraph embedding). -/
def AR.FactorEmbeds [Finite F.obj.V] [Finite X.obj.V] : Prop :=
  ∃ o : ι → ℕ, F.IsFactorAt X o

/-- Offsets clamp to the host's tier lengths: `FactorEmbeds` is a bounded
    search. On tiers where the factor is nonempty the word-window condition
    already forces the bound; empty factor tiers accept any offset, so `min`
    clamps them harmlessly. -/
theorem AR.factorEmbeds_iff_bounded
    {F X : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite F.obj.V] [Finite X.obj.V] :
    F.FactorEmbeds X ↔
      ∃ o : ι → ℕ, (∀ i, o i ≤ X.tierLength i) ∧ F.IsFactorAt X o := by
  constructor
  · rintro ⟨o, hw, hl⟩
    refine ⟨fun i => min (o i) (X.tierLength i), fun i => min_le_right _ _, fun i p hp => ?_,
      fun i j p q h => ?_⟩
    · have horig := hw i p hp
      show (X.tierWord i)[p + min (o i) (X.tierLength i)]? = (F.tierWord i)[p]?
      rcases le_or_gt (o i) (X.tierLength i) with hle | hgt
      · rwa [Nat.min_eq_left hle]
      · exfalso
        have hnone : (X.tierWord i)[p + o i]? = none := by
          rw [List.getElem?_eq_none_iff]
          simp only [AR.length_tierWord]
          omega
        have hsome : p < (F.tierWord i).length := by
          simpa [AR.length_tierWord] using hp
        rw [hnone, List.getElem?_eq_some_iff.mpr ⟨hsome, rfl⟩] at horig
        simp at horig
    · obtain ⟨hpb, hqb, -⟩ := id (hl i j p q h)
      have h' := hl i j p q h
      have hoi : min (o i) (X.tierLength i) = o i := by
        have := hw i p (by obtain ⟨hp', -, -⟩ := id h; omega)
        rcases le_or_gt (o i) (X.tierLength i) with hle | hgt
        · exact Nat.min_eq_left hle
        · exfalso
          obtain ⟨hpX, -, -⟩ := id h'
          omega
      have hoj : min (o j) (X.tierLength j) = o j := by
        rcases le_or_gt (o j) (X.tierLength j) with hle | hgt
        · exact Nat.min_eq_left hle
        · exfalso
          obtain ⟨-, hqX, -⟩ := id h'
          omega
      show X.link i j (p + min (o i) (X.tierLength i)) (q + min (o j) (X.tierLength j))
      rw [hoi, hoj]
      exact h'
  · rintro ⟨o, -, hfa⟩
    exact ⟨o, hfa⟩

/-- `X` avoids every forbidden factor of a banned-subgraph grammar
    ([jardine-2016-diss] Ch. 5's `L^NL_G`). -/
def AR.Free [Finite X.obj.V]
    (B : List {F : AR (Sigma.fst : ((i : ι) × τ i) → ι) // Finite F.obj.V}) :
    Prop :=
  ∀ F ∈ B, haveI := F.property; ¬ F.val.FactorEmbeds X

/-- For a link-free factor, embedding reduces to independent per-tier infix
    occurrences ([jardine-2019]'s link-free fragment). -/
theorem AR.factorEmbeds_iff_infix_of_link_free
    {F X : AR (Sigma.fst : ((i : ι) × τ i) → ι)}
    [Finite F.obj.V] [Finite X.obj.V]
    (hF : ∀ i j p q, ¬ F.link i j p q) :
    F.FactorEmbeds X ↔ ∀ i, F.tierWord i <:+: X.tierWord i := by
  constructor
  · rintro ⟨o, hw, -⟩ i
    rw [List.isInfix_iff_exists_offset]
    rcases Nat.eq_zero_or_pos (F.tierWord i).length with hzero | hpos
    · exact ⟨0, Nat.zero_le _, fun p hp => absurd hp (by omega)⟩
    · have h0 := hw i 0 (by simpa [AR.length_tierWord] using hpos)
      refine ⟨o i, ?_, fun p hp => hw i p
        (by simpa [AR.length_tierWord] using hp)⟩
      rcases List.getElem?_eq_some_iff.mp
        (h0 ▸ (List.getElem?_eq_some_iff.mpr
          ⟨by simpa [AR.length_tierWord] using hpos, rfl⟩ :
            (F.tierWord i)[0]? = some _)) with ⟨hb, -⟩
      omega
  · intro h
    choose o ho using fun i => (List.isInfix_iff_exists_offset _ _).mp (h i)
    refine ⟨o, fun i p hp => ?_, fun i j p q hl => absurd hl (hF i j p q)⟩
    obtain ⟨-, hoff⟩ := ho i
    exact hoff p (by simpa [AR.length_tierWord] using hp)

end Autosegmental
