/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.StrictlyLocal

/-!
# Locally Testable Languages (LT_k, LTT_{k,t})

A language `L` is **locally `k`-testable** when membership depends only on
which length-`k` factors occur in the boundary-augmented form of the input —
ignoring order and multiplicity [rogers-pullum-2011] [lambert-2022].
The **threshold-testable** variant LTT_{k,t} relaxes "ignoring multiplicity"
to "saturating multiplicities at threshold `t`": LT counts only presence vs
absence (`t = 1`), LTT_{k,t} counts up to `t` and treats anything beyond as
"≥ t".

Both are *property-based* (extensional) classifications — there is no
canonical grammar, only an indistinguishability relation on strings:
`w₁ ~_LT w₂` iff their `k`-factor sets coincide. `L` is LT_k iff it is
closed under `~_LT`.

## Main definitions

* `factorSet k w` — the set of `k`-factors of `boundary k w`.
* `IsLocallyTestable k L` — closure of `L` under equality of `factorSet`.
* `factorCount k t f w` — multiplicity of `f` in `boundary k w`, capped at `t`.
* `IsLocallyThresholdTestable k t L` — closure under equality of `factorCount`.

## Inclusions

The cast lemma `IsStrictlyLocal k L → IsLocallyTestable k L` lives at the
end of the file (the larger-class file holds the cast, mathlib-style).
The companion cast `LT_k ⊆ LTT_{k,t}` for `t ≥ 1` lives inside the
`DecidableEq`-scoped section with `IsLocallyThresholdTestable`.
-/

namespace Core.Computability.Subregular

variable {α : Type*}

/-- The set of `k`-factors of the boundary-augmented form of `w`. The LT
indistinguishability relation `w₁ ~_LT w₂` is exactly equality of
`factorSet k w₁` and `factorSet k w₂`. -/
def factorSet (k : ℕ) (w : List α) : Set (Augmented α) :=
  {f | f ∈ kFactors k (boundary k w)}

@[simp] lemma mem_factorSet {k : ℕ} {f : Augmented α} {w : List α} :
    f ∈ factorSet k w ↔ f ∈ kFactors k (boundary k w) :=
  Iff.rfl

/-- A language is **locally `k`-testable** iff strings with the same set of
`k`-factors are either both in `L` or both out. -/
def IsLocallyTestable (k : ℕ) (L : Language α) : Prop :=
  ∀ w₁ w₂ : List α, factorSet k w₁ = factorSet k w₂ → (w₁ ∈ L ↔ w₂ ∈ L)

/-- **SL_k ⊆ LT_k**: every strictly-`k`-local language is locally
`k`-testable. The SL test ("every factor is permitted") trivially
depends only on the *set* of factors, not their order or multiplicity. -/
theorem IsStrictlyLocal.toIsLocallyTestable {k : ℕ} {L : Language α}
    (h : IsStrictlyLocal k L) : IsLocallyTestable k L := by
  obtain ⟨G, rfl⟩ := h
  intro w₁ w₂ heq
  have key : ∀ w, w ∈ G.lang ↔ ∀ f ∈ factorSet k w, f ∈ G.permitted := fun _ => Iff.rfl
  rw [key, key, heq]

section

variable [DecidableEq α]

/-- Saturated multiplicity: how many times factor `f` occurs in `w`'s
boundary-augmented form, capped at threshold `t`. The cap is what makes
LTT a *finite* test even on infinite-input families. -/
def factorCount (k t : ℕ) (f : Augmented α) (w : List α) : ℕ :=
  min t ((kFactors k (boundary k w)).count f)

/-- A language is **locally `(k,t)`-threshold-testable** iff strings with
the same `t`-saturated factor counts agree on membership. Specializing to
`t = 1` recovers `IsLocallyTestable` (presence vs absence of each factor). -/
def IsLocallyThresholdTestable (k t : ℕ) (L : Language α) : Prop :=
  ∀ w₁ w₂ : List α,
    (∀ f, factorCount k t f w₁ = factorCount k t f w₂) → (w₁ ∈ L ↔ w₂ ∈ L)

/-- **LT_k ⊆ LTT_{k,t}** for `t ≥ 1`. A factor occurs in `w` iff its
saturated count is positive, so closure under count-equivalence implies
closure under set-equivalence. -/
theorem IsLocallyTestable.toIsLocallyThresholdTestable
    {k t : ℕ} (ht : 1 ≤ t) {L : Language α}
    (h : IsLocallyTestable k L) : IsLocallyThresholdTestable k t L := by
  intro w₁ w₂ heq
  apply h
  ext f
  have key : ∀ w : List α, f ∈ factorSet k w ↔ 0 < factorCount k t f w := by
    intro w
    simp only [factorSet, Set.mem_setOf_eq, factorCount, lt_min_iff,
               List.count_pos_iff]
    exact ⟨fun hf => ⟨ht, hf⟩, fun ⟨_, hf⟩ => hf⟩
  rw [key w₁, key w₂, heq f]

end

end Core.Computability.Subregular
