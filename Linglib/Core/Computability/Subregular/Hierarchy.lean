/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.LocallyTestable
import Linglib.Core.Computability.Subregular.Tier

/-!
# Subregular Hierarchy: Inclusion Theorems

Inclusions between the local subregular classes formalized in this
directory. This is the language-theoretic skeleton of Lambert (2022)
Figure 3.1 @cite{lambert-2022}, restricted to the local (factor-based)
classes:

```
   IsStrictlyLocal k  ⊆  IsLocallyTestable k             (forget order/multiplicity)
   IsStrictlyLocal k  ⊆  IsTierStrictlyLocal k           (universal tier reduces to SL)
   IsLocallyTestable k ⊆  IsLocallyThresholdTestable k t (set as t = 1 saturated count)
```

The vertical inclusion across `k` (SL_k ⊆ SL_{k+1}, etc.) is genuine but
non-trivial to prove: `boundary k` and `boundary (k+1)` differ in their
edge padding, so a `k`-factor of `boundary k w` does not embed verbatim
into a `(k+1)`-factor of `boundary (k+1) w`. The standard textbook
construction uses the equivalent finite-state characterization (each
level adds one state of memory, inclusion is then immediate), which we
don't yet have infrastructure for. Deferred.

The *piecewise* counterparts (SP_k, TSP_k) and the strict-separation
witnesses live in their own files (`Subregular/Piecewise.lean`;
separations require concrete counterexample languages).
-/

namespace Core.Computability.Subregular

variable {α : Type*}

/-- **SL_k ⊆ LT_k**: every strictly-`k`-local language is locally
`k`-testable. The SL test ("every factor is permitted") trivially
depends only on the *set* of factors, not their order or multiplicity. -/
theorem IsStrictlyLocal.toIsLocallyTestable {k : ℕ} {L : Language α}
    (h : IsStrictlyLocal k L) : IsLocallyTestable k L := by
  obtain ⟨G, rfl⟩ := h
  intro w₁ w₂ heq
  have key : ∀ w, w ∈ G.lang ↔ ∀ f ∈ factorSet k w, f ∈ G.permitted := fun _ => Iff.rfl
  rw [key, key, heq]

/-- **SL_k ⊆ TSL_k**: take the universal tier (every symbol on tier), so
projection is the identity and the TSL grammar's `lang` reduces to the
underlying SL grammar's `lang`. -/
theorem IsStrictlyLocal.toIsTierStrictlyLocal {k : ℕ} {L : Language α}
    (h : IsStrictlyLocal k L) : IsTierStrictlyLocal k L := by
  obtain ⟨G, rfl⟩ := h
  refine ⟨{ tier := fun _ => True, permitted := G.permitted }, ?_⟩
  ext w
  simp only [TSLGrammar.mem_lang, SLGrammar.mem_lang, tierProject_univ]

/-- **LT_k ⊆ LTT_{k,t}** for `t ≥ 1`. A factor occurs in `w` iff its
saturated count is positive, so closure under count-equivalence implies
closure under set-equivalence. -/
theorem IsLocallyTestable.toIsLocallyThresholdTestable [DecidableEq α]
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

end Core.Computability.Subregular
