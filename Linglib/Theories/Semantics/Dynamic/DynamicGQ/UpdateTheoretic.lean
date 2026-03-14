import Linglib.Theories.Semantics.Dynamic.Core.CCP
import Linglib.Core.Mereology

/-!
# Update-Theoretic Dynamic Generalized Quantifiers
@cite{charlow-2021}

Same operators as `DynamicGQ.Basic`, but defined directly over
`StateCCP W E := State W E → State W E` — @cite{charlow-2021}'s main contribution.

The key insight: `Mvar_u` (equation 78) maximizes over **the entire context**,
not per-assignment. This makes it non-distributive, which is exactly what
produces cumulative readings automatically.

## Main results

- `Mvar_u_nondistributive`: M_v is not distributive (@cite{charlow-2021}, Theorem 1)
- `CardTest_u_distributive`: cardinality tests ARE distributive
- `exactlyN_u_cumulative`: the composed meaning has cumulative truth conditions

-/

namespace Semantics.Dynamic.DynamicGQ.UpdateTheoretic

open Semantics.Dynamic.Core
open Mereology

variable {W E : Type*}

/-- Existential dref introduction at the state level (equation 74):
    for each world-assignment pair in the context, non-deterministically
    extend the assignment at position v with some entity satisfying P. -/
def Evar_u (v : Nat) (P : E → Prop) : StateCCP W E :=
  λ s => {p | ∃ q ∈ s, p.1 = q.1 ∧ ∃ (x : E), P x ∧ p.2 = q.2.update v x}

/-- Mereological maximization at the state level (equation 78):
    apply K, then retain only those output pairs where v is maximal
    **across the entire output state**. This is the non-distributive operator. -/
def Mvar_u (v : Nat) (K : StateCCP W E) [PartialOrder E] : StateCCP W E :=
  λ s =>
    let out := K s
    {p ∈ out | Mereology.isMaximal (λ x => ∃ q ∈ out, q.2 v = x) (p.2 v)}

/-- Cardinality test at the state level (equation 75):
    filter the context for pairs where atomCount(v(g)) = n. -/
def CardTest_u (v : Nat) (n : Nat) [PartialOrder E] [Fintype E] : StateCCP W E :=
  λ s => {p ∈ s | Mereology.atomCount E (p.2 v) = n}

/-- Dynamic sequencing at the state level (equation 80):
    function composition. s[L;R] := R(L(s)). -/
def dseq_u (L R : StateCCP W E) : StateCCP W E := R ∘ L

infixl:65 " ⨟ᵤ " => dseq_u

/-- Composed update-theoretic "exactly N" (equation 81):
    E^v_u; M_v_u; n_v_u -/
def exactlyN_u (v : Nat) (P : E → Prop) (n : Nat) [PartialOrder E] [Fintype E] :
    StateCCP W E :=
  dseq_u (dseq_u (Evar_u v P) (Mvar_u v (Evar_u v P))) (CardTest_u v n)

-- ════════════════════════════════════════════════════
-- § Key Theorems
-- ════════════════════════════════════════════════════

/-- M_v is NOT distributive: it surveys the entire context to determine
    which assignments have maximal v-values.

    Proof: with K = id and a context containing two pairs whose v-values are
    `a < b`, whole-context maximization keeps only the b-pair (a is not
    maximal), but per-element processing keeps both (each is trivially
    maximal in its singleton). -/
theorem Mvar_u_nondistributive [PartialOrder E] [Nonempty W]
    (a b : E) (hab : a < b) :
    ∃ (v : Nat) (K : StateCCP W E), ¬ IsDistributive (Mvar_u v K) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  refine ⟨0, id, fun h => ?_⟩
  let g₁ : Core.Assignment E := Function.const _ a
  let g₂ : Core.Assignment E := Function.const _ b
  let s : State W E := {(w, g₁), (w, g₂)}
  -- (w, g₁) is NOT in Mvar_u 0 id s: a is not maximal because b > a is also present
  have hnotmem : (w, g₁) ∉ Mvar_u 0 id s := by
    simp only [Mvar_u, id, Set.mem_sep_iff]
    intro ⟨_, _, hmax⟩
    have : a = b := hmax b ⟨(w, g₂), Or.inr rfl, rfl⟩ (le_of_lt hab)
    exact absurd this (ne_of_lt hab)
  -- But (w, g₁) IS in the per-element union: a is maximal in {(w, g₁)}
  have hmem : (w, g₁) ∈ ({p | ∃ i ∈ s, p ∈ Mvar_u 0 id {i}} : Set _) := by
    refine ⟨(w, g₁), Set.mem_insert _ _, Set.mem_sep (Set.mem_singleton _) ⟨⟨(w, g₁), rfl, rfl⟩, ?_⟩⟩
    intro y ⟨q, hq, hqv⟩ hle
    cases Set.mem_singleton_iff.mp hq
    exact le_antisymm hle (hqv ▸ le_refl _)
  exact hnotmem (h s ▸ hmem)

/-- Cardinality tests ARE distributive: they only inspect one pair at a time. -/
theorem CardTest_u_distributive [PartialOrder E] [Fintype E]
    (v : Nat) (n : Nat) :
    IsDistributive (CardTest_u (W := W) (E := E) v n) := by
  intro s
  ext p
  simp only [CardTest_u, Set.mem_setOf_eq, Set.mem_sep_iff]
  constructor
  · intro ⟨hp, hcard⟩
    exact ⟨p, hp, ⟨Set.mem_singleton p, hcard⟩⟩
  · intro ⟨i, hi, hpi, hcard⟩
    have : p = i := by
      simp only [Set.mem_singleton_iff] at hpi
      exact hpi
    subst this
    exact ⟨hi, hcard⟩

/-- The update-theoretic composed meaning has cumulative truth conditions:
    `exactlyN_u` is not distributive for suitable choices of parameters,
    because it inherits non-distributivity from `Mvar_u`.
    TODO: Construct a concrete counterexample through the full
    Evar_u ; Mvar_u ; CardTest_u pipeline. -/
theorem exactlyN_u_cumulative [PartialOrder E] [Fintype E] [Nonempty W]
    (a b : E) (hab : a < b) :
    ∃ (v : Nat) (P : E → Prop) (n : Nat),
    ¬ IsDistributive (exactlyN_u (W := W) (E := E) v P n) := by
  sorry

end Semantics.Dynamic.DynamicGQ.UpdateTheoretic
