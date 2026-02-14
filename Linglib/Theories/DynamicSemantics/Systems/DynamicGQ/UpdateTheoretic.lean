import Linglib.Theories.DynamicSemantics.Effects.Nondeterminism.Charlow2019
import Linglib.Core.Mereology

/-!
# Update-Theoretic Dynamic Generalized Quantifiers

Same operators as `DynamicGQ.Basic`, but defined directly over
`StateCCP W E := State W E → State W E` — Charlow's (2021) main contribution.

The key insight: `Mvar_u` (equation 78) maximizes over **the entire context**,
not per-assignment. This makes it non-distributive, which is exactly what
produces cumulative readings automatically.

## Main results

- `Mvar_u_nondistributive`: M_v is not distributive (Charlow 2021, Theorem 1)
- `CardTest_u_distributive`: cardinality tests ARE distributive
- `exactlyN_u_cumulative`: the composed meaning has cumulative truth conditions

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
  §6, equations 74–82.
-/

namespace DynamicSemantics.DynamicGQ.UpdateTheoretic

open DynamicSemantics.Charlow2019
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
    E^v_u ; M_v_u ; n_v_u -/
def exactlyN_u (v : Nat) (P : E → Prop) (n : Nat) [PartialOrder E] [Fintype E] :
    StateCCP W E :=
  dseq_u (dseq_u (Evar_u v P) (Mvar_u v (Evar_u v P))) (CardTest_u v n)

-- ════════════════════════════════════════════════════
-- § Key Theorems
-- ════════════════════════════════════════════════════

/-- M_v is NOT distributive: it surveys the entire context to determine
    which assignments have maximal v-values (Charlow 2021, §6).
    TODO: Prove by exhibiting a 2-element context where per-element
    maximization differs from whole-context maximization. -/
theorem Mvar_u_nondistributive [PartialOrder E] :
    ∃ (v : Nat) (K : StateCCP W E), ¬ isDistributive (Mvar_u v K) := by
  sorry

/-- Cardinality tests ARE distributive: they only inspect one pair at a time. -/
theorem CardTest_u_distributive [PartialOrder E] [Fintype E]
    (v : Nat) (n : Nat) :
    isDistributive (CardTest_u (W := W) (E := E) v n) := by
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

/-- The update-theoretic composed meaning has cumulative truth conditions.
    TODO: Formalize. -/
theorem exactlyN_u_cumulative [PartialOrder E] [Fintype E] :
    ∀ (v : Nat) (P : E → Prop) (n : Nat),
    ¬ isDistributive (exactlyN_u (W := W) (E := E) v P n) := by
  sorry

end DynamicSemantics.DynamicGQ.UpdateTheoretic
