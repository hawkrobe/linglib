import Linglib.Theories.Semantics.Dynamic.Core.CCP
import Linglib.Core.Mereology

/-!
# Update-Theoretic Dynamic Generalized Quantifiers
@cite{charlow-2021}

Same operators as `Quantification.Dynamic.Basic`, but defined directly over
`StateCCP W E := State W E → State W E` — @cite{charlow-2021}'s main contribution.

The key insight: `Mvar_u` (equation 78) maximizes over **the entire context**,
not per-assignment. This makes it non-distributive, which is exactly what
produces cumulative readings automatically.

## Main results

- `Mvar_u_nondistributive`: M_v is not distributive (p. 33 of @cite{charlow-2021})
- `CardTest_u_distributive`: cardinality tests ARE distributive
- `sentenceMeaning_u`: the full two-quantifier composed meaning (eq. 82)
- `exactlyN_u_distributive`: the single-quantifier pipeline (no nuclear scope) is distributive

-/

namespace Semantics.Quantification.Dynamic.UpdateTheoretic

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

/-- Relational test at the state level (eq. 73 in @cite{charlow-2021}):
    filter for assignments where R(g(v₁), g(v₂)) holds.
    Used to encode verb meanings in the dynamic pipeline. -/
def RelTest (v₁ v₂ : Nat) (R : E → E → Prop) : StateCCP W E :=
  λ s => {p ∈ s | R (p.2 v₁) (p.2 v₂)}

/-- Single-quantifier "exactly N" pipeline (no nuclear scope):
    E^v P ; M_v(E^v P) ; n_v.
    This is the trivial-scope instantiation of @cite{charlow-2021}'s
    scope-taking GQ (eq. 81), with the nuclear scope set to identity. -/
def exactlyN_u (v : Nat) (P : E → Prop) (n : Nat) [PartialOrder E] [Fintype E] :
    StateCCP W E :=
  dseq_u (dseq_u (Evar_u v P) (Mvar_u v (Evar_u v P))) (CardTest_u v n)

/-- The full update-theoretic sentence meaning for
    "exactly n_subj P_subj R exactly n_obj P_obj" (eq. 82 in @cite{charlow-2021}).

    Structure: `M_v (E^v P_subj ; M_u (E^u P_obj ; R u v)) ; n_obj_u ; n_subj_v`

    The two maximization operators nest: the inner `M_u` maximizes the object
    dref within the scope of the outer subject dref, while the outer `M_v`
    maximizes over the entire state. The non-distributivity of `M_v` is what
    produces the cumulative reading. -/
def sentenceMeaning_u (v u : Nat) (P_subj P_obj : E → Prop)
    (R : E → E → Prop) (n_subj n_obj : Nat)
    [PartialOrder E] [Fintype E] : StateCCP W E :=
  let inner := dseq_u (Evar_u u P_obj) (RelTest u v R)
  let K_v := dseq_u (Evar_u v P_subj) (Mvar_u u inner)
  dseq_u (dseq_u (Mvar_u v K_v) (CardTest_u u n_obj)) (CardTest_u v n_subj)

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
  simp only [CardTest_u, Set.mem_setOf_eq]
  constructor
  · intro ⟨hp, hcard⟩
    exact ⟨p, hp, ⟨Set.mem_singleton p, hcard⟩⟩
  · intro ⟨i, hi, hpi, hcard⟩
    have : p = i := by
      simp only [Set.mem_singleton_iff] at hpi
      exact hpi
    subst this
    exact ⟨hi, hcard⟩

/-- `Evar_u v P` is idempotent: applying it twice gives the same result as
    applying it once, because `(g.update v x).update v y = g.update v y`. -/
private theorem evar_u_idempotent (v : Nat) (P : E → Prop) (s : State W E) :
    Evar_u v P (Evar_u v P s) = Evar_u v P s := by
  ext ⟨w, g⟩; simp only [Evar_u, Set.mem_setOf_eq]; constructor
  · intro ⟨q₁, hq₁, hw₁, y, hPy, hg₁⟩
    obtain ⟨q₂, hq₂s, hw₂, x, _, hg₂⟩ := hq₁
    exact ⟨q₂, hq₂s, hw₂ ▸ hw₁, y, hPy, by rw [hg₁, hg₂, Core.Assignment.update_overwrite]⟩
  · intro ⟨q, hqs, hw, x, hPx, hg⟩
    exact ⟨⟨q.1, q.2.update v x⟩, ⟨q, hqs, rfl, x, hPx, rfl⟩, hw, x, hPx,
           by rw [hg, Core.Assignment.update_overwrite]⟩

/-- Congruence for `isMaximal`: pointwise-equivalent predicates give equivalent maximality. -/
private theorem isMaximal_congr {α : Type*} [PartialOrder α] {P Q : α → Prop}
    (h : ∀ x, P x ↔ Q x) (y : α) :
    Mereology.isMaximal P y ↔ Mereology.isMaximal Q y :=
  ⟨fun ⟨hp, hm⟩ => ⟨(h y).mp hp, fun z hz hle => hm z ((h z).mpr hz) hle⟩,
   fun ⟨hq, hm⟩ => ⟨(h y).mpr hq, fun z hz hle => hm z ((h z).mp hz) hle⟩⟩

/-- The v-values after `Evar_u v P s` are exactly `{x | P x}` (requires nonempty input). -/
private theorem evar_u_vvals (v : Nat) (P : E → Prop) (s : State W E) (y : E)
    (hs : s.Nonempty) :
    (∃ q ∈ Evar_u v P s, q.2 v = y) ↔ P y := by
  simp only [Evar_u, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨_, _⟩, ⟨_, _, _, x, hPx, hg⟩, hv⟩
    rw [hg, Core.Assignment.update_at] at hv; rwa [← hv]
  · intro hPy
    obtain ⟨⟨w₀, g₀⟩, hw₀⟩ := hs
    exact ⟨⟨w₀, g₀.update v y⟩, ⟨⟨w₀, g₀⟩, hw₀, rfl, y, hPy, rfl⟩,
           Core.Assignment.update_at g₀ v y⟩

/-- The v-values after `Evar_u v P {i}` are exactly `{x | P x}`. -/
private theorem evar_u_vvals_single (v : Nat) (P : E → Prop)
    (i : W × Core.Assignment E) (y : E) :
    (∃ q ∈ Evar_u v P ({i} : Set _), q.2 v = y) ↔ P y := by
  simp only [Evar_u, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨_, _⟩, ⟨_, _, _, x, hPx, hg⟩, hv⟩
    rw [hg, Core.Assignment.update_at] at hv; rwa [← hv]
  · intro hPy
    exact ⟨⟨i.1, i.2.update v y⟩, ⟨i, rfl, rfl, y, hPy, rfl⟩,
           Core.Assignment.update_at i.2 v y⟩

/-- The update-theoretic composed "exactly N" is distributive.

    Despite containing the non-distributive `Mvar_u`, the full pipeline
    `Evar_u ; Mvar_u ∘ Evar_u ; CardTest_u` is distributive because `Evar_u`
    normalizes the v-values: after `Evar_u v P`, the set of values at
    position v is always `{x | P x}` regardless of the input state.
    The maximization in `Mvar_u` therefore selects the same maximal
    P-elements whether processing the full state or per-element.

    The cumulative reading (@cite{charlow-2021}) arises from the
    non-distributivity of `Mvar_u` itself (see `Mvar_u_nondistributive`),
    not from the composed pipeline. -/
theorem exactlyN_u_distributive [PartialOrder E] [Fintype E]
    (v : Nat) (P : E → Prop) (n : Nat) :
    IsDistributive (exactlyN_u (W := W) (E := E) v P n) := by
  intro s; ext ⟨w, g⟩
  simp only [exactlyN_u, dseq_u, Function.comp,
             CardTest_u, Mvar_u, Set.mem_sep_iff, evar_u_idempotent]
  constructor
  · -- (⊆) Full pipeline → per-element
    intro ⟨⟨hmem, hmax⟩, hcount⟩
    obtain ⟨q, hqs, hwq, x, hPx, hgq⟩ := hmem
    refine ⟨q, hqs, ⟨⟨⟨q, rfl, hwq, x, hPx, hgq⟩,
      (isMaximal_congr (fun y => (evar_u_vvals v P s y ⟨q, hqs⟩).trans
        (evar_u_vvals_single v P q y).symm) _).mp hmax⟩, hcount⟩⟩
  · -- (⊇) Per-element → full pipeline
    intro ⟨i, his, ⟨⟨hmem_i, hmax_i⟩, hcount_i⟩⟩
    obtain ⟨r, hr_eq, hwr, x, hPx, hgr⟩ := hmem_i
    have hri : r = i := hr_eq; rw [hri] at hwr hgr
    exact ⟨⟨⟨i, his, hwr, x, hPx, hgr⟩,
      (isMaximal_congr (fun y => (evar_u_vvals_single v P i y).trans
        (evar_u_vvals v P s y ⟨i, his⟩).symm) _).mp hmax_i⟩, hcount_i⟩

end Semantics.Quantification.Dynamic.UpdateTheoretic
