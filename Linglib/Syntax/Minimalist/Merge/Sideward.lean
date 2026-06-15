import Linglib.Syntax.Minimalist.Merge.External

/-!
# Sideward Merge: realization on the canonical carrier
[marcolli-chomsky-berwick-2025]

Realizes M-C-B Lemmas 1.4.4 + 1.4.5 (book pp. 54-55) for the three
Sideward-flavored cases of §1.4.1 on the canonical carrier
`ConnesKreimer R (Nonplanar α)`, using the Δ^ρ deletion coproduct
`comulAlgHomN` (cuts are the `cutSummandsN` multiset; crowns are
`Forest (Nonplanar α)`, remainders bare `Nonplanar α`).

## Cut identification

A cut of `T` is a summand `p ∈ cutSummandsN T` with crown `p.1` and
remainder `p.2`. The matching multisets pick the cuts whose crown is a
prescribed accessible-term forest:

- `matchingSingleEdgeCutsN T β`: cuts with `p.1 = {β}` (single accessible
  term β).
- `matchingTwoEdgeCutsN T α_t β`: cuts with `p.1 = {α_t, β}` (two
  accessible terms, case 3(a)).

## Realization theorems

For each case 2b, 3a, 3b:
- `mergeOp_sideward_X_general_pair`: the multi-witness sum form matching
  MCB eq. (1.3.3) — a sum (or double sum) over all matching cuts.
- `mergeOp_sideward_X_pair`: a unique-witness corollary collapsing the
  matching multiset to a singleton `{p0}`.
- `mergeOp_sideward_X` (residual): induction over residual workspace
  `Fhat` via `mergeOp_factor_out_singleton` (from `Merge.External`),
  under `CutAvoidingForestN`.

## Deferred (substrate gap)

The §1.5 cost-suppression theorems (`mergeOp_eps_zero_for_sideward_*`,
showing Sideward configurations vanish in the ε → 0 Minimal-Search limit)
ride the same ε-weighted Δ^ρ gap as `External`/`Internal`'s ε arc: there
is no `cutTotalDepth` analogue on `cutSummandsN` yet. They are queued
behind that substrate and omitted here.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open RootedTree RootedTree.ConnesKreimer

/-! ### Matching-cut multisets -/

/-- Cut summands of `T` whose crown forest is the singleton `{β}` (single
    accessible-term extraction). The `cutSummandsN` analogue of legacy
    `matchingSingleEdgeCuts`. -/
noncomputable def matchingSingleEdgeCutsN {α : Type*} [DecidableEq (Nonplanar α)]
    (T β : Nonplanar α) : Multiset (Forest (Nonplanar α) × Nonplanar α) :=
  (cutSummandsN T).filter (fun p => p.1 = ({β} : Forest (Nonplanar α)))

/-- Cut summands of `T` whose crown forest is `{α_t, β}` (two accessible
    terms, case 3(a)). The `cutSummandsN` analogue of legacy
    `matchingTwoEdgeCuts`. -/
noncomputable def matchingTwoEdgeCutsN {α : Type*} [DecidableEq (Nonplanar α)]
    (T α_t β : Nonplanar α) : Multiset (Forest (Nonplanar α) × Nonplanar α) :=
  (cutSummandsN T).filter (fun p => p.1 = ({α_t, β} : Forest (Nonplanar α)))

/-! ### Sum-reduction helpers -/

/-- A prefixed singleton crown matches the pair `{a, β}` iff the crown is
    `{β}`. The condition-rewriting workhorse for the surviving Sideward
    cross-terms. -/
private theorem prefix_pair_eq_iff {α : Type*} [DecidableEq (Nonplanar α)]
    (a β : Nonplanar α) (F : Forest (Nonplanar α)) :
    (({a} : Forest (Nonplanar α)) + F = ({a, β} : Forest (Nonplanar α)))
      ↔ F = ({β} : Forest (Nonplanar α)) := by
  constructor
  · intro h
    have h' : ({a} : Forest (Nonplanar α)) + F
            = ({a} : Forest (Nonplanar α)) + ({β} : Forest (Nonplanar α)) := h
    exact Multiset.add_right_inj.mp h'
  · intro h; rw [h]; rfl

/-- A `mergePost`-filtered cut-sum collapses to the matching-cut sum: each
    `if p.1 = K then N * ofTree p.2 else 0` summand contributes `N * ofTree
    p.2` exactly when `p.1 = K`. -/
private theorem ite_mul_sum_eq_mul_filter_sum {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)]
    (s : Multiset (Forest (Nonplanar α) × Nonplanar α))
    (K : Forest (Nonplanar α)) (N : ConnesKreimer R (Nonplanar α)) :
    (s.map (fun p => if p.1 = K then N * ofTree (R := R) p.2 else 0)).sum
      = N * ((s.filter (fun p => p.1 = K)).map (fun p => ofTree (R := R) p.2)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.filter_cons,
        Multiset.map_add, Multiset.sum_add, mul_add]
    by_cases h : a.1 = K
    · rw [if_pos h, if_pos h, Multiset.map_singleton, Multiset.sum_singleton]
    · rw [if_neg h, if_neg h]; simp

/-- The double-sum analogue for case 3(b): a doubly-filtered conjunction-if
    cut-sum factors into `N` times the two single matching-cut sums. Proven
    by two applications of `ite_mul_sum_eq_mul_filter_sum`. -/
private theorem ite_and_double_sum_eq {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)]
    (s t : Multiset (Forest (Nonplanar α) × Nonplanar α))
    (Kα Kβ : Forest (Nonplanar α)) (N : ConnesKreimer R (Nonplanar α)) :
    (s.map (fun p => (t.map (fun q =>
        if p.1 = Kα ∧ q.1 = Kβ
          then N * (ofTree (R := R) p.2 * ofTree (R := R) q.2) else 0)).sum)).sum
      = N * ((s.filter (fun p => p.1 = Kα)).map (fun p => ofTree (R := R) p.2)).sum
          * ((t.filter (fun q => q.1 = Kβ)).map (fun q => ofTree (R := R) q.2)).sum := by
  have step1 : ∀ p : Forest (Nonplanar α) × Nonplanar α,
      (t.map (fun q => if p.1 = Kα ∧ q.1 = Kβ
          then N * (ofTree (R := R) p.2 * ofTree (R := R) q.2) else 0)).sum
      = (if p.1 = Kα then N * ofTree (R := R) p.2 else 0)
          * ((t.filter (fun q => q.1 = Kβ)).map (fun q => ofTree (R := R) q.2)).sum := by
    intro p
    by_cases hα : p.1 = Kα
    · rw [if_pos hα]
      have hmap : (t.map (fun q => if p.1 = Kα ∧ q.1 = Kβ
              then N * (ofTree (R := R) p.2 * ofTree (R := R) q.2) else 0))
            = t.map (fun q => if q.1 = Kβ
              then (N * ofTree (R := R) p.2) * ofTree (R := R) q.2 else 0) :=
        Multiset.map_congr rfl fun q _ => by
          by_cases hβ : q.1 = Kβ
          · rw [if_pos ⟨hα, hβ⟩, if_pos hβ, mul_assoc]
          · rw [if_neg (fun h => hβ h.2), if_neg hβ]
      rw [hmap]
      exact ite_mul_sum_eq_mul_filter_sum t Kβ (N * ofTree (R := R) p.2)
    · rw [if_neg hα, zero_mul]
      refine Multiset.sum_eq_zero fun x hx => ?_
      obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hx
      rw [if_neg (fun h => hα h.1)]
  rw [Multiset.map_congr rfl (fun p _ => step1 p),
      Multiset.sum_map_mul_right, ite_mul_sum_eq_mul_filter_sum s Kα N]

/-! ### Case 2(b): one component contributes M(T_i, β), the other T_j/β -/

/-- **Sideward Merge case 2(b), F̂ = ∅, multi-witness sum form** (M-C-B
    Lemma 1.4.4, p. 54, eq. (1.3.3)).

    `mergeOp lbl T_i β` on `{T_i, T_j}` produces a sum over **all** cuts of
    `T_j` whose crown is `{β}`, each contributing `of' {M(T_i, β)} * ofTree
    (T_j/β)`. Only the `prim T_i × cut T_j` cross-term survives; the other
    three vanish. -/
theorem mergeOp_sideward_2b_general_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α) (T_i T_j β : Nonplanar α)
    (h_T_j_no_T_i : ∀ p ∈ cutSummandsN T_j, T_i ∉ p.1)
    (h_distinct : T_i ≠ T_j)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp (R := R) lbl T_i β (of' ({T_i, T_j} : Forest (Nonplanar α)))
      = of' ({Nonplanar.node lbl {T_i, β}} : Forest (Nonplanar α))
        * ((matchingSingleEdgeCutsN T_j β).map (fun p => ofTree (R := R) p.2)).sum := by
  show (mergePost (R := R) (α := α) lbl T_i β ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({T_i, T_j} : Forest (Nonplanar α))) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulAlgHomN_apply_of',
      show comulForestN (R := R) ({T_i, T_j} : Forest (Nonplanar α))
          = comulTreeN (R := R) T_i * comulTreeN (R := R) T_j from by
        rw [show ({T_i, T_j} : Forest (Nonplanar α)) = T_i ::ₘ ({T_j} : Forest (Nonplanar α))
              from rfl, comulForestN_cons,
            show ({T_j} : Forest (Nonplanar α)) = T_j ::ₘ (0 : Forest (Nonplanar α))
              from rfl, comulForestN_cons, comulForestN_zero, mul_one]]
  unfold comulTreeN
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim T_i × prim T_j): vanishes (T_j ≠ β).
  have h_pp : mergePost (R := R) (α := α) lbl T_i β
        ((ofTree T_i ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
          * (ofTree T_j ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_singleton,
        ← of'_add, mergePost_basis_tensor, if_neg]
    intro h_eq
    apply h_β_ne_Tj
    have h' : ({T_i} : Forest (Nonplanar α)) + ({T_j} : Forest (Nonplanar α))
            = ({T_i} : Forest (Nonplanar α)) + ({β} : Forest (Nonplanar α)) := h_eq
    exact (Multiset.singleton_inj.mp (Multiset.add_right_inj.mp h')).symm
  -- Term 2 (prim T_i × cut T_j): the surviving matching sum.
  have h_ps : mergePost (R := R) (α := α) lbl T_i β
        ((ofTree T_i ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
          * ((cutSummandsN T_j).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum)
      = of' ({Nonplanar.node lbl {T_i, β}} : Forest (Nonplanar α))
        * ((matchingSingleEdgeCutsN T_j β).map (fun p => ofTree (R := R) p.2)).sum := by
    rw [← Multiset.sum_map_mul_left, _root_.map_multiset_sum, Multiset.map_map]
    refine Eq.trans (congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_))
      (ite_mul_sum_eq_mul_filter_sum (cutSummandsN T_j) ({β} : Forest (Nonplanar α))
        (of' ({Nonplanar.node lbl {T_i, β}} : Forest (Nonplanar α))))
    show mergePost (R := R) (α := α) lbl T_i β
        ((ofTree T_i ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
          * (of' (R := R) p.1 ⊗ₜ[R] ofTree p.2))
      = if p.1 = ({β} : Forest (Nonplanar α))
          then of' ({Nonplanar.node lbl {T_i, β}} : Forest (Nonplanar α)) * ofTree (R := R) p.2
          else 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← of'_singleton, ← of'_add,
        mergePost_basis_tensor]
    simp only [prefix_pair_eq_iff]
  -- Term 3 (cut T_i × prim T_j): vanishes (T_j ∉ {T_i, β}).
  have h_sp : mergePost (R := R) (α := α) lbl T_i β
        (((cutSummandsN T_i).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum
          * (ofTree T_j ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))) = 0 := by
    rw [← Multiset.sum_map_mul_right, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl T_i β
          ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
            * (ofTree T_j ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_add,
        mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_j_mem : T_j ∈ p.1 + ({T_j} : Forest (Nonplanar α)) :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
    rw [h_eq, show ({T_i, β} : Forest (Nonplanar α)) = T_i ::ₘ ({β} : Forest (Nonplanar α))
          from rfl, Multiset.mem_cons, Multiset.mem_singleton] at h_T_j_mem
    rcases h_T_j_mem with h | h
    · exact h_distinct h.symm
    · exact h_β_ne_Tj h.symm
  -- Term 4 (cut T_i × cut T_j): vanishes (T_i ∉ either crown).
  have h_ss : mergePost (R := R) (α := α) lbl T_i β
        (((cutSummandsN T_i).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum
          * ((cutSummandsN T_j).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum) = 0 := by
    rw [← Multiset.sum_map_mul_right, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl T_i β
          ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
            * ((cutSummandsN T_j).map (fun q => of' (R := R) q.1 ⊗ₜ[R] ofTree q.2)).sum) = 0
    rw [← Multiset.sum_map_mul_left, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun y hy => ?_
    obtain ⟨p', hp', rfl⟩ := Multiset.mem_map.mp hy
    show mergePost (R := R) (α := α) lbl T_i β
          ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2) * (of' (R := R) p'.1 ⊗ₜ[R] ofTree p'.2)) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← of'_add, mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_i_mem : T_i ∈ p.1 + p'.1 := by
      rw [h_eq]; exact Multiset.mem_cons_self _ _
    rcases Multiset.mem_add.mp h_T_i_mem with h | h
    · exact cutSummandsN_self_not_mem_crown T_i p hp h
    · exact h_T_j_no_T_i p' hp' h
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [zero_add, add_zero]

/-- **Sideward Merge case 2(b) realization, F̂ = ∅, unique-witness form.**
    Corollary of `mergeOp_sideward_2b_general_pair` when β has a unique
    matching cut `p0` on `T_j` (the matching multiset is `{p0}`). -/
theorem mergeOp_sideward_2b_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α)
    (T_i T_j β T_j_q : Nonplanar α) (p0 : Forest (Nonplanar α) × Nonplanar α)
    (h_filter : matchingSingleEdgeCutsN T_j β = {p0})
    (h_remainder : p0.2 = T_j_q)
    (h_T_j_no_T_i : ∀ p ∈ cutSummandsN T_j, T_i ∉ p.1)
    (h_distinct : T_i ≠ T_j)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp (R := R) lbl T_i β (of' ({T_i, T_j} : Forest (Nonplanar α)))
      = of' ({Nonplanar.node lbl {T_i, β}, T_j_q} : Forest (Nonplanar α)) := by
  rw [mergeOp_sideward_2b_general_pair lbl T_i T_j β h_T_j_no_T_i h_distinct
        h_β_ne_Tj, h_filter, Multiset.map_singleton, Multiset.sum_singleton, h_remainder,
      ← of'_singleton, ← of'_add]
  rfl

/-- **Sideward Merge case 2(b) realization, full residual workspace** (M-C-B
    Lemma 1.4.4, p. 54). Generalization of `mergeOp_sideward_2b_pair` via the
    factor-out pattern, parameterised on `(S, S') = (T_i, β)`. -/
theorem mergeOp_sideward_2b {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α)
    (T_i T_j β T_j_q : Nonplanar α) (p0 : Forest (Nonplanar α) × Nonplanar α)
    (Fhat : Forest (Nonplanar α))
    (h_filter : matchingSingleEdgeCutsN T_j β = {p0})
    (h_remainder : p0.2 = T_j_q)
    (h_T_j_no_T_i : ∀ p ∈ cutSummandsN T_j, T_i ∉ p.1)
    (h_distinct : T_i ≠ T_j)
    (h_β_ne_Tj : β ≠ T_j)
    (h_F_disjoint : CutAvoidingForestN ({T_i, β} : Forest (Nonplanar α)) Fhat) :
    mergeOp (R := R) lbl T_i β (of' (({T_i, T_j} : Forest (Nonplanar α)) + Fhat))
      = of' (({Nonplanar.node lbl {T_i, β}, T_j_q} : Forest (Nonplanar α)) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_sideward_2b_pair lbl T_i T_j β T_j_q p0 h_filter h_remainder
      h_T_j_no_T_i h_distinct h_β_ne_Tj
  | cons T Fhat' ih =>
    obtain ⟨hT_S, hT_S'⟩ := CutAvoidingForestN.head_pair h_F_disjoint
    have ih' := ih h_F_disjoint.of_cons
    have h_lhs_eq : ({T_i, T_j} : Forest (Nonplanar α)) + T ::ₘ Fhat'
                  = ({T} : Forest (Nonplanar α))
                    + (({T_i, T_j} : Forest (Nonplanar α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (Nonplanar α)) + Fhat' from rfl]; abel
    have h_rhs_eq : ({Nonplanar.node lbl {T_i, β}, T_j_q} : Forest (Nonplanar α)) + T ::ₘ Fhat'
                  = ({T} : Forest (Nonplanar α))
                    + (({Nonplanar.node lbl {T_i, β}, T_j_q} : Forest (Nonplanar α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (Nonplanar α)) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq, of'_add (R := R) ({T} : Forest (Nonplanar α)) _,
        of'_add (R := R) ({T} : Forest (Nonplanar α)) _,
        mergeOp_factor_out_singleton lbl hT_S hT_S']
    exact congrArg (of' (R := R) ({T} : Forest (Nonplanar α)) * ·) ih'

/-! ### Case 3(b): M(α, β) plus T_i/α and T_j/β -/

/-- **Sideward Merge case 3(b), F̂ = ∅, multi-witness double-sum form**
    (M-C-B Lemma 1.4.4, p. 54, eq. (1.3.3)).

    `mergeOp lbl α_t β` on `{T_i, T_j}` produces the **double sum** over all
    `{α_t}`-cuts of `T_i` and `{β}`-cuts of `T_j`. Only the `cut × cut`
    cross-term survives; the count argument forces each surviving crown pair
    to be `({α_t}, {β})`. -/
theorem mergeOp_sideward_3b_general_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α) (T_i T_j α_t β : Nonplanar α)
    (h_T_i_no_β : ∀ p ∈ cutSummandsN T_i, β ∉ p.1)
    (h_T_j_no_α : ∀ p ∈ cutSummandsN T_j, α_t ∉ p.1)
    (h_α_ne_Ti : α_t ≠ T_i) (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i) (h_β_ne_Tj : β ≠ T_j)
    (h_α_ne_β : α_t ≠ β) :
    mergeOp (R := R) lbl α_t β (of' ({T_i, T_j} : Forest (Nonplanar α)))
      = of' ({Nonplanar.node lbl {α_t, β}} : Forest (Nonplanar α))
        * ((matchingSingleEdgeCutsN T_i α_t).map (fun p => ofTree (R := R) p.2)).sum
        * ((matchingSingleEdgeCutsN T_j β).map (fun p => ofTree (R := R) p.2)).sum := by
  show (mergePost (R := R) (α := α) lbl α_t β ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({T_i, T_j} : Forest (Nonplanar α))) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulAlgHomN_apply_of',
      show comulForestN (R := R) ({T_i, T_j} : Forest (Nonplanar α))
          = comulTreeN (R := R) T_i * comulTreeN (R := R) T_j from by
        rw [show ({T_i, T_j} : Forest (Nonplanar α)) = T_i ::ₘ ({T_j} : Forest (Nonplanar α))
              from rfl, comulForestN_cons,
            show ({T_j} : Forest (Nonplanar α)) = T_j ::ₘ (0 : Forest (Nonplanar α))
              from rfl, comulForestN_cons, comulForestN_zero, mul_one]]
  unfold comulTreeN
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim × prim): vanishes (T_i ∉ {α_t, β}).
  have h_pp : mergePost (R := R) (α := α) lbl α_t β
        ((ofTree T_i ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
          * (ofTree T_j ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_singleton,
        ← of'_add, mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_i_mem : T_i ∈ ({T_i} : Forest (Nonplanar α)) + ({T_j} : Forest (Nonplanar α)) :=
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
    rw [h_eq, show ({α_t, β} : Forest (Nonplanar α)) = α_t ::ₘ ({β} : Forest (Nonplanar α))
          from rfl, Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 2 (prim T_i × cut T_j): vanishes (T_i ∉ {α_t, β}).
  have h_ps : mergePost (R := R) (α := α) lbl α_t β
        ((ofTree T_i ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
          * ((cutSummandsN T_j).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum) = 0 := by
    rw [← Multiset.sum_map_mul_left, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl α_t β
          ((ofTree T_i ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
            * (of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← of'_singleton, ← of'_add,
        mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_i_mem : T_i ∈ ({T_i} : Forest (Nonplanar α)) + p.1 :=
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
    rw [h_eq, show ({α_t, β} : Forest (Nonplanar α)) = α_t ::ₘ ({β} : Forest (Nonplanar α))
          from rfl, Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 3 (cut T_i × prim T_j): vanishes (T_j ∉ {α_t, β}).
  have h_sp : mergePost (R := R) (α := α) lbl α_t β
        (((cutSummandsN T_i).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum
          * (ofTree T_j ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))) = 0 := by
    rw [← Multiset.sum_map_mul_right, _root_.map_multiset_sum, Multiset.map_map]
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hx
    show mergePost (R := R) (α := α) lbl α_t β
          ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
            * (ofTree T_j ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← of'_singleton, ← of'_add,
        mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_j_mem : T_j ∈ p.1 + ({T_j} : Forest (Nonplanar α)) :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
    rw [h_eq, show ({α_t, β} : Forest (Nonplanar α)) = α_t ::ₘ ({β} : Forest (Nonplanar α))
          from rfl, Multiset.mem_cons, Multiset.mem_singleton] at h_T_j_mem
    rcases h_T_j_mem with h | h
    · exact h_α_ne_Tj h.symm
    · exact h_β_ne_Tj h.symm
  -- Term 4 (cut × cut): the surviving double matching sum.
  have h_ss : mergePost (R := R) (α := α) lbl α_t β
        (((cutSummandsN T_i).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum
          * ((cutSummandsN T_j).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum)
      = of' ({Nonplanar.node lbl {α_t, β}} : Forest (Nonplanar α))
        * ((matchingSingleEdgeCutsN T_i α_t).map (fun p => ofTree (R := R) p.2)).sum
        * ((matchingSingleEdgeCutsN T_j β).map (fun p => ofTree (R := R) p.2)).sum := by
    rw [← Multiset.sum_map_mul_right, _root_.map_multiset_sum, Multiset.map_map]
    refine Eq.trans (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_))
      (ite_and_double_sum_eq (cutSummandsN T_i) (cutSummandsN T_j)
        ({α_t} : Forest (Nonplanar α)) ({β} : Forest (Nonplanar α))
        (of' ({Nonplanar.node lbl {α_t, β}} : Forest (Nonplanar α))))
    show mergePost (R := R) (α := α) lbl α_t β
        ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
          * ((cutSummandsN T_j).map (fun q => of' (R := R) q.1 ⊗ₜ[R] ofTree q.2)).sum)
      = ((cutSummandsN T_j).map (fun q =>
          if p.1 = ({α_t} : Forest (Nonplanar α)) ∧ q.1 = ({β} : Forest (Nonplanar α))
            then of' ({Nonplanar.node lbl {α_t, β}} : Forest (Nonplanar α))
                  * (ofTree (R := R) p.2 * ofTree (R := R) q.2)
            else 0)).sum
    rw [← Multiset.sum_map_mul_left, _root_.map_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    show mergePost (R := R) (α := α) lbl α_t β
        ((of' (R := R) p.1 ⊗ₜ[R] ofTree p.2) * (of' (R := R) q.1 ⊗ₜ[R] ofTree q.2))
      = if p.1 = ({α_t} : Forest (Nonplanar α)) ∧ q.1 = ({β} : Forest (Nonplanar α))
          then of' ({Nonplanar.node lbl {α_t, β}} : Forest (Nonplanar α))
                * (ofTree (R := R) p.2 * ofTree (R := R) q.2)
          else 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← of'_add, mergePost_basis_tensor]
    by_cases h_sum : p.1 + q.1 = ({α_t, β} : Forest (Nonplanar α))
    · rw [if_pos h_sum]
      have h_split : p.1 = ({α_t} : Forest (Nonplanar α)) ∧
                     q.1 = ({β} : Forest (Nonplanar α)) := by
        refine ⟨?_, ?_⟩
        · apply Multiset.ext.mpr
          intro x
          have h_count := congrArg (Multiset.count x) h_sum
          rw [Multiset.count_add] at h_count
          by_cases hx_α : x = α_t
          · subst hx_α
            rw [Multiset.count_singleton_self]
            have h_target : Multiset.count x ({x, β} : Forest (Nonplanar α)) = 1 := by
              simp [h_α_ne_β]
            rw [h_target] at h_count
            have h_q : Multiset.count x q.1 = 0 :=
              Multiset.count_eq_zero.mpr (h_T_j_no_α q hq)
            omega
          · rw [Multiset.count_singleton, if_neg hx_α]
            by_cases hx_β : x = β
            · subst hx_β
              exact Multiset.count_eq_zero.mpr (h_T_i_no_β p hp)
            · have h_target_zero :
                  Multiset.count x ({α_t, β} : Forest (Nonplanar α)) = 0 := by
                show Multiset.count x (α_t ::ₘ ({β} : Forest (Nonplanar α))) = 0
                rw [Multiset.count_cons, Multiset.count_singleton, if_neg hx_α, if_neg hx_β]
              omega
        · apply Multiset.ext.mpr
          intro x
          have h_count := congrArg (Multiset.count x) h_sum
          rw [Multiset.count_add] at h_count
          by_cases hx_β : x = β
          · subst hx_β
            rw [Multiset.count_singleton_self]
            have h_target : Multiset.count x ({α_t, x} : Forest (Nonplanar α)) = 1 := by
              simp [Ne.symm h_α_ne_β]
            rw [h_target] at h_count
            have h_p : Multiset.count x p.1 = 0 :=
              Multiset.count_eq_zero.mpr (h_T_i_no_β p hp)
            omega
          · rw [Multiset.count_singleton, if_neg hx_β]
            by_cases hx_α : x = α_t
            · subst hx_α
              exact Multiset.count_eq_zero.mpr (h_T_j_no_α q hq)
            · have h_target_zero :
                  Multiset.count x ({α_t, β} : Forest (Nonplanar α)) = 0 := by
                show Multiset.count x (α_t ::ₘ ({β} : Forest (Nonplanar α))) = 0
                rw [Multiset.count_cons, Multiset.count_singleton, if_neg hx_α, if_neg hx_β]
              omega
      rw [if_pos h_split]
    · rw [if_neg h_sum,
          if_neg (show ¬ (p.1 = ({α_t} : Forest (Nonplanar α)) ∧
                          q.1 = ({β} : Forest (Nonplanar α)))
            from fun ⟨hc, hc'⟩ => h_sum (by rw [hc, hc']; rfl))]
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [zero_add, add_zero]

/-- **Sideward Merge case 3(b) realization, F̂ = ∅, unique-witness form.**
    Corollary of `mergeOp_sideward_3b_general_pair` when both α and β have
    unique matching cuts `p_α`, `p_β`. -/
theorem mergeOp_sideward_3b_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α)
    (T_i T_j α_t β T_i_q T_j_q : Nonplanar α)
    (p_α p_β : Forest (Nonplanar α) × Nonplanar α)
    (h_filter_α : matchingSingleEdgeCutsN T_i α_t = {p_α})
    (h_filter_β : matchingSingleEdgeCutsN T_j β = {p_β})
    (h_remainder_α : p_α.2 = T_i_q)
    (h_remainder_β : p_β.2 = T_j_q)
    (h_T_i_no_β : ∀ p ∈ cutSummandsN T_i, β ∉ p.1)
    (h_T_j_no_α : ∀ p ∈ cutSummandsN T_j, α_t ∉ p.1)
    (h_α_ne_Ti : α_t ≠ T_i) (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i) (h_β_ne_Tj : β ≠ T_j)
    (h_α_ne_β : α_t ≠ β) :
    mergeOp (R := R) lbl α_t β (of' ({T_i, T_j} : Forest (Nonplanar α)))
      = of' ({Nonplanar.node lbl {α_t, β}, T_i_q, T_j_q} : Forest (Nonplanar α)) := by
  rw [mergeOp_sideward_3b_general_pair lbl T_i T_j α_t β h_T_i_no_β h_T_j_no_α h_α_ne_Ti
        h_α_ne_Tj h_β_ne_Ti h_β_ne_Tj h_α_ne_β,
      h_filter_α, h_filter_β, Multiset.map_singleton, Multiset.sum_singleton,
      Multiset.map_singleton, Multiset.sum_singleton, h_remainder_α, h_remainder_β,
      ← of'_singleton, ← of'_singleton, ← of'_add, ← of'_add]
  rfl

/-- **Sideward Merge case 3(b) realization, full residual workspace** (M-C-B
    Lemma 1.4.4, p. 54). Generalization of `mergeOp_sideward_3b_pair` via the
    factor-out pattern, parameterised on `(S, S') = (α_t, β)`. -/
theorem mergeOp_sideward_3b {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α)
    (T_i T_j α_t β T_i_q T_j_q : Nonplanar α)
    (p_α p_β : Forest (Nonplanar α) × Nonplanar α) (Fhat : Forest (Nonplanar α))
    (h_filter_α : matchingSingleEdgeCutsN T_i α_t = {p_α})
    (h_filter_β : matchingSingleEdgeCutsN T_j β = {p_β})
    (h_remainder_α : p_α.2 = T_i_q)
    (h_remainder_β : p_β.2 = T_j_q)
    (h_T_i_no_β : ∀ p ∈ cutSummandsN T_i, β ∉ p.1)
    (h_T_j_no_α : ∀ p ∈ cutSummandsN T_j, α_t ∉ p.1)
    (h_α_ne_Ti : α_t ≠ T_i) (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i) (h_β_ne_Tj : β ≠ T_j)
    (h_α_ne_β : α_t ≠ β)
    (h_F_disjoint : CutAvoidingForestN ({α_t, β} : Forest (Nonplanar α)) Fhat) :
    mergeOp (R := R) lbl α_t β (of' (({T_i, T_j} : Forest (Nonplanar α)) + Fhat))
      = of' (({Nonplanar.node lbl {α_t, β}, T_i_q, T_j_q} : Forest (Nonplanar α)) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_sideward_3b_pair lbl T_i T_j α_t β T_i_q T_j_q p_α p_β h_filter_α h_filter_β
      h_remainder_α h_remainder_β h_T_i_no_β h_T_j_no_α h_α_ne_Ti h_α_ne_Tj h_β_ne_Ti
      h_β_ne_Tj h_α_ne_β
  | cons T Fhat' ih =>
    obtain ⟨hT_S, hT_S'⟩ := CutAvoidingForestN.head_pair h_F_disjoint
    have ih' := ih h_F_disjoint.of_cons
    have h_lhs_eq : ({T_i, T_j} : Forest (Nonplanar α)) + T ::ₘ Fhat'
                  = ({T} : Forest (Nonplanar α))
                    + (({T_i, T_j} : Forest (Nonplanar α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (Nonplanar α)) + Fhat' from rfl]; abel
    have h_rhs_eq : ({Nonplanar.node lbl {α_t, β}, T_i_q, T_j_q} : Forest (Nonplanar α)) + T ::ₘ Fhat'
                  = ({T} : Forest (Nonplanar α))
                    + (({Nonplanar.node lbl {α_t, β}, T_i_q, T_j_q} : Forest (Nonplanar α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (Nonplanar α)) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq, of'_add (R := R) ({T} : Forest (Nonplanar α)) _,
        of'_add (R := R) ({T} : Forest (Nonplanar α)) _,
        mergeOp_factor_out_singleton lbl hT_S hT_S']
    exact congrArg (of' (R := R) ({T} : Forest (Nonplanar α)) * ·) ih'

/-! ### Case 3(a): both accessible terms from the same component -/

/-- **Sideward Merge case 3(a), F̂ = ∅, multi-witness sum form** (M-C-B
    Lemma 1.4.5, p. 55, eq. (1.3.3)).

    `mergeOp lbl α_t β` on the single-component workspace `{T_i}` produces a
    sum over all 2-edge cuts of `T_i` whose crown is `{α_t, β}`. -/
theorem mergeOp_sideward_3a_general_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α) (T_i α_t β : Nonplanar α)
    (h_α_ne_Ti : α_t ≠ T_i) (h_β_ne_Ti : β ≠ T_i) :
    mergeOp (R := R) lbl α_t β (of' ({T_i} : Forest (Nonplanar α)))
      = of' ({Nonplanar.node lbl {α_t, β}} : Forest (Nonplanar α))
        * ((matchingTwoEdgeCutsN T_i α_t β).map (fun p => ofTree (R := R) p.2)).sum := by
  show (mergePost (R := R) (α := α) lbl α_t β ∘ₗ comulAlgHomN.toLinearMap)
       (of' ({T_i} : Forest (Nonplanar α))) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      show comulAlgHomN (R := R) (α := α) (of' ({T_i} : Forest (Nonplanar α)))
          = comulTreeN (R := R) T_i from comulAlgHomN_apply_ofTree T_i]
  unfold comulTreeN
  rw [map_add]
  -- Prim term vanishes (T_i ∉ {α_t, β}).
  rw [show mergePost (R := R) (α := α) lbl α_t β
        (ofTree T_i ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))) = 0 from by
      rw [show (ofTree T_i : ConnesKreimer R (Nonplanar α)) = of' ({T_i} : Forest (Nonplanar α))
            from rfl, mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_T_i_mem : T_i ∈ ({T_i} : Forest (Nonplanar α)) := Multiset.mem_singleton.mpr rfl
      rw [h_eq, show ({α_t, β} : Forest (Nonplanar α)) = α_t ::ₘ ({β} : Forest (Nonplanar α))
            from rfl, Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
      rcases h_T_i_mem with h | h
      · exact h_α_ne_Ti h.symm
      · exact h_β_ne_Ti h.symm]
  rw [zero_add, _root_.map_multiset_sum, Multiset.map_map]
  refine Eq.trans (congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_))
    (ite_mul_sum_eq_mul_filter_sum (cutSummandsN T_i)
      ({α_t, β} : Forest (Nonplanar α))
      (of' ({Nonplanar.node lbl {α_t, β}} : Forest (Nonplanar α))))
  show mergePost (R := R) (α := α) lbl α_t β (of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)
    = if p.1 = ({α_t, β} : Forest (Nonplanar α))
        then of' ({Nonplanar.node lbl {α_t, β}} : Forest (Nonplanar α)) * ofTree (R := R) p.2
        else 0
  rw [mergePost_basis_tensor]

/-- **Sideward Merge case 3(a) realization, F̂ = ∅, unique-witness form.**
    Corollary of `mergeOp_sideward_3a_general_pair` when the 2-edge cut
    producing `{α_t, β}` is uniquely witnessed by `p0`. -/
theorem mergeOp_sideward_3a_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α)
    (T_i α_t β T_i_q : Nonplanar α) (p0 : Forest (Nonplanar α) × Nonplanar α)
    (h_filter : matchingTwoEdgeCutsN T_i α_t β = {p0})
    (h_remainder : p0.2 = T_i_q)
    (h_α_ne_Ti : α_t ≠ T_i) (h_β_ne_Ti : β ≠ T_i) :
    mergeOp (R := R) lbl α_t β (of' ({T_i} : Forest (Nonplanar α)))
      = of' ({Nonplanar.node lbl {α_t, β}, T_i_q} : Forest (Nonplanar α)) := by
  rw [mergeOp_sideward_3a_general_pair lbl T_i α_t β h_α_ne_Ti h_β_ne_Ti, h_filter,
      Multiset.map_singleton, Multiset.sum_singleton, h_remainder, ← of'_singleton, ← of'_add]
  rfl

/-- **Sideward Merge case 3(a) realization, full residual workspace** (M-C-B
    Lemma 1.4.5, p. 55). Generalization of `mergeOp_sideward_3a_pair` via the
    factor-out pattern, parameterised on `(S, S') = (α_t, β)`. -/
theorem mergeOp_sideward_3a {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq (Nonplanar α)] (lbl : α)
    (T_i α_t β T_i_q : Nonplanar α) (p0 : Forest (Nonplanar α) × Nonplanar α)
    (Fhat : Forest (Nonplanar α))
    (h_filter : matchingTwoEdgeCutsN T_i α_t β = {p0})
    (h_remainder : p0.2 = T_i_q)
    (h_α_ne_Ti : α_t ≠ T_i) (h_β_ne_Ti : β ≠ T_i)
    (h_F_disjoint : CutAvoidingForestN ({α_t, β} : Forest (Nonplanar α)) Fhat) :
    mergeOp (R := R) lbl α_t β (of' (({T_i} : Forest (Nonplanar α)) + Fhat))
      = of' (({Nonplanar.node lbl {α_t, β}, T_i_q} : Forest (Nonplanar α)) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_sideward_3a_pair lbl T_i α_t β T_i_q p0 h_filter h_remainder
      h_α_ne_Ti h_β_ne_Ti
  | cons T Fhat' ih =>
    obtain ⟨hT_S, hT_S'⟩ := CutAvoidingForestN.head_pair h_F_disjoint
    have ih' := ih h_F_disjoint.of_cons
    have h_lhs_eq : ({T_i} : Forest (Nonplanar α)) + T ::ₘ Fhat'
                  = ({T} : Forest (Nonplanar α))
                    + (({T_i} : Forest (Nonplanar α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (Nonplanar α)) + Fhat' from rfl]; abel
    have h_rhs_eq : ({Nonplanar.node lbl {α_t, β}, T_i_q} : Forest (Nonplanar α)) + T ::ₘ Fhat'
                  = ({T} : Forest (Nonplanar α))
                    + (({Nonplanar.node lbl {α_t, β}, T_i_q} : Forest (Nonplanar α)) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : Forest (Nonplanar α)) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq, of'_add (R := R) ({T} : Forest (Nonplanar α)) _,
        of'_add (R := R) ({T} : Forest (Nonplanar α)) _,
        mergeOp_factor_out_singleton lbl hT_S hT_S']
    exact congrArg (of' (R := R) ({T} : Forest (Nonplanar α)) * ·) ih'

end Minimalist.Merge
