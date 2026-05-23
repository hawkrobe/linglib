import Linglib.Syntax.Minimalist.Merge.External

/-!
# Sideward Merge: realization + cost-suppression
@cite{marcolli-chomsky-berwick-2025}

Realizes M-C-B Lemmas 1.4.4 + 1.4.5 (book pp. 54-55) for the three
Sideward-flavored cases of §1.4.1, plus the §1.5 cost-suppression
theorems showing they vanish in the ε → 0 limit (Prop 1.5.1, p. 60).

## Verbatim from MCB §1.4.5 (p. 54)

> Case 2(b) corresponds to a case of Sideward Merge. Here, one obtains in
> the new workspace F' a component of the form M(T_i, β) and a component
> of the form T_j/β. Similarly, case 3(b) also represents a case of
> Sideward Merge, where in the resulting workspace F', one has new
> components: M(α, β), as well as T_i/α and T_j/β.

Case 3(a) is the "countercyclic-like" Sideward configuration where
both α and β are accessible terms of the *same* component T_i — the cut
identifying them is a 2-edge cut producing `cutForest = {α_t, β}`.

## Cut identification

- `IsSingleEdgeAccessibleCut T_j β c_β` ↔ `cutForest c_β = {β}`: cut
  extracting a single accessible term β.
- `IsTwoEdgeAccessibleCut T_i α_t β c` ↔ `cutForest c = {α_t, β}`: cut
  extracting two distinct accessible terms (used for case 3(a)).
- `matchingSingleEdgeCuts T β`, `matchingTwoEdgeCuts T α β`: the
  Finsets of cuts matching the corresponding predicate. Used in the
  multi-witness sum form of Lemmas 1.4.4 / 1.4.5 (eq. (1.3.3)).

## Realization theorems

For each case 2b, 3a, 3b:
- `mergeOp_sideward_X_general_pair`: the multi-witness double-sum form
  matching MCB eq. (1.3.3).
- `mergeOp_sideward_X_pair`: a unique-witness corollary collapsing the
  filter set to a singleton `{c_β}` (or `{c_α, c_β}`).
- `mergeOp_sideward_X` (residual): induction over residual workspace
  `Fhat` via `mergeOp_factor_out_singleton` (from `Merge.External`).

## Cost-suppression theorems (§4.1)

Per MCB §1.5 (Minimal Search via ε-weighted derivation cost — rules 1-5
of §1.5.2 with eq. (1.5.1)-(1.5.2), pp. 59-60), Sideward configurations
are *subdominant and suppressed* in the ε → 0 limit because the cost of
extracting an accessible term at depth d carries weight ε^d, which goes
to 0 strictly faster than the EM cost (= ε^0 = 1) for d > 0.

`mergeOp_eps_zero_for_sideward_2b/3a/3b` implement the *negative direction*
(Sideward → 0); the positive direction (IM survives at weight 1) is queued
as Phase 7g — requires extending the ε-weighted substrate with rule 2's
negative-depth weight on the right channel (`ε^{-d_v}` on `T/T_v`).

## Status

Realization theorems sorry-free as of 0.230.808 (Phase 7h closed
mergeOp_sideward_3b_general_pair). Cost-suppression theorems sorry-free
as of 0.230.804.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open ConnesKreimer

/-- A `CutShape c_β : CutShape T_j` **identifies an accessible term β** when
    its forest is the singleton `{β}` — i.e., the cut extracts exactly β
    from T_j as a subforest. This is the substrate predicate corresponding
    to "β ∈ Acc(T_j)" in MCB §1.4.1, witnessed at the algebraic level by
    the existence of an admissible cut producing β. -/
def IsSingleEdgeAccessibleCut {α : Type*} [DecidableEq α]
    (T_j β : TraceTree α Unit) (c_β : CutShape T_j) : Prop :=
  CutShape.cutForest c_β = ({β} : TraceForest α Unit)

instance {α : Type*} [DecidableEq α]
    (T_j β : TraceTree α Unit) (c_β : CutShape T_j) :
    Decidable (IsSingleEdgeAccessibleCut T_j β c_β) := by
  unfold IsSingleEdgeAccessibleCut; infer_instance

/-- The Finset of all admissible cuts on `T` whose `cutForest` equals the
    singleton `{β}`. Used to express MCB Lemma 1.4.4 in its full
    multi-witness sum form (eq. (1.3.3)): `mergeOp` produces a sum over
    all matching cuts, not just a unique witness. -/
def matchingSingleEdgeCuts {α : Type*} [DecidableEq α]
    (T β : TraceTree α Unit) : Finset (CutShape T) :=
  Finset.univ.filter (fun c => CutShape.cutForest c = ({β} : TraceForest α Unit))

/-- The Finset of all 2-edge admissible cuts on `T` whose `cutForest` equals
    `{α_t, β}`. Used for MCB Lemma 1.4.5 (Sideward 3(a)) in its full
    multi-witness sum form. -/
def matchingTwoEdgeCuts {α : Type*} [DecidableEq α]
    (T α_t β : TraceTree α Unit) : Finset (CutShape T) :=
  Finset.univ.filter
    (fun c => CutShape.cutForest c = ({α_t, β} : TraceForest α Unit))

/-- **Sideward Merge case 2(b), F̂ = ∅, multi-witness sum form** (M-C-B
    Lemma 1.4.4, p. 54, full eq. (1.3.3)).

    `mergeOp T_i β` on workspace `{T_i, T_j}` produces a sum over **all**
    admissible cuts `c` on T_j with `cutForest c = {β}`, each contributing
    `forestToHc {.node T_i β} * deletionRightChannel (remainderDeletion c)`.

    This is MCB's Lemma 1.4.4 in its full algebraic form (sum over
    matchings); the unique-witness `mergeOp_sideward_2b_pair` below
    follows as a corollary when `matchingSingleEdgeCuts T_j β = {c_β}`. -/
theorem mergeOp_sideward_2b_general_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i T_j β : TraceTree α Unit)
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_T_i : ∀ c : CutShape T_j, T_i ∉ CutShape.cutForest c)
    (h_distinct : T_i ≠ T_j)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp (R := R) T_i β
        (forestToHc ({T_i, T_j} : TraceForest α Unit))
      = forestToHc (R := R) ({.node T_i β} : TraceForest α Unit)
        * ∑ c ∈ matchingSingleEdgeCuts T_j β,
            deletionRightChannel (R := R) (CutShape.remainderDeletion c) := by
  show (mergePost (R := R) (α := α) T_i β ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulDelAlgHom_pair,
      comulTreeDel_eq_prim_add_sum, comulTreeDel_eq_prim_add_sum]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim_{T_i} × prim_{T_j}): vanishes since T_j ≠ β.
  have h_pp : mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    apply h_β_ne_Tj
    have h1 : ({T_i, T_j} : TraceForest α Unit)
            = ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit) := rfl
    have h2 : ({T_i, β} : TraceForest α Unit)
            = ({T_i} : TraceForest α Unit) + ({β} : TraceForest α Unit) := rfl
    rw [h1, h2] at h_eq
    exact (Multiset.singleton_inj.mp (Multiset.add_right_inj.mp h_eq)).symm
  -- Term 2 (prim_{T_i} × cut sum): contributes the FILTERED sum over matching cuts.
  -- Lemma: each summand evaluates to (if cf c' = {β} then ans else 0).
  have h_summand : ∀ c' : CutShape T_j,
      mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c')))
    = (if CutShape.cutForest c' = ({β} : TraceForest α Unit)
        then forestToHc (R := R) ({.node T_i β} : TraceForest α Unit)
              * deletionRightChannel (R := R) (CutShape.remainderDeletion c')
        else 0) := by
    intro c'
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, one_mul,
        mergePost_basis_tensor]
    by_cases h : ({T_i} : TraceForest α Unit) + CutShape.cutForest c'
               = ({T_i, β} : TraceForest α Unit)
    · have h_cf : CutShape.cutForest c' = ({β} : TraceForest α Unit) := by
        have h_target : ({T_i, β} : TraceForest α Unit)
                      = ({T_i} : TraceForest α Unit) + ({β} : TraceForest α Unit) := rfl
        rw [h_target] at h
        exact Multiset.add_right_inj.mp h
      rw [if_pos h, if_pos h_cf]
    · have h_cf : CutShape.cutForest c' ≠ ({β} : TraceForest α Unit) := by
        intro h_eq; apply h; rw [h_eq]; rfl
      rw [if_neg h, if_neg h_cf]
  have h_ps : mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
      = forestToHc (R := R) ({.node T_i β} : TraceForest α Unit)
        * ∑ c ∈ matchingSingleEdgeCuts T_j β,
            deletionRightChannel (R := R) (CutShape.remainderDeletion c) := by
    rw [Finset.mul_sum]
    simp only [map_sum]
    rw [Finset.sum_congr rfl (fun c' _ => h_summand c')]
    -- Pointwise: (if p c' then K * f c' else 0) = K * (if p c' then f c' else 0).
    rw [show (∑ c' : CutShape T_j,
            (if CutShape.cutForest c' = ({β} : TraceForest α Unit)
              then forestToHc (R := R) ({.node T_i β} : TraceForest α Unit)
                    * deletionRightChannel (R := R) (CutShape.remainderDeletion c')
              else (0 : Hc R α)))
        = (∑ c' : CutShape T_j,
            forestToHc (R := R) ({.node T_i β} : TraceForest α Unit) *
              (if CutShape.cutForest c' = ({β} : TraceForest α Unit)
                then deletionRightChannel (R := R) (CutShape.remainderDeletion c')
                else (0 : Hc R α))) from
        Finset.sum_congr rfl (fun c' _ => by split_ifs <;> simp only [mul_zero])]
    rw [← Finset.mul_sum]
    congr 1
    -- ∑ c', if p c' then f c' else 0 = ∑ c ∈ filter p, f c via Finset.sum_filter.
    exact (Finset.sum_filter
            (fun c : CutShape T_j => CutShape.cutForest c = ({β} : TraceForest α Unit))
            (fun c => deletionRightChannel (R := R) (CutShape.remainderDeletion c))).symm
  -- Term 3 (cut sum × prim_{T_j}): vanishes (T_j ∉ {T_i, β}).
  have h_sp : mergePost (R := R) (α := α) T_i β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Finset.sum_mul]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_j_mem : T_j ∈ CutShape.cutForest c + ({T_j} : TraceForest α Unit) :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
    rw [h_eq] at h_T_j_mem
    rw [show ({T_i, β} : TraceForest α Unit) = T_i ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_j_mem
    rcases h_T_j_mem with h | h
    · exact h_distinct h.symm
    · exact h_β_ne_Tj h.symm
  -- Term 4 (cut sum × cut sum): vanishes (no T_i ∈ cf(c) or cf(c')).
  have h_ss : mergePost (R := R) (α := α) T_i β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c')))
      = 0 := by
    rw [Fintype.sum_mul_sum]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro c' _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_i_mem : T_i ∈ CutShape.cutForest c + CutShape.cutForest c' := by
      rw [h_eq]; exact Multiset.mem_cons_self _ _
    rcases Multiset.mem_add.mp h_T_i_mem with h | h
    · exact CutShape.not_mem_cutForest_self c h
    · exact h_T_j_no_T_i c' h
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [add_zero, zero_add]

/-- **Sideward Merge case 2(b) realization, F̂ = ∅ subcase, didactic
    unique-witness form**. Quick corollary of `mergeOp_sideward_2b_general_pair`
    when β has a UNIQUE matching cut `c_β` on T_j. The unique-witness
    framing is convenient for analyst-supplied derivations but is **not**
    in M-C-B Lemma 1.4.4 (which sums over all matching cuts per eq. (1.3.3)).
    For MCB-faithful claims, prefer the `_general_pair` form above. -/
theorem mergeOp_sideward_2b_pair {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i T_j β T_j_q : TraceTree α Unit)
    (c_β : CutShape T_j)
    (h_cut : IsSingleEdgeAccessibleCut T_j β c_β)
    (h_remainder : CutShape.remainderDeletion c_β = some T_j_q)
    (h_unique : ∀ c : CutShape T_j, c ≠ c_β →
                CutShape.cutForest c ≠ ({β} : TraceForest α Unit))
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_T_i : ∀ c : CutShape T_j, T_i ∉ CutShape.cutForest c)
    (h_distinct : T_i ≠ T_j)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp (R := R) T_i β
        (forestToHc ({T_i, T_j} : TraceForest α Unit))
      = forestToHc ({.node T_i β, T_j_q} : TraceForest α Unit) := by
  -- Quickie corollary of the multi-witness `_general_pair`: the matching
  -- cut set reduces to `{c_β}` under `h_unique`, so the sum collapses to
  -- a single `deletionRightChannel`-of-`c_β` term, which equals
  -- `forestToHc {T_j_q}` by `h_remainder`.
  rw [mergeOp_sideward_2b_general_pair (R := R) T_i T_j β
        h_T_i_no_β h_T_j_no_T_i h_distinct h_β_ne_Tj]
  have h_singleton : matchingSingleEdgeCuts T_j β = {c_β} := by
    apply Finset.ext_iff.mpr
    intro c
    simp only [matchingSingleEdgeCuts, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton]
    constructor
    · intro h_cf
      by_contra h_ne
      exact h_unique c h_ne h_cf
    · intro h_eq; subst h_eq; exact h_cut
  rw [h_singleton, Finset.sum_singleton, h_remainder]
  show forestToHc (R := R) ({.node T_i β} : TraceForest α Unit) *
        forestToHc (R := R) ({T_j_q} : TraceForest α Unit) = _
  rw [← forestToHc_add]; rfl

/-- **Sideward Merge case 2(b) realization, full residual workspace**
    (M-C-B Lemma 1.4.4, p. 54). Generalization of `mergeOp_sideward_2b_pair`
    to arbitrary residual workspace `Fhat` via the factor-out pattern.
    The existing `mergeOp_factor_out_singleton` is parametric in (S, S')
    and applies directly to (S, S') = (T_i, β) with
    `CutAvoidingForest ({T_i, β}) Fhat` providing the per-spectator disjointness. -/
theorem mergeOp_sideward_2b {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i T_j β T_j_q : TraceTree α Unit)
    (c_β : CutShape T_j) (Fhat : TraceForest α Unit)
    (h_cut : IsSingleEdgeAccessibleCut T_j β c_β)
    (h_remainder : CutShape.remainderDeletion c_β = some T_j_q)
    (h_unique : ∀ c : CutShape T_j, c ≠ c_β →
                CutShape.cutForest c ≠ ({β} : TraceForest α Unit))
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_T_i : ∀ c : CutShape T_j, T_i ∉ CutShape.cutForest c)
    (h_distinct : T_i ≠ T_j)
    (h_β_ne_Tj : β ≠ T_j)
    (h_F_disjoint : CutAvoidingForest ({T_i, β} : TraceForest α Unit) Fhat) :
    mergeOp (R := R) T_i β
        (forestToHc (({T_i, T_j} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node T_i β, T_j_q} : TraceForest α Unit) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_sideward_2b_pair T_i T_j β T_j_q c_β
      h_cut h_remainder h_unique h_T_i_no_β h_T_j_no_T_i h_distinct h_β_ne_Tj
  | cons T Fhat' ih =>
    obtain ⟨hT_S, hT_S'⟩ := CutAvoidingForest.head_pair h_F_disjoint
    have ih' := ih h_F_disjoint.of_cons
    have h_lhs_eq : ({T_i, T_j} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({T_i, T_j} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    have h_rhs_eq : ({.node T_i β, T_j_q} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({.node T_i β, T_j_q} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _]
    rw [mergeOp_factor_out_singleton hT_S hT_S']
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'

/-- **Sideward Merge case 3(b), F̂ = ∅, multi-witness sum form** (M-C-B
    Lemma 1.4.4, p. 54, full eq. (1.3.3)).

    `mergeOp α_t β` on `{T_i, T_j}` produces the **double sum** over all
    matching α-cuts on T_i and matching β-cuts on T_j. Output:
    ```
    forestToHc {.node α β} * (∑ α-cuts) * (∑ β-cuts)
    ```
    where the two sums are over `matchingSingleEdgeCuts T_i α_t` and
    `matchingSingleEdgeCuts T_j β` respectively. The unique-witness
    `mergeOp_sideward_3b_pair` follows when both filter sets are
    singletons. -/
theorem mergeOp_sideward_3b_general_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i T_j α_t β : TraceTree α Unit)
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_α : ∀ c : CutShape T_j, α_t ∉ CutShape.cutForest c)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j)
    (h_α_ne_β : α_t ≠ β)
    (h_distinct : T_i ≠ T_j) :
    mergeOp (R := R) α_t β
        (forestToHc ({T_i, T_j} : TraceForest α Unit))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * (∑ c ∈ matchingSingleEdgeCuts T_i α_t,
            deletionRightChannel (R := R) (CutShape.remainderDeletion c))
        * (∑ c' ∈ matchingSingleEdgeCuts T_j β,
            deletionRightChannel (R := R) (CutShape.remainderDeletion c')) := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulDelAlgHom_pair,
      comulTreeDel_eq_prim_add_sum, comulTreeDel_eq_prim_add_sum]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim × prim): vanishes (T_i ∉ {α_t, β}).
  have h_pp : mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_i_mem : T_i ∈ ({T_i, T_j} : TraceForest α Unit) := Multiset.mem_cons_self _ _
    rw [h_eq] at h_T_i_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 2 (prim × cut sum): vanishes (T_i ∉ {α_t, β}).
  have h_ps : mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
      = 0 := by
    rw [Finset.mul_sum]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c' _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, one_mul]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_i_mem : T_i ∈ ({T_i} : TraceForest α Unit) + CutShape.cutForest c' :=
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
    rw [h_eq] at h_T_i_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 3 (cut sum × prim): vanishes (T_j ∉ {α_t, β}).
  have h_sp : mergePost (R := R) (α := α) α_t β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Finset.sum_mul]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_j_mem : T_j ∈ CutShape.cutForest c + ({T_j} : TraceForest α Unit) :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
    rw [h_eq] at h_T_j_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_j_mem
    rcases h_T_j_mem with h | h
    · exact h_α_ne_Tj h.symm
    · exact h_β_ne_Tj h.symm
  -- Term 4 (cut × cut): the surviving cross-terms — multi-witness double sum.
  -- For (c, c') to contribute, need cf c + cf c' = {α_t, β}.
  -- By element analysis: cf c ⊆ {α_t} and cf c' ⊆ {β}, so cf c = {α_t} and cf c' = {β}.
  have h_summand : ∀ (c : CutShape T_i) (c' : CutShape T_j),
      mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
            deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c')))
    = (if CutShape.cutForest c = ({α_t} : TraceForest α Unit) ∧
          CutShape.cutForest c' = ({β} : TraceForest α Unit)
        then forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
              * (deletionRightChannel (R := R) (CutShape.remainderDeletion c)
                * deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
        else 0) := by
    intro c c'
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
    rw [mergePost_basis_tensor]
    by_cases h_sum : CutShape.cutForest c + CutShape.cutForest c'
                   = ({α_t, β} : TraceForest α Unit)
    · -- LHS hits the if_pos branch. Show the conjunction holds.
      rw [if_pos h_sum]
      -- Derive cf c = {α_t} and cf c' = {β} from h_sum.
      have h_split : CutShape.cutForest c = ({α_t} : TraceForest α Unit) ∧
                    CutShape.cutForest c' = ({β} : TraceForest α Unit) := by
        constructor
        · -- cf c = {α_t}: by Multiset.ext on element counts.
          apply Multiset.ext.mpr
          intro x
          have h_count := congrArg (Multiset.count x) h_sum
          rw [Multiset.count_add] at h_count
          by_cases hx_α : x = α_t
          · subst hx_α
            rw [Multiset.count_singleton_self]
            have h_target : Multiset.count x ({x, β} : TraceForest α Unit) = 1 := by
              simp [Multiset.count_cons_self, Multiset.count_singleton, h_α_ne_β]
            rw [h_target] at h_count
            have h_c' : Multiset.count x (CutShape.cutForest c') = 0 :=
              Multiset.count_eq_zero.mpr (h_T_j_no_α c')
            omega
          · rw [Multiset.count_singleton, if_neg hx_α]
            by_cases hx_β : x = β
            · subst hx_β
              exact Multiset.count_eq_zero.mpr (h_T_i_no_β c)
            · have h_target_zero : Multiset.count x ({α_t, β} : TraceForest α Unit) = 0 := by
                show Multiset.count x (α_t ::ₘ ({β} : TraceForest α Unit)) = 0
                rw [Multiset.count_cons, Multiset.count_singleton, if_neg hx_α, if_neg hx_β]
              omega
        · -- cf c' = {β}: symmetric.
          apply Multiset.ext.mpr
          intro x
          have h_count := congrArg (Multiset.count x) h_sum
          rw [Multiset.count_add] at h_count
          by_cases hx_β : x = β
          · subst hx_β
            rw [Multiset.count_singleton_self]
            have h_target : Multiset.count x ({α_t, x} : TraceForest α Unit) = 1 := by
              simp [Multiset.count_cons, Multiset.count_singleton, Ne.symm h_α_ne_β]
            rw [h_target] at h_count
            have h_c : Multiset.count x (CutShape.cutForest c) = 0 :=
              Multiset.count_eq_zero.mpr (h_T_i_no_β c)
            omega
          · rw [Multiset.count_singleton, if_neg hx_β]
            by_cases hx_α : x = α_t
            · subst hx_α
              exact Multiset.count_eq_zero.mpr (h_T_j_no_α c')
            · have h_target_zero : Multiset.count x ({α_t, β} : TraceForest α Unit) = 0 := by
                show Multiset.count x (α_t ::ₘ ({β} : TraceForest α Unit)) = 0
                rw [Multiset.count_cons, Multiset.count_singleton, if_neg hx_α, if_neg hx_β]
              omega
      rw [if_pos h_split]
    · -- LHS hits the if_neg branch. Show the conjunction fails.
      rw [if_neg h_sum]
      rw [if_neg]
      intro ⟨h_c, h_c'⟩
      apply h_sum
      rw [h_c, h_c']
      rfl
  have h_ss : mergePost (R := R) (α := α) α_t β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c')))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * (∑ c ∈ matchingSingleEdgeCuts T_i α_t,
            deletionRightChannel (R := R) (CutShape.remainderDeletion c))
        * (∑ c' ∈ matchingSingleEdgeCuts T_j β,
            deletionRightChannel (R := R) (CutShape.remainderDeletion c')) := by
    rw [Fintype.sum_mul_sum]
    simp only [map_sum]
    rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => h_summand c c'))]
    -- Now: ∑ c, ∑ c', if (cf c = {α_t} ∧ cf c' = {β}) then K * (rd c * rd c') else 0.
    -- Re-express each summand as: K * ((if α-match then rd c else 0) * (if β-match then rd c' else 0)).
    have h_split_summand : ∀ (c : CutShape T_i) (c' : CutShape T_j),
        (if CutShape.cutForest c = ({α_t} : TraceForest α Unit) ∧
              CutShape.cutForest c' = ({β} : TraceForest α Unit)
          then forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
                * (deletionRightChannel (R := R) (CutShape.remainderDeletion c)
                  * deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
          else (0 : Hc R α)) =
        forestToHc (R := R) ({.node α_t β} : TraceForest α Unit) *
          ((if CutShape.cutForest c = ({α_t} : TraceForest α Unit)
              then deletionRightChannel (R := R) (CutShape.remainderDeletion c)
              else 0) *
            (if CutShape.cutForest c' = ({β} : TraceForest α Unit)
              then deletionRightChannel (R := R) (CutShape.remainderDeletion c')
              else 0)) := by
      intro c c'
      by_cases hc : CutShape.cutForest c = ({α_t} : TraceForest α Unit)
      · by_cases hc' : CutShape.cutForest c' = ({β} : TraceForest α Unit)
        · simp [hc, hc']
        · simp [hc, hc']
      · simp [hc]
    rw [Finset.sum_congr rfl
        (fun c _ => Finset.sum_congr rfl (fun c' _ => h_split_summand c c'))]
    -- Now: ∑ c, ∑ c', K * ((if α-match then rd c else 0) * (if β-match then rd c' else 0))
    -- = K * (∑ c, if α-match then rd c else 0) * (∑ c', if β-match then rd c' else 0)
    -- Re-bracket: ∑ c, ∑ c', K * (X c * Y c') = K * (∑ c, X c) * (∑ c', Y c').
    -- Strategy: pull K out of both sums (Finset.mul_sum), then combine the
    -- double sum into a product of two single sums (Fintype.sum_mul_sum).
    have h_factor :
        (∑ c : CutShape T_i, ∑ c' : CutShape T_j,
            forestToHc (R := R) ({.node α_t β} : TraceForest α Unit) *
              ((if CutShape.cutForest c = ({α_t} : TraceForest α Unit)
                  then deletionRightChannel (R := R) (CutShape.remainderDeletion c)
                  else 0) *
                (if CutShape.cutForest c' = ({β} : TraceForest α Unit)
                  then deletionRightChannel (R := R) (CutShape.remainderDeletion c')
                  else 0)))
        = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit) *
            (∑ c : CutShape T_i,
              if CutShape.cutForest c = ({α_t} : TraceForest α Unit)
                then deletionRightChannel (R := R) (CutShape.remainderDeletion c)
                else 0) *
            (∑ c' : CutShape T_j,
              if CutShape.cutForest c' = ({β} : TraceForest α Unit)
                then deletionRightChannel (R := R) (CutShape.remainderDeletion c')
                else 0) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    rw [h_factor]
    -- Convert the inner if-form sums to filter form via Finset.sum_filter.
    rw [show ∑ c : CutShape T_i,
            (if CutShape.cutForest c = ({α_t} : TraceForest α Unit)
              then deletionRightChannel (R := R) (CutShape.remainderDeletion c)
              else 0)
          = ∑ c ∈ matchingSingleEdgeCuts T_i α_t,
              deletionRightChannel (R := R) (CutShape.remainderDeletion c) from
        (Finset.sum_filter _ _).symm]
    rw [show ∑ c' : CutShape T_j,
            (if CutShape.cutForest c' = ({β} : TraceForest α Unit)
              then deletionRightChannel (R := R) (CutShape.remainderDeletion c')
              else 0)
          = ∑ c' ∈ matchingSingleEdgeCuts T_j β,
              deletionRightChannel (R := R) (CutShape.remainderDeletion c') from
        (Finset.sum_filter _ _).symm]
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [zero_add, add_zero]

/-- **Sideward Merge case 3(b) realization, F̂ = ∅ subcase, didactic
    unique-witness form**. Quick corollary of `mergeOp_sideward_3b_general_pair`
    when both `α` (in T_i) and `β` (in T_j) have UNIQUE matching cuts
    `c_α`, `c_β`. The unique-witness framing is convenient for analyst-
    supplied derivations but is **not** in M-C-B Lemma 1.4.4 (which sums
    over all matching cuts per eq. (1.3.3)). For MCB-faithful claims,
    prefer the `_general_pair` form above. -/
theorem mergeOp_sideward_3b_pair {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i T_j α_t β T_i_q T_j_q : TraceTree α Unit)
    (c_α : CutShape T_i) (c_β : CutShape T_j)
    (h_cut_α : IsSingleEdgeAccessibleCut T_i α_t c_α)
    (h_cut_β : IsSingleEdgeAccessibleCut T_j β c_β)
    (h_remainder_α : CutShape.remainderDeletion c_α = some T_i_q)
    (h_remainder_β : CutShape.remainderDeletion c_β = some T_j_q)
    (h_unique_α : ∀ c : CutShape T_i, c ≠ c_α →
                  CutShape.cutForest c ≠ ({α_t} : TraceForest α Unit))
    (h_unique_β : ∀ c : CutShape T_j, c ≠ c_β →
                  CutShape.cutForest c ≠ ({β} : TraceForest α Unit))
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_α : ∀ c : CutShape T_j, α_t ∉ CutShape.cutForest c)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j)
    (h_α_ne_β : α_t ≠ β)
    (h_distinct : T_i ≠ T_j) :
    mergeOp (R := R) α_t β
        (forestToHc ({T_i, T_j} : TraceForest α Unit))
      = forestToHc ({.node α_t β} : TraceForest α Unit)
        * forestToHc (R := R) ({T_i_q} : TraceForest α Unit)
        * forestToHc (R := R) ({T_j_q} : TraceForest α Unit) := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulDelAlgHom_pair,
      comulTreeDel_eq_prim_add_sum, comulTreeDel_eq_prim_add_sum]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim × prim): F_left = {T_i, T_j} ≠ {α, β} (α ≠ T_i, etc.)
  have h_pp : mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    -- {T_i, T_j} = {α, β} ⟹ T_i ∈ {α, β}
    have h_T_i_mem : T_i ∈ ({T_i, T_j} : TraceForest α Unit) :=
      Multiset.mem_cons_self _ _
    rw [h_eq] at h_T_i_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 2 (prim × cut): F_left = {T_i} + cf(c') ≠ {α, β} (T_i ∉ {α, β}).
  have h_ps : mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
      = 0 := by
    rw [Finset.mul_sum]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c' _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, one_mul]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    -- T_i ∈ ({T_i} + cf c'), so T_i ∈ {α, β}.
    have h_T_i_mem : T_i ∈ ({T_i} : TraceForest α Unit) + CutShape.cutForest c' :=
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
    rw [h_eq] at h_T_i_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 3 (cut × prim): symmetric — T_j ∉ {α, β}.
  have h_sp : mergePost (R := R) (α := α) α_t β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Finset.sum_mul]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_j_mem : T_j ∈ CutShape.cutForest c + ({T_j} : TraceForest α Unit) :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
    rw [h_eq] at h_T_j_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_j_mem
    rcases h_T_j_mem with h | h
    · exact h_α_ne_Tj h.symm
    · exact h_β_ne_Tj h.symm
  -- Term 4 (cut × cut): only (c_α, c_β) survives.
  have h_ss : mergePost (R := R) (α := α) α_t β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c')))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * forestToHc (R := R) ({T_i_q} : TraceForest α Unit)
        * forestToHc (R := R) ({T_j_q} : TraceForest α Unit) := by
    rw [Fintype.sum_mul_sum]
    simp only [map_sum]
    rw [Finset.sum_eq_single c_α]
    · rw [Finset.sum_eq_single c_β]
      · -- (c_α, c_β): the surviving cross-term.
        rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
        rw [show CutShape.cutForest c_α + CutShape.cutForest c_β
              = ({α_t, β} : TraceForest α Unit) from by
            rw [show CutShape.cutForest c_α = ({α_t} : TraceForest α Unit) from h_cut_α]
            rw [show CutShape.cutForest c_β = ({β} : TraceForest α Unit) from h_cut_β]
            rfl]
        rw [mergePost_basis_tensor, if_pos rfl]
        rw [h_remainder_α, h_remainder_β]
        show forestToHc (R := R) ({.node α_t β} : TraceForest α Unit) *
              (forestToHc (R := R) ({T_i_q} : TraceForest α Unit) *
                forestToHc (R := R) ({T_j_q} : TraceForest α Unit)) = _
        rw [← mul_assoc]
      · -- c' ≠ c_β at the c_α slot: cf(c_α) + cf(c') ≠ {α, β} (c_α gives {α}, c' ≠ {β})
        intro c' _ hc'_ne
        rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
        rw [mergePost_basis_tensor, if_neg]
        intro h_eq
        apply h_unique_β c' hc'_ne
        rw [show CutShape.cutForest c_α = ({α_t} : TraceForest α Unit) from h_cut_α] at h_eq
        have h_target : ({α_t, β} : TraceForest α Unit)
                      = ({α_t} : TraceForest α Unit) + ({β} : TraceForest α Unit) := rfl
        rw [h_target] at h_eq
        exact Multiset.add_right_inj.mp h_eq
      · intro h; exact absurd (Finset.mem_univ _) h
    · -- c ≠ c_α at the outer slot: cf(c) + cf(c') ≠ {α, β} for all c'
      intro c _ hc_ne
      apply Finset.sum_eq_zero
      intro c' _
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      -- α ∈ cf(c) + cf(c') = {α, β}
      have h_α_mem : α_t ∈ CutShape.cutForest c + CutShape.cutForest c' := by
        rw [h_eq]
        exact Multiset.mem_cons_self _ _
      rcases Multiset.mem_add.mp h_α_mem with h | h
      · -- α_t ∈ cf(c). Show cf(c) = {α_t} via element-count analysis on
        -- cf(c) + cf(c') = {α_t, β}, then contradict h_unique_α.
        apply h_unique_α c hc_ne
        -- Strategy: prove cf(c) = {α_t} by Multiset.ext (count-equality on each x).
        apply Multiset.ext.mpr
        intro x
        -- Both sides have count 0 except at x = α_t (count 1).
        -- count x (cf(c) + cf(c')) = count x cf(c) + count x cf(c') = count x {α_t, β}.
        have h_count_sum := congrArg (Multiset.count x) h_eq
        rw [Multiset.count_add] at h_count_sum
        by_cases hx_α : x = α_t
        · -- x = α_t: count α_t in cf(c) = 1.
          subst hx_α
          rw [Multiset.count_singleton_self]
          -- count x ({x, β}) = 1 (since x ≠ β; here `x` is α_t after subst)
          have h_count_target :
              Multiset.count x (({x, β} : TraceForest α Unit)) = 1 := by
            simp [Multiset.count_cons_self, Multiset.count_singleton, h_α_ne_β]
          rw [h_count_target] at h_count_sum
          -- count x (cf c') = 0 (h_T_j_no_α)
          have h_count_c' : Multiset.count x (CutShape.cutForest c') = 0 :=
            Multiset.count_eq_zero.mpr (h_T_j_no_α c')
          rw [h_count_c', add_zero] at h_count_sum
          exact h_count_sum
        · -- x ≠ α_t: count = 0 in {α_t}; need count = 0 in cf(c).
          rw [Multiset.count_singleton]
          rw [if_neg hx_α]
          by_cases hx_β : x = β
          · -- x = β: count β cf(c) = 0 by h_T_i_no_β
            subst hx_β
            exact Multiset.count_eq_zero.mpr (h_T_i_no_β c)
          · -- x ∉ {α_t, β}: count x {α_t, β} = 0, so count x cf(c) = 0.
            have h_count_target_zero :
                Multiset.count x (({α_t, β} : TraceForest α Unit)) = 0 := by
              show Multiset.count x (α_t ::ₘ ({β} : TraceForest α Unit)) = 0
              rw [Multiset.count_cons, Multiset.count_singleton,
                  if_neg hx_α, if_neg hx_β]
            rw [h_count_target_zero] at h_count_sum
            exact (Nat.add_eq_zero_iff.mp h_count_sum).1
      · exact h_T_j_no_α c' h
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [zero_add, add_zero]

/-- **Sideward Merge case 3(b) realization, full residual workspace**
    (M-C-B Lemma 1.4.4, p. 54). Generalization of `mergeOp_sideward_3b_pair`
    via the factor-out pattern, parameterised on (S, S') = (α_t, β). -/
theorem mergeOp_sideward_3b {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i T_j α_t β T_i_q T_j_q : TraceTree α Unit)
    (c_α : CutShape T_i) (c_β : CutShape T_j) (Fhat : TraceForest α Unit)
    (h_cut_α : IsSingleEdgeAccessibleCut T_i α_t c_α)
    (h_cut_β : IsSingleEdgeAccessibleCut T_j β c_β)
    (h_remainder_α : CutShape.remainderDeletion c_α = some T_i_q)
    (h_remainder_β : CutShape.remainderDeletion c_β = some T_j_q)
    (h_unique_α : ∀ c : CutShape T_i, c ≠ c_α →
                  CutShape.cutForest c ≠ ({α_t} : TraceForest α Unit))
    (h_unique_β : ∀ c : CutShape T_j, c ≠ c_β →
                  CutShape.cutForest c ≠ ({β} : TraceForest α Unit))
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_α : ∀ c : CutShape T_j, α_t ∉ CutShape.cutForest c)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j)
    (h_α_ne_β : α_t ≠ β)
    (h_distinct : T_i ≠ T_j)
    (h_F_disjoint : CutAvoidingForest ({α_t, β} : TraceForest α Unit) Fhat) :
    mergeOp (R := R) α_t β
        (forestToHc (({T_i, T_j} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node α_t β, T_i_q, T_j_q} : TraceForest α Unit) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    -- The pair version produces forestToHc {.node α β} * forestToHc {T_i_q} * forestToHc {T_j_q}.
    -- Convert to forestToHc {.node α β, T_i_q, T_j_q}.
    have h_pair := mergeOp_sideward_3b_pair (R := R)
      T_i T_j α_t β T_i_q T_j_q c_α c_β
      h_cut_α h_cut_β h_remainder_α h_remainder_β h_unique_α h_unique_β
      h_T_i_no_β h_T_j_no_α h_α_ne_Ti h_α_ne_Tj h_β_ne_Ti h_β_ne_Tj h_α_ne_β h_distinct
    rw [h_pair]
    rw [show forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
            * forestToHc (R := R) ({T_i_q} : TraceForest α Unit)
            * forestToHc (R := R) ({T_j_q} : TraceForest α Unit)
        = forestToHc (R := R) (({.node α_t β} : TraceForest α Unit)
                                + ({T_i_q} : TraceForest α Unit)
                                + ({T_j_q} : TraceForest α Unit)) from by
        rw [forestToHc_add, forestToHc_add]]
    congr 1
  | cons T Fhat' ih =>
    obtain ⟨hT_S, hT_S'⟩ := CutAvoidingForest.head_pair h_F_disjoint
    have ih' := ih h_F_disjoint.of_cons
    have h_lhs_eq : ({T_i, T_j} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({T_i, T_j} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    have h_rhs_eq : ({.node α_t β, T_i_q, T_j_q} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({.node α_t β, T_i_q, T_j_q} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _]
    rw [mergeOp_factor_out_singleton hT_S hT_S']
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'

/-- **Sideward Merge case 3(a) realization** ("Countercyclic-like Merge",
    M-C-B Lemma 1.4.5, p. 55). Both α and β are disjoint accessible terms
    of the *same* component T_i. The operator `δ_{α, β}` selects
    `T_v ⊔ T_w ⊗ (T_i/(T_v ⊔ T_w) ⊔ F̂)`, producing
    `{M(α, β), T_i/(α ⊔ β)} + Fhat`.

    Proof strategy: the surviving cross-term comes from a single
    *2-edge* admissible cut on T_i (extracting both α ≃ T_v and
    β ≃ T_w as separate subforest elements), yielding `cutForest =
    {α, β}` as a 2-element multiset. This requires the substrate
    extension `IsTwoEdgeAccessibleCut T_i α β c` (hypothesis below):
    a cut whose cutForest contains exactly α and β as distinct
    elements. The mergePost cross-term selection criterion then becomes
    `cutForest c = {α, β}`. -/
def IsTwoEdgeAccessibleCut {α : Type*} [DecidableEq α]
    (T_i α_t β : TraceTree α Unit) (c : CutShape T_i) : Prop :=
  CutShape.cutForest c = ({α_t, β} : TraceForest α Unit)

instance {α : Type*} [DecidableEq α]
    (T_i α_t β : TraceTree α Unit) (c : CutShape T_i) :
    Decidable (IsTwoEdgeAccessibleCut T_i α_t β c) := by
  unfold IsTwoEdgeAccessibleCut; infer_instance

/-- **Sideward Merge case 3(a), F̂ = ∅, multi-witness sum form** (M-C-B
    Lemma 1.4.5, p. 55, full eq. (1.3.3)).

    `mergeOp α_t β` on workspace `{T_i}` produces a sum over **all**
    2-edge admissible cuts `c` on T_i with `cutForest c = {α_t, β}`,
    each contributing `forestToHc {.node α_t β} * deletionRightChannel
    (remainderDeletion c)`. The unique-witness `mergeOp_sideward_3a_pair`
    follows as a corollary. -/
theorem mergeOp_sideward_3a_general_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i α_t β : TraceTree α Unit)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_β_ne_Ti : β ≠ T_i) :
    mergeOp (R := R) α_t β (forestToHc ({T_i} : TraceForest α Unit))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * ∑ c ∈ matchingTwoEdgeCuts T_i α_t β,
            deletionRightChannel (R := R) (CutShape.remainderDeletion c) := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({T_i} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [show comulDelAlgHom (R := R) (α := α)
            (forestToHc (R := R) ({T_i} : TraceForest α Unit))
          = comulTreeDel (R := R) T_i from by
      unfold forestToHc
      rw [comulDelAlgHom_apply_single, comulForestDel_singleton]]
  rw [comulTreeDel_eq_prim_add_sum]
  simp only [map_add]
  -- Term 1 (prim_{T_i}): vanishes (T_i ∉ {α_t, β}).
  have h_p : mergePost (R := R) (α := α) α_t β
        (forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)) = 0 := by
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_i_mem : T_i ∈ ({T_i} : TraceForest α Unit) := Multiset.mem_singleton.mpr rfl
    rw [h_eq] at h_T_i_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 2 (sum c'): contributes the filtered sum over matching 2-edge cuts.
  have h_summand : ∀ c' : CutShape T_i,
      mergePost (R := R) (α := α) α_t β
        (forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
          deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
    = (if CutShape.cutForest c' = ({α_t, β} : TraceForest α Unit)
        then forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
              * deletionRightChannel (R := R) (CutShape.remainderDeletion c')
        else 0) := by
    intro c'
    rw [mergePost_basis_tensor]
  have h_s : mergePost (R := R) (α := α) α_t β
        (∑ c' : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * ∑ c ∈ matchingTwoEdgeCuts T_i α_t β,
            deletionRightChannel (R := R) (CutShape.remainderDeletion c) := by
    simp only [map_sum]
    rw [Finset.sum_congr rfl (fun c' _ => h_summand c')]
    rw [show (∑ c' : CutShape T_i,
            (if CutShape.cutForest c' = ({α_t, β} : TraceForest α Unit)
              then forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
                    * deletionRightChannel (R := R) (CutShape.remainderDeletion c')
              else (0 : Hc R α)))
        = (∑ c' : CutShape T_i,
            forestToHc (R := R) ({.node α_t β} : TraceForest α Unit) *
              (if CutShape.cutForest c' = ({α_t, β} : TraceForest α Unit)
                then deletionRightChannel (R := R) (CutShape.remainderDeletion c')
                else (0 : Hc R α))) from
        Finset.sum_congr rfl (fun c' _ => by split_ifs <;> simp only [mul_zero])]
    rw [← Finset.mul_sum]
    congr 1
    exact (Finset.sum_filter
            (fun c : CutShape T_i => CutShape.cutForest c = ({α_t, β} : TraceForest α Unit))
            (fun c => deletionRightChannel (R := R) (CutShape.remainderDeletion c))).symm
  rw [h_p, h_s, zero_add]

/-- **Sideward Merge case 3(a) realization, F̂ = ∅ subcase, didactic
    unique-witness form**. Quick corollary of `mergeOp_sideward_3a_general_pair`
    when the 2-edge cut producing `{α_t, β}` is uniquely witnessed by `c`.
    The unique-witness framing is convenient for analyst-supplied derivations
    but is **not** in M-C-B Lemma 1.4.5 (which sums over all matching 2-edge
    cuts per eq. (1.3.3)). For MCB-faithful claims, prefer the `_general_pair`
    form above. -/
theorem mergeOp_sideward_3a_pair {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i α_t β T_i_q : TraceTree α Unit)
    (c : CutShape T_i)
    (h_cut : IsTwoEdgeAccessibleCut T_i α_t β c)
    (h_remainder : CutShape.remainderDeletion c = some T_i_q)
    (h_unique : ∀ c' : CutShape T_i, c' ≠ c →
                CutShape.cutForest c' ≠ ({α_t, β} : TraceForest α Unit))
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_β_ne_Ti : β ≠ T_i)
    (_h_α_ne_β : α_t ≠ β) :
    mergeOp (R := R) α_t β (forestToHc ({T_i} : TraceForest α Unit))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * forestToHc (R := R) ({T_i_q} : TraceForest α Unit) := by
  -- Quickie corollary of the multi-witness `_general_pair`: the matching
  -- 2-edge cut set reduces to `{c}` under `h_unique`.
  rw [mergeOp_sideward_3a_general_pair (R := R) T_i α_t β h_α_ne_Ti h_β_ne_Ti]
  have h_singleton : matchingTwoEdgeCuts T_i α_t β = {c} := by
    apply Finset.ext_iff.mpr
    intro c'
    simp only [matchingTwoEdgeCuts, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton]
    constructor
    · intro h_cf
      by_contra h_ne
      exact h_unique c' h_ne h_cf
    · intro h_eq; subst h_eq; exact h_cut
  rw [h_singleton, Finset.sum_singleton, h_remainder]
  rfl

/-- **Sideward Merge case 3(a) realization, full residual workspace**
    (M-C-B Lemma 1.4.5, p. 55). Generalization of `mergeOp_sideward_3a_pair`
    via the factor-out pattern, parameterised on (S, S') = (α_t, β). -/
theorem mergeOp_sideward_3a {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i α_t β T_i_q : TraceTree α Unit)
    (c : CutShape T_i) (Fhat : TraceForest α Unit)
    (h_cut : IsTwoEdgeAccessibleCut T_i α_t β c)
    (h_remainder : CutShape.remainderDeletion c = some T_i_q)
    (h_unique : ∀ c' : CutShape T_i, c' ≠ c →
                CutShape.cutForest c' ≠ ({α_t, β} : TraceForest α Unit))
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_β_ne_Ti : β ≠ T_i)
    (h_α_ne_β : α_t ≠ β)
    (h_F_disjoint : CutAvoidingForest ({α_t, β} : TraceForest α Unit) Fhat) :
    mergeOp (R := R) α_t β
        (forestToHc (({T_i} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node α_t β, T_i_q} : TraceForest α Unit) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    have h_pair := mergeOp_sideward_3a_pair (R := R)
      T_i α_t β T_i_q c h_cut h_remainder h_unique h_α_ne_Ti h_β_ne_Ti h_α_ne_β
    rw [h_pair]
    rw [show forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
            * forestToHc (R := R) ({T_i_q} : TraceForest α Unit)
        = forestToHc (R := R) (({.node α_t β} : TraceForest α Unit)
                                + ({T_i_q} : TraceForest α Unit)) from by
        rw [forestToHc_add]]
    congr 1
  | cons T Fhat' ih =>
    obtain ⟨hT_S, hT_S'⟩ := CutAvoidingForest.head_pair h_F_disjoint
    have ih' := ih h_F_disjoint.of_cons
    have h_lhs_eq : ({T_i} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({T_i} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    have h_rhs_eq : ({.node α_t β, T_i_q} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({.node α_t β, T_i_q} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _]
    rw [mergeOp_factor_out_singleton hT_S hT_S']
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'
/-- **Cost-suppression for Sideward 2(b)** (MCB §1.5.3 + §1.4.5).
    At ε = 0, applying `mergeOp_eps 0 T_i β` to the workspace
    `{T_i, T_j}` (where β is an accessible term of T_j, not a component)
    yields **0** — the Sideward 2(b) realization of `mergeOp` (which
    consumes the cut producing β) is entirely absent at ε = 0 because
    `comulTreeDel_eps 0 T_j` reduces to the primitive part
    `(T_j ⊗ 1) + (1 ⊗ T_j)` (no cut subforests).

    No primitive cross-term of (prim T_i) × (prim T_j) has LEFT-channel
    forest equal to `{T_i, β}` (since β ∉ {T_i, T_j} when β ≠ T_i and
    β ≠ T_j); `mergePost` annihilates all four. -/
theorem mergeOp_eps_zero_for_sideward_2b {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i T_j β : TraceTree α Unit)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp_eps (R := R) 0 T_i β
        (forestToHc ({T_i, T_j} : TraceForest α Unit)) = 0 := by
  show (mergePost (R := R) (α := α) T_i β ∘ₗ
        (comulDelAlgHom_eps (0 : R)).toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = 0
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  show mergePost (R := R) (α := α) T_i β
        (comulDelAlgHom_eps (R := R) (α := α) (0 : R)
          (Finsupp.single ({T_i, T_j} : TraceForest α Unit) (1 : R))) = 0
  rw [comulDelAlgHom_eps_apply_single]
  show mergePost (R := R) (α := α) T_i β
        ((({T_i, T_j} : TraceForest α Unit).map
          (comulTreeDel_eps (R := R) 0)).prod) = 0
  rw [show (({T_i, T_j} : TraceForest α Unit).map (comulTreeDel_eps (R := R) 0)).prod
      = comulTreeDel_eps (R := R) 0 T_i * comulTreeDel_eps (R := R) 0 T_j from
    Multiset.prod_pair _ _]
  rw [comulTreeDel_eps_zero, comulTreeDel_eps_zero]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- 4 cross-terms; LEFT-channel forest = {T_i, T_j}, {T_i}, {T_j}, ∅ — all ≠ {T_i, β}.
  -- Term 1 (prim × prim): LEFT = {T_i, T_j} ≠ {T_i, β} (since T_j ≠ β).
  rw [show mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
      rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      apply h_β_ne_Tj
      have h_target : ({T_i, β} : TraceForest α Unit)
                    = ({T_i} : TraceForest α Unit) + ({β} : TraceForest α Unit) := rfl
      have h_lhs : ({T_i, T_j} : TraceForest α Unit)
                 = ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit) := rfl
      rw [h_lhs, h_target] at h_eq
      exact (Multiset.singleton_inj.mp (Multiset.add_right_inj.mp h_eq)).symm]
  -- Term 2 (prim × empty): LEFT = {T_i}; cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_j} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_i} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({T_i, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 3 (empty × prim): LEFT = {T_j}; cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) T_i β
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_j} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({T_i, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 4 (empty × empty): LEFT = ∅; cardinality 0 ≠ 2.
  rw [show mergePost (R := R) (α := α) T_i β
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_j} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          show (1 : Hc R α) = forestToHc (R := R) (0 : TraceForest α Unit) from
            forestToHc_zero.symm,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : (0 : TraceForest α Unit).card = 0 := Multiset.card_zero
      have h_card_rhs : ({T_i, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  simp only [add_zero]

/-- **Cost-suppression for Sideward 3(a)** (MCB §1.5.3 + §1.4.6).
    At ε = 0, applying `mergeOp_eps 0 α_t β` to the single-component
    workspace `{T_i}` (where α_t, β are accessible terms of T_i) yields
    **0**. Same reasoning: at ε = 0 only the primitive part of
    `comulTreeDel_eps 0 T_i = (T_i ⊗ 1) + (1 ⊗ T_i)` survives; neither
    primitive contributes LEFT = {α_t, β}. -/
theorem mergeOp_eps_zero_for_sideward_3a {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i α_t β : TraceTree α Unit)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_β_ne_Ti : β ≠ T_i) :
    mergeOp_eps (R := R) 0 α_t β
        (forestToHc ({T_i} : TraceForest α Unit)) = 0 := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ
        (comulDelAlgHom_eps (0 : R)).toLinearMap)
       (forestToHc ({T_i} : TraceForest α Unit)) = 0
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  show mergePost (R := R) (α := α) α_t β
        (comulDelAlgHom_eps (R := R) (α := α) (0 : R)
          (Finsupp.single ({T_i} : TraceForest α Unit) (1 : R))) = 0
  rw [comulDelAlgHom_eps_apply_single]
  show mergePost (R := R) (α := α) α_t β
        ((({T_i} : TraceForest α Unit).map
          (comulTreeDel_eps (R := R) 0)).prod) = 0
  rw [Multiset.map_singleton, Multiset.prod_singleton, comulTreeDel_eps_zero]
  -- comulTreeDel_eps 0 T_i = (T_i ⊗ 1) + (1 ⊗ T_i); both vanish under mergePost.
  simp only [map_add]
  -- Term 1 (T_i ⊗ 1): LEFT = {T_i}, cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        (forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
        = 0 from by
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_i} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 2 (1 ⊗ T_i): LEFT = ∅, cardinality 0 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
        = 0 from by
      rw [show (1 : Hc R α) = forestToHc (R := R) (0 : TraceForest α Unit) from
            forestToHc_zero.symm,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : (0 : TraceForest α Unit).card = 0 := Multiset.card_zero
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  rw [add_zero]

/-- **Cost-suppression for Sideward 3(b)** (MCB §1.5.3 + §1.4.5).
    At ε = 0, applying `mergeOp_eps 0 α_t β` to a 2-component workspace
    `{T_i, T_j}` where α_t ∈ Acc(T_i), β ∈ Acc(T_j) yields **0**. Same
    reasoning as 2(b): only primitive parts survive at ε = 0, and no
    primitive cross-term has LEFT = {α_t, β}. -/
theorem mergeOp_eps_zero_for_sideward_3b {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i T_j α_t β : TraceTree α Unit)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp_eps (R := R) 0 α_t β
        (forestToHc ({T_i, T_j} : TraceForest α Unit)) = 0 := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ
        (comulDelAlgHom_eps (0 : R)).toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = 0
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  show mergePost (R := R) (α := α) α_t β
        (comulDelAlgHom_eps (R := R) (α := α) (0 : R)
          (Finsupp.single ({T_i, T_j} : TraceForest α Unit) (1 : R))) = 0
  rw [comulDelAlgHom_eps_apply_single]
  show mergePost (R := R) (α := α) α_t β
        ((({T_i, T_j} : TraceForest α Unit).map
          (comulTreeDel_eps (R := R) 0)).prod) = 0
  rw [show (({T_i, T_j} : TraceForest α Unit).map (comulTreeDel_eps (R := R) 0)).prod
      = comulTreeDel_eps (R := R) 0 T_i * comulTreeDel_eps (R := R) 0 T_j from
    Multiset.prod_pair _ _]
  rw [comulTreeDel_eps_zero, comulTreeDel_eps_zero]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- 4 cross-terms; LEFT-channel forests {T_i, T_j}, {T_i}, {T_j}, ∅ — all ≠ {α_t, β}.
  -- Term 1 (prim × prim): LEFT = {T_i, T_j}. T_i ∉ {α_t, β} → ≠.
  rw [show mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
      rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_T_i_mem : T_i ∈ ({T_i, T_j} : TraceForest α Unit) :=
        Multiset.mem_cons_self _ _
      rw [h_eq] at h_T_i_mem
      rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
          Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
      rcases h_T_i_mem with h | h
      · exact h_α_ne_Ti h.symm
      · exact h_β_ne_Ti h.symm]
  -- Term 2 (prim × empty): LEFT = {T_i}; cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_j} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_i} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 3 (empty × prim): LEFT = {T_j}; cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_j} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 4 (empty × empty): LEFT = ∅; cardinality 0 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_j} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          show (1 : Hc R α) = forestToHc (R := R) (0 : TraceForest α Unit) from
            forestToHc_zero.symm,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : (0 : TraceForest α Unit).card = 0 := Multiset.card_zero
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  simp only [add_zero]


end Minimalist.Merge
