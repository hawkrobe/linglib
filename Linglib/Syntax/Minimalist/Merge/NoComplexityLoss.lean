import Linglib.Syntax.Minimalist.Merge.Internal

/-!
# No Complexity Loss (NCL) for algebraic Merge
[marcolli-chomsky-berwick-2025] Proposition 1.6.10, book p. 72.

Implements M-C-B Definition 1.6.2 (book p. 64) and Proposition 1.6.10
(book p. 72) on the canonical carrier: a workspace transformation
`F → F'` (over `Forest (Nonplanar α)`) satisfies **No Complexity Loss** if
some component map `Φ₀` is nondecreasing in **degree**.

## Grading choice: vertex count

M-C-B grade by leaf count `#L`. We grade by `Nonplanar.numNodes` (vertex
count) — the canonical Connes–Kreimer grading. The deletion coproduct
conserves weight **exactly** (`cutSummandsN_numNodes`) for every cut, with
none of the nullary-node corrections that leaf count incurs when a node
loses all its children under a multi-edge cut. NCL is a *nondecreasing*
condition, and weight delivers every conclusion leaf count would: the
Merge node's weight strictly exceeds each operand's (`numNodes_node` adds
the root), and every deletion quotient's weight is strictly smaller than
its source (a nonempty crown carries positive weight). So the
weight-graded NCL is both cleaner and strictly-more-robust than a
leaf-count port.

## Contents

- `NCLBetween F F'`: existential form — some component map is
  weight-nondecreasing.
- `em_case1_satisfiesNCL`: EM Case 1 `{S, S'} + F̂ → {M(S,S')} + F̂` via
  `S, S' ↦ M(S,S')`, spectators fixed.
- `im_satisfiesNCL`: IM `{T} → {M(Q, β)}` (Q = T/β via a single-edge cut)
  via the constant map; weight follows from `cutSummandsN_numNodes`.
- `InducedMapNCL`/`DLPerComponent`: MCB Def 1.6.2 strict form + the
  per-component degree-loss function (eq. 1.6.4).
- `sideward_{2b,3a,3b}_violatesInducedMapNCL`: under the canonical induced
  map, each Sideward configuration fails NCL — the deletion quotient is
  strictly lighter than its source.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open RootedTree RootedTree.ConnesKreimer

/-- **M-C-B Definition 1.6.2 (book p. 64), existential form.** A workspace
    transformation `F → F'` satisfies No Complexity Loss if some component
    map `Φ₀` lands in `F'` and never decreases `weight` (the vertex-count
    Hopf grading; see the module docstring on the grading choice). -/
def NCLBetween {α : Type*} (F F' : Forest (Nonplanar α)) : Prop :=
  ∃ (Φ₀ : ∀ T, T ∈ F → Nonplanar α),
    (∀ T (h : T ∈ F), Φ₀ T h ∈ F') ∧
    (∀ T (h : T ∈ F), (Φ₀ T h).numNodes ≥ T.numNodes)

/-- **M-C-B Prop 1.6.10, EM Case-1 direction.** The EM workspace equation
    carries a component map satisfying NCL: `S, S' ↦ M(S, S')` (weight
    increases by `1 +` the other operand's weight); each `T ∈ F̂ ↦` itself
    (weight preserved).

    Quoting M-C-B (book p. 72): "deg(𝔐(T_i, T_j)) = deg(T_i) + deg(T_j),
    which is greater than or equal to both deg(T_i) and deg(T_j). All the
    remaining components of the workspace not used by Merge maintain the
    same degree." -/
theorem em_case1_satisfiesNCL {α : Type*} [DecidableEq (Nonplanar α)]
    (lbl : α) (S S' : Nonplanar α) (Fhat : Forest (Nonplanar α)) :
    NCLBetween (({S, S'} : Forest (Nonplanar α)) + Fhat)
               (({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) + Fhat) := by
  refine ⟨fun T _ => if T = S ∨ T = S' then Nonplanar.node lbl {S, S'} else T, ?_, ?_⟩
  -- (a) image is in F'
  · intro T hT
    show (if T = S ∨ T = S' then Nonplanar.node lbl {S, S'} else T)
            ∈ ({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) + Fhat
    by_cases hcase : T = S ∨ T = S'
    · rw [if_pos hcase]
      exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
    · rw [if_neg hcase]
      have hT_Fhat : T ∈ Fhat := by
        rcases Multiset.mem_add.mp hT with hT_pair | hT_Fhat
        · exfalso; apply hcase
          rw [show ({S, S'} : Forest (Nonplanar α)) = S ::ₘ {S'} from rfl,
              Multiset.mem_cons, Multiset.mem_singleton] at hT_pair
          exact hT_pair
        · exact hT_Fhat
      exact Multiset.mem_add.mpr (Or.inr hT_Fhat)
  -- (b) weight nondecreasing
  · intro T _
    show (if T = S ∨ T = S' then Nonplanar.node lbl {S, S'} else T).numNodes ≥ T.numNodes
    by_cases hcase : T = S ∨ T = S'
    · rw [if_pos hcase, Nonplanar.numNodes_node,
          show ({S, S'} : Forest (Nonplanar α)) = S ::ₘ {S'} from rfl,
          Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton]
      rcases hcase with rfl | rfl <;> omega
    · rw [if_neg hcase]

/-- **M-C-B Prop 1.6.10, IM positive direction.** The IM workspace
    transformation `{T} → {M(Q, β)}` (Q = T/β the deletion-quotient of the
    single-edge cut `p0` extracting β) carries the constant component map
    `T ↦ M(Q, β)`, with `(M(Q, β)).numNodes = 1 + Q.numNodes + β.numNodes =
    1 + T.numNodes ≥ T.numNodes` by `cutSummandsN_numNodes`.

    Quoting M-C-B (book p. 72): "For Internal Merge, similarly,
    deg(T_v, T/T_v) = deg(T)." (Under the weight grading the Merge node
    adds its own vertex, so the inequality is strict; NCL holds a fortiori.)

    No `T ≠ β` hypothesis is required (cf. `mergeOp_im_composition`, which
    needs it for non-degeneracy of the algebraic sum, not for NCL). -/
theorem im_satisfiesNCL {α : Type*} (lbl : α) (β T Q : Nonplanar α)
    (p0 : Forest (Nonplanar α) × Nonplanar α) (hp0 : p0 ∈ cutSummandsN T)
    (h_cf : p0.1 = ({β} : Forest (Nonplanar α)))
    (h_remainder : p0.2 = Q) :
    NCLBetween (({T} : Forest (Nonplanar α)))
               (({Nonplanar.node lbl {Q, β}} : Forest (Nonplanar α))) := by
  refine ⟨fun _ _ => Nonplanar.node lbl {Q, β}, ?_, ?_⟩
  -- (a) image is in {M(Q, β)}
  · intro _ _; exact Multiset.mem_singleton.mpr rfl
  -- (b) weight nondecreasing: (M(Q, β)).numNodes = 1 + T.numNodes ≥ T.numNodes
  · intro T' hT'
    rw [Multiset.mem_singleton] at hT'
    subst T'
    show (Nonplanar.node lbl {Q, β}).numNodes ≥ T.numNodes
    rw [Nonplanar.numNodes_node,
        show ({Q, β} : Forest (Nonplanar α)) = Q ::ₘ {β} from rfl,
        Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton]
    have h_cons := cutSummandsN_numNodes T p0 hp0
    rw [h_cf] at h_cons
    simp only [Multiset.map_singleton, Multiset.sum_singleton] at h_cons
    rw [h_remainder] at h_cons
    omega

/-! ### InducedMapNCL — MCB Def 1.6.2 with the canonical map -/

/-- **MCB Definition 1.6.2 (book p. 64), strict form.** The canonical
    induced map `Φ_0 : π_0(F) → π_0(Φ(F))` is named explicitly. NCL holds
    iff every component `T ∈ F` has `(Φ_0 T).numNodes ≥ T.numNodes`.

    Compare `NCLBetween` (existential: "some map works"). The strict form
    is needed for the negative direction: a Sideward operation might satisfy
    `NCLBetween` via some non-canonical map, but its canonical map (each
    root to where its image lives) fails. -/
def InducedMapNCL {α : Type*} (F F' : Forest (Nonplanar α))
    (Φ_0 : ∀ T, T ∈ F → Nonplanar α) : Prop :=
  (∀ T (h : T ∈ F), Φ_0 T h ∈ F') ∧
  (∀ T (h : T ∈ F), (Φ_0 T h).numNodes ≥ T.numNodes)

/-- Strict form ⇒ existential form. -/
theorem NCLBetween_of_InducedMapNCL {α : Type*}
    {F F' : Forest (Nonplanar α)} {Φ_0 : ∀ T, T ∈ F → Nonplanar α}
    (h : InducedMapNCL F F' Φ_0) : NCLBetween F F' :=
  ⟨Φ_0, h.1, h.2⟩

/-- **MCB eq. 1.6.4 — per-component degree-loss function.** Per-component
    weight difference; NCL ⇔ all values `≥ 0` (matches `InducedMapNCL.2`).
    `Int`-valued so violations surface as negative numbers rather than being
    clamped by ℕ-subtraction. -/
def DLPerComponent {α : Type*} {F : Forest (Nonplanar α)}
    (Φ_0 : ∀ T, T ∈ F → Nonplanar α) (T : Nonplanar α) (h : T ∈ F) : Int :=
  ((Φ_0 T h).numNodes : Int) - T.numNodes

/-- NCL inequality (eq. 1.6.3) per component restated via `DLPerComponent`. -/
theorem DLPerComponent_nonneg_iff_NCL {α : Type*}
    {F F' : Forest (Nonplanar α)} (Φ_0 : ∀ T, T ∈ F → Nonplanar α)
    (h_image : ∀ T (h : T ∈ F), Φ_0 T h ∈ F') :
    InducedMapNCL F F' Φ_0 ↔ ∀ T (h : T ∈ F), DLPerComponent Φ_0 T h ≥ 0 := by
  unfold InducedMapNCL DLPerComponent
  refine ⟨fun ⟨_, h2⟩ T hT => by have := h2 T hT; omega,
          fun h => ⟨h_image, fun T hT => by have := h T hT; omega⟩⟩

/-! ### Sideward NCL negative direction (MCB Prop 1.6.10) -/

/-- **MCB Prop 1.6.10 negative — Sideward 2(b) violates InducedMapNCL.**
    Under the canonical induced map, `{T_i, T_j} → {M(T_i, β), T_j/β}`
    fails NCL because `T_j ↦ T_j/β = T_j_q` strictly drops weight.

    MCB (book p. 72): "the root of the component T is mapped … to the root
    of the component T/T_v in the new workspace F', with deg(T/T_v) <
    deg(T); thus, it violates the No Complexity Loss constraint." -/
theorem sideward_2b_violatesInducedMapNCL {α : Type*} [DecidableEq (Nonplanar α)]
    (lbl : α) (T_i T_j β T_j_q : Nonplanar α)
    (p_j : Forest (Nonplanar α) × Nonplanar α) (hp_j : p_j ∈ cutSummandsN T_j)
    (h_cf : p_j.1 = ({β} : Forest (Nonplanar α)))
    (h_rd : p_j.2 = T_j_q)
    (h_distinct : T_i ≠ T_j) :
    ¬ InducedMapNCL ({T_i, T_j} : Forest (Nonplanar α))
                    ({Nonplanar.node lbl {T_i, β}, T_j_q} : Forest (Nonplanar α))
        (fun T _ => if T = T_i then Nonplanar.node lbl {T_i, β} else T_j_q) := by
  intro h_ncl
  have h_T_j_mem : T_j ∈ ({T_i, T_j} : Forest (Nonplanar α)) :=
    Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr rfl)
  have h_neq : T_j ≠ T_i := fun h => h_distinct h.symm
  have h_ineq :
      (if T_j = T_i then Nonplanar.node lbl {T_i, β} else T_j_q).numNodes ≥ T_j.numNodes :=
    h_ncl.2 T_j h_T_j_mem
  rw [if_neg h_neq] at h_ineq
  have h_cons := cutSummandsN_numNodes T_j p_j hp_j
  rw [h_cf] at h_cons
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at h_cons
  rw [h_rd] at h_cons
  have h_β_pos := β.numNodes_pos
  omega

/-- **MCB Prop 1.6.10 negative — Sideward 3(a) violates InducedMapNCL.**
    Workspace `{T_i} → {M(a, b), T_i/(a⊔b)}` for a 2-edge cut on `T_i`
    extracting both `a` and `b`. The canonical map sends `T_i ↦ T_i/(a⊔b)`,
    which has lost both subtrees, so its weight is strictly smaller. (Weight
    conservation is exact here even though leaf count would not be —
    `cutSummandsN_numNodes` holds for the 2-edge crown directly.) -/
theorem sideward_3a_violatesInducedMapNCL {α : Type*}
    (lbl : α) (T_i a b T_iq : Nonplanar α)
    (p_i : Forest (Nonplanar α) × Nonplanar α) (hp_i : p_i ∈ cutSummandsN T_i)
    (h_cf : p_i.1 = ({a, b} : Forest (Nonplanar α)))
    (h_rd : p_i.2 = T_iq) :
    ¬ InducedMapNCL ({T_i} : Forest (Nonplanar α))
                    ({Nonplanar.node lbl {a, b}, T_iq} : Forest (Nonplanar α))
        (fun _ _ => T_iq) := by
  intro h_ncl
  have h_ineq : T_iq.numNodes ≥ T_i.numNodes := h_ncl.2 T_i (Multiset.mem_singleton.mpr rfl)
  have h_cons := cutSummandsN_numNodes T_i p_i hp_i
  rw [h_cf, show ({a, b} : Forest (Nonplanar α)) = a ::ₘ {b} from rfl,
      Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton,
      h_rd] at h_cons
  have h_a_pos := a.numNodes_pos
  have h_b_pos := b.numNodes_pos
  omega

/-- **MCB Prop 1.6.10 negative — Sideward 3(b) violates InducedMapNCL.**
    Workspace `{T_i, T_j} → {M(a, b), T_i/a, T_j/b}`. The canonical map
    sends `T_i ↦ T_i/a` (and `T_j ↦ T_j/b`); the `T_i/a = T_iq` component
    strictly drops weight, so NCL fails already at `T_i`. -/
theorem sideward_3b_violatesInducedMapNCL {α : Type*} [DecidableEq (Nonplanar α)]
    (lbl : α) (T_i T_j a b T_iq T_jq : Nonplanar α)
    (p_i : Forest (Nonplanar α) × Nonplanar α) (hp_i : p_i ∈ cutSummandsN T_i)
    (h_cf_i : p_i.1 = ({a} : Forest (Nonplanar α)))
    (h_rd_i : p_i.2 = T_iq) :
    ¬ InducedMapNCL ({T_i, T_j} : Forest (Nonplanar α))
                    ({Nonplanar.node lbl {a, b}, T_iq, T_jq} : Forest (Nonplanar α))
        (fun T _ => if T = T_i then T_iq else T_jq) := by
  intro h_ncl
  have h_ineq : (if T_i = T_i then T_iq else T_jq).numNodes ≥ T_i.numNodes :=
    h_ncl.2 T_i (Multiset.mem_cons_self _ _)
  rw [if_pos rfl] at h_ineq
  have h_cons := cutSummandsN_numNodes T_i p_i hp_i
  rw [h_cf_i] at h_cons
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at h_cons
  rw [h_rd_i] at h_cons
  have h_a_pos := a.numNodes_pos
  omega

end Minimalist.Merge
