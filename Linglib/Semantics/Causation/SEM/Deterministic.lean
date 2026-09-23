module

public import Linglib.Semantics.Causation.SEM.Defs
public import Linglib.Semantics.Causation.Mechanism.Defs

/-!
# SEM: development of deterministic acyclic models

`developDetVtx M s v : α v` is the value of vertex `v` when the partial valuation `s` is
developed through a deterministic acyclic model, by well-founded recursion on
`IsStrictAncestor`: a vertex `s` settles keeps its value, and any other vertex takes the value
its equation gives to its parents' developed values. `developDet M s` is the whole valuation,
settled everywhere. The strict development `developDetVtx?` of [schulz-2011] and
[nadathur-2023-implicatives] leaves an undetermined exogenous vertex undetermined and resolves
an inner vertex only once all its parents are resolved. The eager development is the strict one
after every silent root takes the value its equation gives it
(`developDetVtx?_or_rootDefaults`).

`developDetVtxFuel` is the kernel-reducible mirror of the strict development. Fuel above any
ranking of the graph reaches it, so fuel `Fintype.card V` does in a finite model
(`developDetVtxFuel_card`, through `CausalGraph.ancestorRanking`), and `developDet_eq_fuel`
computes the eager development the same way. That is how `(M.developDet s).hasValue v x`, and
every predicate stated through it, is decided.

Uncertainty is not a property of the equations. As in Pearl's structural models it is a
probability on the background, which `SEM.probSufficiency` takes as a measure on outcomes that
each settle a background valuation.

## Implementation notes

Proofs about arbitrary valuations open the recursion one layer at a time with
`developDetVtx_unfold` (`developDetVtx_extended` and `developDetVtx_undet` for its two cases, and
the `developDetVtx?_*` lemmas for the strict development); claims about a concrete model are
decided.

## References

* [schulz-2011]
* [nadathur-2023-implicatives]
-/

@[expose] public section

namespace Causation.SEM

variable {V : Type*} {α : V → Type*}

/-- **Per-vertex forward development**: given a deterministic acyclic
    SEM `M` and a partial valuation `s`, compute the value at vertex
    `v` by recursing on parents via `IsStrictAncestor` well-foundedness.

    For determined vertices (`s.get v = some x`), returns `x` (idempotent
    on extension). For undetermined vertices, applies `M.mech v`'s
    deterministic function to the recursively-computed parent values.

    Total: every vertex in a deterministic acyclic SEM reaches a value
    (roots either have explicit values in `s` or are computed by their
    constant mechanisms). The whole-valuation wrapper `developDet`
    therefore returns `some` everywhere. -/
noncomputable def developDetVtx (M : SEM V α) [hDag : CausalGraph.IsDAG M.graph]
    (s : Valuation α) : (v : V) → α v :=
  hDag.fix (C := fun v => α v) (fun v rec =>
    match s.get v with
    | some x => x
    | none =>
      (M.mech v)
        (fun u : M.graph.parents v =>
          rec u.val (Relation.TransGen.single u.property)))

/-- **Canonical forward development** of a deterministic acyclic SEM
    against a partial valuation, returning a `Valuation α`. Wraps
    `developDetVtx` with `some` at every vertex. Total under `IsDAG`. -/
noncomputable def developDet (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) : Valuation α :=
  fun v => some (developDetVtx M s v)

/-! ### Structural unfolding lemmas -/

/-- Step lemma: one layer of `WellFounded.fix_eq` unfolding. Use with
    `rw` to open `developDetVtx M s v` in proofs. -/
theorem developDetVtx_unfold (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V) :
    developDetVtx M s v =
      match s.get v with
      | some x => x
      | none =>
        (M.mech v)
          (fun u : M.graph.parents v => developDetVtx M s u.val) := by
  rw [developDetVtx, WellFounded.fix_eq]

/-- When `v` is already determined in `s`, development is the value. -/
theorem developDetVtx_extended (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V) (x : α v)
    (h : s.get v = some x) : developDetVtx M s v = x := by
  rw [developDetVtx_unfold, h]

/-- When `v` is undetermined in `s`, development applies the mechanism
    to the recursively-developed parent values. -/
theorem developDetVtx_undet (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V)
    (h : s.get v = none) :
    developDetVtx M s v =
      (M.mech v)
        (fun u : M.graph.parents v => developDetVtx M s u.val) := by
  rw [developDetVtx_unfold, h]

/-- `developDet M s` always returns `some` at every vertex. -/
@[simp] theorem developDet_isSome (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V) :
    (M.developDet s v).isSome := rfl

/-- `developDet` is `some ∘ developDetVtx`. -/
theorem developDet_apply (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V) :
    M.developDet s v = some (developDetVtx M s v) := rfl

/-- `(M.developDet s).hasValue v x ↔ developDetVtx M s v = x`. -/
theorem developDet_hasValue_iff (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (s : Valuation α) (v : V) (x : α v) :
    (M.developDet s).hasValue v x ↔ developDetVtx M s v = x :=
  Option.some_inj

/-! ### Partial development (strict T_D dynamics) -/

/-! The strict Schulz/Nadathur development relation T_D ([schulz-2011];
    [nadathur-2023-implicatives] Defs 4–5) never assigns values to
    undetermined background (parentless) variables and never resolves an
    inner variable while any parent is u-valued. `developDetVtx?` is its
    fixed point: `some x` is the paper's "s causally entails ⟨v, x⟩";
    `none` means v stays u-valued. Contrast `developDetVtx` above, which
    eagerly fires `const` mechanisms at exogenous vertices — adequate when
    each root's equation is its default value, but unfaithful to the
    causal-entailment predicates. -/

/-- **Partial per-vertex development**: the strict T_D fixed point.
    Determined vertices keep their value; undetermined exogenous
    (parentless) vertices stay `none`; an undetermined inner vertex
    resolves iff every parent resolves. -/
noncomputable def developDetVtx? (M : SEM V α) [hDag : CausalGraph.IsDAG M.graph]
    [DecidableEq V] (s : Valuation α) :
    (v : V) → Option (α v) :=
  hDag.fix (C := fun v => Option (α v)) (fun v rec =>
    match s.get v with
    | some x => some x
    | none =>
      if M.graph.parents v = ∅ then none
      else if hAll : ∀ u : M.graph.parents v,
          (rec u.val (Relation.TransGen.single u.property)).isSome then
        some ((M.mech v)
          (fun u => (rec u.val (Relation.TransGen.single u.property)).get (hAll u)))
      else none)

section PartialDevelopment

variable (M : SEM V α) [CausalGraph.IsDAG M.graph]
  [DecidableEq V]

/-- Step lemma: one layer of `WellFounded.fix_eq` unfolding for the
    partial development. -/
theorem developDetVtx?_unfold (s : Valuation α) (v : V) :
    developDetVtx? M s v =
      match s.get v with
      | some x => some x
      | none =>
        if M.graph.parents v = ∅ then none
        else if hAll : ∀ u : M.graph.parents v,
            (developDetVtx? M s u.val).isSome then
          some ((M.mech v)
            (fun u => (developDetVtx? M s u.val).get (hAll u)))
        else none := by
  rw [developDetVtx?, WellFounded.fix_eq]

/-- A vertex determined in `s` develops to its value. -/
theorem developDetVtx?_determined {s : Valuation α} {v : V} {x : α v}
    (h : s.get v = some x) : developDetVtx? M s v = some x := by
  rw [developDetVtx?_unfold, h]

/-- An undetermined exogenous vertex stays undetermined: T_D never fires
    parentless mechanisms. -/
theorem developDetVtx?_exogenous {s : Valuation α} {v : V}
    (h : s.get v = none) (hPar : M.graph.parents v = ∅) :
    developDetVtx? M s v = none := by
  rw [developDetVtx?_unfold, h]
  simp [hPar]

/-- An undetermined inner vertex whose parents all resolve fires its
    mechanism on the resolved parent values. -/
theorem developDetVtx?_inner {s : Valuation α} {v : V}
    (h : s.get v = none) (hPar : M.graph.parents v ≠ ∅)
    (ρ : ∀ u : M.graph.parents v, α u.val)
    (hρ : ∀ u : M.graph.parents v, developDetVtx? M s u.val = some (ρ u)) :
    developDetVtx? M s v =
      some (M.mech v ρ) := by
  rw [developDetVtx?_unfold]
  simp only [h]
  have hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome :=
    fun u => by rw [hρ u]; rfl
  rw [ite_eq_right hPar, dite_eq_left hAll]
  refine congrArg some (congrArg _ (funext fun u => ?_))
  simp only [hρ u, Option.get_some]

/-- An undetermined vertex with an unresolved parent stays unresolved:
    T_D is strict. -/
theorem developDetVtx?_inner_none {s : Valuation α} {v : V}
    (h : s.get v = none) (u : M.graph.parents v)
    (hu : developDetVtx? M s u.val = none) :
    developDetVtx? M s v = none := by
  rw [developDetVtx?_unfold]
  simp only [h]
  have hPar : ¬ M.graph.parents v = ∅ :=
    fun hE => (Finset.eq_empty_iff_forall_notMem.mp hE) u.val u.property
  have hAll : ¬ ∀ w : M.graph.parents v, (developDetVtx? M s w.val).isSome :=
    fun hA => by have h2 := hA u; rw [hu] at h2; simp at h2
  rw [ite_eq_right hPar, dite_eq_right hAll]

/-- **Refinement**: wherever the strict dynamics resolves a vertex, the
    eager-total `developDetVtx` agrees. -/
theorem developDetVtx_eq_of_developDetVtx?_eq_some
    {s : Valuation α} {v : V} {x : α v}
    (h : developDetVtx? M s v = some x) : developDetVtx M s v = x := by
  induction v using (inferInstance : M.graph.IsDAG).induction with
  | _ v ih =>
    rw [developDetVtx?_unfold] at h
    rw [developDetVtx_unfold]
    cases hsv : s.get v with
    | some y => simp only [hsv] at h ⊢; exact Option.some.inj h
    | none =>
      simp only [hsv] at h ⊢
      by_cases hPar : M.graph.parents v = ∅
      · simp [hPar] at h
      · simp only [hPar, ite_false] at h
        by_cases hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome
        · rw [dite_eq_left hAll] at h
          rw [← Option.some.inj h]
          refine congrArg _ (funext fun u => ?_)
          exact ih u.val (Relation.TransGen.single u.property)
            (Option.some_get (hAll u)).symm
        · rw [dite_eq_right hAll] at h
          exact absurd h (by simp)

/-- The value each root's equation gives it, which the eager development supplies where a
valuation is silent. Inner vertices are left undetermined. -/
def rootDefaults : Valuation α := fun v ↦
  if h : M.graph.parents v = ∅ then
    some (M.mech v fun u ↦ (Finset.notMem_empty u.1 (h ▸ u.2)).elim)
  else none

/-- **Eager development is strict development after root defaults**: the eager dynamics fires
the equation of every root the valuation leaves silent, which the strict dynamics does once
`rootDefaults` settles the roots. -/
theorem developDetVtx?_or_rootDefaults (s : Valuation α) (v : V) :
    developDetVtx? M (s.or (rootDefaults M)) v = some (developDetVtx M s v) := by
  induction v using (inferInstance : M.graph.IsDAG).induction with
  | _ v ih =>
    rw [developDetVtx_unfold]
    cases hsv : s.get v with
    | some x => exact developDetVtx?_determined M (by simp [hsv])
    | none =>
      by_cases hPar : M.graph.parents v = ∅
      · refine developDetVtx?_determined M ?_
        rw [Valuation.get_or, hsv, Option.none_or]
        simp only [Valuation.get, rootDefaults, hPar, dite_true]
        exact congrArg _ (congrArg _ (funext fun u ↦ (Finset.notMem_empty u.1 (hPar ▸ u.2)).elim))
      · refine developDetVtx?_inner M ?_ hPar _ fun u ↦ ih u.1 (.single u.2)
        rw [Valuation.get_or, hsv, Option.none_or]
        simp [Valuation.get, rootDefaults, hPar]

end PartialDevelopment

/-! ### Fuel mirror (computable, kernel-reducible) -/

/-- Fuel-indexed computable mirror of `developDetVtx?`. Structural
    recursion on fuel, so concrete claims reduce in the kernel and
    `decide` works. `developDetVtxFuel_eq_developDetVtx?` connects it to
    the canonical fixed point once the fuel exceeds the vertex's rank. -/
def developDetVtxFuel (M : SEM V α) [DecidableEq V]
    (s : Valuation α) : ℕ → (v : V) → Option (α v)
  | 0, v => s.get v
  | n + 1, v =>
    match s.get v with
    | some x => some x
    | none =>
      if M.graph.parents v = ∅ then none
      else if hAll : ∀ u : M.graph.parents v,
          (developDetVtxFuel M s n u.val).isSome then
        some ((M.mech v)
          (fun u => (developDetVtxFuel M s n u.val).get (hAll u)))
      else none

section FuelBridge

variable (M : SEM V α) [CausalGraph.IsDAG M.graph]
  [DecidableEq V]

/-- **Fuel bridge**: with fuel exceeding any rank function that strictly
    increases along graph edges (e.g. the depth function a concrete model
    supplies to `CausalGraph.IsDAG.of_depth`), the fuel mirror computes
    the strict fixed point. Soundness and completeness in one equation. -/
theorem developDetVtxFuel_eq_developDetVtx?
    (r : CausalGraph.Ranking M.graph) (s : Valuation α) :
    ∀ {n : ℕ} {v : V}, r v < n →
      developDetVtxFuel M s n v = developDetVtx? M s v := by
  intro n
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    intro v hv
    rw [developDetVtx?_unfold]
    show (match s.get v with
      | some x => some x
      | none =>
        if M.graph.parents v = ∅ then none
        else if hAll : ∀ u : M.graph.parents v,
            (developDetVtxFuel M s n u.val).isSome then
          some ((M.mech v)
            (fun u => (developDetVtxFuel M s n u.val).get (hAll u)))
        else none) = _
    cases hsv : s.get v with
    | some x => rfl
    | none =>
      by_cases hPar : M.graph.parents v = ∅
      · simp [hPar]
      · have hpt : ∀ u : M.graph.parents v,
            developDetVtxFuel M s n u.val = developDetVtx? M s u.val :=
          fun u => ih (by have := r.map_rel u.property; omega)
        simp only [hPar, ite_false]
        by_cases hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome
        · have hAll' : ∀ u : M.graph.parents v,
              (developDetVtxFuel M s n u.val).isSome :=
            fun u => by rw [hpt u]; exact hAll u
          rw [dite_eq_left hAll', dite_eq_left hAll]
          refine congrArg some (congrArg _ (funext fun u => ?_))
          simp only [hpt u]
        · have hAll' : ¬ ∀ u : M.graph.parents v,
              (developDetVtxFuel M s n u.val).isSome :=
            fun hA => hAll (fun u => by rw [← hpt u]; exact hA u)
          rw [dite_eq_right hAll', dite_eq_right hAll]

/-- Fuel `Fintype.card V` computes the strict development of a finite acyclic model. -/
theorem developDetVtxFuel_card [Fintype V] (s : Valuation α) (v : V) :
    developDetVtxFuel M s (Fintype.card V) v = developDetVtx? M s v :=
  developDetVtxFuel_eq_developDetVtx? M M.graph.ancestorRanking s
    (M.graph.ancestorRanking_lt_card v)

/-- The eager development of a finite acyclic model as a fuel computation, the form in which
predicates stated over `developDet` are decided. -/
theorem developDet_eq_fuel [Fintype V] (s : Valuation α) :
    M.developDet s = fun v ↦ developDetVtxFuel M (s.or (rootDefaults M)) (Fintype.card V) v :=
  funext fun v ↦ by rw [developDetVtxFuel_card, developDetVtx?_or_rootDefaults]; rfl

/-- What a finite acyclic model develops is decided by fuel, where the generic instance on
`Valuation.hasValue` would have to reduce the well-founded recursion. -/
instance [Fintype V] [DecidableValuation α] (s : Valuation α) (v : V) (x : α v) :
    Decidable ((M.developDet s).hasValue v x) :=
  decidable_of_iff (developDetVtxFuel M (s.or M.rootDefaults) (Fintype.card V) v = some x)
    (by rw [developDet_eq_fuel]; rfl)

end FuelBridge

end Causation.SEM
