import Linglib.Semantics.Causation.SEM.Defs
import Linglib.Semantics.Causation.Mechanism.Deterministic

/-!
# SEM: Deterministic Specialization (canonical `developDet`)

Per-vertex form of forward development for **deterministic** acyclic
SEMs. The per-vertex pattern is intrinsically the deterministic
specialization — see "Why per-vertex is deterministic-only" below.

`developDetVtx M s v : α v` is the per-vertex value, defined via
`IsDAG.wf.fix` (recurses on `IsStrictAncestor`). The whole-valuation
wrapper `developDet M s : Valuation α` is the **canonical public name**
for "develop a deterministic acyclic SEM against a partial valuation."
Returns `some` at every vertex (every vertex reaches a value via parent
recursion bottoming out at roots).

Mathlib analogue: `Mathlib/Probability/Kernel/Deterministic.lean` —
canonical type is the general `Kernel α β` (measure-valued); the
deterministic case is a Dirac specialization with its own constructor
and bridge theorems. Same pattern here: canonical `develop M s : PMF
(Valuation α)` (in `Basic.lean`) lives alongside this deterministic
specialization, connected by `develop_eq_pure_of_deterministic`.

## Why per-vertex is deterministic-only

The deterministic per-vertex recursion `developDetVtx M s v = mech.toFun
(M.mech v) (fun u => developDetVtx M s u.val)` works because each vertex
has a unique value computable from parents.

Generalizing to stochastic (return `PMF (α v)`) requires composing
**per-parent marginals** into a **joint** parent assignment to feed to
the mechanism. But marginals don't compose into joints via `PMF.bind`
without independence, and parents may be correlated through shared
ancestors. Counterexample: `A → B`, `A → C`, mechanisms `B := A`, `C :=
A`. Per-vertex marginals: B ~ Bernoulli(0.5), C ~ Bernoulli(0.5). Naive
PMF.bind composition: joint = uniform over (0,0)/(0,1)/(1,0)/(1,1).
Truth: joint = (0,0) w.p. 0.5 OR (1,1) w.p. 0.5. The naive composition
is mathematically wrong.

The canonical stochastic object is the **joint** `develop M s : PMF
(Valuation α)` (in `Basic.lean`), which threads `PMF.bind` through the
partial joint, preserving correlations. There is no clean per-vertex
form for stochastic SEMs without belief-propagation infrastructure.

The computational specialization `developDetOn M vs n s` (in `Basic.lean`)
is a separate axis — kernel-reducible iteration over an explicit vertex
list, for proofs over concrete SEMs. Polynomial.eval₂ analogue.

## Reduction

`developDetVtx M s v` reduces structurally via:
1. `rw [developDetVtx_unfold]` (or the convenience lemmas
   `developDetVtx_extended`/`developDetVtx_undet`) — opens one layer of
   the `WellFounded.fix_eq` recursion.
2. `rfl` (or `simp` when `s.get v` is determined) — closes when ground.

For 5-vertex SEMs, ~5 layers of unfolding suffice. No `Fintype` reasoning;
no opaque `Multiset.toList`.
-/

namespace Semantics.Causation.SEM

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
    [SEM.IsDeterministic M]
    (s : Valuation α) : (v : V) → α v :=
  hDag.wf.fix (C := fun v => α v) (fun v rec =>
    match s.get v with
    | some x => x
    | none =>
      Mechanism.IsDeterministic.toFun (M.mech v)
        (fun u : M.graph.parents v =>
          rec u.val (Relation.TransGen.single u.property)))

/-- **Canonical forward development** of a deterministic acyclic SEM
    against a partial valuation, returning a `Valuation α`. Wraps
    `developDetVtx` with `some` at every vertex. Total under
    `IsDAG + IsDeterministic`.

    Replaces the old `Basic.lean` `developDet` (Fintype-based,
    iteration-based, noncomputable, opaque). Same call-site shape
    (`(M.developDet s).hasValue v x`); cleanly reducible internals. -/
noncomputable def developDet (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation α) : Valuation α :=
  fun v => some (developDetVtx M s v)

-- ════════════════════════════════════════════════════
-- § Structural unfolding lemmas
-- ════════════════════════════════════════════════════

/-- Step lemma: one layer of `WellFounded.fix_eq` unfolding. Use with
    `rw` to open `developDetVtx M s v` in proofs. -/
theorem developDetVtx_unfold (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation α) (v : V) :
    developDetVtx M s v =
      match s.get v with
      | some x => x
      | none =>
        Mechanism.IsDeterministic.toFun (M.mech v)
          (fun u : M.graph.parents v => developDetVtx M s u.val) := by
  rw [developDetVtx, WellFounded.fix_eq]

/-- When `v` is already determined in `s`, development is the value. -/
theorem developDetVtx_extended (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation α) (v : V) (x : α v)
    (h : s.get v = some x) : developDetVtx M s v = x := by
  rw [developDetVtx_unfold, h]

/-- When `v` is undetermined in `s`, development applies the mechanism
    to the recursively-developed parent values. -/
theorem developDetVtx_undet (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation α) (v : V)
    (h : s.get v = none) :
    developDetVtx M s v =
      Mechanism.IsDeterministic.toFun (M.mech v)
        (fun u : M.graph.parents v => developDetVtx M s u.val) := by
  rw [developDetVtx_unfold, h]

/-- `developDet M s` always returns `some` at every vertex. -/
@[simp] theorem developDet_isSome (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation α) (v : V) :
    (M.developDet s v).isSome := rfl

/-- `developDet` is `some ∘ developDetVtx`. -/
theorem developDet_apply (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation α) (v : V) :
    M.developDet s v = some (developDetVtx M s v) := rfl

/-- `(M.developDet s).hasValue v x ↔ developDetVtx M s v = x`. -/
theorem developDet_hasValue_iff (M : SEM V α) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation α) (v : V) (x : α v) :
    (M.developDet s).hasValue v x ↔ developDetVtx M s v = x :=
  Option.some_inj

-- ════════════════════════════════════════════════════
-- § Partial development (strict T_D dynamics)
-- ════════════════════════════════════════════════════

/-! The strict Schulz/Nadathur development relation T_D ([schulz-2011];
    [nadathur-2023-implicatives] Defs 4–5) never assigns values to
    undetermined background (parentless) variables and never resolves an
    inner variable while any parent is u-valued. `developDetVtx?` is its
    fixed point: `some x` is the paper's "s causally entails ⟨v, x⟩";
    `none` means v stays u-valued. Contrast `developDetVtx` above, which
    eagerly fires `const` mechanisms at exogenous vertices — adequate for
    the PMF stack (where root mechanisms are genuine priors) but
    unfaithful to the deterministic causal-entailment predicates. -/

/-- **Partial per-vertex development**: the strict T_D fixed point.
    Determined vertices keep their value; undetermined exogenous
    (parentless) vertices stay `none`; an undetermined inner vertex
    resolves iff every parent resolves. -/
noncomputable def developDetVtx? (M : SEM V α) [hDag : CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] [DecidableEq V] (s : Valuation α) :
    (v : V) → Option (α v) :=
  hDag.wf.fix (C := fun v => Option (α v)) (fun v rec =>
    match s.get v with
    | some x => some x
    | none =>
      if M.graph.parents v = ∅ then none
      else if hAll : ∀ u : M.graph.parents v,
          (rec u.val (Relation.TransGen.single u.property)).isSome then
        some (Mechanism.IsDeterministic.toFun (M.mech v)
          (fun u => (rec u.val (Relation.TransGen.single u.property)).get (hAll u)))
      else none)

section PartialDevelopment

variable (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
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
          some (Mechanism.IsDeterministic.toFun (M.mech v)
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
      some (Mechanism.IsDeterministic.toFun (M.mech v) ρ) := by
  rw [developDetVtx?_unfold]
  simp only [h]
  have hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome :=
    fun u => by rw [hρ u]; rfl
  rw [if_neg hPar, dif_pos hAll]
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
  rw [if_neg hPar, dif_neg hAll]

/-- **Refinement**: wherever the strict dynamics resolves a vertex, the
    eager-total `developDetVtx` agrees. -/
theorem developDetVtx_eq_of_developDetVtx?_eq_some
    {s : Valuation α} {v : V} {x : α v}
    (h : developDetVtx? M s v = some x) : developDetVtx M s v = x := by
  induction v using (CausalGraph.IsDAG.wf (G := M.graph)).induction with
  | _ v ih =>
    rw [developDetVtx?_unfold] at h
    rw [developDetVtx_unfold]
    cases hsv : s.get v with
    | some y => simp only [hsv] at h ⊢; exact Option.some.inj h
    | none =>
      simp only [hsv] at h ⊢
      by_cases hPar : M.graph.parents v = ∅
      · simp [hPar] at h
      · simp only [hPar, if_false] at h
        by_cases hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome
        · rw [dif_pos hAll] at h
          rw [← Option.some.inj h]
          refine congrArg _ (funext fun u => ?_)
          exact ih u.val (Relation.TransGen.single u.property)
            (Option.some_get (hAll u)).symm
        · rw [dif_neg hAll] at h
          exact absurd h (by simp)

end PartialDevelopment

-- ════════════════════════════════════════════════════
-- § Fuel mirror (computable, kernel-reducible)
-- ════════════════════════════════════════════════════

/-- Fuel-indexed computable mirror of `developDetVtx?`. Structural
    recursion on fuel, so concrete claims reduce in the kernel and
    `decide` works. `developDetVtxFuel_eq_developDetVtx?` connects it to
    the canonical fixed point once the fuel exceeds the vertex's rank. -/
def developDetVtxFuel (M : SEM V α) [SEM.IsDeterministic M] [DecidableEq V]
    (s : Valuation α) : ℕ → (v : V) → Option (α v)
  | 0, v => s.get v
  | n + 1, v =>
    match s.get v with
    | some x => some x
    | none =>
      if M.graph.parents v = ∅ then none
      else if hAll : ∀ u : M.graph.parents v,
          (developDetVtxFuel M s n u.val).isSome then
        some (Mechanism.IsDeterministic.toFun (M.mech v)
          (fun u => (developDetVtxFuel M s n u.val).get (hAll u)))
      else none

section FuelBridge

variable (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
  [DecidableEq V]

/-- **Fuel bridge**: with fuel exceeding any rank function that strictly
    increases along graph edges (e.g. the depth function a concrete model
    supplies to `CausalGraph.IsDAG.of_depth`), the fuel mirror computes
    the strict fixed point. Soundness and completeness in one equation. -/
theorem developDetVtxFuel_eq_developDetVtx?
    (rank : V → ℕ) (hrank : ∀ {u v : V}, u ∈ M.graph.parents v → rank u < rank v)
    (s : Valuation α) :
    ∀ {n : ℕ} {v : V}, rank v < n →
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
          some (Mechanism.IsDeterministic.toFun (M.mech v)
            (fun u => (developDetVtxFuel M s n u.val).get (hAll u)))
        else none) = _
    cases hsv : s.get v with
    | some x => rfl
    | none =>
      by_cases hPar : M.graph.parents v = ∅
      · simp [hPar]
      · have hpt : ∀ u : M.graph.parents v,
            developDetVtxFuel M s n u.val = developDetVtx? M s u.val :=
          fun u => ih (by have := hrank u.property; omega)
        simp only [hPar, if_false]
        by_cases hAll : ∀ u : M.graph.parents v, (developDetVtx? M s u.val).isSome
        · have hAll' : ∀ u : M.graph.parents v,
              (developDetVtxFuel M s n u.val).isSome :=
            fun u => by rw [hpt u]; exact hAll u
          rw [dif_pos hAll', dif_pos hAll]
          refine congrArg some (congrArg _ (funext fun u => ?_))
          simp only [hpt u]
        · have hAll' : ¬ ∀ u : M.graph.parents v,
              (developDetVtxFuel M s n u.val).isSome :=
            fun hA => hAll (fun u => by rw [← hpt u]; exact hA u)
          rw [dif_neg hAll', dif_neg hAll]

/-- Transfer a concrete fuel computation to the canonical strict fixed
    point. The usual study idiom:
    `developDetVtx?_eq_of_fuel M rank (by intro u v h; revert h; decide) (by omega) (by decide)`. -/
theorem developDetVtx?_eq_of_fuel
    (rank : V → ℕ) (hrank : ∀ {u v : V}, u ∈ M.graph.parents v → rank u < rank v)
    {s : Valuation α} {n : ℕ} {v : V} {o : Option (α v)} (hn : rank v < n)
    (h : developDetVtxFuel M s n v = o) :
    developDetVtx? M s v = o :=
  (developDetVtxFuel_eq_developDetVtx? M rank hrank s hn).symm.trans h

end FuelBridge

end Semantics.Causation.SEM
