import Linglib.Core.Causal.SEM.Defs
import Linglib.Core.Causal.Mechanism.Deterministic

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

namespace Core.Causal.SEM

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

end Core.Causal.SEM
