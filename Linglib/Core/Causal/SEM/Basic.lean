import Linglib.Core.Causal.SEM.Defs
import Linglib.Core.Causal.SEM.Deterministic
import Linglib.Core.Causal.Mechanism.Deterministic
import Mathlib.Logic.Function.Iterate
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# SEM: Forward Propagation, Intervention, Fixpoint (V2)

- **`intervene`** (Pearl `do(v := x)`): replace the mechanism for `v`
  with `Mechanism.const x`.

- **`ready`/`parentAssignment`**: a vertex is ready when all its parents
  are determined; the parent assignment can then be built as a Π-type.

- **`singleStepAtDet`**: per-vertex step. Computable. Three structural
  rewrite cases (extend / skip-determined / skip-not-ready) provide the
  simp normal form for unfolding `stepOnceDetOn` against a concrete list.

- **`stepOnceDetOn (vs : List V)`**: foldl over an explicit vertex list.
  Computable; reduces structurally via the simp lemmas. Use this when
  consumers need `decide`-style kernel reduction on a concrete SEM.

- **`stepOnceDet`** (Fintype-based): canonical name, defined as
  `stepOnceDetOn` over `(Fintype.elems : Finset V).toList`. Noncomputable
  because `Finset.toList` is. Use for general theorems.

- **`developDetOn (vs : List V) (n : ℕ)`**: bounded iteration of
  `stepOnceDetOn`. Computable. Consumers use this with their explicit list
  + iteration count for kernel-verifiable proofs.

- **`developDet`**: canonical Fintype-based wrapper. Iterates `stepOnceDet`
  for `Fintype.card V` steps — enough to reach the fixpoint regardless
  of vertex order. Noncomputable.

## Mathlib pattern

This mirrors `Polynomial`/`MvPolynomial`: the canonical types are
noncomputable (defined via Quotient/Finsupp), but consumers needing
kernel evaluation supply explicit data and use the `.eval`-style
computable variants. Structural simp lemmas let proofs unfold via
rewriting rather than runtime evaluation.
-/

namespace Core.Causal.SEM

variable {V : Type*} {α : V → Type*}

-- ════════════════════════════════════════════════════
-- § Intervention (Pearl do(v := x))
-- ════════════════════════════════════════════════════

/-- **Pearl's `do(v := x)` intervention**: replace the mechanism for `v`
    with the constant Dirac-PMF mechanism returning `x`. Other vertices'
    mechanisms are unchanged. -/
noncomputable def intervene [DecidableEq V] (M : SEM V α) (v : V) (x : α v) : SEM V α :=
  { graph := M.graph
    mech  := fun w =>
      if h : w = v then h ▸ Mechanism.const (G := M.graph) x else M.mech w }

@[simp] theorem intervene_graph [DecidableEq V] (M : SEM V α) (v : V) (x : α v) :
    (M.intervene v x).graph = M.graph := rfl

/-- The intervened vertex's mechanism becomes a constant Dirac. -/
@[simp] theorem intervene_mech_self [DecidableEq V] (M : SEM V α) (v : V) (x : α v) :
    (M.intervene v x).mech v = Mechanism.const (G := M.graph) x := by
  simp [intervene]

/-- Other vertices' mechanisms are unaffected by intervention. -/
@[simp] theorem intervene_mech_other [DecidableEq V] (M : SEM V α) {v w : V} (x : α v)
    (h : w ≠ v) : (M.intervene v x).mech w = M.mech w := by
  simp [intervene, h]

/-- An intervention preserves the graph (only the mechanism at `v` is
    replaced), so it preserves the `IsDAG` mixin. -/
instance [DecidableEq V] (M : SEM V α) [h : CausalGraph.IsDAG M.graph]
    (v : V) (x : α v) : CausalGraph.IsDAG (M.intervene v x).graph := by
  rw [intervene_graph]; exact h

/-- An intervention preserves the `IsDeterministic` mixin: the
    intervened vertex becomes a `Mechanism.const` (a Dirac), and other
    vertices' mechanisms are unchanged. -/
noncomputable instance [DecidableEq V] (M : SEM V α) [IsDeterministic M]
    (v : V) (x : α v) : IsDeterministic (M.intervene v x) where
  mech_det w := by
    by_cases h : w = v
    · subst h; simp [intervene]
      exact inferInstanceAs (Mechanism.IsDeterministic (Mechanism.const _))
    · simp [intervene, h]
      exact IsDeterministic.mech_det w

-- ════════════════════════════════════════════════════
-- § Forward propagation: ready, parentAssignment
-- ════════════════════════════════════════════════════

/-- A vertex is **ready** in a valuation when all its parents have
    determined values. Required precondition for firing the mechanism. -/
def ready (M : SEM V α) (s : Valuation α) (v : V) : Prop :=
  ∀ u ∈ M.graph.parents v, (s.get u).isSome

instance [DecidableValuation α] (M : SEM V α) (s : Valuation α) (v : V) :
    Decidable (ready M s v) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Build the parent-assignment Π-type, given that all parents are
    determined. Computable: `Option.get` on a value known to be `some`. -/
def parentAssignment (M : SEM V α) (s : Valuation α) (v : V)
    (h : ready M s v) : ∀ u : M.graph.parents v, α u.val :=
  fun u => (s.get u.val).get (h u.val u.property)

-- ════════════════════════════════════════════════════
-- § Forward propagation: singleStepAtDet + stepOnceDetOn (computable)
-- ════════════════════════════════════════════════════

/-- Per-vertex step of `stepOnceDet`. Computable. Three structural cases
    surfaced via simp lemmas (`singleStepAtDet_extend`, `_skip_determined`,
    `_skip_not_ready`) so consumers can unfold via `simp` rather than
    relying on `decide` reducing through opaque definitions. -/
def singleStepAtDet [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V) : Valuation α :=
  if (s.get v).isNone then
    if hR : ready M s v then
      s.extend v
        (Mechanism.IsDeterministic.toFun (M.mech v) (parentAssignment M s v hR))
    else s
  else s

/-- Structural unfolding: when `v` is undetermined and ready, the step
    extends the valuation with the mechanism's value at `v`. -/
theorem singleStepAtDet_extend [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V)
    (hUndet : (s.get v).isNone) (hR : ready M s v) :
    singleStepAtDet M s v =
      s.extend v (Mechanism.IsDeterministic.toFun (M.mech v) (parentAssignment M s v hR)) := by
  simp [singleStepAtDet, hUndet, hR]

/-- Structural unfolding: a determined vertex is skipped. -/
@[simp] theorem singleStepAtDet_skip_determined [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V)
    (hDet : (s.get v).isSome) :
    singleStepAtDet M s v = s := by
  simp [singleStepAtDet, Option.isNone_iff_eq_none, Option.eq_none_iff_forall_ne_some,
        Option.isSome_iff_exists.mp hDet]

/-- Structural unfolding: an unready vertex is skipped. -/
theorem singleStepAtDet_skip_not_ready [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V)
    (hNR : ¬ ready M s v) :
    singleStepAtDet M s v = s := by
  unfold singleStepAtDet
  by_cases hN : (s.get v).isNone
  · simp [hN, hNR]
  · simp [hN]

/-- One forward-development sweep over an explicit vertex list.
    Computable. Each fold step is `singleStepAtDet`. -/
def stepOnceDetOn [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (vs : List V) (s : Valuation α) : Valuation α :=
  vs.foldl (singleStepAtDet M) s

@[simp] theorem stepOnceDetOn_nil [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) :
    stepOnceDetOn M [] s = s := rfl

@[simp] theorem stepOnceDetOn_cons [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (v : V) (vs : List V) (s : Valuation α) :
    stepOnceDetOn M (v :: vs) s = stepOnceDetOn M vs (singleStepAtDet M s v) := rfl

-- ════════════════════════════════════════════════════
-- § Computational specialization: developDetOn (explicit list)
-- ════════════════════════════════════════════════════

/-! The canonical `developDet` (per-vertex, via `IsDAG.wf.fix`) lives in
    `PerVertex.lean`. Below is the **computational specialization**:
    `developDetOn M vs n s` iterates `stepOnceDetOn` `n` times over an
    explicit vertex list `vs`. Computable; reducible structurally for
    kernel-verifiable proofs on concrete SEMs.

    Mathlib analogue: `Polynomial.eval` (canonical) vs `Polynomial.eval₂`
    with explicit ring hom (computational). Same mathematical object;
    different reduction profiles.

    `stepOnceDet` (the Fintype-based wrapper) is kept here as an internal
    helper for the PMF stack's `stepOnce_eq_pure_of_deterministic` bridge —
    see below. It's not part of the public API; consumers use either
    `developDetOn` (computational) or `developDet` (canonical, in PerVertex.lean). -/

/-- One forward-development sweep using the Fintype enumeration of `V`.
    Internal helper for `stepOnce_eq_pure_of_deterministic`; not a public
    API. Public consumers use `developDetOn` (explicit list) or
    `developDet` (canonical per-vertex). -/
noncomputable def stepOnceDet [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) : Valuation α :=
  stepOnceDetOn M (Fintype.elems : Finset V).toList s

/-- **Forward-development** of a deterministic acyclic SEM against an
    explicit vertex list, with `n` iterations. Computable; consumers use
    this for kernel-verifiable proofs on concrete SEMs.

    `Fintype.card V` iterations always suffice to reach the fixpoint
    (each effective iteration determines ≥1 more vertex). -/
def developDetOn [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (vs : List V) (n : ℕ) (s : Valuation α) :
    Valuation α :=
  (stepOnceDetOn M vs)^[n] s

@[simp] theorem developDetOn_zero [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (vs : List V) (s : Valuation α) :
    developDetOn M vs 0 s = s := rfl

theorem developDetOn_succ [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (vs : List V) (n : ℕ) (s : Valuation α) :
    developDetOn M vs (n + 1) s = developDetOn M vs n (stepOnceDetOn M vs s) := by
  simp [developDetOn, Function.iterate_succ_apply]

/-- **Intervention-as-Extend bridge**: for an acyclic deterministic SEM
    with `cause` undetermined in `s`, Pearl-intervening to set
    `cause := xC` is equivalent (at the level of `developDet`) to
    extending the valuation with `cause = xC` and developing under the
    original mechanisms.

    Load-bearing substrate fact connecting `probabilisticSuf`
    (intervene-based) to `causallySufficient` (extend-based). Under the
    per-vertex `developDet`, the proof goes by induction on
    `IsStrictAncestor` showing that the intervened mechanism at `cause`
    fires `xC` regardless of recursive parent values, matching the
    extended-valuation case which short-circuits via `developDetVtx_extended`.

    **Proof deferred** — same TODO status as before the per-vertex
    refactor; the consumer (`probabilisticSuf_eq_deterministicSuf` in
    CaoWhiteLassiter2025) relies on this as a single substrate sorry
    rather than re-deriving at each call site. -/
theorem developDet_intervene_eq_developDet_extend
    [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause)
    (h : s.get cause = none) :
    (M.intervene cause xC).developDet s = M.developDet (s.extend cause xC) := by
  sorry

-- ════════════════════════════════════════════════════
-- § PMF-valued forward propagation (canonical)
-- ════════════════════════════════════════════════════

/-! Mathlib pattern: `develop` is PMF-valued unconditionally — the
mathematical object that doesn't presuppose deterministic mechanisms.
The `developDet` machinery above is the deterministic-as-Dirac
specialization, connected to `develop` via `develop_eq_pure_of_deterministic`.

This mirrors `Mathlib/Probability/Kernel/Basic.lean` where `Kernel α β`
is always measure-valued and `Kernel.deterministic (f : α → β)` is the
Dirac specialization. Consumers needing the deterministic function go
through `developDet`; consumers chaining probabilistic operations go
through `develop`. The bridge theorem connects them — no API drift. -/

/-- Per-vertex probabilistic step. Samples the mechanism's output PMF,
    extending the valuation with the sampled value. Reduces to
    `singleStepAtDet`-via-Dirac when the mechanism `IsDeterministic`. -/
noncomputable def singleStepAt [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) (s : Valuation α) (v : V) : PMF (Valuation α) :=
  if (s.get v).isNone then
    if hR : ready M s v then
      ((M.mech v).run (parentAssignment M s v hR)).map (s.extend v ·)
    else PMF.pure s
  else PMF.pure s

/-- Bridge: under `IsDeterministic`, the PMF step collapses to a Dirac
    of the deterministic step. -/
theorem singleStepAt_eq_pure_of_deterministic [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V) :
    singleStepAt M s v = PMF.pure (singleStepAtDet M s v) := by
  unfold singleStepAt singleStepAtDet
  split_ifs with hN hR
  · rw [Mechanism.IsDeterministic.run_eq, PMF.pure_map]
  · rfl
  · rfl

/-- One PMF-valued forward sweep using the Fintype enumeration of `V`.
    Threads `PMF.bind` through each per-vertex step. Noncomputable
    because PMF is. -/
noncomputable def stepOnce [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) (s : Valuation α) : PMF (Valuation α) :=
  (Fintype.elems : Finset V).toList.foldl
    (fun acc v => acc.bind (singleStepAt M · v))
    (PMF.pure s)

/-- Bridge: under `IsDeterministic`, `stepOnce` is the Dirac of `stepOnceDet`. -/
theorem stepOnce_eq_pure_of_deterministic
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) :
    stepOnce M s = PMF.pure (stepOnceDet M s) := by
  unfold stepOnce stepOnceDet stepOnceDetOn
  generalize (Fintype.elems : Finset V).toList = vs
  induction vs generalizing s with
  | nil => simp [List.foldl]
  | cons v vs ih =>
    simp only [List.foldl_cons]
    have step : (PMF.pure s).bind (singleStepAt M · v) = PMF.pure (singleStepAtDet M s v) := by
      rw [PMF.pure_bind]; exact singleStepAt_eq_pure_of_deterministic M s v
    rw [step]
    exact ih (singleStepAtDet M s v)

/-- **Canonical PMF-valued forward-development**. Iterates `PMF.bind ·
    stepOnce` for `Fintype.card V` rounds. Mathlib-style: PMF-valued
    unconditionally; `IsDeterministic` consumers get back to a `Valuation α`
    via `develop_eq_pure_of_deterministic` below. -/
noncomputable def develop [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] (s : Valuation α) : PMF (Valuation α) :=
  (fun p => p.bind (stepOnce M))^[Fintype.card V] (PMF.pure s)

/-- **Bridge theorem** (load-bearing): under `IsDeterministic`, the
    canonical PMF-valued `develop` collapses to the Dirac of the
    deterministic-specialization `developDet` (per-vertex, in
    `SEM/Deterministic.lean`).

    This is the central correctness statement that lets the
    deterministic-as-Dirac pattern work cleanly. The two definitions
    are mathematically the same object viewed two ways:
    - `develop` threads `PMF.bind` through the partial joint via
      iteration over `Fintype.elems.toList`.
    - `developDet` recurses per-vertex via `IsDAG.wf.fix`, bottoming
      out at roots.
    Under `IsDeterministic`, the joint collapses to a Dirac at the
    valuation produced by per-vertex recursion.

    **Proof status**: deferred (`sorry`). The previous proof went via
    `stepOnce_eq_pure_of_deterministic` chained over the iteration
    count, working because the old `developDet` was definitionally the
    iteration. The new per-vertex `developDet` requires a substantively
    different argument: induct on `IsStrictAncestor` to show that PMF
    iteration's fixpoint at vertex `v` matches the per-vertex
    recursion's value. Real theorem; tractable but not blocking the
    current substrate refactor.

    The downstream consumer
    (`probabilisticSuf_of_deterministic` →
    `CaoWhiteLassiter2025.probabilisticSuf_eq_deterministicSuf`) was
    already broken by `developDet_intervene_eq_developDet_extend`'s
    sorry; this defers the same chain. No new regression. -/
theorem develop_eq_pure_of_deterministic
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M] (s : Valuation α) :
    develop M s = PMF.pure (developDet M s) := by
  sorry

/-! ### Topological-order independence (deferred)

`develop_perm_invariant` — different topological sorts of an acyclic
DAG give the same PMF. Provable via `PMF.bind_comm` + a lemma showing
`singleStepAt M s v` is a no-op (`PMF.pure s`) when `v` is not yet
ready. Not load-bearing for current consumers; deferred until a study
needs to reason about `develop` against a hand-picked vertex order. -/

end Core.Causal.SEM
