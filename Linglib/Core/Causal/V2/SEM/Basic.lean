import Linglib.Core.Causal.V2.SEM.Defs
import Linglib.Core.Causal.V2.Mechanism.Deterministic
import Mathlib.Logic.Function.Iterate

/-!
# SEM: Forward Propagation, Intervention, Fixpoint (V2)

- **`intervene`** (Pearl `do(v := x)`): replace the mechanism for `v`
  with `Mechanism.const x`.

- **`ready`/`parentAssignment`**: a vertex is ready when all its parents
  are determined; the parent assignment can then be built as a Π-type.

- **`singleStepAt`**: per-vertex step. Computable. Three structural
  rewrite cases (extend / skip-determined / skip-not-ready) provide the
  simp normal form for unfolding `stepOnceOn` against a concrete list.

- **`stepOnceOn (vs : List V)`**: foldl over an explicit vertex list.
  Computable; reduces structurally via the simp lemmas. Use this when
  consumers need `decide`-style kernel reduction on a concrete SEM.

- **`stepOnce`** (Fintype-based): canonical name, defined as
  `stepOnceOn` over `(Fintype.elems : Finset V).toList`. Noncomputable
  because `Finset.toList` is. Use for general theorems.

- **`developOn (vs : List V) (n : ℕ)`**: bounded iteration of
  `stepOnceOn`. Computable. Consumers use this with their explicit list
  + iteration count for kernel-verifiable proofs.

- **`develop`**: canonical Fintype-based wrapper. Iterates `stepOnce`
  for `Fintype.card V` steps — enough to reach the fixpoint regardless
  of vertex order. Noncomputable.

## Mathlib pattern

This mirrors `Polynomial`/`MvPolynomial`: the canonical types are
noncomputable (defined via Quotient/Finsupp), but consumers needing
kernel evaluation supply explicit data and use the `.eval`-style
computable variants. Structural simp lemmas let proofs unfold via
rewriting rather than runtime evaluation.
-/

namespace Core.Causal.V2.SEM

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
-- § Forward propagation: singleStepAt + stepOnceOn (computable)
-- ════════════════════════════════════════════════════

/-- Per-vertex step of `stepOnce`. Computable. Three structural cases
    surfaced via simp lemmas (`singleStepAt_extend`, `_skip_determined`,
    `_skip_not_ready`) so consumers can unfold via `simp` rather than
    relying on `decide` reducing through opaque definitions. -/
def singleStepAt [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V) : Valuation α :=
  if (s.get v).isNone then
    if hR : ready M s v then
      s.extend v
        (Mechanism.IsDeterministic.toFun (M.mech v) (parentAssignment M s v hR))
    else s
  else s

/-- Structural unfolding: when `v` is undetermined and ready, the step
    extends the valuation with the mechanism's value at `v`. -/
theorem singleStepAt_extend [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V)
    (hUndet : (s.get v).isNone) (hR : ready M s v) :
    singleStepAt M s v =
      s.extend v (Mechanism.IsDeterministic.toFun (M.mech v) (parentAssignment M s v hR)) := by
  simp [singleStepAt, hUndet, hR]

/-- Structural unfolding: a determined vertex is skipped. -/
@[simp] theorem singleStepAt_skip_determined [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V)
    (hDet : (s.get v).isSome) :
    singleStepAt M s v = s := by
  simp [singleStepAt, Option.isNone_iff_eq_none, Option.eq_none_iff_forall_ne_some,
        Option.isSome_iff_exists.mp hDet]

/-- Structural unfolding: an unready vertex is skipped. -/
theorem singleStepAt_skip_not_ready [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) (v : V)
    (hNR : ¬ ready M s v) :
    singleStepAt M s v = s := by
  unfold singleStepAt
  by_cases hN : (s.get v).isNone
  · simp [hN, hNR]
  · simp [hN]

/-- One forward-development sweep over an explicit vertex list.
    Computable. Each fold step is `singleStepAt`. -/
def stepOnceOn [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (vs : List V) (s : Valuation α) : Valuation α :=
  vs.foldl (singleStepAt M) s

@[simp] theorem stepOnceOn_nil [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) :
    stepOnceOn M [] s = s := rfl

@[simp] theorem stepOnceOn_cons [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (v : V) (vs : List V) (s : Valuation α) :
    stepOnceOn M (v :: vs) s = stepOnceOn M vs (singleStepAt M s v) := rfl

-- ════════════════════════════════════════════════════
-- § Forward propagation: stepOnce + develop (Fintype-based, canonical)
-- ════════════════════════════════════════════════════

/-- One forward-development sweep using the Fintype enumeration of `V`.
    Canonical name; noncomputable because `Finset.toList` is. For
    structural reduction on a concrete SEM, use `stepOnceOn` with an
    explicit vertex list. -/
noncomputable def stepOnce [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) : Valuation α :=
  stepOnceOn M (Fintype.elems : Finset V).toList s

theorem stepOnce_eq_stepOnceOn [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (s : Valuation α) :
    stepOnce M s = stepOnceOn M (Fintype.elems : Finset V).toList s := rfl

/-- **Forward-development** of a deterministic acyclic SEM against an
    explicit vertex list, with `n` iterations. Computable; consumers use
    this for kernel-verifiable proofs on concrete SEMs.

    `Fintype.card V` iterations always suffice to reach the fixpoint
    (each effective iteration determines ≥1 more vertex). -/
def developOn [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (vs : List V) (n : ℕ) (s : Valuation α) :
    Valuation α :=
  (stepOnceOn M vs)^[n] s

@[simp] theorem developOn_zero [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (vs : List V) (s : Valuation α) :
    developOn M vs 0 s = s := rfl

theorem developOn_succ [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [IsDeterministic M] (vs : List V) (n : ℕ) (s : Valuation α) :
    developOn M vs (n + 1) s = developOn M vs n (stepOnceOn M vs s) := by
  simp [developOn, Function.iterate_succ_apply]

/-- **Canonical forward-development**: iterates `stepOnce` for
    `Fintype.card V` steps. Noncomputable.

    Replaces the old `normalDevelopment`. The fact that the result is a
    fixpoint of `stepOnce` (i.e., `stepOnce M (develop M s) = develop M s`)
    is `develop_isFixpoint`, deferred. The bound `Fintype.card V`
    suffices because `stepOnce` is info-monotonic and there are only
    `Fintype.card V` vertices to determine. -/
noncomputable def develop [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) : Valuation α :=
  developOn M (Fintype.elems : Finset V).toList (Fintype.card V) s

theorem develop_eq_developOn [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M] (s : Valuation α) :
    develop M s = developOn M (Fintype.elems : Finset V).toList (Fintype.card V) s := rfl

end Core.Causal.V2.SEM
