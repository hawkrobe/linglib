import Linglib.Semantics.Causation.SEM.Defs
import Linglib.Semantics.Causation.SEM.Deterministic
import Linglib.Semantics.Causation.Mechanism.Deterministic
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

namespace Causation.SEM

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

-- ════════════════════════════════════════════════════
-- § Bridge: developDetOn ↦ developDet (soundness)
-- ════════════════════════════════════════════════════

/-! Soundness bridge connecting the iteration form (`developDetOn`,
    computable, `decide`-friendly) to the canonical per-vertex form
    (`developDet`, abstract, `WellFounded.fix`-based).

    **Direction**: `developDetOn → developDet`. If iteration produces
    `some x` at `v`, then the canonical `developDetVtx M s v = x`. Lets
    consumers prove `(M.developDet s).hasValue v x` by computing the
    matching `developDetOn` claim with `decide`, then applying the bridge.

    The reverse direction (completeness) requires proving that
    `Fintype.card V` iterations always reach all reachable values —
    deferred (would need induction on topological depth).

    **Mathlib analogue**: `Multiset.sum_toList`, `Filter.tendsto_atTop_iff`
    — bridges between an abstract canonical form and its computational
    specialization, providing the connecting API. -/

/-- **Consistency invariant** (private): `s'` is a refinement of `s`
    every value of which agrees with the canonical `developDetVtx M s`.
    Used as the load-bearing invariant on `developDetOn` iteration. -/
private def isConsistentDev [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s s' : Valuation α) : Prop :=
  s.le s' ∧ ∀ v x, s'.get v = some x → developDetVtx M s v = x

/-- The starting valuation is consistent with itself. -/
private lemma isConsistentDev_self [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) : isConsistentDev M s s := by
  refine ⟨fun _ _ h => h, fun v x h => ?_⟩
  exact developDetVtx_extended M s v x h

/-- One step of `singleStepAtDet` preserves the consistency invariant. -/
private lemma isConsistentDev_singleStepAtDet [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {s s' : Valuation α} (h : isConsistentDev M s s') (v : V) :
    isConsistentDev M s (singleStepAtDet M s' v) := by
  obtain ⟨hLe, hCons⟩ := h
  -- Case: v is already determined in s'
  by_cases hSome : (s'.get v).isSome
  · rw [singleStepAtDet_skip_determined M s' v hSome]
    exact ⟨hLe, hCons⟩
  -- Case: v is undetermined in s'
  · rw [Option.not_isSome_iff_eq_none] at hSome
    by_cases hReady : ready M s' v
    · -- Mechanism fires; new value at v matches developDetVtx M s v
      rw [singleStepAtDet_extend M s' v (Option.isNone_iff_eq_none.mpr hSome) hReady]
      have hsv : s.get v = none := by
        cases hsv : s.get v with
        | none => rfl
        | some y =>
          have h1 : s'.hasValue v y := hLe v y hsv
          rw [Valuation.hasValue, hSome] at h1
          exact absurd h1 (by simp)
      -- Compute the new value
      let newVal : α v :=
        Mechanism.IsDeterministic.toFun (M.mech v) (parentAssignment M s' v hReady)
      have hNewVal : newVal = developDetVtx M s v := by
        show Mechanism.IsDeterministic.toFun (M.mech v) (parentAssignment M s' v hReady) =
             developDetVtx M s v
        rw [developDetVtx_undet M s v hsv]
        congr 1
        funext u
        -- (parentAssignment M s' v hReady) u = developDetVtx M s u.val
        unfold parentAssignment
        have hReadyU := hReady u.val u.property
        -- hReadyU : (s'.get u.val).isSome
        exact hCons u.val ((s'.get u.val).get hReadyU) (Option.some_get hReadyU).symm |>.symm
      refine ⟨?_, ?_⟩
      · -- s.le (s'.extend v newVal)
        intro w x hwx
        have h1 : s'.hasValue w x := hLe w x hwx
        by_cases hwv : w = v
        · subst hwv
          rw [Valuation.hasValue, hSome] at h1
          exact absurd h1 (by simp)
        · rw [Valuation.hasValue, Valuation.extend_get_ne hwv]; exact h1
      · -- ∀ w x, (s'.extend v newVal).get w = some x → developDetVtx M s w = x
        intro w x hwx
        by_cases hwv : w = v
        · subst hwv
          rw [Valuation.extend_get_same] at hwx
          have : x = newVal := (Option.some.inj hwx).symm
          rw [this, hNewVal]
        · rw [Valuation.extend_get_ne hwv] at hwx
          exact hCons w x hwx
    · -- Skip not ready
      rw [singleStepAtDet_skip_not_ready M s' v hReady]
      exact ⟨hLe, hCons⟩

/-- One sweep of `stepOnceDetOn` preserves the consistency invariant. -/
private lemma isConsistentDev_stepOnceDetOn [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {s s' : Valuation α} (h : isConsistentDev M s s') (vs : List V) :
    isConsistentDev M s (stepOnceDetOn M vs s') := by
  unfold stepOnceDetOn
  induction vs generalizing s' with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih (isConsistentDev_singleStepAtDet M h v)

/-- Iteration of `developDetOn` preserves the consistency invariant. -/
private lemma isConsistentDev_developDetOn [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (vs : List V) (n : ℕ) :
    isConsistentDev M s (developDetOn M vs n s) := by
  induction n with
  | zero => exact isConsistentDev_self M s
  | succ n ih =>
    show isConsistentDev M s ((stepOnceDetOn M vs)^[n + 1] s)
    rw [Function.iterate_succ_apply']
    exact isConsistentDev_stepOnceDetOn M ih vs

/-- **Soundness bridge**: if iteration produces value `x` at `v`, then
    the canonical `developDetVtx M s v = x`.

    Lets consumers prove abstract `developDet`-flavored claims by
    computing the corresponding `developDetOn` form with `decide` and
    lifting via this bridge.

    The reverse direction (completeness — every vertex eventually
    determined) requires substrate work on topological depth and is
    deferred. -/
theorem developDetVtx_of_developDetOn_hasValue [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {s : Valuation α} {vs : List V} {n : ℕ} {v : V} {x : α v}
    (h : (developDetOn M vs n s).hasValue v x) :
    developDetVtx M s v = x :=
  (isConsistentDev_developDetOn M s vs n).2 v x h

/-- **`Valuation`-form bridge**: if iteration's hasValue claim holds, so
    does the canonical `developDet`'s. -/
theorem developDet_hasValue_of_developDetOn_hasValue [DecidableEq V] [DecidableValuation α]
    {M : SEM V α} [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {s : Valuation α} {vs : List V} {n : ℕ} {v : V} {x : α v}
    (h : (developDetOn M vs n s).hasValue v x) :
    (M.developDet s).hasValue v x := by
  rw [developDet_hasValue_iff]
  exact developDetVtx_of_developDetOn_hasValue h

-- ════════════════════════════════════════════════════
-- § Bridge: developDet ↦ developDetOn (completeness)
-- ════════════════════════════════════════════════════

/-! Completeness counterpart to the soundness bridge above. For a
    `Fintype V + IsDAG + IsDeterministic` SEM, `Fintype.card V`
    iterations of `stepOnceDetOn` over any vertex list covering all of
    `V` produce the canonical answer at every vertex.

    Proof outline:
    1. Monotonicity: `s.le (singleStepAtDet M s v)`, etc.
    2. Single-step progress: undetermined+ready ⇒ determined after step.
    3. IsDAG min: nonempty undetermined set has a `WellFounded.has_min`
       member whose strict ancestors (and so parents) are all determined,
       hence ready.
    4. Pass-progress: every non-fixed pass strictly decreases `undetCount`.
    5. Bound: after `Fintype.card V` passes, `undetCount = 0`. -/

section Completeness

variable [DecidableEq V] [DecidableValuation α]
variable (M : SEM V α) [IsDeterministic M]

/-- `singleStepAtDet` only extends the valuation. -/
private lemma singleStepAtDet_le (s : Valuation α) (v : V) :
    s.le (singleStepAtDet M s v) := by
  intro w x hwx
  by_cases hSome : (s.get v).isSome
  · rw [singleStepAtDet_skip_determined M s v hSome]; exact hwx
  · rw [Option.not_isSome_iff_eq_none] at hSome
    by_cases hR : ready M s v
    · rw [singleStepAtDet_extend M s v (Option.isNone_iff_eq_none.mpr hSome) hR]
      by_cases hwv : w = v
      · subst hwv
        rw [Valuation.hasValue, hSome] at hwx
        exact absurd hwx (by simp)
      · rw [Valuation.hasValue, Valuation.extend_get_ne hwv]; exact hwx
    · rw [singleStepAtDet_skip_not_ready M s v hR]; exact hwx

omit [DecidableEq V] [DecidableValuation α] in
/-- `Valuation.le` is transitive. -/
private lemma Valuation.le_trans {s₁ s₂ s₃ : Valuation α}
    (h₁₂ : s₁.le s₂) (h₂₃ : s₂.le s₃) : s₁.le s₃ :=
  fun w x hwx => h₂₃ w x (h₁₂ w x hwx)

/-- `stepOnceDetOn` only extends the valuation. -/
private lemma stepOnceDetOn_le (s : Valuation α) (vs : List V) :
    s.le (stepOnceDetOn M vs s) := by
  unfold stepOnceDetOn
  induction vs generalizing s with
  | nil => intro w x h; exact h
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact Valuation.le_trans (singleStepAtDet_le M s v) (ih (singleStepAtDet M s v))

/-- `developDetOn` only extends the valuation. -/
private lemma developDetOn_le (s : Valuation α) (vs : List V) (n : ℕ) :
    s.le (developDetOn M vs n s) := by
  induction n generalizing s with
  | zero => intro w x h; exact h
  | succ n ih =>
    rw [developDetOn_succ]
    exact Valuation.le_trans (stepOnceDetOn_le M s vs) (ih (stepOnceDetOn M vs s))

omit [DecidableEq V] [DecidableValuation α] [IsDeterministic M] in
/-- `ready` is monotone in the valuation: extending a valuation only
    determines more parents, preserving readiness. -/
private lemma ready_mono {s s' : Valuation α} (hLe : s.le s') (v : V)
    (hR : ready M s v) : ready M s' v := by
  intro u hu
  have hSome : (s.get u).isSome := hR u hu
  have hVal : s.hasValue u ((s.get u).get hSome) := (Option.some_get hSome).symm
  have hVal' : s'.hasValue u ((s.get u).get hSome) := hLe u _ hVal
  rw [Valuation.hasValue] at hVal'
  rw [hVal']
  rfl

/-- After firing `singleStepAtDet` at `v` with `v` undetermined and ready,
    `v` is determined. -/
private lemma singleStepAtDet_isSome_self
    (s : Valuation α) (v : V)
    (hN : (s.get v).isNone) (hR : ready M s v) :
    ((singleStepAtDet M s v).get v).isSome := by
  rw [singleStepAtDet_extend M s v hN hR]
  rw [Valuation.extend_get_same]; rfl

/-- A foldl pass over a list containing `v` determines `v`, provided `v`
    is undetermined and ready in the starting state.

    Proof: induct on the list. If `v` is the head, fire there and propagate
    via `stepOnceDetOn_le`. If not, the head's step preserves `v`'s
    undeterminedness and ready-ness (monotonicity), then apply IH. -/
private lemma stepOnceDetOn_isSome_of_mem_undet_ready
    (s : Valuation α) (vs : List V) (v : V)
    (hMem : v ∈ vs) (hN : (s.get v).isNone) (hR : ready M s v) :
    ((stepOnceDetOn M vs s).get v).isSome := by
  induction vs generalizing s with
  | nil => exact absurd hMem (List.not_mem_nil)
  | cons w vs ih =>
    rw [stepOnceDetOn_cons]
    by_cases hwv : v = w
    · -- Fire at v on this step; propagate via stepOnceDetOn_le.
      subst hwv
      have hSome := singleStepAtDet_isSome_self M s v hN hR
      have hVal : (singleStepAtDet M s v).hasValue v
          ((singleStepAtDet M s v).get v |>.get hSome) :=
        (Option.some_get hSome).symm
      have hVal' :
          (stepOnceDetOn M vs (singleStepAtDet M s v)).hasValue v _ :=
        stepOnceDetOn_le M (singleStepAtDet M s v) vs _ _ hVal
      rw [Valuation.hasValue] at hVal'
      rw [hVal']; rfl
    · -- v is later in the list; preserve undet+ready, then IH.
      have hMem' : v ∈ vs := by
        rcases List.mem_cons.mp hMem with h | h
        · exact absurd h hwv
        · exact h
      apply ih
      · exact hMem'
      · -- (singleStepAtDet M s w).get v = s.get v = none
        by_cases hwSome : (s.get w).isSome
        · rw [singleStepAtDet_skip_determined M s w hwSome]; exact hN
        · rw [Option.not_isSome_iff_eq_none] at hwSome
          by_cases hwReady : ready M s w
          · rw [singleStepAtDet_extend M s w (Option.isNone_iff_eq_none.mpr hwSome) hwReady]
            rw [Valuation.extend_get_ne hwv]; exact hN
          · rw [singleStepAtDet_skip_not_ready M s w hwReady]; exact hN
      · exact ready_mono M (singleStepAtDet_le M s w) v hR

omit [DecidableEq V] [DecidableValuation α] [IsDeterministic M] in
/-- For an `IsDAG`, any nonempty set of undetermined vertices contains a
    member whose strict ancestors are all determined — hence ready.

    Proof: apply `WellFounded.has_min` to `IsStrictAncestor` and the set
    `{v | (s.get v).isNone}`. The minimum vertex `a` has no undet strict
    ancestor; in particular all its parents are determined. -/
private lemma exists_undet_ready [hDag : CausalGraph.IsDAG M.graph]
    (s : Valuation α) (hExists : ∃ v, (s.get v).isNone) :
    ∃ v, (s.get v).isNone ∧ ready M s v := by
  obtain ⟨v₀, hv₀⟩ := hExists
  let S : Set V := {v | (s.get v).isNone}
  have hS_nonempty : S.Nonempty := ⟨v₀, hv₀⟩
  obtain ⟨a, haS, ha_min⟩ := hDag.wf.has_min S hS_nonempty
  refine ⟨a, haS, ?_⟩
  intro u hu
  by_contra hNotSome
  rw [Option.not_isSome_iff_eq_none] at hNotSome
  have huS : u ∈ S := show (s.get u).isNone = true by
    rw [hNotSome]; rfl
  have hAnc : M.graph.IsStrictAncestor u a := Relation.TransGen.single hu
  exact ha_min u huS hAnc

omit [IsDeterministic M] in
/-- Count of undetermined vertices. Strictly decreases when any vertex
    becomes determined. -/
private def undetCount [Fintype V] (s : Valuation α) : ℕ :=
  (Finset.univ.filter (fun v => (s.get v).isNone = true)).card

omit [DecidableValuation α] [IsDeterministic M] in
/-- Pointwise progress at any vertex strictly decreases `undetCount`. -/
private lemma undetCount_lt_of_progress [Fintype V]
    {s s' : Valuation α} (hLe : s.le s') (v : V)
    (hN : (s.get v).isNone) (hS : (s'.get v).isSome) :
    undetCount s' < undetCount s := by
  unfold undetCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  refine ⟨v, ?_, ?_⟩
  · -- v ∉ undet(s')
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Option.isNone_iff_eq_none]
    exact Option.ne_none_iff_isSome.mpr hS
  · -- insert v (undet s') ⊆ undet s
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rcases hu with rfl | hu'
    · exact hN
    · -- (s'.get u).isNone = true ⇒ (s.get u).isNone = true
      rw [Option.isNone_iff_eq_none] at hu' ⊢
      match hsu : s.get u with
      | none => rfl
      | some y =>
        have h1 : s.hasValue u y := hsu
        have h2 : s'.hasValue u y := hLe u y h1
        rw [Valuation.hasValue, hu'] at h2
        exact absurd h2 (by simp)

/-- **Existence**: after `n ≥ undetCount s` iterations of `stepOnceDetOn`
    over a list covering `V`, every vertex is determined.

    Proof: induct on `n`. If no undet vertex, done by `developDetOn_le`.
    Otherwise, `exists_undet_ready` produces an undet+ready vertex `v`;
    `stepOnceDetOn_isSome_of_mem_undet_ready` determines it on this pass;
    `undetCount_lt_of_progress` bounds the count for IH. -/
private lemma developDetOn_isSome_of_card_le [Fintype V]
    [hDag : CausalGraph.IsDAG M.graph]
    (vs : List V) (hCovers : ∀ v : V, v ∈ vs) :
    ∀ (s : Valuation α) (n : ℕ), undetCount s ≤ n → ∀ v : V,
      ((developDetOn M vs n s).get v).isSome := by
  intro s n
  induction n generalizing s with
  | zero =>
    intro hN v
    -- undetCount s = 0 means filter is empty
    have hCount : undetCount s = 0 := Nat.le_zero.mp hN
    rw [developDetOn_zero]
    -- ¬ ((s.get v).isNone)
    by_contra hNotSome
    rw [Option.not_isSome_iff_eq_none] at hNotSome
    have hvUndet : v ∈ Finset.univ.filter (fun w => (s.get w).isNone = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Option.isNone_iff_eq_none]
      exact hNotSome
    have : Finset.univ.filter (fun w => (s.get w).isNone = true) = ∅ :=
      Finset.card_eq_zero.mp hCount
    rw [this] at hvUndet
    exact absurd hvUndet (Finset.notMem_empty v)
  | succ n ih =>
    intro hN v
    rw [developDetOn_succ]
    by_cases hExists : ∃ w, (s.get w).isNone = true
    · obtain ⟨w, hw, hRw⟩ := exists_undet_ready M s hExists
      have hSomeAfter : ((stepOnceDetOn M vs s).get w).isSome :=
        stepOnceDetOn_isSome_of_mem_undet_ready M s vs w (hCovers w) hw hRw
      have hCountLt : undetCount (stepOnceDetOn M vs s) < undetCount s :=
        undetCount_lt_of_progress (stepOnceDetOn_le M s vs) w hw hSomeAfter
      have hN' : undetCount (stepOnceDetOn M vs s) ≤ n :=
        Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hCountLt hN)
      exact ih (stepOnceDetOn M vs s) hN' v
    · -- No undet vertices in s; v is determined in s, propagated via _le.
      push Not at hExists
      have hSv : (s.get v).isSome := by
        by_contra h
        rw [Option.not_isSome_iff_eq_none] at h
        exact hExists v (Option.isNone_iff_eq_none.mpr h)
      let xv : α v := (s.get v).get hSv
      have hVal : s.hasValue v xv := (Option.some_get hSv).symm
      have hValStep : (stepOnceDetOn M vs s).hasValue v xv :=
        stepOnceDetOn_le M s vs v xv hVal
      have hVal' : (developDetOn M vs n (stepOnceDetOn M vs s)).hasValue v xv :=
        developDetOn_le M (stepOnceDetOn M vs s) vs n v xv hValStep
      rw [Valuation.hasValue] at hVal'
      rw [hVal']; rfl

end Completeness

/-- **Headline completeness theorem**: under `Fintype V`, `IsDAG`, and
    `IsDeterministic`, the iteration form `developDetOn` reaches the
    canonical `developDetVtx` value at every vertex, given a covering
    list and at least `Fintype.card V` iterations.

    Proof: combine existence (`developDetOn_isSome_of_card_le`, bounded
    by `Fintype.card V` since `undetCount s ≤ Fintype.card V`) with
    soundness (`developDetVtx_of_developDetOn_hasValue`). -/
theorem developDetOn_hasValue_developDetVtx [DecidableEq V] [DecidableValuation α] [Fintype V]
    {M : SEM V α} [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {s : Valuation α} {vs : List V} (hCovers : ∀ v : V, v ∈ vs)
    {n : ℕ} (hN : Fintype.card V ≤ n) (v : V) :
    (developDetOn M vs n s).hasValue v (developDetVtx M s v) := by
  have hCardLe : undetCount s ≤ Fintype.card V := by
    unfold undetCount
    exact Finset.card_filter_le _ _
  have hSome : ((developDetOn M vs n s).get v).isSome :=
    developDetOn_isSome_of_card_le M vs hCovers s n (Nat.le_trans hCardLe hN) v
  have hVal : (developDetOn M vs n s).hasValue v
      ((developDetOn M vs n s).get v |>.get hSome) :=
    (Option.some_get hSome).symm
  have hCanon := developDetVtx_of_developDetOn_hasValue hVal
  rw [Valuation.hasValue] at hVal
  rw [Valuation.hasValue, hVal, hCanon]

/-- **Iff form of the bridge**: under `IsDAG + IsDeterministic + Fintype`
    with sufficient iterations, `developDetOn` membership and
    `developDetVtx` equality coincide. Soundness gives `→`; completeness
    gives `←` via the headline theorem. -/
theorem developDetOn_hasValue_iff [DecidableEq V] [DecidableValuation α] [Fintype V]
    {M : SEM V α} [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {s : Valuation α} {vs : List V} (hCovers : ∀ v : V, v ∈ vs)
    {n : ℕ} (hN : Fintype.card V ≤ n) (v : V) (x : α v) :
    (developDetOn M vs n s).hasValue v x ↔ developDetVtx M s v = x := by
  refine ⟨developDetVtx_of_developDetOn_hasValue, fun hEq => ?_⟩
  rw [← hEq]
  exact developDetOn_hasValue_developDetVtx hCovers hN v

/-- **Consumer Iff**: `developDet` (canonical, opaque) and `developDetOn`
    (computational, decide-friendly) agree as `hasValue` predicates under
    `IsDAG + IsDeterministic + Fintype + sufficient iterations`. The
    `decide`-shaped form for `(M.developDet s).hasValue v x` proofs. -/
theorem developDet_hasValue_iff_developDetOn_hasValue
    [DecidableEq V] [DecidableValuation α] [Fintype V]
    {M : SEM V α} [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    {s : Valuation α} {vs : List V} (hCovers : ∀ v : V, v ∈ vs)
    {n : ℕ} (hN : Fintype.card V ≤ n) (v : V) (x : α v) :
    (M.developDet s).hasValue v x ↔ (developDetOn M vs n s).hasValue v x := by
  rw [developDet_hasValue_iff, developDetOn_hasValue_iff hCovers hN]

-- Helper: PMF.pure injectivity. Two Diracs agree iff their points agree.
private theorem PMF.pure_inj {β : Type*} {a b : β}
    (h : PMF.pure a = PMF.pure b) : a = b := by
  by_contra hne
  have h1 : PMF.pure a b = 0 := PMF.pure_apply_of_ne _ _ (Ne.symm hne)
  have h2 : PMF.pure a b = 1 := h ▸ PMF.pure_apply_self b
  exact one_ne_zero (h1 ▸ h2).symm

-- Helper: `IsDeterministic.toFun` is determined by the mechanism (not the
-- typeclass instance). Routes through `run_eq` + `PMF.pure_inj`, bypassing
-- the dependent-typeclass motive issues that block direct `rw [m₁ = m₂]`.
-- Both instance arguments are explicit so callers can pin them when
-- automatic resolution doesn't unify the underlying mechanism term.
private theorem Mechanism.toFun_eq_of_mech_eq
    {V : Type*} {α : V → Type*} {G : CausalGraph V} {v : V}
    {m m' : Mechanism G α v}
    (im : Mechanism.IsDeterministic m) (im' : Mechanism.IsDeterministic m')
    (h : m = m') (ρ : ∀ u : G.parents v, α u.val) :
    @Mechanism.IsDeterministic.toFun _ _ _ _ _ im ρ
      = @Mechanism.IsDeterministic.toFun _ _ _ _ _ im' ρ := by
  have e1 : m.run ρ = PMF.pure (@Mechanism.IsDeterministic.toFun _ _ _ _ _ im ρ) :=
    im.run_eq ρ
  have e2 : m'.run ρ = PMF.pure (@Mechanism.IsDeterministic.toFun _ _ _ _ _ im' ρ) :=
    im'.run_eq ρ
  have : PMF.pure (@Mechanism.IsDeterministic.toFun _ _ _ _ _ im ρ)
       = PMF.pure (@Mechanism.IsDeterministic.toFun _ _ _ _ _ im' ρ) := by
    rw [← e1, ← e2, h]
  exact PMF.pure_inj this

/-- **Intervention-as-Extend bridge**: for an acyclic deterministic SEM
    with `cause` undetermined in `s`, Pearl-intervening to set
    `cause := xC` is equivalent (at the level of `developDet`) to
    extending the valuation with `cause = xC` and developing under the
    original mechanisms.

    Substrate fact connecting `intervene`-based development to
    `extend`-based development (the latter underlies `causallySufficient`).
    The proof goes by `IsDAG.wf.induction` on vertices: at `cause` both sides
    produce `xC` (LHS via the constant intervention mechanism; RHS via
    `developDetVtx_extended` short-circuit on the extended valuation);
    off-cause both sides reduce to the same mechanism applied to
    recursively-equal parent values via the IH.

    The dependent-typeclass equality (`toFun ((M.intervene cause xC).mech w)
    ρ = toFun (M'.mech w) ρ` for `M' = M.intervene cause xC` or `M`) is
    discharged via the `Mechanism.toFun_eq_of_mech_eq` helper above,
    which routes through `run_eq` to bypass motive-not-type-correct
    issues that block direct rewriting of the mechanism. -/
theorem developDet_intervene_eq_developDet_extend
    [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [hDag : CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause)
    (h : s.get cause = none) :
    (M.intervene cause xC).developDet s = M.developDet (s.extend cause xC) := by
  funext v
  show some (developDetVtx (M.intervene cause xC) s v) =
       some (developDetVtx M (s.extend cause xC) v)
  congr 1
  induction v using hDag.wf.induction with
  | _ w ih =>
    rw [developDetVtx_unfold (M.intervene cause xC) s w]
    rw [developDetVtx_unfold M (s.extend cause xC) w]
    by_cases hwc : w = cause
    · subst hwc
      simp only [h, Valuation.extend_get_same]
      -- Goal: toFun ((M.intervene w xC).mech w) (...) = xC
      -- Resolve via helper: pin both instances explicitly to bypass synth issues.
      rw [Mechanism.toFun_eq_of_mech_eq
            (IsDeterministic.mech_det (M := M.intervene w xC) w)
            (inferInstanceAs (Mechanism.IsDeterministic
              (Mechanism.const (G := M.graph) xC)))
            (intervene_mech_self M w xC)]
      rfl
    · have hExt : (s.extend cause xC).get w = s.get w :=
        Valuation.extend_get_ne hwc
      rw [hExt]
      cases hsw : s.get w with
      | some y => rfl
      | none =>
        -- Reduce the match-on-none on both sides
        show Mechanism.IsDeterministic.toFun ((M.intervene cause xC).mech w) _
          = Mechanism.IsDeterministic.toFun (M.mech w) _
        rw [Mechanism.toFun_eq_of_mech_eq
              (IsDeterministic.mech_det (M := M.intervene cause xC) w)
              (IsDeterministic.mech_det (M := M) w)
              (intervene_mech_other M xC hwc)]
        congr 1
        funext u
        exact ih u.val (Relation.TransGen.single u.property)

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

    Proof: PMF iteration collapses to `PMF.pure ((stepOnceDet M)^[n] s)`
    by induction on `n` (using `stepOnce_eq_pure_of_deterministic` +
    `PMF.pure_bind`). The pointwise equality with `developDet M s`
    follows from the completeness bridge `developDetOn_hasValue_developDetVtx`
    over the `Fintype.elems.toList` covering with `Fintype.card V`
    iterations: every vertex's iterated value equals
    `some (developDetVtx M s v)`, definitionally `developDet M s v`. -/
theorem develop_eq_pure_of_deterministic
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M] (s : Valuation α) :
    develop M s = PMF.pure (developDet M s) := by
  -- Step 1: PMF iteration collapses to the Dirac of `stepOnceDet` iteration.
  have hIter : ∀ (n : ℕ) (s' : Valuation α),
      (fun p => p.bind (stepOnce M))^[n] (PMF.pure s')
        = PMF.pure ((stepOnceDet M)^[n] s') := by
    intro n
    induction n with
    | zero => intro s'; rfl
    | succ k ih =>
      intro s'
      rw [Function.iterate_succ_apply, PMF.pure_bind,
          stepOnce_eq_pure_of_deterministic, ih,
          ← Function.iterate_succ_apply]
  -- Step 2: `Fintype.elems.toList` covers every vertex.
  have hCovers : ∀ v : V, v ∈ (Fintype.elems : Finset V).toList := fun v => by
    rw [Finset.mem_toList]; exact Fintype.complete v
  -- Step 3: Reduce to pointwise equality and apply the completeness bridge.
  unfold develop
  rw [hIter]
  congr 1
  funext v
  -- `(stepOnceDet M)^[n] s v` reduces to `developDetOn M Fintype.elems.toList n s v`
  -- by eta on `stepOnceDet M = stepOnceDetOn M Fintype.elems.toList`; the RHS
  -- `developDet M s v = some (developDetVtx M s v)` is definitional.
  show developDetOn M (Fintype.elems : Finset V).toList (Fintype.card V) s v
        = some (developDetVtx M s v)
  exact developDetOn_hasValue_developDetVtx hCovers (le_refl _) v

/-! ### Topological-order independence (deferred)

`develop_perm_invariant` — different topological sorts of an acyclic
DAG give the same PMF. Provable via `PMF.bind_comm` + a lemma showing
`singleStepAt M s v` is a no-op (`PMF.pure s`) when `v` is not yet
ready. Not load-bearing for current consumers; deferred until a study
needs to reason about `develop` against a hand-picked vertex order. -/

end Causation.SEM
