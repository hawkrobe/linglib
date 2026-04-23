import Linglib.Core.Causal.V2.SEM.Basic
import Linglib.Core.Causal.V2.SEM.Bool

/-!
# SEM: Causal Counterfactual Predicates (V2)

Polymorphic counterfactual predicates over a `SEM V α`, plus `BoolSEM`-flavored
aliases for legacy SBH-style binary semantics.

- **`developsToValue M s v x`**: after developing `s`, vertex `v` has value `x`.
  Replaces the old `developsToTrue` (Bool-specialized) with a polymorphic version.

- **`causallySufficient M s cause xC effect xE`**: extending `s` with `xC` at
  `cause` then developing produces `xE` at `effect`. Polymorphic generalization
  of @cite{nadathur-lauer-2020} Definition 23.

**Necessity** is *not* exposed as a Core primitive. The 2026 canonical
literature on causal-verb semantics (@cite{nadathur-2024} Def 10b,
@cite{cao-white-lassiter-2025} graded ALT, @cite{beller-gerstenberg-2025}
counterfactual simulation) has moved past simple Lewis but-for. Each
necessity flavor is theory-specific:
- Lewis-style but-for: `¬ causallySufficient M s cause xC_alt effect xE`
  (one-liner — define in `Phenomena/Causation/Studies/Lewis1973.lean`)
- Nadathur 2024 Def 10b: precondition + achievable + supersituation
  (port lazily alongside `Theories/Semantics/Causation/Necessity.lean` migration)
- CWL graded: not a discrete predicate (graded ALT measure)

`BoolSEM`-namespace aliases specialize the polymorphic predicates to
`α := fun _ => Bool` with `xC = true`, `xE = true` (legacy SBH semantics).

## Computability

`develop` is `noncomputable` (cascading from `PMF.pure` and `Finset.toList`),
so all predicates here are `noncomputable`. `Decidable` instances are provided
via `Classical.dec`; consumers wanting `decide` to reduce concretely on small
SEMs should use `native_decide` or supply structural proofs. Matches the
mathlib idiom for probability-flavored predicates (`Mathlib/Probability/`).
-/

namespace Core.Causal.V2.SEM

variable {V : Type*} {α : V → Type*}
variable [Fintype V] [DecidableEq V] [DecidableValuation α]

-- ════════════════════════════════════════════════════
-- § Polymorphic counterfactual predicates
-- ════════════════════════════════════════════════════

/-- After developing the SEM against `s`, vertex `v` has the value `x`.

    Polymorphic generalization of the old `developsToTrue` (which fixed
    `α := fun _ => Bool` and `x := true`). -/
def developsToValue (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (v : V) (x : α v) : Prop :=
  (M.develop s).hasValue v x

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (v : V) (x : α v) :
    Decidable (developsToValue M s v x) :=
  Classical.dec _

/-- **Causal sufficiency**: forcing `cause` to `xC` makes `effect` develop to `xE`.

    Polymorphic generalization of @cite{nadathur-lauer-2020} Definition 23.
    The Bool case (`BoolSEM.causallySufficient`) recovers the legacy semantics
    "`cause = true` produces `effect = true`". -/
def causallySufficient (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause)
    (effect : V) (xE : α effect) : Prop :=
  developsToValue M (s.extend cause xC) effect xE

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causallySufficient M s cause xC effect xE) :=
  Classical.dec _

-- ════════════════════════════════════════════════════
-- § Basic API lemmas (polymorphic)
-- ════════════════════════════════════════════════════

/-- `developsToValue` unfolds to `(develop M s).hasValue v x`. -/
@[simp] theorem developsToValue_iff (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (v : V) (x : α v) :
    developsToValue M s v x ↔ (M.develop s).hasValue v x := Iff.rfl

/-- `causallySufficient` unfolds to `developsToValue` of the extended valuation. -/
@[simp] theorem causallySufficient_iff (M : SEM V α)
    [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    causallySufficient M s cause xC effect xE ↔
      developsToValue M (s.extend cause xC) effect xE := Iff.rfl

/-- **Interventionist manipulation** (Woodward's criterion): cause's value
    affects effect's value under `develop`. Defined via `extend` rather
    than `intervene` because for deterministic acyclic SEMs they agree
    and `extend` doesn't require re-establishing `IsDeterministic` on the
    intervened SEM. -/
def manipulates (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC1 xC2 : α cause) (effect : V) : Prop :=
  (M.develop (s.extend cause xC1)).get effect ≠
  (M.develop (s.extend cause xC2)).get effect

noncomputable instance (M : SEM V α) [CausalGraph.IsDAG M.graph] [IsDeterministic M]
    (s : Valuation α) (cause : V) (xC1 xC2 : α cause) (effect : V) :
    Decidable (manipulates M s cause xC1 xC2 effect) :=
  Classical.dec _

-- ════════════════════════════════════════════════════
-- § Nadathur 2024 Def 10b: causallyNecessary (BoolSEM only)
-- ════════════════════════════════════════════════════

/-! Port of @cite{nadathur-2024} Definition 10b to V2. Specialized to
    `BoolSEM` (the binary substrate the original definition was given on);
    polymorphic generalization to multi-valued α can come if a consumer
    needs it. -/

end Core.Causal.V2.SEM

-- ════════════════════════════════════════════════════
-- § BoolSEM specializations (legacy SBH-style binary semantics)
-- ════════════════════════════════════════════════════

namespace Core.Causal.V2.BoolSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

open Core.Causal.V2 (SEM Valuation BoolSEM)
open Core.Causal.V2.SEM (developsToValue causallySufficient)

/-- `BoolSEM`-flavored `developsToValue`: vertex `v` develops to `true`. -/
abbrev developsToTrue (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool)) (v : V) : Prop :=
  developsToValue M s v true

/-- `BoolSEM`-flavored `causallySufficient`: setting `cause = true` develops
    `effect = true`. Matches old `Core.Causal.causallySufficient` semantics. -/
abbrev causallySufficient (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  SEM.causallySufficient M s cause true effect true

/-- `BoolSEM`-flavored `manipulates`: cause's value (true vs false) flips
    effect's value under `develop`. -/
abbrev manipulates (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool)) (cause effect : V) : Prop :=
  SEM.manipulates M s cause true false effect

/-- **Direct causal connection**: `cause` is a parent of `effect` in
    the SEM's graph. Pure structural predicate (no `develop`); fully
    decidable structurally via `Finset.decidableMem`. -/
def hasDirectLaw (M : BoolSEM V) (cause effect : V) : Prop :=
  cause ∈ M.graph.parents effect

instance (M : BoolSEM V) (cause effect : V) :
    Decidable (hasDirectLaw M cause effect) :=
  inferInstanceAs (Decidable (cause ∈ M.graph.parents effect))

-- ════════════════════════════════════════════════════
-- § Nadathur 2024 Def 10b: causallyNecessary (BoolSEM)
-- ════════════════════════════════════════════════════

/-- All Bool-extensions of a valuation over a list of vertices.
    Each vertex can be left undetermined, set true, or set false (3^n). -/
def allExtensionsBool (s : Valuation (fun _ : V => Bool)) :
    List V → List (Valuation (fun _ : V => Bool))
  | [] => [s]
  | v :: vs =>
    let rest := allExtensionsBool s vs
    rest ++ rest.map (·.extend v true) ++ rest.map (·.extend v false)

/-- Free-extension list: vertices to range over in supersituation
    quantification. Excludes `effect` (the one being tested) and any
    vertex already determined in `base`. Noncomputable because of
    `Finset.toList`. -/
noncomputable def freeExtensionsBool (base : Valuation (fun _ : V => Bool))
    (effect : V) : List V :=
  (Fintype.elems : Finset V).toList.filter fun v =>
    decide (v ≠ effect ∧ (base.get v).isNone)

/-- **Consistent supersituation** check (@cite{nadathur-2024} Def 9b):
    `s'` is a consistent supersituation of `base` iff for each vertex
    `x` undetermined in `base` whose value `s'` sets, that value agrees
    with what `develop` would produce from `base` alone. (Per-vertex
    approximation; not the joint development of `s'`.) -/
noncomputable def SEM.isConsistentSuperBool (M : BoolSEM V)
    [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (base s' : Valuation (fun _ : V => Bool)) : Prop :=
  ∀ x : V,
    (base.get x = none → s'.get x = some true →
      ¬ (M.develop base).hasValue x false) ∧
    (base.get x = none → s'.get x = some false →
      ¬ (M.develop base).hasValue x true)

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (base s' : Valuation (fun _ : V => Bool)) :
    Decidable (SEM.isConsistentSuperBool M base s') := Classical.dec _

namespace causallyNecessary

/-- **Precondition** (@cite{nadathur-2024} Def 10b): neither cause nor
    effect is already entailed by `s` under `M`. -/
noncomputable def precondition (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  ¬ (M.develop s).hasValue cause true ∧
  ¬ (M.develop s).hasValue effect true

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation _) (cause effect : V) :
    Decidable (precondition M s cause effect) := Classical.dec _

/-- **Achievability** clause (i) of @cite{nadathur-2024} Def 10b: some
    consistent supersituation of `s.extend cause true` (with `effect`
    left undetermined) develops to make `effect` true. -/
noncomputable def achievable (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  let sCause := s.extend cause true
  ∃ s' ∈ allExtensionsBool sCause (freeExtensionsBool sCause effect),
    SEM.isConsistentSuperBool M sCause s' ∧
    (M.develop s').hasValue effect true

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation _) (cause effect : V) :
    Decidable (achievable M s cause effect) := Classical.dec _

/-- **But-for** clause (ii) of @cite{nadathur-2024} Def 10b: every
    consistent supersituation of `s` (with `effect` undetermined) that
    achieves `effect` also has `cause` true — no `cause`-free path. -/
noncomputable def noAlternative (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  ∀ s' ∈ allExtensionsBool s (freeExtensionsBool s effect),
    SEM.isConsistentSuperBool M s s' →
    (M.develop s').hasValue effect true →
    (M.develop s').hasValue cause true

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation _) (cause effect : V) :
    Decidable (noAlternative M s cause effect) := Classical.dec _

end causallyNecessary

/-- **Causal Necessity** (@cite{nadathur-2024} Definition 10b).

    ⟨cause, true⟩ is causally necessary for ⟨effect, true⟩ relative
    to `s` under `M` iff:
    - **Precondition**: `s ⊭ cause = true` and `s ⊭ effect = true`
    - **(i) Achievability**: `s.extend cause true` has a consistent
      supersituation `s'` (with `effect` undetermined) where
      `develop s' ⊨ effect = true`
    - **(ii) But-for**: no consistent supersituation `s'` of `s` (with
      `effect` undetermined) achieves `effect` while `s' ⊭ cause = true`

    Supersedes the simple but-for test from @cite{nadathur-lauer-2020}
    Definition 24. Specialized to `BoolSEM`; polymorphic generalization
    to multi-valued α can come if a consumer needs it. -/
noncomputable def causallyNecessary (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation (fun _ : V => Bool))
    (cause effect : V) : Prop :=
  causallyNecessary.precondition M s cause effect ∧
  causallyNecessary.achievable M s cause effect ∧
  causallyNecessary.noAlternative M s cause effect

noncomputable instance (M : BoolSEM V) [CausalGraph.IsDAG M.graph]
    [SEM.IsDeterministic M] (s : Valuation _) (cause effect : V) :
    Decidable (causallyNecessary M s cause effect) := Classical.dec _

end Core.Causal.V2.BoolSEM
