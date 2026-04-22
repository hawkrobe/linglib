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

end Core.Causal.V2.BoolSEM
