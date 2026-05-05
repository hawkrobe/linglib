import Linglib.Core.Assignment
import Mathlib.Data.Set.Basic

/-!
# Plural Partial Compositional DRT — Definitions
@cite{van-den-berg-1996} @cite{brasoveanu-2007} @cite{haug-2014}
@cite{dotlacil-2013} @cite{haug-dalrymple-2020}

The plural partial extension of Compositional DRT (PPCDRT). Plural CDRT
@cite{brasoveanu-2007} replaces single information states with **sets** of
states (plural information states), tracking inter-variable dependencies
necessary for cumulative readings, donkey anaphora with plural pluralities,
and cross-clause anaphora over quantified domains. Partial CDRT
@cite{haug-2014} adds *partial* assignments so a discourse referent can be
introduced without forcing eager pragmatic resolution: the unresolved
condition `u_anaph → u_ant` is *interpreted as a presupposition* via the
`∂` operator.

This file defines the substrate types (Δ-relativized DRS, conditions,
sequencing, distribution, presupposition, anaphoric coreference) for
both flavors. Application-side relations (`bindingCond`,
`groupIdentityCond`, `reciprocityCond`) and the Maximize Anaphora
principle live in `Anaphora.lean`. The cumulativity bridge to
`Plurality.Cumulativity.cumulativeOp` lives in `Cumulativity.lean`.

## Type architecture

```
PPDRSCond E := PluralAssign E → Set Nat → Prop      — paper eq 27 conditions
PPDRS₀  E   := PluralAssign E → PluralAssign E → Prop — unrelativized DRS
PPDRS   E   := Set Nat → PluralAssign E → PluralAssign E → Prop — paper eq 25
```

Conditions take the output plural state plus the distribution context `Δ`
(the set of drefs being distributed over at the current evaluation point).
DRSs are three-place relations `λΔ.λI.λO. …` per paper eq 25.

## Operators

| Notation | Definition       | Paper |
|----------|------------------|-------|
| `⨟`      | `seq`            | §2.1, sequential composition |
| `δ_u`    | `delta`          | eq 14, distribution over plural dref |
| `∂`      | `presup`         | eq 19, gap-on-failure presupposition |
| `∪u`     | `Core.PluralAssign.sumDref` | §2.1, sum over plural state |
| `→`      | `anaphCorefPresup` | eq 29, anaphoric coreference |
| `max^u`  | `maxOp`          | eq 97, max over u in plural state |

## Anchoring

Framework substrate. PPCDRT originates with @cite{brasoveanu-2007} (PCDRT),
@cite{haug-2014} (Partial CDRT), and is composed in @cite{haug-dalrymple-2020}
(PPCDRT). Initial linglib consumer: `Phenomena/Anaphora/Studies/HaugDalrymple2020.lean`;
future consumers expected as Brasoveanu, Dotlačil, and Haug 2014 study files
land. Mirrors `Theories/Semantics/Dynamic/Intensional.lean` (ICDRT
substrate, also single current consumer).

This file does NOT import any `Phenomena/` or `Studies/` content. Phase 4
study consumers project these primitives into concrete sentence-level
analyses.
-/

namespace Theories.Semantics.Dynamic.PPCDRT

open Core

universe u

variable {E : Type u}

-- ════════════════════════════════════════════════════════════════
-- § 1: Atomic + Plural Information-State Extensions
-- @cite{haug-dalrymple-2020} eq 5, 6, 20
-- ════════════════════════════════════════════════════════════════

/-- Singular (partial) extension `i[u]o`: `o` agrees with `i` everywhere
    except at dref `u`, where `i` is undefined and `o` becomes defined.
    @cite{haug-dalrymple-2020} eq 20. -/
def extendOne (i o : PartialAssign E) (u : Nat) : Prop :=
  i u = none ∧ (∃ d, o u = some d) ∧ ∀ u', u' ≠ u → i u' = o u'

/-- Plural extension `I[u]O` (@cite{haug-dalrymple-2020} eq 6): every input
    state in `I` is extended by some output state in `O`, and every output
    state in `O` is the extension of some input state in `I`, with `O`
    nonempty (the standard PCDRT condition that excludes degenerate
    "everything fails" cases). -/
def pluralExtend (I O : PluralAssign E) (u : Nat) : Prop :=
  (∀ i ∈ I, ∃ o ∈ O, extendOne i o u) ∧
  (∀ o ∈ O, ∃ i ∈ I, extendOne i o u) ∧
  O.IsNonempty

-- ════════════════════════════════════════════════════════════════
-- § 2: Equivalence classes `[s]_Δ` (@cite{haug-dalrymple-2020} p. 14)
-- ════════════════════════════════════════════════════════════════

/-- The equivalence class of `s` in `S` with respect to the dref-context
    `Δ`: those states `s'` in `S` that agree with `s` on every dref in `Δ`.
    Δ is the set of drefs whose values fix the local context for
    distribution. -/
def equivClass (S : PluralAssign E) (s : PartialAssign E) (Δ : Set Nat) :
    PluralAssign E :=
  ⟨λ s' => s' ∈ S ∧ ∀ u ∈ Δ, s u = s' u⟩

-- ════════════════════════════════════════════════════════════════
-- § 3: PPDRS Types (@cite{haug-dalrymple-2020} eq 25–27)
-- ════════════════════════════════════════════════════════════════

/-- A PPDRS condition: takes the (output) plural state and the distribution
    context `Δ`. @cite{haug-dalrymple-2020} eq 27. -/
abbrev PPDRSCond (E : Type u) := PluralAssign E → Set Nat → Prop

/-- Unrelativized PPDRS: a relation between input and output plural
    states. Used when no distribution is in scope (Δ = ∅). -/
abbrev PPDRS₀ (E : Type u) := PluralAssign E → PluralAssign E → Prop

/-- Δ-relativized PPDRS: three-place relation `λΔ.λI.λO. …`
    @cite{haug-dalrymple-2020} eq 25. -/
abbrev PPDRS (E : Type u) := Set Nat → PluralAssign E → PluralAssign E → Prop

-- ════════════════════════════════════════════════════════════════
-- § 4: Core Operators
-- ════════════════════════════════════════════════════════════════

/-- Lift a condition to a PPDRS as a test (identity update + condition).
    Tests preserve the input state and check the condition on it. -/
def cond (C : PPDRSCond E) : PPDRS E := λ Δ I O => I = O ∧ C O Δ

/-- Sequential composition of PPDRSs (@cite{haug-dalrymple-2020} §2.1).
    Notation: `K₁ ⨟ K₂`. -/
def seq (K₁ K₂ : PPDRS E) : PPDRS E :=
  λ Δ I O => ∃ M, K₁ Δ I M ∧ K₂ Δ M O

@[inherit_doc] infixl:65 " ⨟ " => seq

/-- Distribution operator `δ_u` (@cite{haug-dalrymple-2020} eq 14).
    Distributes the body `K` over equivalence classes of the input plural
    state induced by the values of dref `u`, while preserving the *summed*
    set of values for `u` between input and output. The distribution
    context Δ grows by `{u}` inside the body — that is what lets the body
    reference `u` distributively. -/
def delta (u : Nat) (K : PPDRS E) : PPDRS E := λ Δ I O =>
  Core.PluralAssign.sumDref I u = Core.PluralAssign.sumDref O u ∧
  ∀ d ∈ Core.PluralAssign.sumDref I u,
    K (insert u Δ) (I.restrict u d) (O.restrict u d)

/-- Presupposition wrapper `∂` (@cite{haug-dalrymple-2020} eq 19). At the
    PPCDRT substrate level this is the identity on conditions; the
    gap-on-failure semantics is realised at the *sentence* level when
    consumers (Phase 4) project a PPDRS into `Truth3` via the homogeneity
    machinery (`Theories/Semantics/Homogeneity/Basic.lean`). Wrapping with
    `presup` here documents the presuppositional intent and admits future
    refinement to a `Truth3`-valued condition. -/
def presup (C : PPDRSCond E) : PPDRSCond E := C

/-- Anaphoric coreference presupposition `u_anaph → u_ant`
    (@cite{haug-dalrymple-2020} eq 29). The asymmetry of the paper —
    anaphor uses the local equivalence class `[s]_Δ`, antecedent uses the
    whole state `S` — collapses to pointwise dref equality when the two
    drefs are jointly defined; the asymmetry only does work when paired
    with `delta` over a different dref. -/
def anaphCorefPresup (uAnaph uAnt : Nat) : PPDRSCond E := λ S _Δ =>
  ∀ s ∈ S, ∃ d, s uAnaph = some d ∧ s uAnt = some d

-- ════════════════════════════════════════════════════════════════
-- § 5: max^u (@cite{haug-dalrymple-2020} eq 97)
-- ════════════════════════════════════════════════════════════════

/-- Maximizing operator `max^u(K)`: returns the relation that holds when
    the body `K` succeeds AND the value-set `∪u(O)` of the output for `u`
    is ⊆-maximal among `K`-output candidates extending `I`. The Set-valued
    `sumDref` makes the maximality statement type at full generality
    (`Set E`), with a `Finset` specialization living in `Cumulativity.lean`
    for decidable cases. -/
def maxOp (u : Nat) (K : PPDRS E) : PPDRS E := λ Δ I O =>
  K (insert u Δ) I O ∧
  ∀ O', K (insert u Δ) I O' →
    Core.PluralAssign.sumDref O' u ⊆ Core.PluralAssign.sumDref O u

-- ════════════════════════════════════════════════════════════════
-- § 6: DRef Introduction `[u₁ … uₙ]`
-- ════════════════════════════════════════════════════════════════

/-- Introduce a single fresh discourse referent `u`: the unrelativized
    DRS `[u]` is the relation `pluralExtend I O u`. -/
def newDref (u : Nat) : PPDRS E := λ _Δ I O => pluralExtend I O u

/-- Introduce a sequence of fresh drefs by iterated extension. -/
def newDrefs : List Nat → PPDRS E
  | [] => λ _Δ I O => I = O
  | u :: us => seq (newDref u) (newDrefs us)

end Theories.Semantics.Dynamic.PPCDRT
