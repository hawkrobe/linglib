import Linglib.Theories.Semantics.Dynamic.Context
import Linglib.Theories.Semantics.Dynamic.Core.CCP
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Probabilistic Lookup — `HasFiberedLookup PMF` instance

@cite{lassiter-goodman-2017} @cite{grove-white-2025} @cite{grove-white-2025b}

The Bayesian/probabilistic third corner of the effect-functor-parameterized
`HasFiberedLookup M` family. Lookup at `(v, w)` returns a `PMF E` —
a probability distribution over what value variable `v` takes at world `w`.

| Family | `M` | Falsifier | Source file |
|---|---|---|---|
| ICDRT | `Entity` | `.star` | `Dynamic/Context.lean` |
| Charlow | `Set` | `∅` | `Dynamic/Nondeterminism/Charlow2019.lean` |
| Bayesian | `PMF` | zero-mass | this file |
| FCS | partial-`Dom` | `Dom` partiality | `Dynamic/FileChange/Basic.lean` |

## Bayesian state — fibered shape (this file)

`BayesianState W E := W → PMF (Assignment E)` — for each world, a
distribution over assignments. The lookup `iLookup s v w` marginalizes
out variables other than `v` by mapping `(· v)` over `s w`.

## SEAM (Seam 2): Joint-state Bayesian deferred

@cite{grove-white-2025b}'s **parameterized dynamic semantics** (PDS) uses
a *joint* shape: `Pσ σ σ' α := σ → P(α × σ')`, formalized as
`Probability/Basic.lean:PState`. The natural Bayesian-as-`HasJointState`
instance would refactor `BayesianState` to `PMF (W × Assignment E)` and
declare `HasJointState PMF`. The `joint` field is then the identity (no
marginalization at all); deriving the fibered `iLookup` requires
`PMF.cond` machinery with a mass-zero-handling story (return `Option`
or `WithBot`, since conditioning on a measure-zero world is undefined).

The fibered shape preserved here is the *honest projection*; the joint
upgrade is tracked separately to avoid churning every downstream file
that consumes per-world `PMF (Assignment E)` priors. See
`PState`/`Pσ`/`Probability/Basic.lean` for the joint shape that an
eventual `HasJointState PMF` instance would hook into.

## Bridges to `Set` (Charlow)

The bridge maps to the Charlow family use mathlib's `PMF.support`
(non-zero-mass elements) and `PMF.uniformOfFinset` (uniform distribution
on a nonempty finite set). These ship as natural transformations between
the per-world `Set` and `PMF` fibers.
-/

namespace Semantics.Dynamic.Probabilistic

open Semantics.Dynamic.Core
open Semantics.Dynamic.Context

/-- Bayesian dynamic state: per-world probability distribution over
assignments. The natural `M = PMF` analog of Charlow's per-world set
of alternatives. -/
def BayesianState (W E : Type) : Type := W → PMF (Assignment E)

/-- Bayesian state as the **probabilistic** (`M = PMF`) instance of the
unified lookup interface. The lookup at `(v, w)` is the marginal
distribution of variable `v`'s value: take `s w` (the joint distribution
over assignments at `w`) and map `(· v)`.

## SEAM (Falsifier, Seam 1): Bayesian commits to **zero-mass** as the
no-referent case. There is no value-level falsifier — "no referent"
shows up as `(s w).map (· v) v = 0`, not as a distinguished `Entity.star`
or empty alternative-set. Bridge to Charlow via `supportFiber`
(probability → possibility) is lossy whenever the PMF has nontrivial
spread. -/
noncomputable instance instBayesianHasFiberedLookup (W E : Type) :
    HasFiberedLookup PMF (BayesianState W E) Nat W E where
  iLookup s v w := (s w).map (· v)

-- ════════════════════════════════════════════════════════════════
-- Bridge natural transformations — Bayesian ↔ Charlow (per-world fiber)
-- ════════════════════════════════════════════════════════════════

/-- **Bayesian ↠ Charlow** (per world): the support of the per-world
PMF gives the set of possible-value alternatives. Mathlib supplies
`PMF.support : PMF α → Set α` directly; this is the natural
transformation `PMF ⟶ Set` applied at each world. -/
noncomputable def supportFiber {W E : Type} (s : BayesianState W E)
    (w : W) : Set (Assignment E) :=
  (s w).support

/-- **Charlow ↪ Bayesian** (per world, when supported): the uniform
distribution on a nonempty finite set of alternatives. The lift
requires a nonemptiness witness; outside it, no probability assignment
is well-defined (Charlow's "nothing rules anything out" is incompatible
with the PMF normalization axiom).

This is the natural transformation `Set ⟶ PMF` whose existence is
gated by finite nonempty support — matching the Set/PMF asymmetry
visible in mathlib (`PMF.uniformOfFinset` requires `Finset.Nonempty`). -/
noncomputable def uniformFiber {W E : Type} [DecidableEq (Assignment E)]
    (s : W → Finset (Assignment E))
    (h : ∀ w, (s w).Nonempty) : BayesianState W E :=
  fun w => PMF.uniformOfFinset (s w) (h w)

end Semantics.Dynamic.Probabilistic
