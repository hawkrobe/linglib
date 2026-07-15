import Linglib.Core.Logic.Assignment
import Mathlib.Data.Set.Basic

/-!
# Plural Partial Compositional DRT — Definitions
[van-den-berg-1996] [brasoveanu-2007] [haug-2014]
[dotlacil-2013] [haug-dalrymple-2020]

The plural partial extension of Compositional DRT (PPCDRT). Plural CDRT
[brasoveanu-2007] replaces single information states with **sets** of
states (plural information states), tracking inter-variable dependencies.
Partial CDRT [haug-2014] adds *partial* assignments so a discourse
referent can be introduced without forcing eager pragmatic resolution: the
unresolved condition `u_anaph → u_ant` is interpreted as a presupposition.

This file defines the **condition** type used by `Anaphora.lean` for the
`bindingCond` / `groupIdentityCond` / `reciprocityCond` predicates and by
`Cumulativity.lean` for the bridge to `Plurality.Cumulativity.cumulativeOp`.

## What lives here

```
PPDRSCond E := PluralAssign E → Set Nat → Prop      -- condition shape
                                                      (paper eq 27)
```

A PPDRS condition takes the (output) plural state plus the distribution
context `Δ` (the set of drefs being distributed over). The Δ argument is
used by future distribution machinery (`δ_u`, paper eq 14) but not by the
present binding/group-identity/reciprocity conditions, all of which ignore
it — see `Anaphora.lean`.

## What does NOT live here (yet)

The full PPCDRT operator set from [haug-dalrymple-2020] eq 25 — the
Δ-relativized DRS as a 3-place relation `λΔ.λI.λO.…`, the sequencing
operator `⨟`, the distribution operator `δ_u`, the presupposition wrapper
`∂`, the `max^u` maximizing operator, the dref-introduction `[u₁ … uₙ]` —
was prototyped but trimmed because **no current consumer exercises any of
them**. Per [haug-dalrymple-2020]'s presentation those operators
*are* the substrate's expressive interest; their absence here is honest
about the substrate-façade flag from the second-pass audit. They will land
when:

- A Brasoveanu 2007 / Dotlačil 2013 / Haug 2014 study file consumes them, OR
- The H&D study file extends to §3.1 intensionality (currently the
  narrow-vs-wide contrast is at the value-set level, not at the level of
  `δ_w`-distributed doxastic alternatives).

The `Anaphora.lean` and `Cumulativity.lean` files in this directory only
need `PPDRSCond` plus the `Core.PluralAssign` primitives (`singularAt`,
`sumDref`, `singleton`, `restrict`, `defined`, `null`, `ofPred`).

## Anchoring

Framework substrate. PPCDRT originates with [brasoveanu-2007] (PCDRT)
and [haug-2014] (Partial CDRT); [haug-dalrymple-2020] composes
them into PPCDRT. Initial linglib consumer:
`Studies/HaugDalrymple2020.lean`. Mirrors
`Semantics/Dynamic/Intensional.lean` (ICDRT substrate, also
single current consumer).
-/

namespace PPCDRT

open Core

universe u

variable {E : Type u}

/-- A PPDRS condition: takes the (output) plural state and the
    distribution context `Δ`. [haug-dalrymple-2020] eq 27.

    The Δ argument is part of the eq-25 three-place DRS shape but is
    ignored by the present `bindingCond` / `groupIdentityCond` /
    `reciprocityCond` (which are evaluated at the unrelativized layer
    Δ = ∅). It is preserved in the type so consumers that DO need
    distribution (e.g. a future Dotlačil 2013 study file) can plug in
    without changing this signature. -/
abbrev PPDRSCond (E : Type u) := PluralAssign E → Set Nat → Prop

end PPCDRT
