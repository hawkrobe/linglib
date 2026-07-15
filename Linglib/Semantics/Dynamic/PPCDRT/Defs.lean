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

This file defines the **condition** type `PPDRSCond` used by
`Anaphora.lean` for the `bindingCond` / `groupIdentityCond` /
`reciprocityCond` predicates and by `Cumulativity.lean` for the bridge to
`Plurality.Cumulativity.Cumulative`. A PPDRS condition takes the (output)
plural state plus the distribution context `Δ` (the set of drefs being
distributed over); the Δ argument is used by distribution machinery
(`δ_u`, paper eq 14) but ignored by the present
binding/group-identity/reciprocity conditions — see `Anaphora.lean`.

## Anchoring

Framework substrate. PPCDRT originates with [brasoveanu-2007] (PCDRT)
and [haug-2014] (Partial CDRT); [haug-dalrymple-2020] composes
them into PPCDRT. Initial linglib consumer:
`Studies/HaugDalrymple2020.lean`. Mirrors
`Semantics/Dynamic/ICDRT/Defs.lean` (ICDRT substrate, also single
current consumer).
-/

namespace PPCDRT

open Core

/-- A PPDRS condition: takes the (output) plural state and the
    distribution context `Δ`. [haug-dalrymple-2020] eq 27.

    The Δ argument is part of the eq-25 three-place DRS shape but is
    ignored by the present `bindingCond` / `groupIdentityCond` /
    `reciprocityCond` (which are evaluated at the unrelativized layer
    Δ = ∅). It is preserved in the type so consumers that DO need
    distribution (e.g. a future Dotlačil 2013 study file) can plug in
    without changing this signature. -/
abbrev PPDRSCond (E : Type*) := PluralAssign E → Set Nat → Prop

end PPCDRT
