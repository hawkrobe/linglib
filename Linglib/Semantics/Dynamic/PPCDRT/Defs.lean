import Linglib.Logic.Assignment
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
distributed over), which group identity reads through the equivalence
classes of eq 26 — see `Anaphora.lean`.

## Anchoring

Framework substrate. PPCDRT originates with [brasoveanu-2007] (PCDRT)
and [haug-2014] (Partial CDRT); [haug-dalrymple-2020] composes
them into PPCDRT. Initial linglib consumer:
`Studies/HaugDalrymple2020.lean`. Mirrors
`Semantics/Dynamic/ICDRT/Defs.lean` (ICDRT substrate, also single
current consumer).
-/

namespace PPCDRT


/-- A PPDRS condition: takes the (output) plural state and the
    distribution context `Δ`. [haug-dalrymple-2020] eq 27.

    The Δ argument is the set of discourse referents distributed over in
    the three-place DRS of eq 25; `groupIdentityCond` sums the anaphor over
    the equivalence class it induces (eq 26), while `bindingCond` is
    pointwise and ignores it (eq 30). -/
abbrev PPDRSCond (E : Type*) := PluralAssign ℕ E → Set Nat → Prop

end PPCDRT
