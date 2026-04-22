import Linglib.Core.Causal.V2.SEM.Defs

/-!
# BoolSEM: Legacy Binary-Substrate Convenience Alias (V2)

`BoolSEM V := SEM V (fun _ => Bool)`. Convenience for consumers that
work in the SBH 2009 deterministic-binary substrate (the special case
where every vertex has value type `Bool`). Lives in its own file so the
core `SEM/Defs.lean` stays focused on the general API.
-/

namespace Core.Causal.V2

/-- A `BoolSEM V` is the SBH-style binary substrate: every vertex's
    value is `Bool`. Convenience abbreviation for consumers that don't
    need multi-valued variables. -/
abbrev BoolSEM (V : Type*) := SEM V (fun _ => Bool)

end Core.Causal.V2
