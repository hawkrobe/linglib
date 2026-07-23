import Linglib.Semantics.Causation.SEM.Defs

/-!
# BoolSEM: Legacy Binary-Substrate Convenience Alias

`BoolSEM V := SEM V (fun _ => Bool)`. Convenience for consumers that
work in the SBH 2009 deterministic-binary substrate (the special case
where every vertex has value type `Bool`). Lives in its own file so the
core `SEM/Defs.lean` stays focused on the general API.
-/

namespace Causation

/-- A `BoolSEM V` is the SBH-style binary substrate: every vertex's
    value is `Bool`. Convenience abbreviation for consumers that don't
    need multi-valued variables. -/
abbrev BoolSEM (V : Type*) := SEM V (fun _ => Bool)

end Causation
