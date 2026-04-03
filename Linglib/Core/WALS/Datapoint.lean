/-!
# WALS Generic Datapoint

Shared infrastructure for all 192 WALS feature files. Each feature file
defines its own inductive type for feature values and a `List (Datapoint V)`
of observations. The generic lookup functions and datapoint structure
live here.

See `Core/WALS/Features/` for the per-feature data files, auto-generated
by `python3 scripts/gen_wals.py`.
-/

namespace Core.WALS

/-- A single WALS datapoint, parameterized by the feature value type `V`. -/
structure Datapoint (V : Type) where
  walsCode : String
  language : String
  iso : String
  value : V
  deriving Repr, DecidableEq

/-- Look up a language by WALS code. -/
def Datapoint.lookup {V : Type} [BEq V] (data : List (Datapoint V))
    (code : String) : Option (Datapoint V) :=
  data.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def Datapoint.lookupISO {V : Type} [BEq V] (data : List (Datapoint V))
    (iso : String) : Option (Datapoint V) :=
  data.find? (·.iso == iso)

end Core.WALS
