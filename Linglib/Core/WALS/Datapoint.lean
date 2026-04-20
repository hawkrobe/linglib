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

/-- A single WALS datapoint, parameterized by the feature value type `V`.

The human-readable language name is intentionally absent from this struct —
each entry already references a `walsCode`, and `Core.WALS.Languages.findLanguage`
is the canonical lookup for human names. Storing the name in every per-feature
entry duplicates ~2660 strings across 192 feature files for no consumer benefit
and inflates Lean elaboration time. -/
structure Datapoint (V : Type) where
  walsCode : String
  iso : String
  value : V
  deriving Repr, DecidableEq

/-- Look up a language by WALS code. -/
def Datapoint.lookup {V : Type} [BEq V] (data : List (Datapoint V))
    (code : String) : Option (Datapoint V) :=
  data.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code.

Returns `none` for empty queries: WALS marks a handful of languages with an
empty `iso` field (e.g. WALS code `tbu`, `aze`), and a naive `find?` on `""`
would return one of those entries arbitrarily. -/
def Datapoint.lookupISO {V : Type} [BEq V] (data : List (Datapoint V))
    (iso : String) : Option (Datapoint V) :=
  if iso.isEmpty then none
  else data.find? (·.iso == iso)

end Core.WALS
