import Linglib.Features.Case.Basic

/-!
# Polish interrogative pronouns

*kto* 'who' and *co* 'what' by case: *kogo* serves *kto* as both genitive and
accusative, and *co* serves as both nominative and accusative.

## References

* [M. Dalrymple and R. M. Kaplan, *Feature indeterminacy and feature resolution*
  (2000)][dalrymple-kaplan-2000]
-/

namespace Polish.Pronouns

/-- *kto* 'who' by case. -/
def kto : Case → Option String
  | .nom => some "kto"
  | .gen => some "kogo"
  | .dat => some "komu"
  | .acc => some "kogo"
  | .inst => some "kim"
  | .loc => some "kim"
  | _ => none

/-- *co* 'what' by case. -/
def co : Case → Option String
  | .nom => some "co"
  | .gen => some "czego"
  | .dat => some "czemu"
  | .acc => some "co"
  | .inst => some "czym"
  | .loc => some "czym"
  | _ => none

end Polish.Pronouns
