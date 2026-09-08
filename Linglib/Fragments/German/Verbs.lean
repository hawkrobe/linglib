import Linglib.Features.Number.Basic
import Linglib.Features.Person.Basic

/-!
# German verb paradigms

The present indicative of *kaufen* 'buy' by person and number: the first and third
plural share *kaufen*, the second plural and the third singular share *kauft*.

## References

* [M. Dalrymple and R. M. Kaplan, *Feature indeterminacy and feature resolution*
  (2000)][dalrymple-kaplan-2000]
-/

namespace German.Verbs

/-- The present indicative of *kaufen* 'buy'. -/
def kaufen : Person × Number → Option String
  | (.first, .singular) => some "kaufe"
  | (.second, .singular) => some "kaufst"
  | (.third, .singular) => some "kauft"
  | (.first, .plural) => some "kaufen"
  | (.second, .plural) => some "kauft"
  | (.third, .plural) => some "kaufen"
  | _ => none

end German.Verbs
