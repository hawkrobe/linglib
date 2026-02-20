import Linglib.Core.Reichenbach

/-!
# Utterance Context

Utterance-fixed temporal anchor: bundles the speech time as a minimal
context for utterance evaluation. Provides a projection to
`ReichenbachFrame` (filling P = S as the root-clause default) and a
reverse projection from `ReichenbachFrame` back to `UtteranceContext`.

This does NOT restructure `ReichenbachFrame` — it provides a parallel
type and bidirectional projections.

## References

- Reichenbach, H. (1947). *Elements of Symbolic Logic*.
- Kiparsky, P. (2002). Event structure and the perfect.
-/

namespace Core

structure UtteranceContext (Time : Type*) where
  speechTime : Time

namespace UtteranceContext

variable {Time : Type*}

/-- Project an `UtteranceContext` into a `ReichenbachFrame` by supplying
    R and E. The perspective time P defaults to S (root clause). -/
def toReichenbachFrame (ctx : UtteranceContext Time) (R E : Time) :
    Reichenbach.ReichenbachFrame Time where
  speechTime := ctx.speechTime
  perspectiveTime := ctx.speechTime  -- root clause default: P = S
  referenceTime := R
  eventTime := E

end UtteranceContext

/-- Extract an `UtteranceContext` from a `ReichenbachFrame` by
    retaining only the speech time. -/
def Reichenbach.ReichenbachFrame.utteranceContext {Time : Type*}
    (f : Reichenbach.ReichenbachFrame Time) : UtteranceContext Time :=
  { speechTime := f.speechTime }

end Core
