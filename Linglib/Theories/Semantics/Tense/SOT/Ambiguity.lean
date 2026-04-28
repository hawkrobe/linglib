/-!
# Past-tense ambiguity (concept-level)
@cite{ogihara-1996}

The structural commitment that past tense morphology in embedded
contexts is **ambiguous** between a genuine-past reading (temporal
precedence) and a zero-tense reading (bound variable, no independent
temporal content). Originally proposed by @cite{ogihara-1996}; rejected
by @cite{kratzer-1998} (who treats past as never ambiguous, with the
simultaneous reading deriving from deletion at LF) and finessed by
@cite{klecha-2016} (who derives the simultaneous reading from
modal-base × tense composition without past-tense ambiguity).

This file carries the *type-level* commitment (the 2-case enum). The
*paper-attributed* theorems and the Ogihara-vs-Kratzer divergence
claim live in `Phenomena/TenseAspect/Studies/Ogihara1996.lean`.

Mathlib analogue: this is a `Mathlib/Order/SuccPred/Basic.lean`-style
substrate — orders that aren't successor-preorders simply don't import
it; theories that don't share Ogihara's ambiguity thesis simply don't
import this file.
-/

namespace Semantics.Tense.SOT.Ambiguity


/-- Two readings of past morphology in embedded contexts (Ogihara). -/
inductive PastReading where
  /-- Genuine past: temporal precedence (R < eval time). -/
  | genuinePast
  /-- Zero tense: bound variable, no independent temporal content. -/
  | zeroTense
  deriving DecidableEq, Repr

/-- Both readings are available for past-under-past in SOT languages. -/
def pastUnderPastReadings : List PastReading :=
  [.genuinePast, .zeroTense]

/-- Structural distinctness of the two readings. The *theoretical
    significance* of the distinction (i.e., that this is the
    Ogihara-vs-Kratzer divide) is in the Studies file. -/
theorem genuinePast_ne_zeroTense :
    PastReading.genuinePast ≠ PastReading.zeroTense := nofun


end Semantics.Tense.SOT.Ambiguity
