import Linglib.Syntax.Voice.Basic

/-!
# Voice: middle constructions

[beavers-udayana-2022]

The middle/diathesis axis of the unified `Voice` substrate: the two orthogonal
dimensions of [beavers-udayana-2022]'s Indonesian middle typology — how a
suppressed argument is interpreted, and how the base object is realized. The
2×2 of constructions is the literal product `ObjectRealization × SuppressedVarReading`
(no bundling record). Which argument surfaces as pivot is derived from object
realization via `ObjectRealization.pivot`.
-/

namespace Voice

/-- How a suppressed argument variable is interpreted vis-à-vis the surface
    subject: coreferent (reflexive) or disjoint (dispositional/passive). -/
inductive SuppressedVarReading where
  | coreferent
  | disjoint
  deriving DecidableEq, Repr

/-- How the base object is realized: incorporated NP (head-adjoined to V) or
    full DP (functional application). -/
inductive ObjectRealization where
  | incorporation
  | noIncorporation
  deriving DecidableEq, Repr

/-- The pivot a middle promotes, derived from object realization: incorporation
    leaves the agent surfacing, no-incorporation leaves the patient
    ([beavers-udayana-2022]). -/
def ObjectRealization.pivot : ObjectRealization → PivotTarget
  | .incorporation   => .agent
  | .noIncorporation => .patient

/-- Does the agent surface as subject? (Equivalently, the object is incorporated.) -/
def ObjectRealization.agentSurfaces (o : ObjectRealization) : Prop :=
  o = .incorporation

instance : DecidablePred ObjectRealization.agentSurfaces :=
  fun o => decEq o .incorporation

end Voice
