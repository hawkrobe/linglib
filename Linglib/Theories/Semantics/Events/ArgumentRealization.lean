/-!
# Argument Realization and Suppression

General types for describing how arguments are suppressed and realized
in voice alternations. These capture two independent dimensions:

1. **Suppressed variable interpretation**: whether a suppressed argument
   is interpreted as coreferent with the surface subject (reflexive)
   or disjoint (dispositional/passive).

2. **Object realization**: whether the internal argument is realized
   as a full DP (functional application) or an incorporated NP
   (head-adjunction to V).

The cross-product of these two dimensions yields a 2×2 typology of
middle constructions, first articulated for Indonesian *ber-* by
@cite{beavers-udayana-2022} but applicable cross-linguistically.
-/

namespace Semantics.Events.ArgumentRealization

/-- How a suppressed argument variable is interpreted vis-à-vis the
    surface subject. -/
inductive SuppressedVarReading where
  /-- The suppressed variable is interpreted as coreferent with the
      surface subject, yielding a reflexive reading. -/
  | coreferent
  /-- The suppressed variable is interpreted as disjoint from the
      surface subject, yielding a dispositional/passive reading. -/
  | disjoint
  deriving DecidableEq, Repr

/-- How the base object is syntactically realized. -/
inductive ObjectRealization where
  /-- Object = incorporated NP (head-adjoined to V). -/
  | incorporation
  /-- Object = full DP (functional application). -/
  | noIncorporation
  deriving DecidableEq, Repr

/-- A middle type classified by two independent dimensions:
    how the suppressed variable is interpreted and how the object
    is realized. -/
structure MiddleType where
  objRealization : ObjectRealization
  suppressedVar : SuppressedVarReading
  deriving DecidableEq, Repr

/-- Which argument surfaces as subject in a middle construction depends
    on object realization, not on the suppression operation itself.

    - Incorporation: agent surfaces (patient is incorporated)
    - No incorporation: patient surfaces (agent is suppressed)

    This connects the `MiddleType` typology to the voice system's
    `PivotTarget` (@cite{beavers-udayana-2022}, (32d)). -/
def MiddleType.agentSurfaces (m : MiddleType) : Bool :=
  match m.objRealization with
  | .incorporation => true
  | .noIncorporation => false

end Semantics.Events.ArgumentRealization
