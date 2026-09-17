/-!
# Middle constructions

The two dimensions of [beavers-udayana-2022]'s Indonesian middle typology: how a
suppressed argument is interpreted, and how the base object is realized. The
2×2 of constructions is the product `ObjectRealization × SuppressedVarReading`,
and which base argument surfaces as subject is read off object realization
(`ObjectRealization.agentSurfaces`).

## References

* [beavers-udayana-2022]
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

/-- The agent surfaces as subject: the object is incorporated, so the agent is the sole DP;
without incorporation the patient surfaces ([beavers-udayana-2022]). -/
def ObjectRealization.agentSurfaces (o : ObjectRealization) : Prop :=
  o = .incorporation

instance : DecidablePred ObjectRealization.agentSurfaces :=
  fun o => decEq o .incorporation

end Voice
