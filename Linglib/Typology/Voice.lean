/-!
# Voice Typology: Argument Realization and Suppression
[kemmer-1993] [kemmer-1994] [beavers-udayana-2022]

Cross-linguistic substrate for voice alternations — the family of
constructions (active / passive / antipassive / middle / reflexive /
anticausative) that systematically vary which argument surfaces as
subject and how event participants map to surface arguments.

The umbrella framing follows [kemmer-1993]'s monograph *The Middle
Voice*, which establishes middles as a coherent voice category
distinct from passive/reflexive while sharing surface affinities with
both. This file specifically formalizes Beavers-Udayana 2022's 2×2
middle-construction typology along two orthogonal dimensions:

1. **Suppressed variable interpretation**: whether a suppressed
   argument is interpreted as coreferent with the surface subject
   (reflexive) or disjoint (dispositional/passive).

2. **Object realization**: whether the internal argument is realized
   as a full DP (functional application) or an incorporated NP
   (head-adjunction to V).

Both dimensions generalize beyond middles proper — `ObjectRealization`
covers noun-incorporation typology (cf. Mithun 1984) and
`SuppressedVarReading` covers reflexive/anticausative readings broadly.

WALS-side neighbors: `Typology.ArgumentStructure` covers WALS chs
105--111 (ditransitives, reciprocals, passives, antipassives,
applicatives, causatives); voice alternations specifically are at
ch 107 (`PassivePresence`) and ch 106 (`ReciprocalType`).
-/

namespace Typology.Voice

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
    `PivotTarget` ([beavers-udayana-2022], (32d)). -/
def MiddleType.agentSurfaces (m : MiddleType) : Prop :=
  m.objRealization = .incorporation

instance : DecidablePred MiddleType.agentSurfaces :=
  fun m => decEq m.objRealization .incorporation

end Typology.Voice
