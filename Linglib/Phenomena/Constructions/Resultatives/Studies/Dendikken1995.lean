import Linglib.Theories.Syntax.Minimalism.Core.SmallClause
import Linglib.Phenomena.Constructions.Resultatives.Data

/-!
# Resultative — Small Clause Bridge

@cite{dendikken-1995} @cite{goldberg-jackendoff-2004}@cite{dendikken-1995}: resultative constructions instantiate
SC predication with an adjectival or prepositional predicate:

    "They hammered the metal flat" → V [SC DP AP]
    "She kicked the ball into the field" → V [SC DP PP]

The result-state XP (AP or PP) is the SC predicate; the direct object
DP is the SC subject to which the property/path is ascribed.

## Resultative types as SC predicate categories

@cite{goldberg-jackendoff-2004} five-way resultative typology maps
onto SC predicate categories:

| Resultative type | SC pred | Example |
|---|---|---|
| causativeProperty | A | "hammer the metal flat" |
| causativePath | P | "kick the ball into the field" |
| noncausativeProperty | A | "the river froze solid" |
| noncausativePath | P | "the ball rolled into the field" |
| fakeReflexive | A | "She laughed herself silly" |

## Cross-references

- `Phenomena.ArgumentStructure.Studies.HaddicanEtAl2026`: SC family
  geometry; `resultative_sc` defined there has shape
  `node(leaf, node(leaf, leaf))`, same as PVC and DOC.
- `Phenomena.Constructions.ParticleVerbs.Studies.Dendikken1995`:
  path resultatives share SC predicate category P with PVCs.

-/

namespace Phenomena.Constructions.Resultatives.Studies.Dendikken1995

open Minimalism
open Phenomena.Constructions.Resultatives

/-! ## §1. Resultative types → SC predicate categories

Property resultatives have AP predicates; path resultatives have
PP predicates. Both are SC predication structures. -/

/-- Map resultative type to SC predicate category.
    Property resultatives → A (adjective phrase as SC predicate).
    Path resultatives → P (prepositional phrase as SC predicate).
    Fake reflexive → A (reflexive is the SC subject, AP is predicate). -/
def resToSCPred : ResultativeType → SCPredCategory
  | .causativeProperty    => .A
  | .causativePath        => .P
  | .noncausativeProperty => .A
  | .noncausativePath     => .P
  | .fakeReflexive        => .A

/-- Whether a resultative type involves a causative agent. -/
def ResultativeType.hasCausativeAgent : ResultativeType → Bool
  | .causativeProperty    => true
  | .causativePath        => true
  | .noncausativeProperty => false
  | .noncausativePath     => false
  | .fakeReflexive        => true

/-! ## §2. Verification: categorization covers all types -/

/-- All five resultative types map to either A or P. -/
theorem all_types_categorized :
    resToSCPred .causativeProperty = .A ∧
    resToSCPred .causativePath = .P ∧
    resToSCPred .noncausativeProperty = .A ∧
    resToSCPred .noncausativePath = .P ∧
    resToSCPred .fakeReflexive = .A :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Property resultatives all have SC predicate category A. -/
theorem property_resultatives_are_A :
    resToSCPred .causativeProperty = .A ∧
    resToSCPred .noncausativeProperty = .A ∧
    resToSCPred .fakeReflexive = .A :=
  ⟨rfl, rfl, rfl⟩

/-- Path resultatives all have SC predicate category P. -/
theorem path_resultatives_are_P :
    resToSCPred .causativePath = .P ∧
    resToSCPred .noncausativePath = .P :=
  ⟨rfl, rfl⟩

/-- Resultative SC predicates are always A or P. -/
theorem resultative_cats_are_A_or_P (rt : ResultativeType) :
    resToSCPred rt = .A ∨ resToSCPred rt = .P := by
  cases rt <;> simp [resToSCPred]

/-! ## §3. SC construction from resultative data -/

/-- Build a small clause from a resultative datum. -/
def datumToSC (d : ResultativeDatum) (dpId predId : Nat) : SmallClause :=
  { subject := mkLeafPhon .D [] "DP_patient" dpId
    predicate := mkLeafPhon (SCPredCategory.toCat (resToSCPred d.resType))
                            [] "XP_result" predId
    predCat := resToSCPred d.resType }

/-- The SC predicate category is determined by the resultative type. -/
theorem datum_sc_cat_consistent (d : ResultativeDatum) (dpId predId : Nat) :
    (datumToSC d dpId predId).predCat = resToSCPred d.resType := rfl

/-! ## §4. Per-datum SC categorization -/

/-- "She hammered the metal flat" — SC predicate is AP (property). -/
theorem hammer_flat_is_AP :
    resToSCPred hammer_flat.resType = .A := rfl

/-- "She kicked the ball into the field" — SC predicate is PP (path). -/
theorem kick_into_field_is_PP :
    resToSCPred kick_into_field.resType = .P := rfl

/-- "The river froze solid" — noncausative, SC predicate is AP. -/
theorem freeze_solid_is_AP :
    resToSCPred freeze_solid.resType = .A := rfl

/-- "The ball rolled into the field" — noncausative path, SC predicate is PP. -/
theorem roll_into_field_is_PP :
    resToSCPred roll_into_field.resType = .P := rfl

/-- "She laughed herself silly" — fake reflexive, SC predicate is AP. -/
theorem laugh_silly_is_AP :
    resToSCPred laugh_silly.resType = .A := rfl

/-! ## §5. Cross-construction bridge

Path resultatives share SC predicate category P with PVCs (particles).
This follows from den Dikken's thesis: both involve a P head as
the SC predicate. The difference is that in PVCs, the P is a
particle (intransitive), while in path resultatives, the P heads
a full PP (transitive). -/

/-- Path resultatives and PVCs share SC predicate category P. -/
theorem path_res_shares_cat_with_pvc :
    resToSCPred .causativePath = .P ∧
    resToSCPred .noncausativePath = .P :=
  ⟨rfl, rfl⟩

end Phenomena.Constructions.Resultatives.Studies.Dendikken1995
