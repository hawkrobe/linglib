import Linglib.Semantics.Root.Kinds
import Linglib.Semantics.ArgumentStructure.Valency
import Linglib.Semantics.ArgumentStructure.SalienceClass
import Linglib.Semantics.Composition.Ty

/-!
# Root classification

The coordinates by which a change-of-state verb root is classified when its
lexical entailments are not decomposed into atoms. `ChangeType` is
[dixon-1982]'s split between property-concept states and states that result
from an action, taken up at root level by [beavers-etal-2021]; `PCClass` is
Dixon's semantic classes of property concepts; and `Classification` records
valency, change type, semantic type ([coon-2019] (3)), and transitive-Voice
licensing. `Classification.salienceClass` reads [lucy-1994]'s salience class
off the record and agrees with the signature-level `SalienceClass.ofKinds` on
manner-free signatures.

## Main declarations

* `ChangeType`, `ChangeType.EntailsChange`, `ChangeType.ofKinds`
* `PCClass`
* `Classification`, `Classification.salienceClass`

## References

* [dixon-1982]: Where Have All the Adjectives Gone?
* [beavers-etal-2021]: States and changes of state.
* [coon-2019]: Building verbs in Chuj.
-/

open ArgumentStructure

namespace Semantics.Root

/-! ### Change type -/

/-- The two types of change-of-state root, property-concept roots naming a gradable
property (√flat, √red) and result roots naming the state an event brings about
(√crack, √shatter) ([beavers-etal-2021] §3.1). -/
inductive ChangeType where
  | propertyConcept
  | result
  deriving DecidableEq, Repr

namespace ChangeType

/-- A result root entails a prior change and a property-concept root does not
([beavers-etal-2021] §3.6). -/
def EntailsChange : ChangeType → Prop
  | propertyConcept => False
  | result => True

instance : DecidablePred EntailsChange
  | propertyConcept => isFalse id
  | result => isTrue trivial

/-- The change type of a kind signature, `result` iff the signature carries `result`. -/
def ofKinds (s : Kinds) : ChangeType :=
  if Kind.result ∈ s then result else propertyConcept

end ChangeType

/-- [dixon-1982]'s semantic classes of property concepts ([beavers-etal-2021] (5)). -/
inductive PCClass where
  /-- large, small, long, short, deep, wide, tall. -/
  | dimension
  /-- old. -/
  | age
  /-- bad, good. -/
  | value
  /-- white, black, red, green, blue, brown. -/
  | color
  /-- cold, warm, dry, soft, smooth. -/
  | physicalProperty
  /-- angry, embarrassed. -/
  | humanPropensity
  /-- fast, slow. -/
  | speed
  deriving DecidableEq, Repr

/-! ### The annotation record -/

/-- An annotation of a root by its valency, change type, semantic type, and
transitive-Voice licensing, for fragments that do not decompose the root into atoms. -/
structure Classification where
  /-- The core-argument positions the root introduces, at most the internal argument
  ([coon-2019]; `Valency.IsRootValency`). -/
  valency : Valency
  /-- Whether the root entails prior change. -/
  changeType : ChangeType
  /-- The root's semantic type ([coon-2019] (3)), where annotated. -/
  denotationType : Option Semantics.Composition.Ty := none
  /-- Whether the root combines with the transitive-forming v ~ Voice head that merges an
  agent, the coordinate separating [coon-2019]'s √TV from its unaccusative √ITV (§3.3). -/
  licensesTransitiveVoice : Bool := false
  deriving DecidableEq, Repr

namespace Classification

/-- The salience class the annotation determines, agent-patient for a root licensing
transitive Voice and patient for any other result root ([lucy-1994]; [coon-2019] §3.3).
A property-concept root without transitive Voice is left undetermined, since
`ChangeType` cannot tell a manner root from a stative one. -/
def salienceClass (c : Classification) : Option SalienceClass :=
  if c.licensesTransitiveVoice then some .agentPatient
  else match c.changeType with
    | .result => some .patient
    | .propertyConcept => none

/-- On manner-free signatures the annotation-level classifier agrees with
`SalienceClass.ofKinds`. -/
theorem salienceClass_ofKinds {s : Kinds} (v : Valency) (h : Kind.manner ∉ s) :
    ({ valency := v, changeType := .ofKinds s,
       licensesTransitiveVoice := decide (.internal ∈ v) } :
      Classification).salienceClass = SalienceClass.ofKinds s v := by
  simp only [salienceClass, SalienceClass.ofKinds, ChangeType.ofKinds, IsAgentSalient,
    IsPatientSalient, h, decide_eq_true_eq]
  split_ifs <;> simp_all

end Classification

end Semantics.Root
