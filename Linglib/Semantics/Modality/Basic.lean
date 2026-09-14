import Linglib.Pragmatics.SocialMeaning.Register
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Modal force and flavor

This file defines the vocabulary of modal typology. A modal force is a quantificational
strength, necessity, weak necessity or possibility, ordered by strength; a modal flavor is a
source of modality, epistemic, deontic, bouletic or circumstantial ([kratzer-1981]); and a
modal item pairs a form with the force-flavor pairs it can express, the representation of a
modal's meaning in [imel-guo-steinert-threlkeld-2026]. A force analysis records how an item
comes by its force, and the temporal perspective and orientation of [condoravdi-2002] locate a
modal claim in time.

## Main definitions

* `Modality.ModalForce`, with the strength order `possibility < weakNecessity < necessity`,
  the classical dual `ModalForce.dual`, and the concord class `ModalForce.IsUniversal`.
* `Modality.ModalFlavor` and the pair type `Modality.ForceFlavor`.
* `Modality.ModalItem`, with its domain and variation predicates.
* `Modality.ForceAnalysis`: fixed, variable or strengthened force, and its consistency with
  a meaning.
* `Modality.TemporalPerspective`, `Modality.TemporalOrientation`.

## References

* [kratzer-1981]
* [von-fintel-iatridou-2008]
* [rubinstein-2014]
* [agha-jeretic-2022]
* [agha-jeretic-2026]
* [imel-guo-steinert-threlkeld-2026]
* [zeijlstra-2007]
* [matthewson-2013]
* [matthewson-2016]
* [deal-2011]
* [condoravdi-2002]
-/

namespace Modality

/-! ### Modal force -/

/-- A modal force is a quantificational strength. Weak necessity, *ought* and *should*, lies
between necessity and possibility ([von-fintel-iatridou-2008]); whether it quantifies
universally over a narrower domain ([von-fintel-iatridou-2008]), compares alternatives
([rubinstein-2014]) or predicates of a plurality of worlds ([agha-jeretic-2022]) is open
([agha-jeretic-2026]). -/
inductive ModalForce where
  | necessity
  | weakNecessity
  | possibility
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace ModalForce

/-- The strength of a force, possibility the weakest. -/
def rank : ModalForce → ℕ
  | possibility => 0
  | weakNecessity => 1
  | necessity => 2

/-- Forces are ordered by strength: a necessity claim entails the weak necessity claim, which
entails the possibility claim. -/
instance : LinearOrder ModalForce := LinearOrder.lift' rank (by decide)

instance : BoundedOrder ModalForce where
  top := necessity
  le_top := by decide
  bot := possibility
  bot_le := by decide

/-- The classical dual exchanges necessity and possibility. Weak necessity has no settled
possibility counterpart ([agha-jeretic-2026] §2.4) and is sent to possibility. -/
def dual : ModalForce → ModalForce
  | necessity => possibility
  | weakNecessity => possibility
  | possibility => necessity

/-- Necessity and weak necessity quantify universally, the concord class that separates them
from possibility ([zeijlstra-2007]). -/
def IsUniversal (f : ModalForce) : Prop := f ≠ possibility

instance : DecidablePred IsUniversal := λ _ => inferInstanceAs (Decidable (_ ≠ _))

end ModalForce

/-! ### Modal flavor -/

/-- A modal flavor is the source of a modal claim, the four conversational backgrounds of
[kratzer-1981]; teleological modality counts as circumstantial. -/
inductive ModalFlavor where
  | epistemic
  | deontic
  | bouletic
  | circumstantial
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A force-flavor pair is one point of the modal semantic space of
[imel-guo-steinert-threlkeld-2026]. Their database uses two forces and three flavors; weak
necessity ([agha-jeretic-2026]) and bouletic flavor ([kratzer-1981]) extend the space to twelve
points. -/
abbrev ForceFlavor := ModalForce × ModalFlavor

/-- The force of a force-flavor pair. -/
abbrev ForceFlavor.force : ForceFlavor → ModalForce := Prod.fst

/-- The flavor of a force-flavor pair. -/
abbrev ForceFlavor.flavor : ForceFlavor → ModalFlavor := Prod.snd

/-! ### Modal items -/

/-- A modal item is the shared core of an expression carrying modal meaning, which
`Auxiliary.toModalItem` and `ModalAdvEntry.toModalItem` project onto. -/
structure ModalItem where
  form : String
  /-- The force-flavor pairs the item can express. -/
  meaning : Finset ForceFlavor
  register : SocialMeaning.Register.Level := .neutral
  deriving DecidableEq

namespace ModalItem

/-- A modal item is epistemic when every pair it expresses is. -/
def Epistemic (m : ModalItem) : Prop := ∀ ff ∈ m.meaning, ff.flavor = .epistemic

/-- A modal item is circumstantial, in the broad sense covering the priority flavours, when no
pair it expresses is epistemic. -/
def Circumstantial (m : ModalItem) : Prop := ∀ ff ∈ m.meaning, ff.flavor ≠ .epistemic

/-- A modal item varies in force when it expresses two forces. -/
def VariesForce (m : ModalItem) : Prop := 2 ≤ (m.meaning.image Prod.fst).card

/-- A modal item varies in flavour when it expresses two flavours. -/
def VariesFlavor (m : ModalItem) : Prop := 2 ≤ (m.meaning.image Prod.snd).card

instance : DecidablePred Epistemic := λ _ => inferInstanceAs (Decidable (∀ _ ∈ _, _ = _))

instance : DecidablePred Circumstantial := λ _ => inferInstanceAs (Decidable (∀ _ ∈ _, _ ≠ _))

instance : DecidablePred VariesForce := λ _ => inferInstanceAs (Decidable (_ ≤ _))

instance : DecidablePred VariesFlavor := λ _ => inferInstanceAs (Decidable (_ ≤ _))

end ModalItem

/-! ### Force analysis

Three mechanisms give a modal its force, which a set of force-flavor pairs conflates: a fixed
lexical force, as with English *must* and *can*; variable force, compatibility with necessity
and possibility contexts alike without ambiguity, as with Gitksan *ima('a)* and *gat*
([matthewson-2013]); and a fixed base force strengthened pragmatically in the absence of a
contrasting dual, as with Nez Perce *o'qa* ([deal-2011]), a possibility modal read as necessity
because no necessity modal competes with it. -/

/-- How a modal comes by its force. -/
inductive ForceAnalysis where
  | fixed (force : ModalForce)
  | variableForce
  | strengthened (base : ModalForce)
  deriving DecidableEq, Repr

/-- A modal admits a necessity reading, semantically or pragmatically, unless it is fixed for
possibility. -/
def ForceAnalysis.AdmitsNecessity (a : ForceAnalysis) : Prop := a ≠ .fixed .possibility

instance : DecidablePred ForceAnalysis.AdmitsNecessity := λ _ => inferInstanceAs (Decidable (_ ≠ _))

/-- A modal admits a possibility reading when its force is possibility, variable, or
strengthened from possibility. -/
def ForceAnalysis.AdmitsPossibility (a : ForceAnalysis) : Prop :=
  a = .fixed .possibility ∨ a = .variableForce ∨ a = .strengthened .possibility

instance : DecidablePred ForceAnalysis.AdmitsPossibility :=
  λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- A force analysis is consistent with a meaning when the forces the meaning attests are the
one the analysis fixes or strengthens, or two for a variable-force analysis. -/
def ForceAnalysis.Consistent : ForceAnalysis → Finset ForceFlavor → Prop
  | .fixed fo, m | .strengthened fo, m => m.image Prod.fst = {fo}
  | .variableForce, m => 2 ≤ (m.image Prod.fst).card

instance (a : ForceAnalysis) (m : Finset ForceFlavor) : Decidable (a.Consistent m) := by
  cases a <;> unfold ForceAnalysis.Consistent <;> infer_instance

/-! ### Modal-temporal axes

The two temporal axes of modal interpretation ([condoravdi-2002] §2): the perspective is the
time at which the modal base and ordering source are evaluated, the orientation the relation
between the perspective time and the prejacent's time. [condoravdi-2002] uses only the future
and past orientations. -/

/-- The time at which a modal base and ordering source are evaluated. -/
inductive TemporalPerspective where
  /-- Evaluation at the utterance time. -/
  | present
  /-- Evaluation at a prior time, as under a perfect. -/
  | past
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The relation between the perspective time and the prejacent's instantiation time. -/
inductive TemporalOrientation where
  /-- The prejacent is instantiated before the perspective time. -/
  | past
  /-- The prejacent coincides with the perspective time. -/
  | present
  /-- The prejacent is instantiated at or after the perspective time. -/
  | future
  deriving DecidableEq, Repr, Inhabited, Fintype

end Modality
