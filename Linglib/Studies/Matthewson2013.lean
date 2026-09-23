module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Data.Examples.Matthewson2013
public import Linglib.Fragments.Gitksan.Modals
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.Statimcets.Modals
public import Linglib.Fragments.Javanese.Modals
public import Linglib.Studies.Condoravdi2002

/-!
# Matthewson (2013): Gitksan Modals

This file formalizes the description of the Gitksan modal system in [matthewson-2013]. Gitksan
is a mixed system (Fig. 1): every modal is specified for modality type, epistemic or
circumstantial, and modal strength is encoded among the circumstantial modals, *da'akhlxw* and
*anook* for possibility against *sgi* for weak necessity, but not among the epistemic clitics
*ima('a)* and *gat*, which are compatible with necessity and possibility contexts alike
([peterson-2010]). The system fills the empty diagonal of the classification of modal systems
by selectivity for type and for strength (Fig. 2), whose other cells English, St'át'imcets and
Javanese occupy in the fragments. Gitksan has no strong circumstantial necessity modal: the
sneeze case takes the plain future.

Gitksan modals are not inherently future-oriented, against the English analysis of
[condoravdi-2002]: future orientation is supplied by the prospective marker *dim*, necessary
and sufficient for it with the epistemic modals and obligatory with the circumstantial ones,
which the paper's paradigms are checked to show, and every cell of Fig. 4, perspective by
orientation, is attested. The circumstantial possibility modal has no actuality entailment,
its obligatory *dim* keeping it out of the perfective configuration of [hacquard-2006].

## Implementation notes

* The paper is agnostic between [peterson-2010]'s variable-force analysis of *ima('a)* and
  [deal-2011]'s strengthened possibility, the negation diagnostic (30) not separating them;
  the force analysis recorded is Fig. 1's.
* The pure circumstantial and teleological readings of *da'akhlxw* and *sgi* are one
  circumstantial flavour in the library.

## References

* [matthewson-2013]
* [peterson-2010]
* [deal-2011]
* [condoravdi-2002]
* [hacquard-2006]
* [rullmann-matthewson-davis-2008]
-/

@[expose] public section

namespace Matthewson2013

open Modality Data.Examples Gitksan

/-! ### The modal system (Fig. 1) -/

/-- Fig. 1's analyses: the epistemic clitics are variable in force, *da'akhlxw* and *anook*
fixed possibility, and *sgi* fixed weak necessity. -/
def forceAnalysis (m : ModalItem) : ForceAnalysis :=
  if m = imaa ∨ m = gat then .variableForce
  else if m = sgi then .fixed .weakNecessity else .fixed .possibility

theorem forceAnalysis_consistent :
    ∀ m ∈ modals, (forceAnalysis m).Consistent m.meaning := by
  decide

/-- Gitksan has no strong circumstantial necessity modal. -/
theorem no_strong_circumstantial_necessity :
    ∀ m ∈ circumstantialModals, ∀ ff ∈ m.meaning, ff.force ≠ .necessity := by
  decide

/-- (95)–(96): the sneeze case, pure circumstantial strong necessity, takes the plain future
and not *sgi*. -/
theorem sneeze_rows :
    ∀ e ∈ Examples.all, e.feature? "test" = some "sneeze" →
      (e.judgment = .acceptable ↔ e.feature? "modal" ≠ some "sgi") := by
  decide

/-! ### Modal systems (Fig. 2) -/

/-- An inventory selects modality type when each of its modals is epistemic or circumstantial. -/
def TypeSelective (L : List ModalItem) : Prop := ∀ m ∈ L, m.Epistemic ∨ m.Circumstantial

/-- An inventory selects modal strength when none of its modals varies in force. -/
def StrengthSelective (L : List ModalItem) : Prop := ∀ m ∈ L, ¬ m.VariesForce

instance (L : List ModalItem) : Decidable (TypeSelective L) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _ ∨ _))

instance (L : List ModalItem) : Decidable (StrengthSelective L) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ¬ _))

/-- A mixed system selects type throughout and strength among its circumstantial modals only. -/
def Mixed (L : List ModalItem) : Prop :=
  TypeSelective L ∧ StrengthSelective (L.filter (·.Circumstantial)) ∧
    ¬ StrengthSelective (L.filter (·.Epistemic))

instance (L : List ModalItem) : Decidable (Mixed L) := inferInstanceAs (Decidable (_ ∧ _ ∧ ¬ _))

theorem gitksan_mixed : Mixed modals := by decide

/-- Fig. 2 from the fragments: English selects strength and not type, St'át'imcets type and not
strength, and Javanese both ([rullmann-matthewson-davis-2008], Fig. 3). -/
theorem fig2 :
    (StrengthSelective (English.Auxiliaries.modals.map Auxiliary.toModalItem) ∧
        ¬ TypeSelective (English.Auxiliaries.modals.map Auxiliary.toModalItem)) ∧
      (TypeSelective Statimcets.modals ∧
        ¬ StrengthSelective Statimcets.modals) ∧
      TypeSelective Javanese.modals ∧
        StrengthSelective Javanese.modals := by
  decide

/-! ### Modal–temporal interaction (§3.3, §4, Fig. 4) -/

/-- The prospective *dim* is required with a circumstantial modal, and with an epistemic modal
exactly for a future orientation. -/
def RequiresDim (m : ModalItem) (o : TemporalOrientation) : Prop := m.Circumstantial ∨ o = .future

instance (m : ModalItem) (o : TemporalOrientation) : Decidable (RequiresDim m o) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The modal a row names. -/
def modalOf : String → Option ModalItem
  | "ima('a)" => some imaa
  | "gat" => some gat
  | "da'akhlxw" => some daakhlxw
  | "anook(xw)" => some anookxw
  | "sgi" => some sgi
  | _ => none

/-- The orientation a row records. -/
def orientationOf : String → Option TemporalOrientation
  | "past" => some .past
  | "present" => some .present
  | "future" => some .future
  | _ => none

/-- The perspective a row records. -/
def perspectiveOf : String → Option TemporalPerspective
  | "past" => some .past
  | "present" => some .present
  | _ => none

/-- The paradigms (38)–(48), (53), (56), (73) and (83): a modal sentence is accepted exactly
when *dim* is present iff the modal and orientation require it, so *dim* is necessary and
sufficient for future orientation with the epistemic modals and obligatory with the
circumstantial ones. -/
theorem dim_rows :
    ∀ e ∈ Examples.all, ∀ m ∈ (e.feature? "modal").bind modalOf,
      ∀ o ∈ (e.feature? "orientation").bind orientationOf,
        (e.judgment = .acceptable ↔
          (e.feature? "prospective" = some "true" ↔ RequiresDim m o)) := by
  decide

/-- Fig. 4: *ima('a)* is attested at every temporal perspective and orientation. -/
theorem fig4 :
    ∀ p : TemporalPerspective, ∀ o : TemporalOrientation, ∃ e ∈ Examples.all,
      e.feature? "modal" = some "ima('a)" ∧ (e.feature? "perspective").bind perspectiveOf = some p ∧
        (e.feature? "orientation").bind orientationOf = some o ∧ e.judgment = .acceptable := by
  decide

/-- (35) against (39): an unmarked English possibility modal is future-oriented on
[condoravdi-2002]'s analysis, an unmarked Gitksan epistemic never is. -/
theorem unmarked_orientation :
    Condoravdi2002.Scope.modal.orientation = .future ∧ RequiresDim imaa .future := by
  decide

/-- (62): *da'akhlxw* with its *dim* has no actuality entailment, the ability holding while the
event fails. -/
theorem no_actuality_entailment :
    ∀ e ∈ Examples.all, e.feature? "actualityEntailment" = some "false" →
      e.feature? "modal" = some "da'akhlxw" ∧ e.feature? "prospective" = some "true" ∧
        e.judgment = .acceptable := by
  decide

end Matthewson2013
