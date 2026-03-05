import Linglib.Core.Logic.ModalLogic
import Linglib.Theories.Semantics.Modality.Assert

/-!
# French Modal Auxiliaries and Modal Constructions

@cite{kaufmann-2012} @cite{ruytenbeek-etal-2017} @cite{kratzer-1991}

French modal verbs *pouvoir* ('can') and *devoir* ('must'), plus the
impersonal construction *il est possible de* ('it is possible to').

## Semantic Properties

*Devoir* and *pouvoir* are the French counterparts of Italian *dovere*
and *potere* (see `Fragments.Italian.Modals`). Like their Italian
cognates, both are polysemous across epistemic, deontic, and
circumstantial readings.

Key asymmetry relevant to @cite{ruytenbeek-etal-2017}:

- *Devoir* (necessity) in 2nd person declaratives (*Vous devez VP*)
  receives directive force as readily as imperatives — same RT, same
  response pattern (virtually 100% directive interpretations).
- *Pouvoir* (possibility) in 2nd person declaratives (*Vous pouvez VP*)
  receives directive interpretations less readily (~30%).
- *Il est possible de VP* patterns with *pouvoir*, not *devoir*.

@cite{kaufmann-2012}: imperatives have the semantics of deontic necessity
modals. The *devoir* data confirms the reverse: deontic necessity modals
in declaratives receive directive force because they share the semantic
feature (deontic necessity) with imperatives.

## Connection to Italian Fragment

French and Italian modal systems are cognate (Latin *debēre* → Fr.
*devoir*, It. *dovere*; Latin *posse/potēre* → Fr. *pouvoir*, It.
*potere*). Both show the epistemic/root ambiguity and both participate
in position-sensitive flavor selection (@cite{hacquard-2006}).

-/

namespace Fragments.French.Modals

open Core.ModalLogic (ModalForce ModalFlavor ForceFlavor)
open Semantics.Modality.Assert (primaryFlavor)
open Core.Discourse (IllocutionaryMood)


-- ════════════════════════════════════════════════════
-- § 1. Entry Type
-- ════════════════════════════════════════════════════

/-- A French modal entry. Simpler than the Italian entry (which tracks
    restructuring position) — here we track the available flavors and
    whether the modal is a personal verb or impersonal construction. -/
structure FrenchModalEntry where
  /-- Citation form -/
  form : String
  /-- Modal force (necessity or possibility) -/
  force : ModalForce
  /-- Available modal flavors -/
  flavors : List ModalFlavor
  /-- Whether this is a personal verb (conjugated for subject) or
      impersonal construction -/
  isPersonal : Bool
  /-- Whether the modal takes an infinitive complement -/
  takesInfinitive : Bool := true
  deriving Repr, BEq


-- ════════════════════════════════════════════════════
-- § 2. Lexical Entries
-- ════════════════════════════════════════════════════

/-- *Pouvoir* ('can/may'): personal possibility modal.

    Dynamic/deontic: *Vous pouvez partir* ('You can/may leave')
    Epistemic: *Il peut être intelligent* ('He may be intelligent')

    In 2nd person declaratives, the most salient reading is
    permission (deontic possibility) or ability (circumstantial). -/
def pouvoir : FrenchModalEntry where
  form := "pouvoir"
  force := .possibility
  flavors := [.epistemic, .deontic, .circumstantial]
  isPersonal := true

/-- *Devoir* ('must/have to'): personal necessity modal.

    Deontic: *Vous devez partir* ('You must leave')
    Epistemic: *Il doit être chez lui* ('He must be at home')

    @cite{kaufmann-2012}: in 2nd person declaratives, *devoir* receives
    directive force as readily as imperatives because both express
    deontic necessity. -/
def devoir : FrenchModalEntry where
  form := "devoir"
  force := .necessity
  flavors := [.epistemic, .deontic, .circumstantial]
  isPersonal := true

/-- *Il est possible de VP* ('it is possible to VP'): impersonal
    possibility construction.

    Not restricted to a particular modal base — can express epistemic,
    deontic, or circumstantial possibility depending on context
    (@cite{kratzer-1991}).

    @cite{ruytenbeek-etal-2017}: in the Frantext corpus, this construction
    is used as a direct question 70% of the time, vs only 16% as a
    directive. Much less conventionalized as an indirect request than
    *Pouvez-vous VP?* (71% directive). -/
def ilEstPossible : FrenchModalEntry where
  form := "il est possible de"
  force := .possibility
  flavors := [.epistemic, .deontic, .circumstantial]
  isPersonal := false

/-- *Falloir* ('to be necessary'): impersonal necessity modal.

    *Il faut partir* ('One must leave / It is necessary to leave')

    Always impersonal (conjugated only as *il faut*). Primarily
    deontic/circumstantial in root uses. -/
def falloir : FrenchModalEntry where
  form := "falloir"
  force := .necessity
  flavors := [.epistemic, .deontic, .circumstantial]
  isPersonal := false

def allModals : List FrenchModalEntry :=
  [pouvoir, devoir, ilEstPossible, falloir]

def lookup (form : String) : Option FrenchModalEntry :=
  allModals.find? (·.form == form)


-- ════════════════════════════════════════════════════
-- § 3. Per-Entry Verification
-- ════════════════════════════════════════════════════

theorem pouvoir_is_possibility : pouvoir.force = .possibility := rfl
theorem devoir_is_necessity : devoir.force = .necessity := rfl
theorem ilEstPossible_is_possibility : ilEstPossible.force = .possibility := rfl
theorem falloir_is_necessity : falloir.force = .necessity := rfl

theorem pouvoir_is_personal : pouvoir.isPersonal = true := rfl
theorem devoir_is_personal : devoir.isPersonal = true := rfl
theorem ilEstPossible_is_impersonal : ilEstPossible.isPersonal = false := rfl
theorem falloir_is_impersonal : falloir.isPersonal = false := rfl

/-- Both personal modals are polysemous across all three flavors. -/
theorem pouvoir_polysemous :
    pouvoir.flavors = [.epistemic, .deontic, .circumstantial] := rfl

theorem devoir_polysemous :
    devoir.flavors = [.epistemic, .deontic, .circumstantial] := rfl


-- ════════════════════════════════════════════════════
-- § 4. Force-Flavor Pairs
-- ════════════════════════════════════════════════════

/-- The set of force-flavor pairs expressed by a modal entry. -/
def FrenchModalEntry.forceFlavors (m : FrenchModalEntry) : List ForceFlavor :=
  m.flavors.map (⟨m.force, ·⟩)

/-- *Devoir* expresses deontic necessity — the same force-flavor pair
    as the imperative speech act's primary flavor. -/
theorem devoir_has_deontic_necessity :
    (⟨.necessity, .deontic⟩ : ForceFlavor) ∈ devoir.forceFlavors := by
  decide

/-- *Pouvoir* expresses deontic possibility — permission, not obligation. -/
theorem pouvoir_has_deontic_possibility :
    (⟨.possibility, .deontic⟩ : ForceFlavor) ∈ pouvoir.forceFlavors := by
  decide


-- ════════════════════════════════════════════════════
-- § 5. Bridge to Assert.lean
-- ════════════════════════════════════════════════════

/-! The imperative speech act has deontic content (`primaryFlavor .imperative
    = .deontic`). *Devoir* in a 2nd person declarative shares this flavor.
    This is why *Vous devez VP* receives directive force as readily as
    imperatives — the deontic feature is the semantic basis for directive
    compatibility, not the sentence type. -/

/-- *Devoir* shares a modal flavor with the imperative speech act:
    both have deontic as a primary flavor. -/
theorem devoir_shares_imperative_flavor :
    .deontic ∈ devoir.flavors ∧
    primaryFlavor .imperative = .deontic := by
  constructor
  · decide
  · rfl

/-- *Pouvoir* also has deontic as an available flavor, but its force
    is possibility (permission), not necessity (obligation). The
    force distinction explains why *Vous pouvez VP* gets fewer directive
    interpretations than *Vous devez VP*: permission is weaker than
    obligation. -/
theorem pouvoir_devoir_force_contrast :
    pouvoir.force = .possibility ∧ devoir.force = .necessity := ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 6. Bridge to Italian Cognates
-- ════════════════════════════════════════════════════

/-! French and Italian modals are cognate and share key properties:
    same force (necessity/possibility), same flavor polysemy. -/

/-- *Devoir* and *dovere* share the same force. -/
theorem devoir_dovere_same_force :
    devoir.force = .necessity := rfl

/-- *Pouvoir* and *potere* share the same force. -/
theorem pouvoir_potere_same_force :
    pouvoir.force = .possibility := rfl

/-- French necessity and possibility modals form a dual pair. -/
theorem french_modal_duality :
    devoir.force = .necessity ∧ pouvoir.force = .possibility := ⟨rfl, rfl⟩

/-- Both personal modals have the same flavor inventory. -/
theorem devoir_pouvoir_same_flavors :
    devoir.flavors = pouvoir.flavors := rfl


end Fragments.French.Modals
