import Linglib.Data.UD.Basic
import Linglib.Syntax.Category.Auxiliary.Basic
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities
import Linglib.Features.Person.Decomposition
import Linglib.Semantics.Modality.ModalTypes
import Linglib.Features.Register
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# English Auxiliaries

The English auxiliaries as `Auxiliary` entries: the modals *can*, *could*,
*will*, *would*, *shall*, *should*, *may*, *might*, *must*, the periphrastic
*have to* and the semi-modals *dare*, *need*, *ought*, each with its
force–flavor meanings and register; and the agreeing forms of do-support,
*be* and *have*. The contracted negatives (*can't*, *won't*, …) are entries
in their own right, carrying `Polarity=Neg`, paired with their bases in
`contractions`; *mayn't* and *amn't* are paradigm gaps.

The modal adverbs (*certainly*, *possibly*, …) and the infinitival marker
*to* also live here, since they enter the same modal-concord and
control constructions.

## References

* [kratzer-1981]
* [palmer-2001]
* [zwicky-pullum-1983], Table 1
* [imel-guo-steinert-threlkeld-2026]
-/


namespace English.Auxiliaries


section Modals
open Modality (ForceFlavor ModalForce ModalFlavor ModalInterpretability ModalFeature)
open Features.Register (Level)

/-- Agreement features of a finite auxiliary. "Past" modals (*could*,
*would*) carry `Past` as a morphological feature even where they are
semantically non-past. -/
private def agr (person : Option UD.Person := none)
    (number : Option UD.Number := none) (tense : Option UD.Tense := none) :
    UD.MorphFeatures :=
  { verbForm := some .Fin, person := person, number := number, tense := tense }

/-- The contracted negative of an auxiliary: the same entry with the
contracted form and `Polarity=Neg`. -/
private def contract (a : Auxiliary) (form : String) : Auxiliary :=
  { a with form := form, features := { a.features with polarity := some .Neg } }

private abbrev cp := ForceFlavor.cartesianProduct

-- Modals. Negative forms from [zwicky-pullum-1983], Table 1.
def can : Auxiliary where
  form := "can"
  modality := cp [.possibility] [.epistemic, .deontic, .circumstantial]
def could : Auxiliary where
  form := "could"
  features := agr (tense := some .Past)
  modality := cp [.possibility] [.epistemic, .deontic, .circumstantial]
def will : Auxiliary where
  form := "will"
  modality := cp [.necessity] [.epistemic, .circumstantial]
def would : Auxiliary where
  form := "would"
  features := agr (tense := some .Past)
  modality := cp [.necessity] [.epistemic, .circumstantial]
def shall : Auxiliary where
  form := "shall"
  register := .formal
  modality := cp [.necessity] [.deontic]
def should : Auxiliary where
  form := "should"
  features := agr (tense := some .Past)
  modality := cp [.weakNecessity] [.deontic, .epistemic]
def may : Auxiliary where
  form := "may"
  modality := cp [.possibility] [.epistemic, .deontic]
def might : Auxiliary where
  form := "might"
  features := agr (tense := some .Past)
  modality := cp [.possibility] [.epistemic]
def must : Auxiliary where
  form := "must"
  register := .formal
  modality := cp [.necessity] [.epistemic, .deontic, .circumstantial]

-- Semi-modals and periphrastic modals

/-- *Have to*: periphrastic deontic/circumstantial necessity.
    Informal register variant of *must*.
    Inflects unlike true modals: *has to*, *had to*, *having to*. -/
def haveTo : Auxiliary where
  form := "have to"
  register := .informal
  modality := cp [.necessity] [.deontic, .circumstantial]

-- Semi-modals (Z&P Table 1 rows o–q)
def dare : Auxiliary where
  form := "dare"
def need : Auxiliary where
  form := "need"
  modality := cp [.necessity] [.deontic, .circumstantial]
def ought : Auxiliary where
  form := "ought"
  modality := cp [.weakNecessity] [.deontic, .epistemic]

-- Do-support
def do_ : Auxiliary where
  form := "do"
  features := agr (number := some .Plur)
def does : Auxiliary where
  form := "does"
  features := agr (person := some .third) (number := some .Sing)
def did : Auxiliary where
  form := "did"
  features := agr (tense := some .Past)

-- Be
def am : Auxiliary where
  form := "am"
  features := agr (person := some .first) (number := some .Sing)
def is_ : Auxiliary where
  form := "is"
  features := agr (person := some .third) (number := some .Sing)
def are : Auxiliary where
  form := "are"
  features := agr (number := some .Plur)
def was : Auxiliary where
  form := "was"
  features := agr (number := some .Sing) (tense := some .Past)
def were : Auxiliary where
  form := "were"
  features := agr (number := some .Plur) (tense := some .Past)

-- Have
def have_ : Auxiliary where
  form := "have"
  features := agr (number := some .Plur)
def has : Auxiliary where
  form := "has"
  features := agr (person := some .third) (number := some .Sing)
def had : Auxiliary where
  form := "had"
  features := agr (tense := some .Past)

/-- The modal auxiliaries. -/
def modals : List Auxiliary :=
  [can, could, will, would, shall, should, may, might, must, haveTo, dare, need, ought]

/-- The forms of do-support. -/
def doForms : List Auxiliary := [do_, does, did]

/-- The finite forms of *be*. -/
def beForms : List Auxiliary := [am, is_, are, was, were]

/-- The finite forms of *have*. -/
def haveForms : List Auxiliary := [have_, has, had]

def allAuxiliaries : List Auxiliary := modals ++ doForms ++ beForms ++ haveForms

/-! ### Contracted negatives

The *-n't* forms ([zwicky-pullum-1983] Table 1). *mayn't* and *amn't* are
paradigm gaps and have no entry. -/

def cant : Auxiliary := contract can "can't"
def couldnt : Auxiliary := contract could "couldn't"
def wont : Auxiliary := contract will "won't"
def wouldnt : Auxiliary := contract would "wouldn't"
def shant : Auxiliary := contract shall "shan't"
def shouldnt : Auxiliary := contract should "shouldn't"
def mightnt : Auxiliary := contract might "mightn't"
def mustnt : Auxiliary := contract must "mustn't"
def darent : Auxiliary := contract dare "daren't"
def neednt : Auxiliary := contract need "needn't"
def oughtnt : Auxiliary := contract ought "oughtn't"
def dont : Auxiliary := contract do_ "don't"
def doesnt : Auxiliary := contract does "doesn't"
def didnt : Auxiliary := contract did "didn't"
def isnt : Auxiliary := contract is_ "isn't"
def arent : Auxiliary := contract are "aren't"
def wasnt : Auxiliary := contract was "wasn't"
def werent : Auxiliary := contract were "weren't"
def havent : Auxiliary := contract have_ "haven't"
def hasnt : Auxiliary := contract has "hasn't"
def hadnt : Auxiliary := contract had "hadn't"

/-- The contracted negatives. -/
def negatives : List Auxiliary := [cant, couldnt, wont, wouldnt, shant, shouldnt, mightnt, mustnt, darent, neednt, oughtnt, dont, doesnt, didnt, isnt, arent, wasnt, werent, havent, hasnt, hadnt]

/-- Each auxiliary paired with its contracted negative. -/
def contractions : List (Auxiliary × Auxiliary) :=
  [(can, cant), (could, couldnt), (will, wont), (would, wouldnt), (shall, shant), (should, shouldnt), (might, mightnt), (must, mustnt), (dare, darent), (need, neednt), (ought, oughtnt), (do_, dont), (does, doesnt), (did, didnt), (is_, isnt), (are, arent), (was, wasnt), (were, werent), (have_, havent), (has, hasnt), (had, hadnt)]

/-- The contracted negative of an auxiliary, if it has one. -/
def negative (a : Auxiliary) : Option Auxiliary :=
  (contractions.find? (·.1 == a)).map (·.2)

end Modals

-- ============================================================================
-- Modal Adverbs
-- ============================================================================

section ModalAdverbs
open Modality (ForceFlavor ModalForce ModalFlavor)
open Features.Register (Level)

/-- Modal adverb entry: an adverb expressing modal force and flavor
    without auxiliary morphology.

    Modal adverbs participate in concord constructions where two modal
    expressions yield a single-modality reading. -/
structure ModalAdvEntry where
  form : String
  /-- Modal meaning in the force-flavor space. -/
  modalMeaning : List ForceFlavor
  /-- Register level. -/
  register : Level := .neutral
  deriving Repr, BEq

def ModalAdvEntry.toWord (a : ModalAdvEntry) : Word :=
  { form := a.form, cat := .ADV, features := {} }

/-- Project to the shared modal item core (form + meaning + register). -/
def ModalAdvEntry.toModalItem (a : ModalAdvEntry) : Modality.ModalItem where
  form := a.form
  meaning := a.modalMeaning
  register := a.register

private abbrev mcp := ForceFlavor.cartesianProduct

def certainly : ModalAdvEntry where
  form := "certainly"
  modalMeaning := mcp [.necessity] [.epistemic]
  register := .formal

def definitely : ModalAdvEntry where
  form := "definitely"
  modalMeaning := mcp [.necessity] [.epistemic, .deontic]

def necessarily : ModalAdvEntry where
  form := "necessarily"
  modalMeaning := mcp [.necessity] [.epistemic, .circumstantial]
  register := .formal

def possibly : ModalAdvEntry where
  form := "possibly"
  modalMeaning := mcp [.possibility] [.epistemic]

def perhaps : ModalAdvEntry where
  form := "perhaps"
  modalMeaning := mcp [.possibility] [.epistemic]
  register := .formal

def maybe : ModalAdvEntry where
  form := "maybe"
  modalMeaning := mcp [.possibility] [.epistemic]
  register := .informal

def probably : ModalAdvEntry where
  form := "probably"
  modalMeaning := mcp [.necessity] [.epistemic]

def potentially : ModalAdvEntry where
  form := "potentially"
  modalMeaning := mcp [.possibility] [.circumstantial]

def allModalAdverbs : List ModalAdvEntry :=
  [certainly, definitely, necessarily, possibly, perhaps, maybe, probably, potentially]

end ModalAdverbs

-- ============================================================================
-- Infinitival Marker
-- ============================================================================

/-- Infinitival marker "to" (UD: PART). Distinct from the preposition "to" (ADP).
    Used in infinitival complements: "John managed to sleep". -/
def toInf : Word := Word.mk' "to" .PART

end English.Auxiliaries
