import Linglib.Data.UD.Basic
import Linglib.Syntax.Category.Auxiliary.Basic
import Linglib.Syntax.Number.Basic
import Linglib.Syntax.Person.Basic
import Linglib.Syntax.Person.Category
import Linglib.Semantics.Modality.Basic
import Linglib.Pragmatics.SocialMeaning.Register
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

The infinitival marker *to* also lives here.

## References

* [kratzer-1981]
* [palmer-2001]
* [zwicky-pullum-1983], Table 1
* [imel-guo-steinert-threlkeld-2026]
-/


namespace English.Auxiliaries


section Modals
open Modality (ForceFlavor ModalForce ModalFlavor)
open SocialMeaning.Register (Level)

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

/-! ### Modals -/

def can : Auxiliary where
  form := "can"
  modality := {.possibility} ×ˢ {.epistemic, .deontic, .circumstantial}
def could : Auxiliary where
  form := "could"
  features := agr (tense := some .Past)
  modality := {.possibility} ×ˢ {.epistemic, .deontic, .circumstantial}
def will : Auxiliary where
  form := "will"
  modality := {.necessity} ×ˢ {.epistemic, .circumstantial}
def would : Auxiliary where
  form := "would"
  features := agr (tense := some .Past)
  modality := {.necessity} ×ˢ {.epistemic, .circumstantial}
def shall : Auxiliary where
  form := "shall"
  register := .formal
  modality := {.necessity} ×ˢ {.deontic}
def should : Auxiliary where
  form := "should"
  features := agr (tense := some .Past)
  modality := {.weakNecessity} ×ˢ {.deontic, .epistemic}
def may : Auxiliary where
  form := "may"
  modality := {.possibility} ×ˢ {.epistemic, .deontic}
def might : Auxiliary where
  form := "might"
  features := agr (tense := some .Past)
  modality := {.possibility} ×ˢ {.epistemic}
def must : Auxiliary where
  form := "must"
  register := .formal
  modality := {.necessity} ×ˢ {.epistemic, .deontic, .circumstantial}

/-! ### Semi-modals and periphrastic modals -/

/-- *Have to*: periphrastic deontic/circumstantial necessity.
    Informal register variant of *must*.
    Inflects unlike true modals: *has to*, *had to*, *having to*. -/
def haveTo : Auxiliary where
  form := "have to"
  register := .informal
  modality := {.necessity} ×ˢ {.deontic, .circumstantial}

def dare : Auxiliary where
  form := "dare"
def need : Auxiliary where
  form := "need"
  modality := {.necessity} ×ˢ {.deontic, .circumstantial}
def ought : Auxiliary where
  form := "ought"
  modality := {.weakNecessity} ×ˢ {.deontic, .epistemic}

/-! ### Do-support -/

def do_ : Auxiliary where
  form := "do"
  features := agr (number := some .Plur)
def does : Auxiliary where
  form := "does"
  features := agr (person := some .third) (number := some .Sing)
def did : Auxiliary where
  form := "did"
  features := agr (tense := some .Past)

/-! ### *Be* -/

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

/-! ### *Have* -/

def have_ : Auxiliary where
  form := "have"
  features := agr (number := some .Plur)
def has : Auxiliary where
  form := "has"
  features := agr (person := some .third) (number := some .Sing)
def had : Auxiliary where
  form := "had"
  features := agr (tense := some .Past)

/-! ### Inventories -/

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

/-- Each auxiliary paired with its contracted negative. -/
def contractions : List (Auxiliary × Auxiliary) :=
  [(can, cant), (could, couldnt), (will, wont), (would, wouldnt), (shall, shant),
    (should, shouldnt), (might, mightnt), (must, mustnt), (dare, darent), (need, neednt),
    (ought, oughtnt), (do_, dont), (does, doesnt), (did, didnt), (is_, isnt), (are, arent),
    (was, wasnt), (were, werent), (have_, havent), (has, hasnt), (had, hadnt)]

/-- The contracted negatives. -/
def negatives : List Auxiliary := contractions.map (·.2)

/-- The contracted negative of an auxiliary, if it has one. -/
def negative (a : Auxiliary) : Option Auxiliary :=
  (contractions.find? (·.1 == a)).map (·.2)

end Modals

/-! ### The infinitival marker -/

/-- The infinitival marker *to*, UD `PART`, distinct from the preposition `English.Adpositions.to_`:
*John managed to sleep*. -/
def toInf : Word := Word.mk' "to" .PART

end English.Auxiliaries
