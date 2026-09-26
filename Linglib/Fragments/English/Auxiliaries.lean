module

public import Linglib.Data.UD.UPOS
public import Linglib.Data.UD.Features
public import Linglib.Syntax.Category.Auxiliary.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic
public import Linglib.Syntax.Person.Category
public import Linglib.Semantics.Modality.Basic
public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Morphology.Word.Basic

/-!
# English auxiliaries

This file defines the English auxiliaries as `Auxiliary` entries: the modals *can*, *could*,
*will*, *would*, *shall*, *should*, *may*, *might* and *must*, the periphrastic *have to* and
the semi-modals *dare*, *need* and *ought*, each with its force–flavor meanings and register,
and the agreeing finite forms of do-support, *be* and *have*. The contracted negatives *can't*,
*won't* and the rest are entries in their own right carrying negative polarity, paired with
their bases in `contractions`; *mayn't* and *amn't* are the gaps of Zwicky and Pullum's table.
The infinitival marker *to* is also here, apart from the preposition.

## References

* [kratzer-1981]
* [palmer-2001]
* [zwicky-pullum-1983], Table 1
* [imel-guo-steinert-threlkeld-2026]
-/

@[expose] public section

open Morphology (Word Features)

namespace English.Auxiliaries


section Modals
open Modality (ForceFlavor ModalForce ModalFlavor)

/-- Agreement features of a finite auxiliary. "Past" modals (*could*,
*would*) carry `Past` as a morphological feature even where they are
semantically non-past. -/
def agr (person : Option Person := none) (number : Option Number := none)
    (tense : Option UD.Tense := none) : Features :=
  Features.of (verbForm := some .Fin) (person := person) (number := number) (tense := tense)

/-- The contracted negative of an auxiliary is the same entry with the contracted form and
negative polarity. -/
def contract (a : Auxiliary) (form : String) : Auxiliary :=
  { a with form := form, features := Bundle.set .polarity .Neg a.features }

/-! ### Modals -/

/-- *can*. -/
def can : Auxiliary where
  form := "can"
  modality := {.possibility} ×ˢ {.epistemic, .deontic, .circumstantial}
/-- *could*. -/
def could : Auxiliary where
  form := "could"
  features := agr (tense := some .Past)
  modality := {.possibility} ×ˢ {.epistemic, .deontic, .circumstantial}
/-- *will*. -/
def will : Auxiliary where
  form := "will"
  modality := {.necessity} ×ˢ {.epistemic, .circumstantial}
/-- *would*. -/
def would : Auxiliary where
  form := "would"
  features := agr (tense := some .Past)
  modality := {.necessity} ×ˢ {.epistemic, .circumstantial}
/-- *shall*. -/
def shall : Auxiliary where
  form := "shall"
  register := .formal
  modality := {.necessity} ×ˢ {.deontic}
/-- *should*. -/
def should : Auxiliary where
  form := "should"
  features := agr (tense := some .Past)
  modality := {.weakNecessity} ×ˢ {.deontic, .epistemic}
/-- *may*. -/
def may : Auxiliary where
  form := "may"
  modality := {.possibility} ×ˢ {.epistemic, .deontic}
/-- *might*. -/
def might : Auxiliary where
  form := "might"
  features := agr (tense := some .Past)
  modality := {.possibility} ×ˢ {.epistemic}
/-- *must*. -/
def must : Auxiliary where
  form := "must"
  register := .formal
  modality := {.necessity} ×ˢ {.epistemic, .deontic, .circumstantial}

/-! ### Semi-modals and periphrastic modals -/

/-- *have to*, the periphrastic deontic and circumstantial necessity, an informal variant of
*must*, which inflects unlike the modals, *has to*, *had to*, *having to*. -/
def haveTo : Auxiliary where
  form := "have to"
  register := .informal
  modality := {.necessity} ×ˢ {.deontic, .circumstantial}

/-- *dare*. -/
def dare : Auxiliary where
  form := "dare"
/-- *need*. -/
def need : Auxiliary where
  form := "need"
  modality := {.necessity} ×ˢ {.deontic, .circumstantial}
/-- *ought*. -/
def ought : Auxiliary where
  form := "ought"
  modality := {.weakNecessity} ×ˢ {.deontic, .epistemic}

/-! ### Do-support -/

/-- *do*. -/
def do_ : Auxiliary where
  form := "do"
  features := agr (number := some .plural)
/-- *does*. -/
def does : Auxiliary where
  form := "does"
  features := agr (person := some .third) (number := some .singular)
/-- *did*. -/
def did : Auxiliary where
  form := "did"
  features := agr (tense := some .Past)

/-! ### *Be* -/

/-- *am*. -/
def am : Auxiliary where
  form := "am"
  features := agr (person := some .first) (number := some .singular)
/-- *is*. -/
def is_ : Auxiliary where
  form := "is"
  features := agr (person := some .third) (number := some .singular)
/-- *are*. -/
def are : Auxiliary where
  form := "are"
  features := agr (number := some .plural)
/-- *was*. -/
def was : Auxiliary where
  form := "was"
  features := agr (number := some .singular) (tense := some .Past)
/-- *were*. -/
def were : Auxiliary where
  form := "were"
  features := agr (number := some .plural) (tense := some .Past)

/-! ### *Have* -/

/-- *have*. -/
def have_ : Auxiliary where
  form := "have"
  features := agr (number := some .plural)
/-- *has*. -/
def has : Auxiliary where
  form := "has"
  features := agr (person := some .third) (number := some .singular)
/-- *had*. -/
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

/-- The auxiliaries. -/
def allAuxiliaries : List Auxiliary := modals ++ doForms ++ beForms ++ haveForms

/-! ### Contracted negatives

The *-n't* forms ([zwicky-pullum-1983] Table 1). *mayn't* and *amn't* are
paradigm gaps and have no entry. -/

/-- *can't*. -/
def cant : Auxiliary := contract can "can't"
/-- *couldn't*. -/
def couldnt : Auxiliary := contract could "couldn't"
/-- *won't*. -/
def wont : Auxiliary := contract will "won't"
/-- *wouldn't*. -/
def wouldnt : Auxiliary := contract would "wouldn't"
/-- *shan't*. -/
def shant : Auxiliary := contract shall "shan't"
/-- *shouldn't*. -/
def shouldnt : Auxiliary := contract should "shouldn't"
/-- *mightn't*. -/
def mightnt : Auxiliary := contract might "mightn't"
/-- *mustn't*. -/
def mustnt : Auxiliary := contract must "mustn't"
/-- *daren't*. -/
def darent : Auxiliary := contract dare "daren't"
/-- *needn't*. -/
def neednt : Auxiliary := contract need "needn't"
/-- *oughtn't*. -/
def oughtnt : Auxiliary := contract ought "oughtn't"
/-- *don't*. -/
def dont : Auxiliary := contract do_ "don't"
/-- *doesn't*. -/
def doesnt : Auxiliary := contract does "doesn't"
/-- *didn't*. -/
def didnt : Auxiliary := contract did "didn't"
/-- *isn't*. -/
def isnt : Auxiliary := contract is_ "isn't"
/-- *aren't*. -/
def arent : Auxiliary := contract are "aren't"
/-- *wasn't*. -/
def wasnt : Auxiliary := contract was "wasn't"
/-- *weren't*. -/
def werent : Auxiliary := contract were "weren't"
/-- *haven't*. -/
def havent : Auxiliary := contract have_ "haven't"
/-- *hasn't*. -/
def hasnt : Auxiliary := contract has "hasn't"
/-- *hadn't*. -/
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
