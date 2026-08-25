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
# English Auxiliaries Lexicon Fragment

Lexical entries for English auxiliary verbs — the modal hub of the
English Fragment. Three integrated sub-inventories:

- **Modals**: `can`, `could`, `will`, `would`, `shall`, `should`,
  `may`, `might`, `must`; periphrastic `haveTo`; semi-modals `dare`,
  `need`, `ought`. Morphology + force-flavor classification + register
  + contracted-negative form + Zeijlstra-style modal feature
  interpretability.
- **Do-support / Be / Have**: `do_`/`does`/`did`, `am`/`is_`/`are`/
  `was`/`were`, `have_`/`has`/`had`. Carry person/number/tense
  agreement.
- **Modal adverbs**: `certainly`, `definitely`, `necessarily`,
  `possibly`, `perhaps`, `maybe`, `probably`, `potentially`. Adverbial
  expressions of modal force/flavor (used with auxiliaries in modal
  concord constructions).

Also includes the infinitival marker `toInf` (PART) — distinct from
the preposition *to* (ADP).

## Studies that bind to these entries

This file is a hub: studies analysing English auxiliaries import
specific entries from here and contribute precondition theorems that
break if the morphological classification changes. Consumers (as of
the last audit):

- Modality: `Studies/{Ferreira2023, Rubinstein2014,
  CarianiSantorio2018, AghaJeretic2022, AghaJeretic2026,
  CiardelliGuerrini2026, ImelGuoST2026, LiuRotter2025,
  RotterLiu2025, YingEtAl2025}`
- Auxiliary diagnostics: `Studies/ZwickyPullum1983`
- Argument structure / control: `Studies/
  Osborne2019`, `Studies/Osborne2019Control`
- Reference: `Studies/Percus2000` (via modal-adverb
  side, indirectly)

To find every claim made about a particular entry, grep for
`English.Auxiliaries.<entry>` across the library.
-/


namespace English.Auxiliaries


section Modals
open Modality (ForceFlavor ModalForce ModalFlavor ModalInterpretability ModalFeature)
open Features.Register (Level)

/-- Auxiliary type -/
inductive AuxType where
  | modal      -- can, will, must, should, etc.
  | doSupport  -- do, does, did
  | be         -- am, is, are, was, were
  | have       -- have, has, had
  deriving DecidableEq, Repr

/-- Agreement features of a finite auxiliary. "Past" modals (*could*,
*would*) carry `Past` as a morphological feature even where they are
semantically non-past. -/
private def agr (person : Option UD.Person := none)
    (number : Option UD.Number := none) (tense : Option UD.Tense := none) :
    UD.MorphFeatures :=
  { verbForm := some .Fin, person := person, number := number, tense := tense }

/-- The *-n't* contracted negative of an auxiliary. `irregular` records
phonological irregularity ([zwicky-pullum-1983] criterion C): *won't* is
[woʊnt] rather than what suffixing *will* would give, and *don't* is [doʊnt]
even though its spelling is regular. -/
structure NegContraction where
  form : String
  irregular : Bool := false
  deriving Repr, BEq

/-- The modal content of an auxiliary: its meanings in the force-flavor space
([imel-guo-steinert-threlkeld-2026]) and the interpretability of its modal
feature ([zeijlstra-2007]). Modal auxiliaries carry **uninterpretable**
[u∃/∀-MOD]: they are semantically vacuous and checked by a c-commanding
interpretable operator, which is how [ciardelli-guerrini-2026] derive
narrow-scope LFs for *may A or may B* — both *may*s carry [u∃-MOD], checked by
one silent [i∃-MOD]. -/
structure ModalContent where
  meaning : List ForceFlavor := []
  interpretability : Option ModalInterpretability := none
  deriving Repr, BEq

/-- An English auxiliary: the `AUX` word it spells out, its type, and the
modal and negative-contraction content that only some auxiliaries have.
Non-modals carry no `modal`, and the auxiliaries with a paradigm gap
(*mayn't*, *amn't*) carry no `negContraction`. -/
structure Auxiliary where
  form : String
  /-- Agreement and verb-form features; every auxiliary is finite. -/
  features : UD.MorphFeatures := agr
  auxType : AuxType
  /-- Formal (*must*, *shall*) vs informal (*have to*) vs unmarked. -/
  register : Level := .neutral
  modal : Option ModalContent := none
  negContraction : Option NegContraction := none
  deriving Repr, BEq

namespace Auxiliary

/-- Morphological tense; `none` for the base forms (*can*, *will*). -/
def tense (a : Auxiliary) : Option UD.Tense := a.features.tense

/-- Agreement person. -/
def person (a : Auxiliary) : Option UD.Person := a.features.person

/-- Agreement number. -/
def number (a : Auxiliary) : Option UD.Number := a.features.number

/-- The force-flavor meanings; empty for the non-modal auxiliaries. -/
def modalMeaning (a : Auxiliary) : List ForceFlavor := (a.modal.map (·.meaning)).getD []

/-- The contracted negative form, absent for the paradigm gaps *mayn't* and
*amn't*. -/
def negForm (a : Auxiliary) : Option String := a.negContraction.map (·.form)

/-- Whether the contracted negative is phonologically irregular. -/
def negIrregular (a : Auxiliary) : Bool := (a.negContraction.map (·.irregular)).getD false

/-- The interpretability of the modal feature, if the auxiliary has one. -/
def interpretability (a : Auxiliary) : Option ModalInterpretability :=
  a.modal.bind (·.interpretability)

end Auxiliary

/-- An auxiliary bears its agreement number (`HasNumber`). -/
instance : HasNumber Auxiliary :=
  ⟨fun a => a.features.number.bind Number.fromUD⟩

instance : HasPerson Auxiliary :=
  ⟨fun a => a.features.person.map Person.fromUD⟩

-- Modals (no agreement). Modal meanings follow [kratzer-1981], [palmer-2001].
-- Each uses cartesianProduct with singleton force (fixed force, variable flavor).
private abbrev cp := ForceFlavor.cartesianProduct

-- Modals. Negative forms from [zwicky-pullum-1983], Table 1.
def can : Auxiliary where
  form := "can"
  auxType := .modal
  modal := some { meaning := cp [.possibility] [.epistemic, .deontic, .circumstantial], interpretability := some .uninterpretable }
  negContraction := some { form := "can't", irregular := true }
def could : Auxiliary where
  form := "could"
  features := agr (tense := some .Past)
  auxType := .modal
  modal := some { meaning := cp [.possibility] [.epistemic, .deontic, .circumstantial], interpretability := some .uninterpretable }
  negContraction := some { form := "couldn't" }
def will : Auxiliary where
  form := "will"
  auxType := .modal
  modal := some { meaning := cp [.necessity] [.epistemic, .circumstantial], interpretability := some .uninterpretable }
  negContraction := some { form := "won't", irregular := true }
def would : Auxiliary where
  form := "would"
  features := agr (tense := some .Past)
  auxType := .modal
  modal := some { meaning := cp [.necessity] [.epistemic, .circumstantial], interpretability := some .uninterpretable }
  negContraction := some { form := "wouldn't" }
def shall : Auxiliary where
  form := "shall"
  auxType := .modal
  register := .formal
  modal := some { meaning := cp [.necessity] [.deontic], interpretability := some .uninterpretable }
  negContraction := some { form := "shan't", irregular := true }
def should : Auxiliary where
  form := "should"
  features := agr (tense := some .Past)
  auxType := .modal
  modal := some { meaning := cp [.weakNecessity] [.deontic, .epistemic], interpretability := some .uninterpretable }
  negContraction := some { form := "shouldn't" }
def may : Auxiliary where
  form := "may"
  auxType := .modal
  modal := some { meaning := cp [.possibility] [.epistemic, .deontic], interpretability := some .uninterpretable }
def might : Auxiliary where
  form := "might"
  features := agr (tense := some .Past)
  auxType := .modal
  modal := some { meaning := cp [.possibility] [.epistemic], interpretability := some .uninterpretable }
  negContraction := some { form := "mightn't" }
def must : Auxiliary where
  form := "must"
  auxType := .modal
  register := .formal
  modal := some { meaning := cp [.necessity] [.epistemic, .deontic, .circumstantial], interpretability := some .uninterpretable }
  negContraction := some { form := "mustn't", irregular := true }

-- Semi-modals and periphrastic modals

/-- *Have to*: periphrastic deontic/circumstantial necessity.
    Informal register variant of *must*.
    Inflects unlike true modals: *has to*, *had to*, *having to*. -/
def haveTo : Auxiliary where
  form := "have to"
  auxType := .modal
  register := .informal
  modal := some { meaning := cp [.necessity] [.deontic, .circumstantial], interpretability := some .uninterpretable }

-- Semi-modals (Z&P Table 1 rows o–q)
def dare : Auxiliary where
  form := "dare"
  auxType := .modal
  modal := some { interpretability := some .uninterpretable }
  negContraction := some { form := "daren't" }
def need : Auxiliary where
  form := "need"
  auxType := .modal
  modal := some { meaning := cp [.necessity] [.deontic, .circumstantial], interpretability := some .uninterpretable }
  negContraction := some { form := "needn't" }
def ought : Auxiliary where
  form := "ought"
  auxType := .modal
  modal := some { meaning := cp [.weakNecessity] [.deontic, .epistemic], interpretability := some .uninterpretable }
  negContraction := some { form := "oughtn't" }

-- Do-support
def do_ : Auxiliary where
  form := "do"
  features := agr (number := some .Plur)
  auxType := .doSupport
  negContraction := some { form := "don't", irregular := true }
def does : Auxiliary where
  form := "does"
  features := agr (person := some .third) (number := some .Sing)
  auxType := .doSupport
  negContraction := some { form := "doesn't" }
def did : Auxiliary where
  form := "did"
  features := agr (tense := some .Past)
  auxType := .doSupport
  negContraction := some { form := "didn't" }

-- Be
def am : Auxiliary where
  form := "am"
  features := agr (person := some .first) (number := some .Sing)
  auxType := .be
def is_ : Auxiliary where
  form := "is"
  features := agr (person := some .third) (number := some .Sing)
  auxType := .be
  negContraction := some { form := "isn't" }
def are : Auxiliary where
  form := "are"
  features := agr (number := some .Plur)
  auxType := .be
  negContraction := some { form := "aren't" }
def was : Auxiliary where
  form := "was"
  features := agr (number := some .Sing) (tense := some .Past)
  auxType := .be
  negContraction := some { form := "wasn't" }
def were : Auxiliary where
  form := "were"
  features := agr (number := some .Plur) (tense := some .Past)
  auxType := .be
  negContraction := some { form := "weren't" }

-- Have
def have_ : Auxiliary where
  form := "have"
  features := agr (number := some .Plur)
  auxType := .have
  negContraction := some { form := "haven't" }
def has : Auxiliary where
  form := "has"
  features := agr (person := some .third) (number := some .Sing)
  auxType := .have
  negContraction := some { form := "hasn't" }
def had : Auxiliary where
  form := "had"
  features := agr (tense := some .Past)
  auxType := .have
  negContraction := some { form := "hadn't" }

def allAuxiliaries : List Auxiliary := [
  can, could, will, would, shall, should, may, might, must,
  haveTo, dare, need, ought,
  do_, does, did,
  am, is_, are, was, were,
  have_, has, had
]

/-- The UD `AUX` word an auxiliary spells out. The category is fixed here
rather than stored, so the `_root_.Auxiliary` interface cannot disagree with
it. -/
def Auxiliary.toWord (a : Auxiliary) : Word :=
  { form := a.form, cat := .AUX, features := a.features }

instance : _root_.Auxiliary Auxiliary := ⟨Auxiliary.toWord, fun _ => rfl⟩

/-- Project to the shared modal item core (form + meaning + register). -/
def Auxiliary.toModalItem (a : Auxiliary) : Modality.ModalItem where
  form := a.form
  meaning := a.modalMeaning
  register := a.register

/-- The modal feature (force × interpretability) for the primary force value;
`none` for an auxiliary with no modal content. -/
def Auxiliary.toModalFeature (a : Auxiliary) : Option ModalFeature :=
  match a.interpretability, a.modalMeaning with
  | some interp, ff :: _ => some ⟨ff.force, interp⟩
  | _, _ => none

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
