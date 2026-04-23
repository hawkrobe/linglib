import Linglib.Core.Lexical.Word
import Linglib.Core.Modality.ModalTypes
import Linglib.Features.Register

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

- Word-order / inversion: `Phenomena/WordOrder/Studies/{SagWasowBender2003,
  Adger2003}`, `Theories/Syntax/Minimalism/Inversion.lean`,
  `Theories/Syntax/HPSG/Inversion.lean`
- Modality: `Phenomena/Modality/Studies/{Ferreira2023, Rubinstein2014,
  CarianiSantorio2018, AghaJeretic2022, AghaJeretic2026,
  CiardelliGuerrini2026, ImelGuoST2026, LiuRotter2025,
  RotterLiu2025Concord, YingEtAl2025}`
- Auxiliary diagnostics: `Phenomena/AuxiliaryVerbs/{Diagnostics,
  Typology}`, `Phenomena/Morphology/Studies/ZwickyPullum1983`
- Argument structure / control: `Phenomena/ArgumentStructure/Studies/
  Osborne2019`, `Phenomena/Complementation/Studies/Osborne2019Control`
- Reference: `Phenomena/Reference/Studies/Percus2000` (via modal-adverb
  side, indirectly)

To find every claim made about a particular entry, grep for
`Fragments.English.Auxiliaries.<entry>` across `Phenomena/` and
`Theories/`.
-/

namespace Fragments.English.Auxiliaries

section Modals
open Core.Modality (ForceFlavor ModalForce ModalFlavor ModalInterpretability ModalFeature)
open Features.Register (Level)

/-- Auxiliary type -/
inductive AuxType where
  | modal      -- can, will, must, should, etc.
  | doSupport  -- do, does, did
  | be         -- am, is, are, was, were
  | have       -- have, has, had
  deriving DecidableEq, Repr

structure AuxEntry where
  form : String
  auxType : AuxType
  /-- Person/number agreement -/
  person : Option Person := none
  number : Option Number := none
  /-- Morphological tense. `none` for base forms (modals like *can*, *will*).
      Note: "past" modals (*could*, *would*) carry `Past` as a morphological
      feature even when semantically non-past (counterfactual, polite). -/
  tense : Option UD.Tense := none
  /-- Modal meaning in the force-flavor space (Imel, Guo, & @cite{imel-guo-steinert-threlkeld-2026}).
      Empty for non-modal auxiliaries. -/
  modalMeaning : List ForceFlavor := []
  /-- Register level. Formal items (*must*,
      *shall*) vs informal items (*have to*) vs unmarked (*can*, *will*). -/
  register : Level := .neutral
  /-- Contracted negative form with *-n't*, if it exists. `none` for paradigm gaps (*mayn't*, *amn't*). -/
  negForm : Option String := none
  /-- Phonological irregularity in the negative form (Z&P criterion C).
      `true` when the contracted form cannot be derived by regular *-n't*
      suffixation (e.g., *won't* ← *will*, *can't* ← *can*, *don't* ← *do*). -/
  negIrregular : Bool := false
  /-- Modal feature interpretability (@cite{zeijlstra-2007}).
      Modal auxiliaries carry **uninterpretable** features [u∃/∀-MOD]:
      they are semantically vacuous and checked by a c-commanding
      interpretable operator. Non-modal auxiliaries (do, be, have) carry
      no modal feature (`none`).

      @cite{ciardelli-guerrini-2026} use this to derive narrow-scope
      LFs for "may A or may B" via modal concord: both "may"s carry
      [u∃-MOD], checked by a single silent [i∃-MOD] operator. -/
  interpretability : Option ModalInterpretability := none
  deriving Repr, BEq

-- Modals (no agreement). Modal meanings follow @cite{kratzer-1981}, @cite{palmer-2001}.
-- Each uses cartesianProduct with singleton force (fixed force, variable flavor).
private abbrev cp := ForceFlavor.cartesianProduct

-- Modals. Negative forms from @cite{zwicky-pullum-1983}, Table 1.
def can : AuxEntry where
  form := "can"; auxType := .modal
  modalMeaning := cp [.possibility] [.epistemic, .deontic, .circumstantial]
  negForm := some "can't"; negIrregular := true   -- [kænt] not *[kænənt]
  interpretability := some .uninterpretable
def could : AuxEntry where
  form := "could"; auxType := .modal; tense := some .Past
  modalMeaning := cp [.possibility] [.epistemic, .deontic, .circumstantial]
  negForm := some "couldn't"
  interpretability := some .uninterpretable
def will : AuxEntry where
  form := "will"; auxType := .modal
  modalMeaning := cp [.necessity] [.epistemic, .circumstantial]
  negForm := some "won't"; negIrregular := true    -- [wont] not *[wɪlnt]
  interpretability := some .uninterpretable
def would : AuxEntry where
  form := "would"; auxType := .modal; tense := some .Past
  modalMeaning := cp [.necessity] [.epistemic, .circumstantial]
  negForm := some "wouldn't"
  interpretability := some .uninterpretable
def shall : AuxEntry where
  form := "shall"; auxType := .modal
  modalMeaning := cp [.necessity] [.deontic]
  register := .formal
  negForm := some "shan't"; negIrregular := true   -- [ʃænt] not *[ʃælnt]
  interpretability := some .uninterpretable
def should : AuxEntry where
  form := "should"; auxType := .modal; tense := some .Past
  modalMeaning := cp [.weakNecessity] [.deontic, .epistemic]
  negForm := some "shouldn't"
  interpretability := some .uninterpretable
def may : AuxEntry where
  form := "may"; auxType := .modal
  modalMeaning := cp [.possibility] [.epistemic, .deontic]
  negForm := none                                  -- *mayn't: paradigm gap
  interpretability := some .uninterpretable
def might : AuxEntry where
  form := "might"; auxType := .modal; tense := some .Past
  modalMeaning := cp [.possibility] [.epistemic]
  negForm := some "mightn't"
  interpretability := some .uninterpretable
def must : AuxEntry where
  form := "must"; auxType := .modal
  modalMeaning := cp [.necessity] [.epistemic, .deontic, .circumstantial]
  register := .formal
  negForm := some "mustn't"; negIrregular := true  -- [t] deletion: [mʌsnt]
  interpretability := some .uninterpretable

-- Semi-modals and periphrastic modals

/-- *Have to*: periphrastic deontic/circumstantial necessity.
    Informal register variant of *must*.
    Inflects unlike true modals: *has to*, *had to*, *having to*. -/
def haveTo : AuxEntry where
  form := "have to"; auxType := .modal
  modalMeaning := cp [.necessity] [.deontic, .circumstantial]
  register := .informal
  interpretability := some .uninterpretable

-- Semi-modals (Z&P Table 1 rows o–q)
def dare : AuxEntry where
  form := "dare"; auxType := .modal
  negForm := some "daren't"
  interpretability := some .uninterpretable
def need : AuxEntry where
  form := "need"; auxType := .modal
  modalMeaning := cp [.necessity] [.deontic, .circumstantial]
  negForm := some "needn't"
  interpretability := some .uninterpretable
def ought : AuxEntry where
  form := "ought"; auxType := .modal
  modalMeaning := cp [.weakNecessity] [.deontic, .epistemic]
  negForm := some "oughtn't"
  interpretability := some .uninterpretable

-- Do-support
def do_ : AuxEntry where
  form := "do"; auxType := .doSupport; number := some .pl
  negForm := some "don't"; negIrregular := true    -- [dont] not *[dunt]
def does : AuxEntry where
  form := "does"; auxType := .doSupport; person := some .third; number := some .sg
  negForm := some "doesn't"
def did : AuxEntry where
  form := "did"; auxType := .doSupport; tense := some .Past
  negForm := some "didn't"

-- Be
def am : AuxEntry where
  form := "am"; auxType := .be; person := some .first; number := some .sg
  negForm := none                                  -- *amn't: paradigm gap
def is_ : AuxEntry where
  form := "is"; auxType := .be; person := some .third; number := some .sg
  negForm := some "isn't"
def are : AuxEntry where
  form := "are"; auxType := .be; number := some .pl
  negForm := some "aren't"
def was : AuxEntry where
  form := "was"; auxType := .be; number := some .sg; tense := some .Past
  negForm := some "wasn't"
def were : AuxEntry where
  form := "were"; auxType := .be; number := some .pl; tense := some .Past
  negForm := some "weren't"

-- Have
def have_ : AuxEntry where
  form := "have"; auxType := .have; number := some .pl
  negForm := some "haven't"
def has : AuxEntry where
  form := "has"; auxType := .have; person := some .third; number := some .sg
  negForm := some "hasn't"
def had : AuxEntry where
  form := "had"; auxType := .have; tense := some .Past
  negForm := some "hadn't"

def allAuxiliaries : List AuxEntry := [
  can, could, will, would, shall, should, may, might, must,
  haveTo, dare, need, ought,
  do_, does, did,
  am, is_, are, was, were,
  have_, has, had
]

def AuxEntry.toWord (a : AuxEntry) : Word :=
  { form := a.form
  , cat := .AUX
  , features := {
      finite := true
      , person := a.person
      , number := a.number
    }
  }

/-- Project to the shared modal item core (form + meaning + register). -/
def AuxEntry.toModalItem (a : AuxEntry) : Core.Modality.ModalItem where
  form := a.form
  meaning := a.modalMeaning
  register := a.register

/-- Project to the modal feature (force × interpretability) for the primary
    force value. Returns `none` for non-modal auxiliaries or entries without
    modal meaning. -/
def AuxEntry.toModalFeature (a : AuxEntry) : Option ModalFeature :=
  match a.interpretability, a.modalMeaning with
  | some interp, ff :: _ => some ⟨ff.force, interp⟩
  | _, _ => none

end Modals

-- ============================================================================
-- Modal Adverbs
-- ============================================================================

section ModalAdverbs
open Core.Modality (ForceFlavor ModalForce ModalFlavor)
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
def ModalAdvEntry.toModalItem (a : ModalAdvEntry) : Core.Modality.ModalItem where
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

end Fragments.English.Auxiliaries
