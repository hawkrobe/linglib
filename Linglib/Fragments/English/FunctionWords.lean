/-
# English Function Words Lexicon Fragment

Lexical entries for English closed-class function words:
- Prepositions
- Complementizers
- Auxiliaries
- Conjunctions
-/

import Linglib.Core.Basic
import Linglib.Core.ModalLogic

namespace Fragments.English.FunctionWords

-- ============================================================================
-- Prepositions
-- ============================================================================

structure PrepEntry where
  form : String
  /-- Can introduce an agent in passive? -/
  passiveAgent : Bool := false
  deriving Repr, BEq

def to_ : PrepEntry := { form := "to" }
def on : PrepEntry := { form := "on" }
def in_ : PrepEntry := { form := "in" }
def at_ : PrepEntry := { form := "at" }
def by_ : PrepEntry := { form := "by", passiveAgent := true }
def with_ : PrepEntry := { form := "with" }
def from_ : PrepEntry := { form := "from" }
def before : PrepEntry := { form := "before" }
def after : PrepEntry := { form := "after" }

def allPrepositions : List PrepEntry := [to_, on, in_, at_, by_, with_, from_, before, after]

def PrepEntry.toWord (p : PrepEntry) : Word :=
  { form := p.form, cat := .ADP, features := {} }

-- ============================================================================
-- Complementizers
-- ============================================================================

structure CompEntry where
  form : String
  /-- Introduces a question? -/
  question : Bool := false
  /-- Introduces a conditional? -/
  conditional : Bool := false
  /-- Can be omitted? -/
  optional : Bool := false
  deriving Repr, BEq

def that : CompEntry := { form := "that", optional := true }
def if_ : CompEntry := { form := "if", question := true, conditional := true }
def whether : CompEntry := { form := "whether", question := true }
def because : CompEntry := { form := "because" }
def although : CompEntry := { form := "although" }
def while_ : CompEntry := { form := "while" }

def allComplementizers : List CompEntry := [that, if_, whether, because, although, while_]

def CompEntry.toWord (c : CompEntry) : Word :=
  { form := c.form, cat := .SCONJ, features := {} }

-- ============================================================================
-- Auxiliaries
-- ============================================================================

section Auxiliaries
open Core.ModalLogic (ForceFlavor ModalForce ModalFlavor)

/-- Auxiliary type -/
inductive AuxType where
  | modal      -- can, will, must, should, etc.
  | doSupport  -- do, does, did
  | be         -- am, is, are, was, were
  | have       -- have, has, had
  deriving DecidableEq, Repr, BEq

structure AuxEntry where
  form : String
  auxType : AuxType
  /-- Person/number agreement -/
  person : Option Person := none
  number : Option Number := none
  /-- Tense -/
  past : Bool := false
  /-- Modal meaning in the force-flavor space (Imel, Guo, & Steinert-Threlkeld 2026).
      Empty for non-modal auxiliaries. -/
  modalMeaning : List ForceFlavor := []
  deriving Repr, BEq

-- Modals (no agreement). Modal meanings follow Kratzer (1981), Palmer (2001).
-- Each uses cartesianProduct with singleton force (fixed force, variable flavor).
private abbrev cp := ForceFlavor.cartesianProduct

def can : AuxEntry where
  form := "can"; auxType := .modal
  modalMeaning := cp [.possibility] [.epistemic, .deontic, .circumstantial]
def could : AuxEntry where
  form := "could"; auxType := .modal; past := true
  modalMeaning := cp [.possibility] [.epistemic, .deontic, .circumstantial]
def will : AuxEntry where
  form := "will"; auxType := .modal
  modalMeaning := cp [.necessity] [.epistemic, .circumstantial]
def would : AuxEntry where
  form := "would"; auxType := .modal; past := true
  modalMeaning := cp [.necessity] [.epistemic, .circumstantial]
def shall : AuxEntry where
  form := "shall"; auxType := .modal
  modalMeaning := cp [.necessity] [.deontic]
def should : AuxEntry where
  form := "should"; auxType := .modal; past := true
  modalMeaning := cp [.necessity] [.deontic, .epistemic]
def may : AuxEntry where
  form := "may"; auxType := .modal
  modalMeaning := cp [.possibility] [.epistemic, .deontic]
def might : AuxEntry where
  form := "might"; auxType := .modal; past := true
  modalMeaning := cp [.possibility] [.epistemic]
def must : AuxEntry where
  form := "must"; auxType := .modal
  modalMeaning := cp [.necessity] [.epistemic, .deontic, .circumstantial]

-- Do-support
def do_ : AuxEntry := { form := "do", auxType := .doSupport, number := some .pl }
def does : AuxEntry := { form := "does", auxType := .doSupport, person := some .third, number := some .sg }
def did : AuxEntry := { form := "did", auxType := .doSupport, past := true }

-- Be
def am : AuxEntry := { form := "am", auxType := .be, person := some .first, number := some .sg }
def is : AuxEntry := { form := "is", auxType := .be, person := some .third, number := some .sg }
def are : AuxEntry := { form := "are", auxType := .be, number := some .pl }
def was : AuxEntry := { form := "was", auxType := .be, number := some .sg, past := true }
def were : AuxEntry := { form := "were", auxType := .be, number := some .pl, past := true }

-- Have
def have_ : AuxEntry := { form := "have", auxType := .have, number := some .pl }
def has : AuxEntry := { form := "has", auxType := .have, person := some .third, number := some .sg }
def had : AuxEntry := { form := "had", auxType := .have, past := true }

def allAuxiliaries : List AuxEntry := [
  can, could, will, would, shall, should, may, might, must,
  do_, does, did,
  am, is, are, was, were,
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

end Auxiliaries

-- ============================================================================
-- Conjunctions
-- ============================================================================

structure ConjEntry where
  form : String
  /-- Coordinating or subordinating? -/
  coordinating : Bool := true
  deriving Repr, BEq

def and_ : ConjEntry := { form := "and" }
def or_ : ConjEntry := { form := "or" }
def but : ConjEntry := { form := "but" }
def nor : ConjEntry := { form := "nor" }

def allConjunctions : List ConjEntry := [and_, or_, but, nor]

def ConjEntry.toWord (c : ConjEntry) : Word :=
  { form := c.form, cat := .SCONJ, features := {} }

-- ============================================================================
-- Discourse Particles (Focus-sensitive)
-- ============================================================================

structure ParticleEntry where
  form : String
  /-- Does this particle require the CQ to be commonly shared? -/
  requiresSharedCQ : Bool
  /-- Can it access non-Roothian alternatives? -/
  nonRoothianAlts : Bool
  deriving Repr, BEq

def just_ : ParticleEntry := { form := "just", requiresSharedCQ := false, nonRoothianAlts := true }
def only_ : ParticleEntry := { form := "only", requiresSharedCQ := true, nonRoothianAlts := false }

def allParticles : List ParticleEntry := [just_, only_]

end Fragments.English.FunctionWords
