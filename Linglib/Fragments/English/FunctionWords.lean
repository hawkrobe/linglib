/-
# English Function Words Lexicon Fragment

Lexical entries for English closed-class function words:
- Prepositions
- Complementizers
- Auxiliaries
- Conjunctions
-/

import Linglib.Core.Basic

namespace Fragments.English.FunctionWords

-- ============================================================================
-- Prepositions
-- ============================================================================

structure PrepEntry where
  form : String
  /-- Can introduce an agent in passive? -/
  passiveAgent : Bool := false
  deriving Repr, BEq

def to : PrepEntry := { form := "to" }
def on : PrepEntry := { form := "on" }
def in_ : PrepEntry := { form := "in" }
def at_ : PrepEntry := { form := "at" }
def by_ : PrepEntry := { form := "by", passiveAgent := true }
def with_ : PrepEntry := { form := "with" }
def from_ : PrepEntry := { form := "from" }
def before : PrepEntry := { form := "before" }
def after : PrepEntry := { form := "after" }

def allPrepositions : List PrepEntry := [to, on, in_, at_, by_, with_, from_, before, after]

def PrepEntry.toWord (p : PrepEntry) : Word :=
  { form := p.form, cat := .P, features := {} }

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
  { form := c.form, cat := .C, features := {} }

-- ============================================================================
-- Auxiliaries
-- ============================================================================

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
  deriving Repr, BEq

-- Modals (no agreement)
def can : AuxEntry := { form := "can", auxType := .modal }
def could : AuxEntry := { form := "could", auxType := .modal, past := true }
def will : AuxEntry := { form := "will", auxType := .modal }
def would : AuxEntry := { form := "would", auxType := .modal, past := true }
def shall : AuxEntry := { form := "shall", auxType := .modal }
def should : AuxEntry := { form := "should", auxType := .modal, past := true }
def may : AuxEntry := { form := "may", auxType := .modal }
def might : AuxEntry := { form := "might", auxType := .modal, past := true }
def must : AuxEntry := { form := "must", auxType := .modal }

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
  , cat := .Aux
  , features := {
      finite := true
      , person := a.person
      , number := a.number
    }
  }

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
  { form := c.form, cat := .C, features := {} }

end Fragments.English.FunctionWords
