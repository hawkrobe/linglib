import Linglib.Data.UD.Basic
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# English Miscellaneous Function Words Fragment

Closed-class items that don't fit a more specific Fragment file:

- **Prepositions** (`to_`, `on`, `in_`, `at_`, `by_`, `with_`,
  `from_`, `before`, `after`)
- **Coordinating conjunctions** (`and_`, `or_`, `but`, `nor`)

The auxiliaries (modals + do-support + be + have + infinitival particle)
live in `Fragments/English/Auxiliaries.lean`; the modal adverbs and adverbs
of quantification in `Fragments/English/Adverbs.lean`.
The complementizers (`that`, `if`, `whether`, ...) live in
`Fragments/English/Complementizers.lean`.

This file may be split further as topic-specific Fragment files
emerge.
-/

namespace English.FunctionWords


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
def out : PrepEntry := { form := "out" }

def allPrepositions : List PrepEntry := [to_, on, in_, at_, by_, with_, from_, before, after, out]

def PrepEntry.toWord (p : PrepEntry) : Word :=
  { form := p.form, cat := .ADP, features := {} }

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
  { form := c.form, cat := if c.coordinating then .CCONJ else .SCONJ, features := {} }

end English.FunctionWords
