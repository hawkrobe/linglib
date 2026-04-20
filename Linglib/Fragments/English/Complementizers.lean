import Linglib.Core.Lexical.Word

/-!
# English Complementizers Lexicon Fragment

Lexical entries for English subordinating complementizers: `that`,
`if`, `whether`, `because`, `although`, `while`. Surface-form
classification (question-introducing, conditional-introducing,
optional) only — semantic clauses live in the relevant Theory or
Study files.

`if` is split between conditional and embedded-question uses; the
single Fragment entry carries both flags. The morphologically distinct
preposition *to* and the infinitival particle *to* live in
`Auxiliaries.lean` and `FunctionWords.lean` respectively.
-/

namespace Fragments.English.Complementizers

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

end Fragments.English.Complementizers
