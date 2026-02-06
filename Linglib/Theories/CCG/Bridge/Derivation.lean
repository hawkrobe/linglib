/-
# CCG Semantic Interpretation

Converts CCG derivations to Montague semantic derivations.
This is one instantiation of the syntax→semantics interface.

## Key Function

`toDerivation : DerivStep → SemDeriv.Derivation`

This allows CCG derivations to feed into pragmatics (NeoGricean, RSA).
-/

import Linglib.Theories.CCG.Core.Basic
import Linglib.Theories.CCG.Bridge.Interface
import Linglib.Theories.TruthConditional.Core.Derivation
import Linglib.Theories.TruthConditional.Core.Lexicon

namespace CCG.Interpret

open CCG
open TruthConditional
open TruthConditional.SemDeriv
-- Qualified names avoid SemLexEntry conflict between TruthConditional.Core and CCG.Semantics

-- Extract Words from Derivation

/-- Get all words (surface forms) from a derivation, left to right -/
def getWords : DerivStep → List String
  | .lex entry => [entry.form]
  | .fapp d1 d2 => getWords d1 ++ getWords d2
  | .bapp d1 d2 => getWords d1 ++ getWords d2
  | .fcomp d1 d2 => getWords d1 ++ getWords d2
  | .bcomp d1 d2 => getWords d1 ++ getWords d2
  | .ftr d _ => getWords d
  | .btr d _ => getWords d
  | .coord d1 d2 => getWords d1 ++ ["and"] ++ getWords d2

-- Identify Scalar Items

/-- Check if a word form is a scalar item and return its lexical entry -/
def getScalarEntry (form : String) : Option (TruthConditional.Core.SemLexEntry toyModel) :=
  match TruthConditional.Core.toyLexicon form with
  | some entry => if entry.isScalar then Option.some entry else none
  | none => none

/-- Helper to find scalar items with positions -/
def findScalarsHelper (words : List String) (pos : Nat)
    : List (SemDeriv.ScalarOccurrence toyModel) :=
  match words with
  | [] => []
  | w :: ws =>
    match getScalarEntry w with
    | some entry => ⟨pos, entry⟩ :: findScalarsHelper ws (pos + 1)
    | none => findScalarsHelper ws (pos + 1)

/-- Find all scalar items in a derivation with their positions -/
def findScalarItems (d : DerivStep) : List (SemDeriv.ScalarOccurrence toyModel) :=
  findScalarsHelper (getWords d) 0

-- Convert to Semantic Derivation

/--
Convert a CCG derivation to a Montague semantic derivation.

Note: For a full implementation, we'd need to compositionally compute
the meaning from the derivation tree. For now, we provide the structure
and a placeholder for the meaning (requiring it to be provided separately).
-/
def toDerivation (d : DerivStep) (ty : Ty) (meaning : toyModel.interpTy ty)
    : Derivation toyModel :=
  { surface := getWords d
  , ty := ty
  , meaning := meaning
  , scalarItems := findScalarItems d
  }

-- Example Derivations

/-- CCG derivation for "John sleeps" -/
def ccg_john_sleeps : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩)

/-- Convert to semantic derivation -/
def john_sleeps_sem : Derivation toyModel :=
  toDerivation ccg_john_sleeps .t (ToyLexicon.sleeps_sem ToyEntity.john)

/-- CCG derivation for "some student sleeps" -/
-- Simplified: full CCG would have Det combining with N
def ccg_some_student_sleeps : DerivStep :=
  .bapp
    (.fapp (.lex ⟨"some", Det⟩) (.lex ⟨"student", N⟩))
    (.lex ⟨"sleeps", IV⟩)

/-- Convert to semantic derivation with scalar item -/
def some_student_sleeps_sem : Derivation toyModel :=
  toDerivation
    ccg_some_student_sleeps
    .t
    (Determiner.Quantifier.some_sem toyModel Determiner.Quantifier.student_sem ToyLexicon.sleeps_sem)

-- Verification

-- Verify the derivations via #eval
#eval getWords ccg_john_sleeps           -- ["John", "sleeps"]
#eval getWords ccg_some_student_sleeps   -- ["some", "student", "sleeps"]

#eval john_sleeps_sem.surface            -- ["John", "sleeps"]
#eval some_student_sleeps_sem.surface    -- ["some", "student", "sleeps"]

-- Notes

/-
A full SemanticsProducer instance would require computing meanings compositionally.
For now, we show the structure; actual meaning must be provided.

To use: construct Derivation directly using toDerivation with the meaning,
or use the pre-built examples like some_student_sleeps_sem.
-/

end CCG.Interpret
