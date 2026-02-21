import Linglib.Core.Word
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners

/-!
# Unified English Lexicon

Provides unified lookup across all English word classes.

This module re-exports the specific lexicons and provides a unified
`lookup` function that searches across verbs, pronouns, nouns, etc.
-/

namespace Fragments.English.Lexicon

open Fragments.English.Predicates.Verbal (VerbEntry)
open Fragments.English.Pronouns (PronounEntry)
open Fragments.English.Nouns (NounEntry)
open Fragments.English.Determiners (QuantifierEntry)

/--
Result of unified lexicon lookup.

Since different word classes have different entry types, we use a sum type.
-/
inductive LexResult where
  | verb : VerbEntry → LexResult
  | pronoun : PronounEntry → LexResult
  | noun : NounEntry → LexResult
  | determiner : QuantifierEntry → LexResult
  deriving Repr

/--
Convert a lookup result to a Word (for derivations).

Note: This picks a default form (e.g., 3sg for verbs, singular for nouns).
For morphologically-aware parsing, use the specific entry functions.
-/
def LexResult.toWord : LexResult → Word
  | .verb v => v.toWord3sg
  | .pronoun p => p.toWord
  | .noun n => n.toWordSg
  | .determiner d => d.toWord

/--
Look up a verb by any of its forms (infinitive, 3sg, past, etc.).
-/
def lookupVerbByForm (form : String) : Option VerbEntry :=
  Predicates.Verbal.allVerbs.find? fun v =>
    v.form == form || v.form3sg == form || v.formPast == form ||
    v.formPastPart == form || v.formPresPart == form

/--
Unified lookup across all word classes.

Searches in order: pronouns, determiners, verbs, nouns.
(Pronouns and determiners first since they're closed classes.)
Returns the first match found.
-/
def lookup (form : String) : Option LexResult :=
  -- Try pronouns first (closed class, exact match)
  if let some p := Pronouns.lookup form then
    some (.pronoun p)
  -- Try determiners (closed class)
  else if let some d := Determiners.lookup form then
    some (.determiner d)
  -- Try verbs (with morphological variants)
  else if let some v := lookupVerbByForm form then
    some (.verb v)
  -- Try nouns
  else if let some n := Nouns.lookup form then
    some (.noun n)
  else
    none

/--
Look up multiple words, returning None if any lookup fails.
-/
def lookupAll (forms : List String) : Option (List LexResult) :=
  forms.mapM lookup

/--
Parse a sentence string into lexical entries.

Splits on whitespace and looks up each token.
-/
def parseSentence (s : String) : Option (List LexResult) :=
  let tokens := s.splitOn " " |>.filter (· ≠ "")
  lookupAll tokens

/--
Parse a sentence and convert to Words.
-/
def parseToWords (s : String) : Option (List Word) :=
  parseSentence s |>.map (·.map LexResult.toWord)

end Fragments.English.Lexicon
