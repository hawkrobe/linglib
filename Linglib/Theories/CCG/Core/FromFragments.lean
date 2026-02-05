import Linglib.Theories.CCG.Core.Basic
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Lexicon

/-!
# CCG Interpretation of Fragment Entries

Maps Fragment lexical entries to CCG categories.

This is the **theory interpretation layer**: Fragment entries are theory-neutral,
and this module provides the CCG-specific interpretation.

## Design

- `VerbEntry → CCG.Cat`: based on complement type and valence
- `PronounEntry → CCG.Cat`: NP for personal/reflexive, complex for wh-
- `NounEntry → CCG.Cat`: N for common nouns, NP for proper names
- `QuantifierEntry → CCG.Cat`: NP/N for determiners

## Example

```
VerbEntry.sleep (intransitive) → S\NP (IV)
VerbEntry.eat (transitive) → (S\NP)/NP (TV)
VerbEntry.give (ditransitive) → ((S\NP)/NP)/NP (DTV)
```
-/

namespace CCG.FromFragments

open CCG
open Fragments.English.Predicates.Verbal (VerbEntry ComplementType)
open Fragments.English.Pronouns (PronounEntry PronounType)
open Fragments.English.Nouns (NounEntry)
open Fragments.English.Determiners (QuantifierEntry)
open Fragments.English.Lexicon (LexResult)

/--
Map a VerbEntry's complement type to a CCG category.

The mapping follows standard CCG practice:
- Intransitive: S\NP
- Transitive: (S\NP)/NP
- Ditransitive: ((S\NP)/NP)/NP
- Clause-embedding: (S\NP)/S
-/
def verbToCat (v : VerbEntry) : Cat :=
  match v.complementType with
  | .none => IV              -- S\NP
  | .np => TV                -- (S\NP)/NP
  | .np_np => DTV            -- ((S\NP)/NP)/NP
  | .np_pp => TV             -- (S\NP)/NP (simplified: PP handled separately)
  | .finiteClause => S \ NP / S  -- (S\NP)/S
  | .infinitival => S \ NP / IV  -- (S\NP)/(S\NP) - control verbs
  | .gerund => S \ NP / IV       -- Same as infinitival
  | .smallClause => (S \ NP) / AdjPred / NP  -- consider X happy
  | .question => S \ NP / S      -- Simplified: question as S

/--
Map a PronounEntry to a CCG category.
-/
def pronounToCat (p : PronounEntry) : Cat :=
  match p.pronounType with
  | .personal => NP
  | .reflexive => NP
  | .wh => NP              -- Simplified: wh-words as NP (can be type-raised)
  | .relative => NP / S    -- Relative pronouns: (NP/S) or similar
  | .demonstrative => NP

/--
Map a NounEntry to a CCG category.
-/
def nounToCat (n : NounEntry) : Cat :=
  if n.proper then NP else N

/--
Map a QuantifierEntry to a CCG category.

Determiners are NP/N: they take a noun and produce an NP.
-/
def determinerToCat (_d : QuantifierEntry) : Cat :=
  Det  -- NP/N

/--
Map a unified LexResult to a CCG category.
-/
def lexResultToCat : LexResult → Cat
  | .verb v => verbToCat v
  | .pronoun p => pronounToCat p
  | .noun n => nounToCat n
  | .determiner d => determinerToCat d

/--
Convert a LexResult to a CCG LexEntry.
-/
def lexResultToEntry (r : LexResult) : LexEntry :=
  match r with
  | .verb v => ⟨v.form3sg, verbToCat v⟩
  | .pronoun p => ⟨p.form, pronounToCat p⟩
  | .noun n => ⟨n.formSg, nounToCat n⟩
  | .determiner d => ⟨d.form, determinerToCat d⟩

/--
Parse a sentence and produce CCG lexical entries.
-/
def parseToLexEntries (s : String) : Option (List LexEntry) :=
  Fragments.English.Lexicon.parseSentence s |>.map (·.map lexResultToEntry)

/--
Build a CCG lexicon from all Fragment verbs.
-/
def verbsToLexicon : List LexEntry :=
  Fragments.English.Predicates.Verbal.allVerbs.map fun v =>
    ⟨v.form3sg, verbToCat v⟩

/--
Build a CCG lexicon from all Fragment pronouns.
-/
def pronounsToLexicon : List LexEntry :=
  Fragments.English.Pronouns.allPronouns.map fun p =>
    ⟨p.form, pronounToCat p⟩

/--
Build a CCG lexicon from all Fragment nouns.
-/
def nounsToLexicon : List LexEntry :=
  Fragments.English.Nouns.allNouns.map fun n =>
    ⟨n.formSg, nounToCat n⟩

/--
Build a CCG lexicon from all Fragment determiners.
-/
def determinersToLexicon : List LexEntry :=
  Fragments.English.Determiners.allDeterminers.map fun d =>
    ⟨d.form, determinerToCat d⟩

/--
Complete CCG lexicon derived from all Fragments.
-/
def fragmentLexicon : Lexicon :=
  verbsToLexicon ++ pronounsToLexicon ++ nounsToLexicon ++ determinersToLexicon

-- ============================================================================
-- Verification Examples
-- ============================================================================

-- Verify intransitive verbs get IV
example : verbToCat Fragments.English.Predicates.Verbal.sleep = IV := rfl
example : verbToCat Fragments.English.Predicates.Verbal.run = IV := rfl

-- Verify transitive verbs get TV
example : verbToCat Fragments.English.Predicates.Verbal.eat = TV := rfl
example : verbToCat Fragments.English.Predicates.Verbal.kick = TV := rfl

-- Verify ditransitive verbs get DTV
example : verbToCat Fragments.English.Predicates.Verbal.give = DTV := rfl

-- Verify proper names get NP, common nouns get N
example : nounToCat Fragments.English.Nouns.john = NP := rfl
example : nounToCat Fragments.English.Nouns.cat = N := rfl

end CCG.FromFragments
