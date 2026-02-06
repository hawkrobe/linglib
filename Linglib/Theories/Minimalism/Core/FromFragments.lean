import Linglib.Theories.Minimalism.Core.Basic
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Lexicon

/-!
# Minimalist Interpretation of Fragment Entries

Maps Fragment lexical entries to Minimalist feature bundles.

This is the **theory interpretation layer**: Fragment entries are theory-neutral,
and this module provides the Minimalist-specific interpretation.

## Design

- `VerbEntry → FeatureBundle`: category features + selectional features
- `PronounEntry → FeatureBundle`: D features + phi-features + wh
- `NounEntry → FeatureBundle`: N features + phi-features
- `QuantifierEntry → FeatureBundle`: D features + quantificational features

## Example

```
VerbEntry.sleep (intransitive) → [cat V]
VerbEntry.eat (transitive) → [cat V, selectsNP]
VerbEntry.give (ditransitive) → [cat V, selectsNP, selectsNP]
```
-/

namespace Minimalism.Core.FromFragments

open Minimalism
open Fragments.English.Predicates.Verbal (VerbEntry ComplementType)
open Fragments.English.Pronouns (PronounEntry PronounType)
open Fragments.English.Nouns (NounEntry)
open Fragments.English.Determiners (QuantifierEntry)
open Fragments.English.Lexicon (LexResult)

/--
Selectional feature - what the verb selects.
-/
inductive SelFeature where
  | selectsNP    -- Selects an NP argument
  | selectsCP    -- Selects a CP (finite clause)
  | selectsIP    -- Selects an IP (infinitival)
  | selectsVP    -- Selects a VP (gerund)
  deriving DecidableEq, Repr, BEq

/--
Map a VerbEntry's complement type to selectional features.
-/
def verbToSelFeatures (v : VerbEntry) : List SelFeature :=
  match v.complementType with
  | .none => []                           -- Intransitive: no selection
  | .np => [.selectsNP]                   -- Transitive: selects NP
  | .np_np => [.selectsNP, .selectsNP]    -- Ditransitive: selects two NPs
  | .np_pp => [.selectsNP]                -- NP + PP (PP handled separately)
  | .finiteClause => [.selectsCP]         -- Clause-embedding
  | .infinitival => [.selectsIP]          -- Control/raising
  | .gerund => [.selectsVP]               -- Gerund complement
  | .smallClause => [.selectsNP]          -- Small clause (simplified)
  | .question => [.selectsCP]             -- Question-embedding

/--
Map a VerbEntry to a Minimalist feature bundle.
-/
def verbToFeatures (v : VerbEntry) : FeatureBundle :=
  [.cat .VERB] ++
  -- Add EPP if verb is transitive (needs internal argument)
  (if v.complementType != .none then [.epp true] else [])

/--
Map a PronounEntry to a Minimalist feature bundle.
-/
def pronounToFeatures (p : PronounEntry) : FeatureBundle :=
  [.cat .DET] ++
  (if p.wh then [.wh true] else [])

/--
Map a NounEntry to a Minimalist feature bundle.
-/
def nounToFeatures (n : NounEntry) : FeatureBundle :=
  if n.proper then
    [.cat .DET]  -- Proper names are D
  else
    [.cat .NOUN]  -- Common nouns are N

/--
Map a QuantifierEntry to a Minimalist feature bundle.
-/
def determinerToFeatures (_d : QuantifierEntry) : FeatureBundle :=
  [.cat .DET]

/--
Map a unified LexResult to a Minimalist feature bundle.
-/
def lexResultToFeatures : LexResult → FeatureBundle
  | .verb v => verbToFeatures v
  | .pronoun p => pronounToFeatures p
  | .noun n => nounToFeatures n
  | .determiner d => determinerToFeatures d

/--
Convert a LexResult to a SynObj (lexical item with features).
-/
def lexResultToSynObj (r : LexResult) : SynObj :=
  match r with
  | .verb v => .lex (v.toWord3sg) (verbToFeatures v)
  | .pronoun p => .lex (p.toWord) (pronounToFeatures p)
  | .noun n => .lex (n.toWordSg) (nounToFeatures n)
  | .determiner d => .lex (d.toWord) (determinerToFeatures d)

/--
Parse a sentence and produce Minimalist lexical items.
-/
def parseToSynObjs (s : String) : Option (List SynObj) :=
  Fragments.English.Lexicon.parseSentence s |>.map (·.map lexResultToSynObj)

-- ============================================================================
-- Verification Examples
-- ============================================================================

-- Verify verb features
example : verbToFeatures Fragments.English.Predicates.Verbal.sleep = [.cat .VERB] := rfl
example : verbToFeatures Fragments.English.Predicates.Verbal.eat = [.cat .VERB, .epp true] := rfl

-- Verify noun features
example : nounToFeatures Fragments.English.Nouns.john = [.cat .DET] := rfl
example : nounToFeatures Fragments.English.Nouns.cat = [.cat .NOUN] := rfl

-- Verify pronoun features
example : pronounToFeatures Fragments.English.Pronouns.he = [.cat .DET] := rfl
example : pronounToFeatures Fragments.English.Pronouns.who = [.cat .DET, .wh true] := rfl

end Minimalism.Core.FromFragments
