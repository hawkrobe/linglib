import Linglib.Theories.Syntax.HPSG.Core.Basic
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Lexicon

/-!
# HPSG Interpretation of Fragment Entries

Maps Fragment lexical entries to HPSG Signs (words with appropriate Synsem).

This is the **theory interpretation layer**: Fragment entries are theory-neutral,
and this module provides the HPSG-specific interpretation.

## Design

- `VerbEntry → Sign`: based on complement type, sets HEAD and VAL
- `PronounEntry → Sign`: NP-like signs with appropriate features
- `NounEntry → Sign`: N or NP depending on proper/common
- `QuantifierEntry → Sign`: determiners

## Example

```
VerbEntry.sleep (intransitive) → word "sleeps" { cat := VERB, val := { subj := [NOUN] } }
VerbEntry.eat (transitive)     → word "eats" { cat := VERB, val := { subj := [NOUN], comps := [NOUN] } }
VerbEntry.give (ditransitive)  → word "gives" { cat := VERB, val := { subj := [NOUN], comps := [NOUN, NOUN] } }
```
-/

namespace HPSG.FromFragments

open HPSG
open Fragments.English.Predicates.Verbal (VerbEntry ComplementType)
open Fragments.English.Pronouns (PronounEntry PronounType)
open Fragments.English.Nouns (NounEntry)
open Fragments.English.Determiners (QuantifierEntry)
open Fragments.English.Lexicon (LexResult)

/--
Map a VerbEntry's complement type to an HPSG Valence.

The mapping follows standard HPSG practice (Pollard & Sag 1994):
- Intransitive: SUBJ ⟨NP⟩, COMPS ⟨⟩
- Transitive: SUBJ ⟨NP⟩, COMPS ⟨NP⟩
- Ditransitive: SUBJ ⟨NP⟩, COMPS ⟨NP, NP⟩
- Clause-embedding: SUBJ ⟨NP⟩, COMPS ⟨S⟩
-/
def verbToValence (v : VerbEntry) : Valence :=
  match v.complementType with
  | .none => { subj := [.NOUN], comps := [] }
  | .np => { subj := [.NOUN], comps := [.NOUN] }
  | .np_np => { subj := [.NOUN], comps := [.NOUN, .NOUN] }
  | .np_pp => { subj := [.NOUN], comps := [.NOUN, .ADP] }
  | .finiteClause => { subj := [.NOUN], comps := [.VERB] }
  | .infinitival => { subj := [.NOUN], comps := [.VERB] }
  | .gerund => { subj := [.NOUN], comps := [.VERB] }
  | .smallClause => { subj := [.NOUN], comps := [.NOUN, .ADJ] }
  | .question => { subj := [.NOUN], comps := [.VERB] }

/--
Map a VerbEntry to an HPSG Sign.
-/
def verbToSign (v : VerbEntry) : Sign :=
  .word (v.toWord3sg) { cat := .VERB, val := verbToValence v }

/--
Map a NounEntry to an HPSG Sign.

Proper names are NP (saturated); common nouns are N (unsaturated,
needing a determiner).
-/
def nounToSign (n : NounEntry) : Sign :=
  if n.proper then
    .word (n.toWordSg) { cat := .PROPN }
  else
    .word (n.toWordSg) { cat := .NOUN }

/--
Map a PronounEntry to an HPSG Sign.
-/
def pronounToSign (p : PronounEntry) : Sign :=
  .word (p.toWord) { cat := .PRON }

/--
Map a QuantifierEntry to an HPSG Sign.

Determiners select an N complement and yield an NP.
-/
def determinerToSign (d : QuantifierEntry) : Sign :=
  .word (d.toWord) { cat := .DET, val := { comps := [.NOUN] } }

/--
Map a unified LexResult to an HPSG Sign.
-/
def lexResultToSign : LexResult → Sign
  | .verb v => verbToSign v
  | .pronoun p => pronounToSign p
  | .noun n => nounToSign n
  | .determiner d => determinerToSign d

/--
Build an HPSG lexicon (list of Signs) from all Fragment verbs.
-/
def verbsToLexicon : List Sign :=
  Fragments.English.Predicates.Verbal.allVerbs.map verbToSign

/--
Build an HPSG lexicon from all Fragment pronouns.
-/
def pronounsToLexicon : List Sign :=
  Fragments.English.Pronouns.allPronouns.map pronounToSign

/--
Build an HPSG lexicon from all Fragment nouns.
-/
def nounsToLexicon : List Sign :=
  Fragments.English.Nouns.allNouns.map nounToSign

/--
Complete HPSG lexicon derived from all Fragments.
-/
def fragmentLexicon : List Sign :=
  verbsToLexicon ++ pronounsToLexicon ++ nounsToLexicon

-- ============================================================================
-- Verification Examples
-- ============================================================================

-- Verify intransitive verbs get empty COMPS
example : (verbToSign Fragments.English.Predicates.Verbal.sleep).synsem.val.comps = [] := rfl
example : (verbToSign Fragments.English.Predicates.Verbal.run).synsem.val.comps = [] := rfl

-- Verify transitive verbs get one NP complement
example : (verbToSign Fragments.English.Predicates.Verbal.eat).synsem.val.comps = [.NOUN] := rfl
example : (verbToSign Fragments.English.Predicates.Verbal.kick).synsem.val.comps = [.NOUN] := rfl

-- Verify ditransitive verbs get two NP complements
example : (verbToSign Fragments.English.Predicates.Verbal.give).synsem.val.comps = [.NOUN, .NOUN] := rfl

-- Verify all verbs have VERB category
example : (verbToSign Fragments.English.Predicates.Verbal.sleep).synsem.cat = .VERB := rfl
example : (verbToSign Fragments.English.Predicates.Verbal.eat).synsem.cat = .VERB := rfl

-- Verify proper names get PROPN, common nouns get NOUN
example : (nounToSign Fragments.English.Nouns.john).synsem.cat = .PROPN := rfl
example : (nounToSign Fragments.English.Nouns.cat).synsem.cat = .NOUN := rfl

-- Verify all verbs have a subject requirement
example : (verbToSign Fragments.English.Predicates.Verbal.sleep).synsem.val.subj = [.NOUN] := rfl
example : (verbToSign Fragments.English.Predicates.Verbal.give).synsem.val.subj = [.NOUN] := rfl

end HPSG.FromFragments
