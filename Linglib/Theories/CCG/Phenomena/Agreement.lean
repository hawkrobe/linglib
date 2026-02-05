import Linglib.Core.Basic
import Linglib.Theories.CCG.Core.Basic
import Linglib.Theories.CCG.Core.FromFragments
import Linglib.Fragments.English.Lexicon
import Linglib.Phenomena.Agreement.Basic

/-!
# CCG Bridge: Agreement Phenomena

Connects string-based Agreement phenomena to CCG derivations.

This module demonstrates the Bridge pattern:
1. String data lives in `Phenomena/Agreement/Basic.lean`
2. Lexical entries live in `Fragments/English/`
3. This module connects them via CCG interpretation

## Architecture

```
Phenomena.Agreement.data         ← Pure strings: "he sleeps" ✓
       ↓ (parse via Lexicon)
Fragments.English.Lexicon        ← Unified lookup
       ↓ (interpret via FromFragments)
CCG.FromFragments                ← VerbEntry → CCG.Cat
       ↓ (derive)
CCG.DerivStep                    ← Syntactic derivation
```
-/

namespace CCG.Bridge.Agreement

open CCG
open CCG.FromFragments
open Fragments.English.Lexicon

/--
Parse a sentence string to CCG lexical entries.

Uses the unified lexicon from Fragments/English/Lexicon.lean
and interprets results via CCG.FromFragments.
-/
def parse (s : String) : Option (List LexEntry) :=
  parseToLexEntries s

/--
Attempt to build a simple CCG derivation from a list of lexical entries.

This is a simplified version that handles basic subject-verb structures.
A full implementation would use chart parsing or similar.
-/
def tryDerive (entries : List LexEntry) : Option DerivStep :=
  match entries with
  | [subj, verb] =>
    -- Try subject + intransitive verb: NP + (S\NP) → S
    let d1 := DerivStep.lex subj
    let d2 := DerivStep.lex verb
    -- Backward application: NP (S\NP) → S
    let combined := DerivStep.bapp d1 d2
    if combined.cat == some S then some combined else none
  | [subj, verb, obj] =>
    -- Try subject + transitive verb + object: NP + ((S\NP)/NP) + NP → S
    let d1 := DerivStep.lex subj
    let d2 := DerivStep.lex verb
    let d3 := DerivStep.lex obj
    -- Forward application: (S\NP)/NP NP → S\NP
    let vp := DerivStep.fapp d2 d3
    -- Backward application: NP (S\NP) → S
    let s := DerivStep.bapp d1 vp
    if s.cat == some S then some s else none
  | _ => none

/--
Check if CCG can derive a sentence string.
-/
def canDerive (s : String) : Bool :=
  match parse s with
  | some entries => (tryDerive entries).isSome
  | none => false

/--
Check if CCG captures a sentence pair (derives good, blocks bad).
-/
def capturesPair (pair : SentencePair) : Bool :=
  canDerive pair.grammatical && !canDerive pair.ungrammatical

-- ============================================================================
-- Verification Theorems
-- ============================================================================

-- Parsing succeeds for grammatical strings in the lexicon
theorem parse_he_sleeps : (parse "he sleeps").isSome = true := by native_decide
theorem parse_they_sleep : (parse "they sleep").isSome = true := by native_decide
theorem parse_John_sleeps : (parse "John sleeps").isSome = true := by native_decide

-- Derivation succeeds for grammatical SV sentences
theorem derive_he_sleeps : canDerive "he sleeps" = true := by native_decide
theorem derive_they_sleep : canDerive "they sleep" = true := by native_decide
theorem derive_John_sleeps : canDerive "John sleeps" = true := by native_decide

-- Note: Full agreement checking would require morphological features on CCG categories.
-- Currently CCG encodes only syntactic categories, not phi-features.
-- A complete bridge would:
-- 1. Extend CCG.Cat with agreement features
-- 2. Add feature unification to combinatory rules
-- 3. Prove that "he sleep" fails due to agreement mismatch

/-
TODO: Prove CCG captures the full agreement phenomenon

theorem ccg_captures_agreement :
    Phenomena.Agreement.data.pairs.all capturesPair = true := by
  native_decide

This requires:
- Extending CCG with agreement features
- Feature checking in combinatory rules
- The lexicon to assign correct features
-/

end CCG.Bridge.Agreement
