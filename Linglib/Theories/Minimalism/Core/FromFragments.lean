import Linglib.Theories.Minimalism.Core.Basic
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Lexicon

/-!
# Minimalist Interpretation of Fragment Entries

Maps Fragment lexical entries to formal `SyntacticObject`s via `LIToken`.

This is the **theory interpretation layer**: Fragment entries are theory-neutral,
and this module provides the Minimalist-specific interpretation using the
formal `SyntacticObject` type from `SyntacticObjects.lean`.

## Design

- `VerbEntry → SyntacticObject`: V with selectional stack from complement type
- `PronounEntry → SyntacticObject`: D (pronouns project as DP heads)
- `NounEntry → SyntacticObject`: N (common) or D (proper names)
- `QuantifierEntry → SyntacticObject`: D with N selection

## Example

```
VerbEntry.sleep (intransitive) → .leaf ⟨.simple .V [], "sleeps"⟩
VerbEntry.eat (transitive)     → .leaf ⟨.simple .V [.D], "eats"⟩
VerbEntry.give (ditransitive)  → .leaf ⟨.simple .V [.D, .D], "gives"⟩
```
-/

namespace Minimalism.Core.FromFragments

open Minimalism
open Fragments.English.Predicates.Verbal (VerbEntry ComplementType)
open Fragments.English.Pronouns (PronounEntry PronounType)
open Fragments.English.Nouns (NounEntry)
open Fragments.English.Determiners (QuantifierEntry)
open Fragments.English.Lexicon (LexResult)

/-- Map a VerbEntry's complement type to a formal selectional stack. -/
def verbToSelStack (v : VerbEntry) : SelStack :=
  match v.complementType with
  | .none => []                -- intransitive
  | .np => [.D]               -- transitive: selects DP
  | .np_np => [.D, .D]        -- ditransitive: selects two DPs
  | .np_pp => [.D]            -- NP + PP (PP handled separately)
  | .finiteClause => [.C]     -- clause-embedding: selects CP
  | .infinitival => [.T]      -- control/raising: selects TP
  | .gerund => [.V]           -- gerund complement
  | .smallClause => [.D]      -- small clause (simplified)
  | .question => [.C]         -- question-embedding: selects CP

/-- Convert a VerbEntry to a formal SyntacticObject.

    Uses `uposToCat` indirectly: verbs always map to `Cat.V`. -/
def verbToSO (v : VerbEntry) (id : Nat) : SyntacticObject :=
  mkLeafPhon .V (verbToSelStack v) v.form3sg id

/-- Convert a PronounEntry to a formal SyntacticObject.

    Pronouns are D heads (they project as DPs). -/
def pronounToSO (p : PronounEntry) (id : Nat) : SyntacticObject :=
  mkLeafPhon .D [] p.form id

/-- Convert a NounEntry to a formal SyntacticObject.

    Proper names are D (project as DP heads); common nouns are N. -/
def nounToSO (n : NounEntry) (id : Nat) : SyntacticObject :=
  if n.proper then
    mkLeafPhon .D [] n.formSg id
  else
    mkLeafPhon .N [] n.formSg id

/-- Convert a QuantifierEntry to a formal SyntacticObject.

    Determiners are D heads that select N. -/
def determinerToSO (d : QuantifierEntry) (id : Nat) : SyntacticObject :=
  mkLeafPhon .D [.N] d.form id

/-- Convert a unified LexResult to a formal SyntacticObject. -/
def lexResultToSO (r : LexResult) (id : Nat) : SyntacticObject :=
  match r with
  | .verb v => verbToSO v id
  | .pronoun p => pronounToSO p id
  | .noun n => nounToSO n id
  | .determiner d => determinerToSO d id

-- ============================================================================
-- Verification Examples
-- ============================================================================

-- Verify verb selectional stacks
example : verbToSelStack Fragments.English.Predicates.Verbal.sleep = [] := rfl
example : verbToSelStack Fragments.English.Predicates.Verbal.eat = [.D] := rfl
example : verbToSelStack Fragments.English.Predicates.Verbal.give = [.D, .D] := rfl

-- Verify noun categories
example : (nounToSO Fragments.English.Nouns.john 1).isLeaf = true := rfl
example : (nounToSO Fragments.English.Nouns.cat 1).isLeaf = true := rfl

end Minimalism.Core.FromFragments
