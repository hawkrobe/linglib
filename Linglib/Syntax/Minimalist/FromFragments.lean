import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners

/-!
# Minimalism: Fragment Lexicon → Syntactic Object Interpretation

Maps Fragment lexical entries (`VerbEntry`, `PersonalPronoun`, `NounEntry`,
`Quantifier`) into Minimalist `SyntacticObject` leaves with the
appropriate `Cat` and `SelStack` features.

Concrete derivation *instances* using these projections live in
`Studies/`, anchored to specific paper analyses (e.g.
`Studies/Adger2003.lean` for c-selection).

## Sections

- §1 Selectional encoding (`verbToSelStack`)
- §2 Per-entry-type projections (`verbToSO`, `pronounToSO`, `nounToSO`,
  `determinerToSO`)
- §3 Sanity examples

## Selectional encoding

`verbToSelStack` derives `SelStack` from `VerbEntry.complementType`.
This is a substantive theory commitment: transitives c-select [.D],
ditransitives [.D, .D], etc. The encoding is faithful to Adger 2003 ch. 3
c-selection (eq. 110: `kiss [V, uN]`) modulo a few documented
simplifications (e.g. `.np_pp` collapses *put NP PP*-type frames; small
clauses use `.D` rather than a dedicated predicational head).
-/

namespace Minimalist.FromFragments

open Minimalist
open English.Predicates.Verbal (VerbEntry)
open English.Nouns (NounEntry)

section SelectionalEncoding

/-- Map a `VerbEntry`'s complement type to a formal selectional stack.

    Encodes Adger 2003 ch. 3 c-selection: each lexically required argument
    contributes one `Cat` feature consumed by complement Merge. The choice
    of `.D` for nominal arguments matches Adger ch. 7 (all argumental
    nominals are DPs). -/
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

end SelectionalEncoding

section EntryProjections

/-- Convert a `VerbEntry` to a `SyntacticObject` leaf with `Cat = .V` and
    `SelStack` derived from `complementType`. -/
def verbToSO (v : VerbEntry) (id : Nat) : SyntacticObject :=
  SO.mkLeafPhon .V (verbToSelStack v) v.form3sg id

/-- Convert a `PersonalPronoun` to a `SyntacticObject` leaf. Pronouns are D
    heads (they project as DPs per Adger ch. 7). -/
def pronounToSO (p : PersonalPronoun) (id : Nat) : SyntacticObject :=
  SO.mkLeafPhon .D [] p.form id

/-- Convert a `NounEntry` to a `SyntacticObject` leaf. Proper names are
    D-projecting (Longobardi 1994 / Adger ch. 7); common nouns are bare N
    (need null-D wrapping or an overt determiner to project as DPs). -/
def nounToSO (n : NounEntry) (id : Nat) : SyntacticObject :=
  if n.proper then
    SO.mkLeafPhon .D [] n.formSg id
  else
    SO.mkLeafPhon .N [] n.formSg id

/-- Convert a `Quantifier` (determiner) to a `SyntacticObject` leaf
    with `Cat = .D` and `SelStack = [.N]` (Adger ch. 7 eq. 110:
    `the [D, uN]`). -/
def determinerToSO (d : Quantifier) (id : Nat) : SyntacticObject :=
  SO.mkLeafPhon .D [.N] d.form id

end EntryProjections

section Sanity

example : verbToSelStack English.Predicates.Verbal.sleep = [] := rfl
example : verbToSelStack English.Predicates.Verbal.eat = [.D] := rfl
example : verbToSelStack English.Predicates.Verbal.give = [.D, .D] := rfl
example : (nounToSO English.Nouns.john 1).isLeaf := by decide
example : (nounToSO English.Nouns.cat 1).isLeaf := by decide

end Sanity

end Minimalist.FromFragments
