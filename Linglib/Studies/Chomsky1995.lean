import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.Linearization.Replay
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Nouns

/-!
# Chomsky 1995: Minimalist derivations of word order

This file verifies that Minimalist Merge derivations of [chomsky-1995] model English SVO order:
the phonological yield of a transitive derivation — the verb merging its complement, then the
subject merging as specifier — comes out subject-verb-object. The derivation is built from
Fragment verb and noun entries through `verbToSelStack`, which reads a verb's selectional stack
off its complement type.

## Main results

* `models_svo_word_order` — the derivation of *John sees Mary* linearizes as "John sees Mary"

## References

* [chomsky-1995]
-/

namespace Chomsky1995

open Minimalist SyntacticObject
open English.Predicates.Verbal (VerbEntry)

/-- Map a verb's complement type to its selectional stack: each c-selected argument is one
    `Cat` feature consumed by complement Merge; nominal arguments are `.D` (the DP hypothesis).
    Folded in from the former `Syntax/Minimalist/FromFragments.lean` (its only consumer). -/
def verbToSelStack (v : VerbEntry) : SelStack :=
  match v.complementType with
  | .none => [] | .np => [.D] | .np_np => [.D, .D] | .np_pp => [.D]
  | .finiteClause => [.C] | .infinitival => [.T] | .gerund => [.V]
  | .smallClause => [.D] | .question => [.C]

/-- A `VerbEntry` as a `SyntacticObject` leaf (`Cat = .V`, selStack from `complementType`). -/
def verbToSO (v : VerbEntry) (id : Nat) : SyntacticObject :=
  mkLeafPhon .V (verbToSelStack v) v.form3sg id

/-- A proper name as a leaf, projecting as `.D`. -/
def nameToSO (n : ProperName) (id : Nat) : SyntacticObject := mkLeafPhon .D [] n.form id

/-- "John sees Mary" as a Minimalist Merge derivation: *see*'s complement
    is *Mary* (`em .right`), then *John* is added as specifier (`em .left`). -/
def john_sees_mary : Derivation :=
  { initial := verbToSO English.Predicates.Verbal.see 31
    steps   := [.em .right (nameToSO English.Nouns.mary 11),
                .em .left (nameToSO English.Nouns.john 10)] }

/-- The phonological yield of `john_sees_mary` is the SVO string
    "John sees Mary": the Minimalist derivation (built by `em .right` then
    `em .left` over `verbToSO`/`nameToSO`) linearizes subject-verb-object via the
    derivation-grounded computable externalization (`SyntacticObject.Derivation.surfacePhon`). -/
theorem models_svo_word_order :
    String.intercalate " " john_sees_mary.surfacePhon = "John sees Mary" := by decide

end Chomsky1995
