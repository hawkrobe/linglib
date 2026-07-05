import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.Linearization.Replay
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Nouns

/-!
# Minimalist Derivations of Word Order
[chomsky-1995]

Verifies that Minimalist Merge derivations model English SVO order: the
phonological yield of a transitive derivation comes out subject-verb-object.
The transitive derivation is defined locally (chronological discipline:
Chomsky 1995 cannot import Adger 2003 where the canonical Minimalism
English-derivation lexicon now lives).
-/

namespace Chomsky1995

open Minimalist
open English.Predicates.Verbal (VerbEntry)
open English.Nouns (NounEntry)

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
  SyntacticObject.mkLeafPhon .V (verbToSelStack v) v.form3sg id

/-- A `NounEntry` as a leaf: proper names project as `.D`, common nouns as bare `.N`. -/
def nounToSO (n : NounEntry) (id : Nat) : SyntacticObject :=
  if n.proper then SyntacticObject.mkLeafPhon .D [] n.formSg id
  else SyntacticObject.mkLeafPhon .N [] n.formSg id

/-- "John sees Mary" as a Minimalist Merge derivation: *see*'s complement
    is *Mary* (`emR`), then *John* is added as specifier (`emL`). -/
def john_sees_mary : SyntacticObject.Derivation :=
  { initial := verbToSO English.Predicates.Verbal.see 31
    steps   := [.emR (nounToSO English.Nouns.mary 11),
                .emL (nounToSO English.Nouns.john 10)] }

/-- The phonological yield of `john_sees_mary` is the SVO string
    "John sees Mary": the Minimalist derivation (built by `emR` then
    `emL` over `verbToSO`/`nounToSO`) linearizes subject-verb-object via the
    derivation-grounded computable externalization (`SyntacticObject.Derivation.surfacePhon`). -/
theorem models_svo_word_order :
    String.intercalate " " john_sees_mary.surfacePhon = "John sees Mary" := by decide

end Chomsky1995
