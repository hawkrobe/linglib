import Linglib.Syntax.Minimalist.FromFragments
import Linglib.Syntax.Minimalist.SyntacticObject.Derivation

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

open Minimalist Minimalist.FromFragments

/-- "John sees Mary" as a Minimalist Merge derivation: *see*'s complement
    is *Mary* (`emR`), then *John* is added as specifier (`emL`). -/
def john_sees_mary : SO.Derivation :=
  { initial := verbToSO English.Predicates.Verbal.see 31
    steps   := [.emR (nounToSO English.Nouns.mary 11),
                .emL (nounToSO English.Nouns.john 10)] }

/-- The phonological yield of `john_sees_mary` is the SVO string
    "John sees Mary": the Minimalist derivation (built by `emR` then
    `emL` over `verbToSO`/`nounToSO`) linearizes subject-verb-object via the
    derivation-grounded computable externalization (`SO.Derivation.surfacePhon`). -/
theorem models_svo_word_order :
    String.intercalate " " john_sees_mary.surfacePhon = "John sees Mary" := by decide

end Chomsky1995
