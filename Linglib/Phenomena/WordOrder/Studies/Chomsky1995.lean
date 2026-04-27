import Linglib.Theories.Syntax.Minimalist.FromFragments
import Linglib.Theories.Syntax.Minimalist.Derivation
import Linglib.Phenomena.WordOrder.Basic

/-!
# Minimalist Derivations of Word Order
@cite{chomsky-1995}

Verifies that Minimalist Merge derivations model SVO sentences from the
phenomena data, with phonological yields matching expected word order.
The transitive derivation is defined locally (chronological discipline:
Chomsky 1995 cannot import Adger 2003 where the canonical Minimalism
English-derivation lexicon now lives).
-/

namespace Chomsky1995

open Minimalist Minimalist.FromFragments

/-- "John sees Mary" as a Minimalist Merge derivation: *see*'s complement
    is *Mary* (`emR`), then *John* is added as specifier (`emL`). -/
def john_sees_mary : Derivation :=
  { initial := verbToSO Fragments.English.Predicates.Verbal.see 31
    steps   := [.emR (nounToSO Fragments.English.Nouns.mary 11),
                .emL (nounToSO Fragments.English.Nouns.john 10)] }

/-- The phonological yield of `john_sees_mary` matches one of the
    grammatical SVO sentences in `WordOrder.data`. This connects the
    Minimalist derivation (built by `emR` then `emL` over `verbToSO`/
    `nounToSO`) to the empirical word-order data. -/
theorem models_svo_word_order :
    let yield := String.intercalate " " john_sees_mary.final.phonYield
    Phenomena.WordOrder.data.pairs.any (·.grammatical == yield) := by
  decide

end Chomsky1995
