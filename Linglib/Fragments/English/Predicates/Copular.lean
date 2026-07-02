import Linglib.Semantics.Degree.Gradability.ClauseEmbedding
import Linglib.Semantics.Verb.Basic

/-!
# English Copular Predicate Fragment

English clause-embedding adjectives that appear in copular constructions:
"be annoyed (that p)", "be right (that p)".

The adjective entries use `ClauseEmbeddingAdj` (cross-linguistic type);
the copular realization ("be" + adjective) is English-specific. The
`toVerb` helper constructs the combined form for bridge theorems
that need a uniform `Verb` interface.
-/

namespace English.Predicates.Copular

open Semantics.Gradability (ClauseEmbeddingAdj)
open Semantics.Lexical

/-- "annoyed (that p)" — emotive factive clause-embedding adjective.
    [degen-tonhauser-2021], [degen-tonhauser-2022]: canonically factive.
    Presupposes its complement via emotive semantics, not doxastic
    veridicality — hence `factivePresup` on the derived `Verb` is
    `false`, while `presupType = some .softTrigger`. -/
def beAnnoyed : ClauseEmbeddingAdj where
  adjForm := "annoyed"
  presupType := some .softTrigger

/-- "right (that p)" — veridical nonfactive clause-embedding adjective.
    [degen-tonhauser-2021], [degen-tonhauser-2022]: veridical nonfactive.
    Entails its complement but does not presuppose it. -/
def beRight : ClauseEmbeddingAdj where
  adjForm := "right"

/-- "able (to VP)" — copular predicate with infinitival complement.
    [karttunen-1971] §11: necessary-only (negation → ¬VP; affirmative ↛ VP).
    [nadathur-2023]: one-way positive, **aspect-governed** — the actuality
    entailment arises in perfective contexts, not from the lexicon. Therefore
    NO `implicative`: the entailment is not unconditional like *manage*.

    Not modeled via `ClauseEmbeddingAdj` because `toVerb` doesn't transfer
    `controlType`. Constructed as a direct `Verb` instead. -/
def beAble : Verb where
  form := "be able"
  frames := [Frame.infinitival]
  readings := [{ frame := Frame.infinitival, control := some .subjectControl }]

end English.Predicates.Copular

-- ════════════════════════════════════════════════════
-- § English copular realization
-- ════════════════════════════════════════════════════

open Semantics.Lexical in
/-- Construct a `Verb` for an English copular predicate.
    The copula contributes "be"; the adjective contributes the semantics.
    This is English-specific — other languages realize clause-embedding
    adjectives differently (zero copula, verbal adjectives, etc.). -/
def Semantics.Gradability.ClauseEmbeddingAdj.toVerb
    (a : Semantics.Gradability.ClauseEmbeddingAdj) : Verb where
  form := "be " ++ a.adjForm
  frames := [a.complementType.toFrame]
  presupType := a.presupType
  attitude := a.attitude
  opaqueContext := a.opaqueContext
  complementSig := a.complementSig
