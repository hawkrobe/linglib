import Linglib.Theories.Semantics.Gradability.ClauseEmbedding

/-!
# English Copular Predicate Fragment

English clause-embedding adjectives that appear in copular constructions:
"be annoyed (that p)", "be right (that p)".

The adjective entries use `ClauseEmbeddingAdj` (cross-linguistic type);
the copular realization ("be" + adjective) is English-specific. The
`toVerbCore` helper constructs the combined form for bridge theorems
that need a uniform `VerbCore` interface.
-/

namespace Fragments.English.Predicates.Copular

open Semantics.Gradability (ClauseEmbeddingAdj)
open Core.Verbs

/-- "annoyed (that p)" — emotive factive clause-embedding adjective.
    @cite{degen-tonhauser-2021}, @cite{degen-tonhauser-2022}: canonically factive.
    Presupposes its complement via emotive semantics, not doxastic
    veridicality — hence `factivePresup` on the derived `VerbCore` is
    `false`, while `presupType = some .softTrigger`. -/
def beAnnoyed : ClauseEmbeddingAdj where
  adjForm := "annoyed"
  presupType := some .softTrigger

/-- "right (that p)" — veridical nonfactive clause-embedding adjective.
    @cite{degen-tonhauser-2021}, @cite{degen-tonhauser-2022}: veridical nonfactive.
    Entails its complement but does not presuppose it. -/
def beRight : ClauseEmbeddingAdj where
  adjForm := "right"

/-- "able (to VP)" — copular predicate with infinitival complement.
    @cite{karttunen-1971} §11: necessary-only (negation → ¬VP; affirmative ↛ VP).
    @cite{nadathur-2023}: one-way positive, **aspect-governed** — the actuality
    entailment arises in perfective contexts, not from the lexicon. Therefore
    NO `implicative`: the entailment is not unconditional like *manage*.

    Not modeled via `ClauseEmbeddingAdj` because `toVerbCore` doesn't transfer
    `controlType`. Constructed as a direct `VerbCore` instead. -/
def beAble : VerbCore where
  form := "be able"
  complementType := .infinitival
  controlType := .subjectControl

end Fragments.English.Predicates.Copular

-- ════════════════════════════════════════════════════
-- § English copular realization
-- ════════════════════════════════════════════════════

open Core.Verbs in
/-- Construct a `VerbCore` for an English copular predicate.
    The copula contributes "be"; the adjective contributes the semantics.
    This is English-specific — other languages realize clause-embedding
    adjectives differently (zero copula, verbal adjectives, etc.). -/
def Semantics.Gradability.ClauseEmbeddingAdj.toVerbCore
    (a : Semantics.Gradability.ClauseEmbeddingAdj) : VerbCore where
  form := "be " ++ a.adjForm
  complementType := a.complementType
  presupType := a.presupType
  attitude := a.attitude
  opaqueContext := a.opaqueContext
  complementSig := a.complementSig
