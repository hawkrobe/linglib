import Linglib.Theories.Semantics.Lexical.Adjective.ClauseEmbedding

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

open Semantics.Lexical.Adjective (ClauseEmbeddingAdj)
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

end Fragments.English.Predicates.Copular

-- ════════════════════════════════════════════════════
-- § English copular realization
-- ════════════════════════════════════════════════════

open Core.Verbs in
/-- Construct a `VerbCore` for an English copular predicate.
    The copula contributes "be"; the adjective contributes the semantics.
    This is English-specific — other languages realize clause-embedding
    adjectives differently (zero copula, verbal adjectives, etc.). -/
def Semantics.Lexical.Adjective.ClauseEmbeddingAdj.toVerbCore
    (a : Semantics.Lexical.Adjective.ClauseEmbeddingAdj) : VerbCore where
  form := "be " ++ a.adjForm
  complementType := a.complementType
  presupType := a.presupType
  attitudeBuilder := a.attitudeBuilder
  opaqueContext := a.opaqueContext
  complementSig := a.complementSig
