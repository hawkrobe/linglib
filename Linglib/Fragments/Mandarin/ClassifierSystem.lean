import Linglib.Typology.ClassifierSystem
import Linglib.Fragments.Mandarin.Classifiers

/-!
# Mandarin noun-categorization system
@cite{aikhenvald-2000} (typological schema); @cite{li-thompson-1981} §4.2.1
(Mandarin-specific empirical anchor)

Classifier-system metadata for Mandarin (ISO `cmn`). The lexical
classifier inventory itself lives in `Fragments/Mandarin/Classifiers.lean`;
this file aggregates that inventory into the typological-system summary
(`NounCategorizationSystem`) consumed by `Phenomena/Classifiers/Typology.lean`.

The per-language claims (obligatoriness with numerals + demonstratives,
default 个 gè, semantic-with-lexical-residue assignment) follow
@cite{li-thompson-1981} §4.2.1, pp. 104–112; @cite{aikhenvald-2000}
provides the typological schema (the `NounCategorizationSystem` field
ontology). @cite{li-thompson-1981} in turn cites @cite{chao-1968} §7.9 as
the canonical inventory source.
-/

namespace Mandarin

open Typology (collectSemantics) in
/-- Mandarin numeral classifier system: obligatory CL with numerals and
    demonstratives (@cite{li-thompson-1981} p. 104: "must occur with a
    number ... and/or a demonstrative"); default 个 gè (ibid. p. 112: 个
    "is gradually becoming the general classifier and replacing the more
    specialized ones"); preferred semantics derived from the lexical
    inventory. -/
def classifierSystem : Typology.NounCategorizationSystem :=
  { family := "Sino-Tibetan"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP, .attributiveNP]  -- CLF with numerals AND demonstratives (那本书) per L&T 1981 p. 104
  , assignment := .semantic
    -- Substrate gap: L&T 1981 p. 112 explicitly note "which nouns occur with
    -- which classifier must be memorized, though there is a slight amount of
    -- regularity with respect to the meanings of groups of nouns." This is
    -- semantic core + LEXICAL (not morphophonological) overlay; `.mixed`
    -- would over-claim morphophonological assignment, so `.semantic` remains
    -- the closest fit available in `AssignmentPrinciple`. A future enum
    -- enrichment (`.semanticWithLexicalIdiosyncrasy`) would capture this.
  , realizations := [.freeForm]
  , hasAgreement := false
  , inventorySize := Classifiers.allClassifiers.length
  , isObligatory := true
  , hasUnmarkedDefault := true  -- 个 gè is default per L&T 1981 p. 112
  , preferredSemantics := collectSemantics Classifiers.allClassifiers
  , source := "@cite{li-thompson-1981} §4.2.1 pp. 104–112; @cite{aikhenvald-2000} (schema)" }

end Mandarin
