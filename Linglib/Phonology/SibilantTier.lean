/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Subregular.Agree
import Linglib.Phonology.Subregular.OCP

/-!
# Sibilant-tier substrate

A small alphabet shared across linglib's sibilant-harmony formalisations
(Athabaskan, Berber, Chumash, …): three classes — *anterior* (alveolar
sibilants `[s, z, ts, dz, …]`), *posterior* (postalveolar `[ʃ, ʒ, tʃ, dʒ,
…]`), and *neutral* (everything else, off the harmony tier). Plus the
canonical on-tier predicate, the symmetric harmony grammar (Navajo,
Berber Tashlhiyt — both directions of disagreement forbidden), and the
asymmetric harmony grammars (Tsuut'ina — only one direction forbidden).

The audit chronology: Lambert (2026) §4.2 (Tsuut'ina) and Hansson (2010)
§2.4.1 (Navajo) independently stipulated their own three- and four-case
inductive types for the same primitive. The four-case Navajo alphabet
(`NSeg`) preserves a `neutralC` vs `vowel` distinction that no theorem
uses but that documents word-list examples; it is left in place as the
educational alphabet. The three-case substrate here is what Tsuut'ina
(and any future asymmetric-harmony paper) consumes directly.

## Main definitions

* `SibilantTierSeg` — the three-case shared alphabet.
* `SibilantTierSeg.onTier` — the harmony-tier predicate (drops `neutral`).
* `SibilantTierSeg.symmetricHarmony` — Navajo-style symmetric harmony
  TSL_2 grammar (forbids both `[anterior, posterior]` and `[posterior,
  anterior]` adjacencies on tier).
* `SibilantTierSeg.asymmetricHarmonyAntFirst` — Tsuut'ina-style
  asymmetric harmony TSL_2 grammar (forbids only `[anterior, posterior]`
  on tier; the reverse is permitted).
* `SibilantTierSeg.asymmetricHarmonyPostFirst` — the dual asymmetric
  grammar (forbids only `[posterior, anterior]`).

## References

* [cook-1978] (Tsuut'ina/Sarcee), [sapir-hoijer-1967] (Navajo);
  Heinz (2010) for the PT-vs-TSL lifting; Lambert (2026) §4.1-4.2 for
  the symmetric/asymmetric multitier classification.
-/

namespace Phonology.SibilantTier

open Phonology.Subregular
open Core.Computability.Subregular

-- ============================================================================
-- § 1. Alphabet and on-tier predicate
-- ============================================================================

/-- Three-class sibilant-tier alphabet: anterior (`s`-class), posterior
(`ʃ`-class), and neutral (off the harmony tier). The minimal alphabet
sufficient for sibilant-harmony formalisations; finer-grained alphabets
(e.g. Hansson 2010's `NSeg` distinguishing non-sibilant consonants from
vowels) are paper-specific elaborations that don't change the harmony
constraint. -/
inductive SibilantTierSeg | anterior | posterior | neutral
  deriving DecidableEq, Repr

/-- The harmony-tier predicate: only sibilants project onto the tier;
neutral material is transparent. -/
@[reducible] def SibilantTierSeg.onTier : SibilantTierSeg → Prop
  | .anterior | .posterior => True
  | .neutral => False

instance : DecidablePred SibilantTierSeg.onTier
  | .anterior | .posterior => isTrue trivial
  | .neutral => isFalse not_false

-- ============================================================================
-- § 2. Symmetric harmony (Navajo-style)
-- ============================================================================

/-- The symmetric sibilant-harmony TSL_2 grammar: any disagreement
between adjacent (on-tier) sibilants is forbidden. Identity-relation-
inverse specialisation of `TSLGrammar.agree` to the three-case alphabet.
Matches the [sapir-hoijer-1967] / [hansson-2010] Navajo
analysis and other Athabaskan symmetric-harmony languages. -/
def symmetricHarmony : TSLGrammar 2 SibilantTierSeg :=
  TSLGrammar.agree (α := SibilantTierSeg) SibilantTierSeg.onTier

-- ============================================================================
-- § 3. Asymmetric harmony (Tsuut'ina-style)
-- ============================================================================

/-- Forbidden-pair relation for "anterior preceding posterior is
forbidden on the tier" — the [cook-1978] Tsuut'ina pattern. -/
def antPostForbidden : SibilantTierSeg → SibilantTierSeg → Prop
  | .anterior, .posterior => True
  | _, _ => False

instance : DecidableRel antPostForbidden
  | .anterior, .posterior => isTrue trivial
  | .anterior, .anterior => isFalse not_false
  | .anterior, .neutral => isFalse not_false
  | .posterior, _ => isFalse not_false
  | .neutral, _ => isFalse not_false

/-- The asymmetric sibilant-harmony TSL_2 grammar with anterior-first
prohibition: an anterior sibilant immediately preceding a posterior
sibilant on the tier is forbidden, but the reverse adjacency
`[posterior, anterior]` is permitted. The [cook-1978]
[lambert-2026] §4.2 Tsuut'ina pattern. -/
def asymmetricHarmonyAntFirst : TSLGrammar 2 SibilantTierSeg :=
  TSLGrammar.ofForbiddenPairs (α := SibilantTierSeg)
    antPostForbidden SibilantTierSeg.onTier

/-- Dual: posterior preceding anterior is forbidden. The reverse
direction of `asymmetricHarmonyAntFirst`; provided for completeness so
either asymmetric direction can be selected by name. -/
def postAntForbidden : SibilantTierSeg → SibilantTierSeg → Prop
  | .posterior, .anterior => True
  | _, _ => False

instance : DecidableRel postAntForbidden
  | .posterior, .anterior => isTrue trivial
  | .posterior, .posterior => isFalse not_false
  | .posterior, .neutral => isFalse not_false
  | .anterior, _ => isFalse not_false
  | .neutral, _ => isFalse not_false

/-- Posterior-first asymmetric sibilant-harmony TSL_2 grammar. -/
def asymmetricHarmonyPostFirst : TSLGrammar 2 SibilantTierSeg :=
  TSLGrammar.ofForbiddenPairs (α := SibilantTierSeg)
    postAntForbidden SibilantTierSeg.onTier

-- ============================================================================
-- § 4. Symmetric/asymmetric inclusion
-- ============================================================================

/-- The symmetric harmony language is contained in each asymmetric
harmony language: anything ruled out by the asymmetric constraint
(which forbids only one direction) is also ruled out by the symmetric
one (which forbids both). Application of `lang_antitone_R`: forbidding
more pairs (`antPostForbidden ⊆ (· ≠ ·)`) shrinks the language. -/
theorem symmetricHarmony_lang_subset_asymAntFirst :
    symmetricHarmony.lang ≤ asymmetricHarmonyAntFirst.lang :=
  lang_antitone_R (R := antPostForbidden) (R' := (· ≠ ·))
    (fun a b h => by
      cases a <;> cases b <;> simp_all [antPostForbidden])
    SibilantTierSeg.onTier

/-- Dual inclusion. -/
theorem symmetricHarmony_lang_subset_asymPostFirst :
    symmetricHarmony.lang ≤ asymmetricHarmonyPostFirst.lang :=
  lang_antitone_R (R := postAntForbidden) (R' := (· ≠ ·))
    (fun a b h => by
      cases a <;> cases b <;> simp_all [postAntForbidden])
    SibilantTierSeg.onTier

end Phonology.SibilantTier
