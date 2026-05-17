import Linglib.Data.Examples.Schema

/-!
# @cite{musan-1995}: On the Temporal Interpretation of Noun Phrases
@cite{musan-1995}

Musan's dissertation establishes the **lifetime effects** diagnostic: past
tense with individual-level predicates implicates that the subject no longer
exists. The diagnostic minimal pair, ex (2a)/(2b) p. 11:

- (2a) *Gregory was silent* — stage-level predicate (`silent`); no lifetime
  implicature.
- (2b) *Gregory was from America* — individual-level predicate (`from
  America`); implicates Gregory is dead.

The implicature is not part of the truth conditions but a strong inference
arising from past tense + individual-level predicate composition. Central
to Musan's argument that NP temporal interpretation depends on the
predicate's lexical aspect.

## Schema gap

The lifetime-effects implicature is **not** captured by `ReichenbachFrame`
— the frame can encode past-tense locating (R < P), but the
stage-level/individual-level distinction and the pragmatic inference live
in a separate dimension (lexical aspect of the predicate + Gricean reasoning
over past-tense felicity). The empirical data is anchored in the
`LinguisticExample` JSON; no Reichenbach frame is provided here, since the
relevant content isn't reducible to S/P/R/E.

See `feedback_reichenbach_morph_vs_interp_conflation.md` for the broader
pattern: many tense-related phenomena are not faithfully modeled by
Reichenbach frames alone. -/

namespace Phenomena.TenseAspect.Studies.Musan1995

open Data.Examples (LinguisticExample)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/Musan1995.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def ex2a : LinguisticExample :=
  { id := "musan1995_ex2a"
    source := ⟨"musan-1995", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gregory was silent."
    discourseSegments := []
    glossedTokens := []
    translation := "Gregory was silent."
    context := "Past tense with a stage-level predicate (`silent`). Does NOT implicate that Gregory is dead — silence is a temporary state; the sentence is felicitous regardless of Gregory's current existence."
    judgment := .acceptable
    alternatives := []
    readings := [("no-lifetime-implicature (stage-level)", .acceptable)]
    paperFeatures := []
    comment := "Musan 1995 (dissertation) ex (2a) p. 11, Introduction. First half of the (2a)/(2b) minimal pair that establishes the lifetime-effects diagnostic: stage-level predicates do not implicate the subject's death."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "musan1995_ex2b"
    source := ⟨"musan-1995", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gregory was from America."
    discourseSegments := []
    glossedTokens := []
    translation := "Gregory was from America."
    context := "Past tense with an individual-level predicate (`from America` — a permanent origin/property). IMPLICATES that Gregory is dead. The lifetime effect: past tense + individual-level predicate → subject's lifetime has ended."
    judgment := .acceptable
    alternatives := []
    readings := [("lifetime-implicature (Gregory is dead)", .acceptable)]
    paperFeatures := []
    comment := "Musan 1995 ex (2b) p. 11. Second half of the minimal pair. The implicature is not part of the truth conditions but a strong inference from past tense + individual-level predicate composition. Central to the dissertation's argument that NP temporal interpretation depends on the predicate's lexical aspect."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex2a, ex2b]

end Examples
-- END GENERATED EXAMPLES

end Phenomena.TenseAspect.Studies.Musan1995
