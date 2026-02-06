/-!
# Cross-Linguistic Causative Typology (Song 1996)

Song's typology of causative constructions, orthogonal to the
force-dynamic builder classification. This module classifies how
causative meaning is **expressed** (morphosyntactic packaging), while
`CausativeBuilder` classifies what causative meaning **is** (force-dynamic
mechanism).

## Key Typology (§5.1-5.3)

| Type | Structure | Implicative? | Example |
|------|-----------|-------------|---------|
| COMPACT | Vcause ⊕ Veffect fused | Yes | English *kill*, Turkish *-dür* |
| AND | Two clauses, sequential | Yes | Vata *le* |
| PURP | Two clauses, purposive | No | Korean *-ke ha-* |

The COMPACT type subsumes both lexical causatives (English *kill*) and
morphological causatives (Turkish *-dür*, Japanese *-ase*, French *faire*).

## Cognitive Structure (§5.3)

All causative events involve: GOAL → EVENT → RESULT

- AND type highlights: EVENT + RESULT (factual sequencing)
- PURP type highlights: GOAL + EVENT (purposive, non-implicative)
- COMPACT type: entire sequence collapsed into single predicate

## References

- Song, J. J. (1996). Causatives and Causation: A Universal-Typological
  Perspective. Longman.
-/

namespace Phenomena.Causatives.Typology

/-- Morphosyntactic type of causative construction.

    This is orthogonal to the force-dynamic builder: a `.make` builder
    can be realized as COMPACT (English *make*), AND, or PURP depending
    on the language.

    - `compact`: Cause and effect fused into a single predicate.
      Includes lexical (*kill*) and morphological (*-dür*, *-ase*) causatives.
    - `and_`: Two clauses joined sequentially. Effect clause is factual.
    - `purp`: Two clauses, with purposive semantics. Effect clause is
      non-implicative (not entailed to have occurred). -/
inductive CausativeConstructionType where
  /-- Cause + effect fused (lexical: *kill*; morphological: Turkish *-dür*) -/
  | compact
  /-- Two clauses, sequential (Vata *le*; effect is factual) -/
  | and_
  /-- Two clauses, purposive (Korean *-ke ha-*; effect not entailed) -/
  | purp
  deriving DecidableEq, Repr, BEq

/-- Whether a causative construction type is implicative.

    Implicative = the cause clause entails the effect clause.

    - COMPACT: Yes — *kill* entails death occurred
    - AND: Yes — sequential structure implies effect is factual
    - PURP: No — purposive structure leaves effect open -/
def CausativeConstructionType.isImplicative : CausativeConstructionType → Bool
  | .compact => true
  | .and_ => true
  | .purp => false

/-- Morphosyntactic realization of the causative morpheme.

    Within COMPACT causatives, the causal element can be realized as:
    - A bound morpheme (Turkish *-dür*, Japanese *-ase*)
    - A free morpheme forming a tight unit (French *faire*)
    - A lexical fusion with no separable morpheme (English *kill*) -/
inductive CausativeMorphology where
  /-- Bound morpheme (affix): Turkish *-dür*, Japanese *-(s)ase* -/
  | suffix
  /-- Free morpheme forming tight unit: French *faire* -/
  | freeMorpheme
  /-- No separable morpheme: English *kill* (lexical causative) -/
  | lexical
  deriving DecidableEq, Repr, BEq

/-- A cross-linguistic causative construction datum. -/
structure CausativeConstructionDatum where
  /-- Language name -/
  language : String
  /-- Surface form or morpheme -/
  form : String
  /-- Construction type in Song's typology -/
  constructionType : CausativeConstructionType
  /-- Morphological realization (for compact types) -/
  morphology : Option CausativeMorphology := none
  /-- Gloss / translation -/
  gloss : String := ""
  deriving Repr, BEq

/-! ## Cross-linguistic data -/

/-- English *kill* — lexical COMPACT causative (kill = cause-to-die) -/
def englishKill : CausativeConstructionDatum :=
  { language := "English"
  , form := "kill"
  , constructionType := .compact
  , morphology := some .lexical
  , gloss := "cause to die (lexical)" }

/-- Turkish *-dür* — morphological COMPACT causative suffix -/
def turkishDur : CausativeConstructionDatum :=
  { language := "Turkish"
  , form := "-dür"
  , constructionType := .compact
  , morphology := some .suffix
  , gloss := "öl-dür 'die-CAUS = kill'" }

/-- Japanese *-(s)ase* — morphological COMPACT causative suffix -/
def japaneseAse : CausativeConstructionDatum :=
  { language := "Japanese"
  , form := "-(s)ase"
  , constructionType := .compact
  , morphology := some .suffix
  , gloss := "ik-ase 'go-CAUS = make go'" }

/-- French *faire* — COMPACT causative with free morpheme -/
def frenchFaire : CausativeConstructionDatum :=
  { language := "French"
  , form := "faire"
  , constructionType := .compact
  , morphology := some .freeMorpheme
  , gloss := "faire lire 'make read'" }

/-- Korean *-ke ha-* — PURP-type causative (non-implicative) -/
def koreanKeHa : CausativeConstructionDatum :=
  { language := "Korean"
  , form := "-ke ha-"
  , constructionType := .purp
  , gloss := "wus-ke ha- 'smile-PURP do = cause to smile'" }

/-- Vata *le* — AND-type causative (sequential, implicative) -/
def vataLe : CausativeConstructionDatum :=
  { language := "Vata"
  , form := "le"
  , constructionType := .and_
  , gloss := "le ... 'and' (overt coordinator)" }

def allData : List CausativeConstructionDatum :=
  [englishKill, turkishDur, japaneseAse, frenchFaire, koreanKeHa, vataLe]

/-! ## Implicativity theorems -/

/-- COMPACT causatives are implicative. -/
theorem compact_is_implicative :
    CausativeConstructionType.compact.isImplicative = true := rfl

/-- AND-type causatives are implicative. -/
theorem and_is_implicative :
    CausativeConstructionType.and_.isImplicative = true := rfl

/-- PURP-type causatives are NOT implicative. -/
theorem purp_not_implicative :
    CausativeConstructionType.purp.isImplicative = false := rfl

/-- Per-datum verification: each datum's implicativity matches its type. -/
theorem englishKill_implicative :
    englishKill.constructionType.isImplicative = true := rfl
theorem turkishDur_implicative :
    turkishDur.constructionType.isImplicative = true := rfl
theorem japaneseAse_implicative :
    japaneseAse.constructionType.isImplicative = true := rfl
theorem frenchFaire_implicative :
    frenchFaire.constructionType.isImplicative = true := rfl
theorem koreanKeHa_not_implicative :
    koreanKeHa.constructionType.isImplicative = false := rfl
theorem vataLe_implicative :
    vataLe.constructionType.isImplicative = true := rfl

end Phenomena.Causatives.Typology
