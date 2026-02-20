# Typology Roadmap

A plan for systematizing cross-linguistic typological coverage in linglib,
anchored to the World Atlas of Language Structures (WALS; Haspelmath et al. 2005).

---

## Architectural Conventions

### The Phenomena/Theories split for typology

Typological files follow the same data-vs-theory split as everything else:

- **`Phenomena/X/Typology.lean`** — Cross-linguistic data: language inventories,
  WALS cross-tabulations, paradigm profiles. Theory-neutral. Does not import
  from `Theories/`.
- **`Phenomena/X/TypologyBridge.lean`** — Connects typological data to theoretical
  universals. Imports from both `Theories/` and `Phenomena/`.
- **`Theories/.../Typology.lean`** — Formal universals: type classes, predicates,
  implicational hierarchies. No language data.

The naming follows the general `X.lean` / `XBridge.lean` convention: raw data
in the unprefixed file, theory connections in the Bridge-suffixed file.
`Bridge.lean` without a prefix is shorthand for `DataBridge.lean` — it bridges
the primary `Data.lean`. `TypologyBridge.lean` bridges `Typology.lean`.

### Five-part anatomy of a phenomenon directory

Typology files are the fourth and fifth roles alongside Data, Bridge, Compare,
and Studies:

```
Phenomena/{Phenomenon}/
  Data.lean            -- empirical contrasts (judgments, corpus data)
  Bridge.lean          -- connects ONE theory to the data
  Compare.lean         -- connects TWO+ theories to the same data
  Typology.lean        -- cross-linguistic data (theory-neutral)
  TypologyBridge.lean  -- connects typological data to theoretical universals
  Studies/             -- paper-specific formalizations
```

Not every phenomenon directory needs all five. Most start with `Data.lean` and
grow the others as coverage expands.

---

## Current Coverage

14 typology files across 2 Theories/ and 12 Phenomena/ locations, covering
~150 languages.

### Theories/ (formal universals)

| File | Content |
|------|---------|
| `Theories/Semantics/Modality/Typology.lean` | IFF and SAV universal type classes for modal systems |
| `Theories/Semantics/Events/RootTypology.lean` | Beavers et al. 2021 root semantic typology (PC vs result roots) |

### Phenomena/ (cross-linguistic data + bridges)

| File | Languages | Framework |
|------|-----------|-----------|
| `Modality/TypologyBridge.lean` | 10 | Nauze 2008; IFF/SAV verification |
| `Coordination/Typology.lean` | 17 | Haspelmath 2007 + Mitrovic & Sauerland 2014 |
| `Complementation/Typology.lean` | 7 | Noonan 2007; CTP classes |
| `Negation/CzechThreeWayNeg/TypologyBridge.lean` | 1 (deep) | Romero's PQ typology |
| `Anaphora/PronounTypology.lean` | 11 | Patel-Grosz & Grosz 2017 |
| `Agreement/PersonMarkingTypology.lean` | 12 | Cysouw 2009 |
| `Quantification/Typology.lean` | 3 | Quantifier inventories from Fragments |
| `Causatives/Typology.lean` | 6 | Song 1996; COMPACT/AND/PURP |
| `Causatives/ChangeOfStateTypology.lean` | 88 (WALS) | Beavers et al. 2021 |
| `AuxiliaryVerbs/Typology.lean` | 5 | Anderson 2006; AVC inflection |
| `Questions/Typology.lean` | 5 | Dayal 2025; Q-particle typology |
| `WordOrder/Typology.lean` | ~2100 (WALS) | Dryer 1992/2013, Gibson 2025 |
| `Morphology/Typology.lean` | 10 | Ackerman & Malouf 2013 |

### Naming normalization needed

- `Anaphora/PronounTypology.lean` should be `Anaphora/Typology.lean` (the
  pronoun specificity belongs in the file content, not the filename)
- `Causatives/ChangeOfStateTypology.lean` should be merged into or split from
  `Causatives/Typology.lean` using a consistent convention

---

## WALS Chapter Mapping

### Out of scope

- **A. Phonology (Ch 1--19)**: Consonant/vowel inventories, tone, stress.
  Linglib is semantics/pragmatics/syntax focused.
- **I. Lexicon (Ch 129--138)**: Body parts, color terms, tea. Semantic field
  typology, not compositional semantics.
- **J. Sign Languages (Ch 139--140)**: Not currently in scope.
- **K. Other (Ch 141--142)**: Writing systems, clicks.

### Tier 1: Low effort, high value

Existing Phenomena/ directory with substantial infrastructure but no
`Typology.lean`. Adding one means systematizing cross-linguistic data that's
partly already present.

#### Tense/Aspect (WALS Ch 65--69)

Target: `Tense/Typology.lean`, `Aspect/Typology.lean`

WALS chapters:
- 65: Perfective/imperfective aspect
- 66: The past tense
- 67: The future tense
- 68: The perfect
- 69: Position of tense-aspect affixes

Existing infrastructure: 7 Tense files, 2 Aspect files,
`Theories/Semantics/Tense/` with evidential and compositional tense types.

What to formalize: Cross-linguistic tense/aspect inventories. Which languages
have grammaticalized perfective/imperfective? Which lack morphological tense?
How do tense-aspect systems correlate with evidentiality (Ch 77--78)?

Key sources: Dahl (1985) *Tense and Aspect Systems*, Bybee et al. (1994)
*The Evolution of Grammar*, Comrie (1976) *Aspect*.

#### Negation (WALS Ch 112--115)

Target: `Negation/Typology.lean`

WALS chapters:
- 112: Negative morphemes (particle, affix, auxiliary, verb)
- 113: Symmetric and asymmetric standard negation
- 114: Subtypes of asymmetric standard negation
- 115: Negative indefinite pronouns and predicate negation

Existing infrastructure: 10 Negation files including expletive negation, NPIs,
polarity builders, Czech three-way negation with Romero PQ mapping.

What to formalize: How negation is expressed (morpheme type), whether negation
triggers structural asymmetry, and how negative indefinites interact with
clausal negation (negative concord vs negative spread vs double negation).

Key sources: Miestamo (2005), Dryer (2013), Haspelmath (1997) on indefinites.

#### Nominal Plurality (WALS Ch 33--36)

Target: `Plurals/Typology.lean`

WALS chapters:
- 33: Coding of nominal plurality
- 34: Occurrence of nominal plurality
- 35: Plurality in independent personal pronouns
- 36: The associative plural

Existing infrastructure: 7 Plurals files.

What to formalize: How languages mark plurality (suffix, prefix, stem change,
clitic, word), obligatoriness of plural marking, associative plurals.
Connects to Link (1983) lattice semantics already in Theories/.

Key sources: Corbett (2000) *Number*, Dryer (2013).

#### Articles and Demonstratives (WALS Ch 37--38, 41--43)

Target: extend `Quantification/Typology.lean` (articles), `Reference/Typology.lean` (demonstratives)

WALS chapters:
- 37: Definite articles
- 38: Indefinite articles
- 41: Distance contrasts in demonstratives
- 42: Pronominal and adnominal demonstratives
- 43: Third-person pronouns and demonstratives

Existing infrastructure: `Quantification/Typology.lean` (3 languages),
`Reference/` (3 files), `Theories/Semantics/Lexical/Determiner/`.

What to formalize: Which languages have definite/indefinite articles (and
their diachronic sources), demonstrative distance systems (2-way, 3-way,
4+-way), and whether 3rd-person pronouns derive from demonstratives.

Key sources: Dryer (2013), Diessel (1999) *Demonstratives*.

#### Valence and Voice (WALS Ch 106--111)

Target: extend `Causatives/Typology.lean`, new `ArgumentStructure/Typology.lean`

WALS chapters:
- 106: Reciprocal constructions
- 107: Passive constructions
- 108: Antipassive constructions
- 109: Applicative constructions
- 110: Periphrastic causative constructions
- 111: Nonperiphrastic causative constructions

Existing infrastructure: `Causatives/Typology.lean` (Song's COMPACT/AND/PURP),
`Causatives/ChangeOfStateTypology.lean` (88-language WALS sample),
`ArgumentStructure/` (3 files).

What to formalize: Cross-linguistic voice alternations. Which languages have
morphological passives vs periphrastic? Antipassive as an ergative-language
phenomenon? Applicative as valence-increasing? Song's causative typology
already covers Ch 110--111; extend to 106--109.

Key sources: Siewierska (2013), Dixon & Aikhenvald (2000).

### Tier 2: Moderate effort, fills real gaps

#### Imperatives and Mood (WALS Ch 70--73)

Target: `Imperatives/Typology.lean`

WALS chapters:
- 70: The morphological imperative
- 71: The prohibitive
- 72: Imperative-hortative systems
- 73: The optative

Existing infrastructure: 1 file in Imperatives/.

What to formalize: How imperatives are formed (dedicated morphology vs
suppletive vs bare stem), whether prohibitives use the same negation as
declaratives, the hortative/jussive/optative landscape. Connects to
`Theories/Semantics/Mood/`.

Key sources: van der Auwera et al. (2013), Aikhenvald (2010) *Imperatives*.

#### Evidentiality (WALS Ch 77--78)

Target: `Modality/Typology.lean` (extend) or new phenomenon dir

WALS chapters:
- 77: Semantic distinctions of evidentiality
- 78: Coding of evidentiality

Existing infrastructure: `Theories/Semantics/Tense/` has evidential types,
`Modality/TypologyBridge.lean` has modal inventories.

What to formalize: How many evidential distinctions (direct, reported,
inferential, etc.), whether evidentiality is grammaticalized or lexical,
and the relationship to epistemic modality (Ch 75--76 overlap).

Key sources: Aikhenvald (2004) *Evidentiality*, de Haan (2013).

#### Indefinite Pronouns (WALS Ch 46)

Target: `Polarity/Typology.lean`

Haspelmath's (1997) indefinite pronoun map is one of the most celebrated
results in semantic typology. Nine function types (specific known, specific
unknown, irrealis, question, conditional, indirect negation, direct negation,
comparative, free choice) with an implicational map governing which functions
share a single form.

Existing infrastructure: 6 Polarity files, Theories/Semantics/Entailment/
with monotonicity and anti-additivity.

Key sources: Haspelmath (1997) *Indefinite Pronouns*.

#### Case (WALS Ch 49--52)

Target: `Agreement/Typology.lean` (extend) or new file

WALS chapters:
- 49: Number of cases
- 50: Asymmetrical case marking (differential object marking)
- 51: Position of case affixes
- 52: Comitatives and instrumentals

Existing infrastructure: `Agreement/PersonMarkingTypology.lean` (person
marking, not case per se).

What to formalize: Case inventories (from 0 to 10+), differential object
marking (definiteness/animacy splits), and the comitative-instrumental
syncretism pattern.

Key sources: Iggesen (2013), de Hoop & de Swart (2009).

#### Comparative Constructions (WALS Ch 121)

Target: `Gradability/Typology.lean`

How languages express comparison: particle comparatives ("taller than"),
exceed comparatives ("exceed X in height"), conjoined comparatives ("X is
tall, Y is short"), locational ("tall at X"), etc.

Existing infrastructure: 8 Gradability files, `Theories/Semantics/Lexical/Adjective/`
with Kennedy (2007) degree semantics.

Key sources: Stassen (2013), Beck et al. (2009).

#### Basic Word Order (WALS Ch 81--83)

Target: extend `WordOrder/Typology.lean`

The existing file has Dryer's head-direction cross-tabulations but not the
basic 6-way SOV/SVO/VSO/VOS/OVS/OSV classification. Adding the primary word
order distribution would be a natural complement.

Key sources: Dryer (2013), Greenberg (1963).

### Tier 3: New infrastructure needed

#### Alignment (WALS Ch 98--100)

Target: new `ArgumentStructure/Typology.lean` or `Alignment/` dir

The ergative/accusative/active alignment typology. Which argument of a
transitive verb patterns like the sole argument of an intransitive? Major
typological parameter with implications for case, agreement, and word order.

Key sources: Comrie (1978), Dixon (1994), Bickel & Nichols (2009).

#### Relativization (WALS Ch 122--123)

Target: `FillerGap/Typology.lean`

Relativization strategies (gap, resumptive pronoun, relative pronoun) and
which positions are accessible to relativization (Keenan & Comrie 1977
accessibility hierarchy).

Existing infrastructure: 6 FillerGap files (islands, gaps).

Key sources: Keenan & Comrie (1977), Comrie & Kuteva (2013).

#### Gender (WALS Ch 30--32)

Target: `Agreement/GenderTypology.lean` or extend `Agreement/Typology.lean`

Number of genders, sex-based vs semantic vs formal assignment, and the
relationship between gender and noun class systems.

Key sources: Corbett (1991) *Gender*, Corbett (2013).

#### Predication and Copulas (WALS Ch 117--120)

Target: new phenomenon dir or `Constructions/Typology.lean`

Predicative possession, predicative adjectives, nominal predication, zero
copulas. Largely uncharted in linglib.

Key sources: Stassen (2013), Dryer (2007).

#### Numeral Classifiers (WALS Ch 53--56)

Target: `Numerals/Typology.lean`

Classifier systems, ordinal formation, distributive numerals. Current
Numerals/ work is pragmatics-focused (roundness, precision); this would
add the morphosyntactic dimension.

Key sources: Gil (2013), Aikhenvald (2000) *Classifiers*.

---

## Suggested Sequencing

Ordered by infrastructure depth (how much existing work we can build on):

1. **Tense/Aspect** and **Negation** — two largest Phenomena directories
   with no typology file
2. **Plurals** and **Articles/Demonstratives** — nominal categories with
   existing files to extend
3. **Valence/Voice** — extends the already-strong Causatives typology
4. **Imperatives** and **Evidentiality** — fills gaps in the modality
   landscape
5. **Indefinite Pronouns** and **Comparatives** — connects to existing
   Polarity and Gradability work
6. **Basic Word Order** — small extension to existing file
7. **Alignment**, **Relativization**, **Gender** — requires more new
   infrastructure

---

## Verified Universals (Current)

Typological universals already formalized and verified in linglib:

| Universal | Source | File |
|-----------|--------|------|
| IFF (Independence of Force and Flavor) | Nauze 2008 | `Modality/TypologyBridge.lean` |
| SAV implies IFF | Steinert-Threlkeld et al. | `Theories/Semantics/Modality/Typology.lean` |
| Head-direction generalization | Dryer 1992 | `WordOrder/Typology.lean` |
| MU-additive generalization | Mitrovic & Sauerland | `Coordination/Typology.lean` |
| Person marking implicational hierarchy | Cysouw 2009 | `Agreement/PersonMarkingTypology.lean` |
| Root semantic-morphosyntactic biconditional | Beavers et al. 2021 | `Theories/Semantics/Events/RootTypology.lean` |

## Universals to Target

| Universal | Source | Target File |
|-----------|--------|-------------|
| Haspelmath indefinite pronoun map | Haspelmath 1997 | `Polarity/Typology.lean` |
| Keenan-Comrie accessibility hierarchy | Keenan & Comrie 1977 | `FillerGap/Typology.lean` |
| Greenberg word order universals | Greenberg 1963 | `WordOrder/Typology.lean` |
| Negative concord parameter | Zeijlstra 2004 | `Negation/Typology.lean` |
| Differential object marking hierarchy | Aissen 2003 | `Agreement/Typology.lean` |
| Complementation implicational hierarchy | Noonan 2007 | already in `Complementation/Typology.lean` |
