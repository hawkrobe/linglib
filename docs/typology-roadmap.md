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

28 typology files across 2 Theories/ and 26 Phenomena/ locations, covering
~250 languages.

### Theories/ (formal universals)

| File | Content |
|------|---------|
| `Theories/Semantics/Modality/Typology.lean` | IFF and SAV universal type classes for modal systems |
| `Theories/Semantics/Events/RootTypology.lean` | Beavers et al. 2021 root semantic typology (PC vs result roots) |

### Phenomena/ (cross-linguistic data + bridges)

**Pre-existing** (from before the WALS systematization):

| File | Languages | Framework |
|------|-----------|-----------|
| `Modality/TypologyBridge.lean` | 10 | Nauze 2008; IFF/SAV verification |
| `Coordination/Typology.lean` | 17 | Haspelmath 2007 + Mitrovic & Sauerland 2014 |
| `Complementation/Typology.lean` | 7 | Noonan 2007; CTP classes |
| `Negation/CzechThreeWayNegBridge/TypologyBridge.lean` | 1 (deep) | Romero's PQ typology |
| `Anaphora/Typology.lean` | 11 | Patel-Grosz & Grosz 2017 |
| `Agreement/Typology.lean` | 12 | Cysouw 2009 |
| `Quantification/Typology.lean` | 3 | Quantifier inventories from Fragments |
| `Causatives/Typology.lean` | 6 | Song 1996; COMPACT/AND/PURP |
| `Causatives/Studies/BeaversEtAl2021.lean` | 88 (WALS) | Beavers et al. 2021 |
| `AuxiliaryVerbs/Typology.lean` | 5 | Anderson 2006; AVC inflection |
| `Questions/Typology.lean` | 5 | Dayal 2025; clause-typing, shiftiness |
| `Questions/TypologyBridge.lean` | 5 | Dayal 2025; Q-particle layers |
| `Morphology/Typology.lean` | 10 | Ackerman & Malouf 2013 |

**Tier 1 — WALS-based** (added 0.224.60):

| File | Lines | Languages | WALS Chapters |
|------|-------|-----------|---------------|
| `Tense/Typology.lean` | ~713 | 19 | Ch 65--69: aspect, past/future/perfect, TA affix position |
| `Negation/Typology.lean` | ~700 | 17 | Ch 112--115: morphemes, symmetry, neg indefinites |
| `Plurals/Typology.lean` | ~700 | 16 | Ch 33--36: coding, occurrence, pronoun plurality, associative |
| `Reference/Typology.lean` | ~1097 | 16 | Ch 37--38, 41--43: articles, demonstratives |
| `ArgumentStructure/Typology.lean` | ~700 | 18 | Ch 106--111: reciprocals, passives, antipassives, applicatives |

**Tier 2 — WALS-based** (added 0.224.65):

| File | Lines | Languages | WALS Chapters |
|------|-------|-----------|---------------|
| `Imperatives/Typology.lean` | 948 | 17 | Ch 70--73: morphological imperative, prohibitive, hortative, optative |
| `Modality/Typology.lean` | 813 | 17 | Ch 77--78: evidential systems and coding |
| `Polarity/Typology.lean` | 1146 | 17 | Ch 46: Haspelmath's indefinite pronoun implicational map |
| `Case/Typology.lean` | 818 | 16 | Ch 49--52: case count, differential marking, affix position, comitative |
| `Gradability/Typology.lean` | 875 | 18 | Ch 121: comparative constructions, degree words, superlatives |
| `WordOrder/Typology.lean` | 815 | 20 | Ch 81--83: basic SOV/SVO order + head-direction (Dryer/Gibson) |

**Tier 2b — New phenomenon directories** (added 0.224.65):

| File | Lines | Languages | WALS Chapters |
|------|-------|-----------|---------------|
| `Possession/Typology.lean` | ~700 | 15+ | Ch 58--59: obligatory possession, possessive classification |
| `Gender/Typology.lean` | ~700 | 15+ | Ch 30--32: gender count, sex-based systems, assignment |
| `Copulas/Typology.lean` | ~700 | 15+ | Ch 117--120: predicative adjectives/nouns, zero copula |

---

## Phenomena Directory Reorganization (0.224.65)

Applied alongside Tier 2 to ensure directories correspond to basic-level
linguist self-identification keywords.

### Merges (directories too narrow)

| Old | New | Rationale |
|-----|-----|-----------|
| `AdditiveParticles/` (4 files) | `Focus/AdditiveParticles/` | Focus-sensitive particles belong under Focus |
| `Attitudes/` (3 files) | `Complementation/Attitudes/` | Attitude reports are what complement clauses express |
| `Imprecision/` (8 files) | `Gradability/Imprecision/` | Vagueness/approximation is degree semantics |

### Breakouts (awkward placement)

| Old | New | Rationale |
|-----|-----|-----------|
| `Agreement/Case.lean` | `Case/Data.lean` | Case ≠ agreement; standalone phenomenon |
| `Agreement/CaseTypology.lean` | `Case/Typology.lean` | WALS Ch 49--52 data |

### New phenomenon directories

| Directory | Content | WALS Chapters |
|-----------|---------|---------------|
| `Case/` | Case marking data + typology | Ch 49--52 |
| `Possession/` | Possessive constructions typology | Ch 58--59 |
| `Gender/` | Gender/noun class systems | Ch 30--32 |
| `Copulas/` | Predication and copula typology | Ch 117--120 |

### Kept as-is (defensible despite quibbles)

- `AuxiliaryVerbs/` — word class, but syntacticians self-identify with it
- `Entailment/` — semantic test suite category, not a phenomenon per se
- `Morphology/` — level of analysis, but recognized keyword
- `Nonliteral/` — consolidated grab-bag (humor + metaphor + hyperbole)
- `Constructions/` — CxG/DG bridge files + resultatives; genuinely about constructions
- `Polysemy/` (2 files) — too small to act on; will grow or merge later

### Result

36 → 33 directories (via merges) → 36 directories (adding new phenomenon dirs).
Within the 30--40 range for basic-level categories.

---

## WALS Chapter Mapping

### Out of scope

- **A. Phonology (Ch 1--19)**: Consonant/vowel inventories, tone, stress.
  Linglib is semantics/pragmatics/syntax focused.
- **I. Lexicon (Ch 129--138)**: Body parts, color terms, tea. Semantic field
  typology, not compositional semantics.
- **J. Sign Languages (Ch 139--140)**: Not currently in scope.
- **K. Other (Ch 141--142)**: Writing systems, clicks.

### Completed

#### Tier 1 (done: 0.224.60)

- Tense/Aspect (Ch 65--69) → `Tense/Typology.lean`
- Negation (Ch 112--115) → `Negation/Typology.lean`
- Nominal Plurality (Ch 33--36) → `Plurals/Typology.lean`
- Articles and Demonstratives (Ch 37--38, 41--43) → `Reference/Typology.lean`
- Valence and Voice (Ch 106--111) → `ArgumentStructure/Typology.lean`

#### Tier 2 (done: 0.224.65)

- Imperatives and Mood (Ch 70--73) → `Imperatives/Typology.lean`
- Evidentiality (Ch 77--78) → `Modality/Typology.lean`
- Indefinite Pronouns (Ch 46) → `Polarity/Typology.lean`
- Case (Ch 49--52) → `Case/Typology.lean`
- Comparative Constructions (Ch 121) → `Gradability/Typology.lean`
- Basic Word Order (Ch 81--83) → `WordOrder/Typology.lean` (extended)

#### Tier 2b: New phenomenon directories (done: 0.224.65)

- Possession (Ch 58--59) → `Possession/Typology.lean`
- Gender (Ch 30--32) → `Gender/Typology.lean`
- Predication/Copulas (Ch 117--120) → `Copulas/Typology.lean`

### Tier 3: Remaining gaps

#### Alignment (WALS Ch 98--100)

Target: `ArgumentStructure/AlignmentTypology.lean` or new `Alignment/` dir

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

#### Numeral Classifiers (WALS Ch 53--56)

Target: `Numerals/Typology.lean`

Classifier systems, ordinal formation, distributive numerals. Current
Numerals/ work is pragmatics-focused (roundness, precision); this would
add the morphosyntactic dimension.

Key sources: Gil (2013), Aikhenvald (2000) *Classifiers*.

#### Morphological mechanisms (WALS B: Ch 20--29)

Target: extend `Morphology/Typology.lean`

Cross-cutting chapters on fusion, exponence, locus of marking (head vs
dependent), prefixing/suffixing, reduplication. These organize by
*mechanism* rather than *phenomenon*, which makes placement tricky.

Key sources: Bickel & Nichols (2013), Dryer (2013).

#### Subordination (WALS Ch 94--95, 122--123)

Target: `Complementation/Typology.lean` (extend) or `FillerGap/Typology.lean`

Relative clause position, adverbial subordination strategies, complementizer
placement. Overlaps with word order and relativization.

Key sources: Dryer (2013), Diessel (2013).

---

## Verified Universals

### Current

Typological universals formalized and verified in linglib:

| Universal | Source | File |
|-----------|--------|------|
| IFF (Independence of Force and Flavor) | Nauze 2008 | `Modality/TypologyBridge.lean` |
| SAV implies IFF | Steinert-Threlkeld et al. | `Theories/Semantics/Modality/Typology.lean` |
| Head-direction generalization | Dryer 1992 | `WordOrder/Typology.lean` |
| Greenberg Universal 1 (S before O) | Greenberg 1963 | `WordOrder/Typology.lean` |
| MU-additive generalization | Mitrovic & Sauerland | `Coordination/Typology.lean` |
| Person marking implicational hierarchy | Cysouw 2009 | `Agreement/Typology.lean` |
| Root semantic-morphosyntactic biconditional | Beavers et al. 2021 | `Theories/Semantics/Events/RootTypology.lean` |
| Haspelmath indefinite pronoun map (contiguity) | Haspelmath 1997 | `Polarity/Typology.lean` |
| Negative concord dominance | Haspelmath 2013 | `Negation/Typology.lean` |
| Bipartite negation implies asymmetry | Miestamo 2013 | `Negation/Typology.lean` |
| SOV + SVO majority | Dryer 2013 | `WordOrder/Typology.lean` |
| Prohibitive specialization | van der Auwera 2013 | `Imperatives/Typology.lean` |
| Case-rich languages are suffixal | Iggesen 2013 | `Case/Typology.lean` |
| Locational comparatives correlate with SOV | Stassen 2013 | `Gradability/Typology.lean` |

### To target

| Universal | Source | Target File |
|-----------|--------|-------------|
| Keenan-Comrie accessibility hierarchy | Keenan & Comrie 1977 | `FillerGap/Typology.lean` |
| Differential object marking hierarchy | Aissen 2003 | `Case/Typology.lean` (extend) |
| Corbett agreement target hierarchy | Corbett 1991 | `Gender/Typology.lean` (extend) |
| Ergative-absolutive implicational patterns | Dixon 1994 | `ArgumentStructure/AlignmentTypology.lean` |
| Numeral classifier hierarchy | Gil 2013 | `Numerals/Typology.lean` |
