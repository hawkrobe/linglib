# Phenomena Directory: Audit & Conventions

## What Phenomena/ is for

Phenomena/ houses **empirical contrasts** — the data that theories must explain.
A file belongs here if deleting every theory from LingLib would leave it
meaningful. It records *what happens* in natural language, not *why*.

The critical architectural invariant: **Data files never import from Theories/.**
Bridge files connect data to theories and are the only Phenomena files that may
import from Theories/.

---

## Current problems

### 1. 86 theory-specific files in Phenomena/{Syntax,Semantics,Pragmatics}

The earlier migration left 86 files that belong in Theories/ still sitting
under Phenomena/. These are framework-specific implementations (CCG parsers,
RSA implementations, Minimalist formal proofs) that happen to be co-located
with the phenomena they analyze. **This is the highest-priority migration.**

### 2. Inconsistent file naming

Four naming conventions coexist with no clear rules:

| Pattern | Count | Example |
|---------|-------|---------|
| `Data.lean` | 18 | `Causatives/Data.lean` |
| `Basic.lean` | 15 | `Modality/Basic.lean` |
| `*Bridge.lean` | 35 | `ThickThinBridge.lean` |
| Descriptive name | ~134 | `DonkeyAnaphora.lean`, `FreeChoice.lean` |

Problems:
- `Data.lean` and `Basic.lean` are used interchangeably for the same role
  (theory-neutral empirical data)
- `Basic.lean` in Phenomena sometimes means "re-export hub" (Modality/Basic.lean
  just imports other files), sometimes means "core data" (Negation/Basic.lean
  defines negation contrasts)
- Bridge naming is inconsistent: `Bridge.lean` vs `XBridge.lean` vs
  `XYZBridge.lean`

### 3. Mislabeled files

- `Modality/ConditionalModality/Data.lean` imports `Theories.Semantics.Modality.Kratzer`
  — it's a bridge, not data
- `Quantification/Bridge.lean` does NOT import Theories — it's actually data
- `Tense/Studies/Cumming2026/Bridge.lean` imports only Fragments, not Theories
- `Modality/PracticalReasoning.lean` and `Modality/InformationalBackgrounds.lean`
  import Theories but have no "Bridge" marker

### 4. Author-named files outside Studies/

13 author+year files sit directly in phenomenon directories rather than in
`Studies/`:

```
FillerGap/Sag2010.lean
Modality/ModalConcord/LiuRotter2025.lean
Numerals/ClausWalch2024.lean
Numerals/HuangSpelkeSnedeker2013.lean
Numerals/WoodinEtAl2024.lean
Polarity/VonFintel1999.lean
WordOrder/FutrellEtAl2020.lean
WordOrder/HahnDegenFutrell2021.lean
...
```

These should be in `Studies/` for consistency — author names signal
"specific empirical contribution" not "general phenomenon description."

### 5. Inconsistent sub-phenomenon structure

Some phenomena have subdirectories for specific sub-phenomena, others don't:

```
Modality/ConditionalModality/    # sub-phenomenon gets its own dir
Modality/ModalConcord/           # sub-phenomenon gets its own dir
Modality/FreeChoice.lean         # sub-phenomenon stays as file
Modality/ActualityInferences.lean # sub-phenomenon stays as file
```

No clear threshold for when a sub-phenomenon earns a directory.

---

## Proposed conventions

### Convention 1: Three file roles, mechanically distinguishable

Every file in Phenomena/ has exactly one of three roles, determined by a
simple import test:

| Role | Naming | Import rule | Purpose |
|------|--------|-------------|---------|
| **Data** | `Data.lean` or descriptive | Imports only Core/, Fragments/, other Phenomena/ | Theory-neutral empirical contrasts |
| **Bridge** | `*Bridge.lean` suffix | Imports from Theories/ | Connects data to a specific theory |
| **Hub** | `_.lean` (directory name) | Imports only sibling files | Re-export convenience; no content |

The mechanical test: `grep "import Linglib.Theories" file.lean`. If yes →
bridge. If no → data (or hub).

### Convention 2: Bridge naming uses the `*Bridge.lean` suffix

The rule: if and only if a file imports from Theories/, its name ends in
`Bridge`. The name before "Bridge" describes what the file *does*, not
which theory it uses. The imports tell you the theory.

```
ThickThinBridge.lean            — about thick/thin causation
StructuralCausationBridge.lean  — about structural causation
TypologyBridge.lean             — about modal typology
GermanModalsBridge.lean         — about German modals
IntensifiersBridge.lean         — about intensifiers
DiagnosticsBridge.lean          — about aspectual diagnostics
EvaluativityBridge.lean         — about evaluativity
```

The `Bridge` suffix:
- Makes the data/bridge distinction visible at a glance
- Follows standard Lean naming (no underscores in module names;
  mathlib avoids them, and `import Linglib.Phenomena.Modality.Bridge_Kratzer`
  reads oddly)
- Multiple bridges per phenomenon directory is expected and good — it means
  multiple theories analyze the same data

### Convention 3: Retire `Basic.lean` in Phenomena/

`Basic.lean` is ambiguous between "core data" and "re-export hub."
Replace with:

- If it defines data → rename to `Data.lean` (the canonical name for
  theory-neutral empirical content)
- If it just re-exports → rename to the directory name (Lean convention
  for module hubs, e.g., `Modality.lean` re-exports `Modality/`)

### Convention 4: Studies/ for paper-specific contributions

Any file organized around a specific paper (author+year) goes in `Studies/`:

```
Phenomena/Numerals/
  Data.lean                            # General numeral contrasts
  Embedding.lean                       # Embedded numeral patterns
  Studies/
    ClausWalch2024.lean                # Data from Claus & Walch 2024
    HuangSpelkeSnedeker2013.lean       # Data from Huang et al. 2013
    WoodinEtAl2024.lean                # Data from Woodin et al. 2024
    Snyder2026/
      Data.lean                        # Snyder 2026 experimental data
      Snyder2026RSABridge.lean         # RSA analysis of Snyder data
```

Rules for `Studies/`:
- Files named `AuthorYear.lean` (no Bridge suffix) → pure data from that paper
- Files named `*Bridge.lean` within a study directory → theory applied to
  that paper's data specifically
- A study gets its own subdirectory only when it has both `Data.lean` and
  one or more `*Bridge.lean` files (otherwise it's a single file)

Files describing general phenomena (not tied to one paper) stay at the
phenomenon level: `DonkeyAnaphora.lean`, `FreeChoice.lean`, etc.

### Convention 5: Sub-phenomena earn directories at 4+ files

Same threshold as everywhere else in LingLib. A sub-phenomenon directory
is justified when it has 4+ files (data + bridges combined).

Current status:
- `ModalConcord/` — 4 files (Data, LiuRotter2025, LiuRotter2025Bridge,
  Bridge) → keeps directory, but LiuRotter files should move to Studies/
- `ConditionalModality/` — 2 files → flatten
- `Islands/` — 2 files → flatten (but will likely grow)
- `CzechThreeWayNeg/` — 2 files → flatten
- `MeasurePhrases/` — 2 files → flatten
- `Resultatives/` — 1 file → flatten

Exception: `Islands/` may stay if growth is imminent, since island
constraints are a substantial sub-domain of filler-gap research.

### Convention 6: No theory-level grouping in Phenomena/

`Phenomena/Syntax/`, `Phenomena/Semantics/`, `Phenomena/Pragmatics/` must
be dissolved. Phenomena are organized by *what empirical domain they
describe*, not by which level of theory analyzes them. Scalar implicatures
are `Phenomena/ScalarImplicatures/`, not `Phenomena/Pragmatics/ScalarImplicatures/`.

This is already mostly true for the 202 well-organized files. The 86
misplaced theory files are a legacy migration problem, not a convention
question.

---

## Data.lean and hub files

If a phenomenon has a single core data file, call it `Data.lean`. When
bridge files import empirical content, `Data.lean` is the predictable
target.

If the data is naturally split by sub-phenomenon
(`Anaphora/DonkeyAnaphora.lean`, `Anaphora/CrossSentential.lean`), don't
force a hub — let each file stand on its own. Consumers import the
specific file they need. Most phenomenon directories are small enough
that a re-export hub adds no value.

A hub is warranted only when a directory is large enough that downstream
files routinely need "all the data" and listing 5+ imports is painful.
In that case, use the Lean directory-name convention (`Anaphora.lean`
re-exports `Anaphora/*`).

---

## Canonical directory structure (template)

```
Phenomena/
  ExamplePhenomenon/
    Data.lean                      # Core empirical contrasts (NO Theory imports)
    SubPhenomenonA.lean            # Specific data (NO Theory imports)
    SubPhenomenonB.lean            # Specific data (NO Theory imports)
    Typology.lean                  # Cross-linguistic variation (NO Theory imports)
    TheoryXBridge.lean             # Connects data to Theory X
    TheoryYBridge.lean             # Connects data to Theory Y
    Studies/
      AuthorYear.lean              # Paper-specific data (single file)
      BigStudy2025/
        Data.lean                  # Paper-specific data (multi-file)
        RSABridge.lean             # Theory X applied to this study
```

---

## Migration priorities

### Priority 1: Migrate 86 theory files from Phenomena/{Syntax,Semantics,Pragmatics}

The biggest structural violation. 86 framework-specific files sitting under
`Phenomena/Syntax/`, `Phenomena/Semantics/`, `Phenomena/Pragmatics/` need
to move into the appropriate phenomenon directories as bridge files, or
into `Theories/` if they contain no empirical content. This connects
directly to the Theories reorganization.

### Priority 2: Fix mislabeled files

| File | Problem | Action |
|------|---------|--------|
| `Modality/ConditionalModality/Data.lean` | Imports Theories | Rename to `KratzerBridge.lean` |
| `Quantification/Bridge.lean` | No Theory imports | Rename to `Data.lean` or merge into existing Data |
| `Modality/PracticalReasoning.lean` | Imports Theories, no Bridge marker | Rename to `PracticalReasoningBridge.lean` |
| `Modality/InformationalBackgrounds.lean` | Imports Theories, no Bridge marker | Rename to `InformationalBackgroundsBridge.lean` |
| `Tense/Studies/Cumming2026/Bridge.lean` | Only imports Fragments | Rename to `Data.lean` |

### Priority 3: Move author-named files into Studies/

13 files with author+year names sitting outside `Studies/` directories.
Mechanical move, no content changes.

### Priority 4: Rename Basic.lean → Data.lean

15 files. Check each: if it defines empirical data, rename to `Data.lean`.
If it's a re-export hub, rename to directory-name convention.

### Priority 5: Flatten small sub-phenomenon directories

Dissolve directories under the 4-file threshold:
- `ConditionalModality/` → flatten into `Modality/`
- `CzechThreeWayNeg/` → flatten into `Negation/`
- `MeasurePhrases/` → flatten into `Quantification/`
- `Resultatives/` → flatten into `Constructions/`

---

## Validation checklist for new files

Before adding a file to Phenomena/:

1. **Does it import from Theories/?**
   - Yes → it's a Bridge file. Name it `*Bridge.lean` (suffix)
   - No → it's a Data file
2. **Is it organized around a specific paper?**
   - Yes → put it in `Studies/`
   - No → put it at the phenomenon level
3. **Does deleting all Theories/ leave this file meaningful?**
   - Yes → correct placement
   - No → it probably belongs in Theories/, not Phenomena/
4. **Is the phenomenon directory getting large?**
   - 10+ files → consider splitting into sub-phenomenon directories
   - Sub-phenomenon has 4+ files → earns its own directory
