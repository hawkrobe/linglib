/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# [anand-hardt-mccloskey-2021] — The Santa Cruz sluicing data set

[anand-hardt-mccloskey-2021]

Distributional findings from the **Santa Cruz sluicing data set**, a 4,700-example
annotated corpus of naturally occurring English sluices drawn from the New York
Times subset of the Gigaword corpus, built by the Santa Cruz Ellipsis Project
(SCEP).

## Key Findings

1. **Sprouting dominates**: 65.5% of sluices have no overt correlate, overturning
   the theoretical literature's focus on merger (34.5%).

2. ***why* / Reason is the largest remnant type**, not a majority. *why* sluices
   are 53.8% of *sprouting* and 37.2% of *all* sluices; the Reason semantic type
   (Table 1) totals 1,752/4,700 (≈37.3%) — the single most frequent remnant type,
   but well short of a majority of all sluices. (The "53.8% of the total" figure
   holds only in the paper's footnote variant that folds in *why not* questions,
   which the authors caution "should probably not be analyzed in the same terms as
   sluicing.")

3. **Mismatches are systematic but bounded**: tense (129), modality (394), polarity
   (28), and new-words (71 clear cases) mismatches between antecedent and ellipsis
   site are attested. Voice and argument-structure (transitivity) mismatches have
   **zero attestations** — which the paper is careful to note is consistent with
   great rarity, not demonstrated impossibility.

4. **Embedding is the norm**: 72.4% of sluices are embedded (3,404), vs. 27.6% root
   (1,296).

The paper is a descriptive data-set report; it explicitly defers theoretical
interpretation to a companion paper. The Syntactic-Isomorphism-Condition bridge
theorems that relate this corpus to a formal-matching account therefore live in
`Studies/AnandHardtMcCloskey2025.lean`, not here (chronological grounding).
-/

namespace AnandHardtMcCloskey2021

/-! ### Antecedent–ellipsis mismatch dimensions (§5)

The data set documents which form/interpretation mismatches between antecedent and
ellipsis site are attested and which are absent. Attested mismatches challenge
strict syntactic-identity requirements; the absent ones (especially argument
structure) constrain theories of ellipsis licensing. These six dimensions are the
§5 mismatch taxonomy — distinct from the paper's broader annotation ontology
(antecedent/wh-remnant/paraphrase/correlate obligatory tags; the E-TYPE, IGNORE,
ISLAND, MISSINGANTE, QEMBEDDER global tags), which is not modelled here. -/

/-- Dimension along which antecedent and ellipsis site can differ (§5). -/
inductive MismatchDimension where
  | tense              -- §5.1: past/present mismatch (129 cases)
  | modality           -- §5.2: modal in ellipsis absent from antecedent (394 cases)
  | polarity           -- §5.3: negation added or removed (28 cases)
  | newWords           -- §5.4: novel lexical material in paraphrase (71 clear cases)
  | voice              -- §5.5: active/passive — 0 attestations
  | argumentStructure  -- §5.5: transitivity change — 0 attestations
  deriving DecidableEq, Repr

/-- Corpus count for each mismatch dimension (§5).

    The two zero counts (voice, argument structure) record *non-attestation in this
    4,700-example corpus*. The paper (§5.5) stresses this is consistent with the
    mismatches being very rare rather than impossible. -/
def MismatchDimension.corpusCount : MismatchDimension → Nat
  | .tense             => 129
  | .modality          => 394
  | .polarity          => 28
  | .newWords          => 71   -- clear cases after filtering (of ~160 NEW WORDS tags)
  | .voice             => 0
  | .argumentStructure => 0

/-! ### Remnant semantic-type distribution (Table 1)

The wh-remnant semantic-type distribution is a central descriptive contribution:
prior work (Ross 1969, Chung et al. 1995, Merchant 2001) focused on Entity remnants,
which are only 13.8% here, while Reason (typically *why*) and Degree dominate. -/

/-- Semantic type of the wh-remnant (Table 1). -/
inductive RemnantSemanticType where
  | reason          -- typically *why*
  | degree          -- *how much*, *how tall*, *how often*
  | entity          -- *who*, *what*
  | manner          -- *how*
  | temporal        -- *when*
  | locative        -- *where*
  | classificatory  -- *which* N
  | other
  deriving DecidableEq, Repr

/-- Count of embedded sluices of each remnant type (Table 1, EMBEDDED column). -/
def RemnantSemanticType.embeddedCount : RemnantSemanticType → Nat
  | .reason         => 1642
  | .degree         => 685
  | .entity         => 335
  | .manner         => 290
  | .temporal       => 253
  | .locative       => 137
  | .classificatory => 15
  | .other          => 47

/-- Count of root sluices of each remnant type (Table 1, ROOT column). -/
def RemnantSemanticType.rootCount : RemnantSemanticType → Nat
  | .reason         => 110
  | .degree         => 353
  | .entity         => 315
  | .manner         => 45
  | .temporal       => 9
  | .locative       => 20
  | .classificatory => 45
  | .other          => 399

/-- Total count of each remnant type (Table 1, TOTAL column), derived. -/
def RemnantSemanticType.totalCount (t : RemnantSemanticType) : Nat :=
  t.embeddedCount + t.rootCount

/-! ### Corpus summary statistics

Percentages are stored as integer tenths (655 = 65.5%) since every downstream fact
about them is an integer (in)equality; this preserves the paper's reported
precision without rational arithmetic. -/

/-- Summary statistics from the Santa Cruz sluicing data set. -/
structure CorpusSummary where
  totalSluices : Nat
  sproutingPctTenths : Nat    -- 655 = 65.5%
  mergerPctTenths : Nat       -- 345 = 34.5%
  rootPctTenths : Nat         -- 276 = 27.6%
  embeddedPctTenths : Nat     -- 724 = 72.4%
  antecedentlessCount : Nat   -- 167 well-formed antecedentless examples (3.6%)
  deriving Repr

/-- The data-set summary. -/
def dataSet : CorpusSummary where
  totalSluices := 4700
  sproutingPctTenths := 655
  mergerPctTenths := 345
  rootPctTenths := 276
  embeddedPctTenths := 724
  antecedentlessCount := 167

/-! ### Corpus distribution -/

/-- Sprouting is the majority sluice kind (overturning the literature's focus on
    merger). -/
theorem sprouting_is_majority_kind :
    dataSet.sproutingPctTenths > 500 := by decide

/-- Embedding is the majority context. -/
theorem embedded_is_majority_context :
    dataSet.embeddedPctTenths > 500 := by decide

/-- The reported sprouting/merger percentages are mutually consistent (sum to
    100%). -/
theorem sprouting_merger_exhaustive :
    dataSet.sproutingPctTenths + dataSet.mergerPctTenths = 1000 := by decide

/-- The reported root/embedded percentages are mutually consistent (sum to 100%). -/
theorem root_embedded_exhaustive :
    dataSet.rootPctTenths + dataSet.embeddedPctTenths = 1000 := by decide

/-- The Table 1 semantic-type totals partition the full corpus. -/
theorem semantic_type_totals_exhaustive :
    RemnantSemanticType.reason.totalCount
      + RemnantSemanticType.degree.totalCount
      + RemnantSemanticType.entity.totalCount
      + RemnantSemanticType.manner.totalCount
      + RemnantSemanticType.temporal.totalCount
      + RemnantSemanticType.locative.totalCount
      + RemnantSemanticType.classificatory.totalCount
      + RemnantSemanticType.other.totalCount
      = dataSet.totalSluices := by decide

/-- Reason (typically *why*) is the largest remnant semantic type. -/
theorem reason_largest_remnant_type :
    RemnantSemanticType.degree.totalCount < RemnantSemanticType.reason.totalCount ∧
    RemnantSemanticType.entity.totalCount < RemnantSemanticType.reason.totalCount ∧
    RemnantSemanticType.manner.totalCount < RemnantSemanticType.reason.totalCount ∧
    RemnantSemanticType.temporal.totalCount < RemnantSemanticType.reason.totalCount ∧
    RemnantSemanticType.locative.totalCount < RemnantSemanticType.reason.totalCount ∧
    RemnantSemanticType.classificatory.totalCount < RemnantSemanticType.reason.totalCount ∧
    RemnantSemanticType.other.totalCount < RemnantSemanticType.reason.totalCount := by
  decide

/-- Reason is the largest remnant type but NOT a majority of all sluices: at
    1,752/4,700 (≈37.3%), twice the Reason count still falls short of the total.
    This is the corrected form of the paper's "*why* dominates" finding — *why* is
    the single most frequent remnant type, not a majority. -/
theorem reason_not_majority :
    2 * RemnantSemanticType.reason.totalCount < dataSet.totalSluices := by decide

/-! ### Attested vs. absent mismatches -/

/-- Modality mismatches are the most frequent mismatch type. -/
theorem modality_most_frequent_mismatch :
    MismatchDimension.corpusCount .modality >
      MismatchDimension.corpusCount .tense ∧
    MismatchDimension.corpusCount .modality >
      MismatchDimension.corpusCount .polarity ∧
    MismatchDimension.corpusCount .modality >
      MismatchDimension.corpusCount .newWords :=
  ⟨by decide, by decide, by decide⟩

/-- Voice mismatches have zero attestations in the corpus (the paper notes this is
    consistent with rarity, not proven impossibility — §5.5). -/
theorem no_voice_mismatches :
    MismatchDimension.corpusCount .voice = 0 := rfl

/-- Argument-structure (transitivity) mismatches have zero attestations in the
    corpus (likewise consistent with rarity rather than impossibility — §5.5). -/
theorem no_argstructure_mismatches :
    MismatchDimension.corpusCount .argumentStructure = 0 := rfl

end AnandHardtMcCloskey2021
