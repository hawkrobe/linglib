import Linglib.Core.Word

/-!
# Anand, Hardt & McCloskey (2021) — Corpus Data

@cite{anand-hardt-mccloskey-2021}

Distributional findings from the Santa Cruz Sluicing Corpus (SCSS),
a 4,700-example annotated data set of naturally occurring English sluices.

## Key Findings

1. **Sprouting dominates**: 65.5% of sluices have no overt correlate,
   overturning the theoretical literature's focus on merger.

2. **Why dominates**: *why* accounts for 53.8% of all sluices (2,529/4,700).

3. **Mismatches are systematic**: Tense (129), modality (394), and polarity
   (28) mismatches between antecedent and ellipsis site are attested.
   Argument structure mismatches (voice, transitivity) are entirely absent.

4. **Embedding is the norm**: 72.4% of sluices are embedded.

## References

- Anand, P., Hardt, D. & McCloskey, J. (2021). The Santa Cruz sluicing
  data set. *Language* 97(1): e68–e88.
-/

namespace Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021.Data

-- ============================================================================
-- § 1: Sluice Classification
-- ============================================================================

/-- Whether a sluice has an overt correlate in the antecedent.

    Merger: "Someone₁ left, but I don't know who₁" — *someone* is the correlate.
    Sprouting: "John left, but I don't know why" — no overt correlate. -/
inductive SluiceKind where
  | merger    -- Overt correlate (inner antecedent) present
  | sprouting -- No overt correlate; wh-phrase corresponds to an implicit argument
  deriving DecidableEq, BEq, Repr

/-- Embedding context of a sluice. -/
inductive EmbeddingContext where
  | root     -- Matrix clause: "Who did she see?"
  | embedded -- Subordinate: "I don't know who she saw"
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Antecedent–Ellipsis Mismatches (§5)
-- ============================================================================

/-- Dimension along which antecedent and ellipsis site can differ.

    The SCSS documents which mismatches are attested and which are absent.
    Attested mismatches challenge strict syntactic identity requirements;
    absent mismatches (especially argument structure) constrain theories
    of ellipsis licensing. -/
inductive MismatchDimension where
  | tense              -- §5.1: Past/present mismatch (129 cases)
  | modality           -- §5.2: Modal in ellipsis absent from antecedent (394 cases)
  | polarity           -- §5.3: Negation added or removed (28 cases)
  | newWords           -- §5.4: Novel lexical material in paraphrase (71 clear cases)
  | voice              -- §5.5: Active/passive — NOT ATTESTED
  | argumentStructure  -- §5.5: Transitivity change — NOT ATTESTED
  deriving DecidableEq, BEq, Repr

/-- Whether a mismatch dimension is attested in the corpus. -/
def MismatchDimension.attested : MismatchDimension → Bool
  | .tense             => true
  | .modality          => true
  | .polarity          => true
  | .newWords          => true
  | .voice             => false
  | .argumentStructure => false

/-- Corpus count for each mismatch dimension (SCSS §5). -/
def MismatchDimension.corpusCount : MismatchDimension → Nat
  | .tense             => 129
  | .modality          => 394
  | .polarity          => 28
  | .newWords          => 71   -- clear cases after filtering (§5.4)
  | .voice             => 0
  | .argumentStructure => 0

-- ============================================================================
-- § 3: Polarity Mismatch Subtypes (§5.3)
-- ============================================================================

/-- Discourse contexts licensing polarity reversal under sluicing (§5.3).

    Following Kroll (2016, 2019): polarity reversal is pragmatically
    conditioned — it requires the discourse context to make the reversed
    polarity salient. -/
inductive PolarityReversalContext where
  | negRaising       -- "I don't think she'll pass, but I don't know why" (ex. 33)
  | withoutAdjunct   -- "without" phrases adjoin to VP (ex. 32)
  | disjunction      -- Disjunction/doubt/remember (ex. 34)
  | qudPartialAnswer -- Negative partial answer to a superordinate QUD (ex. 35)
  | howEmbedded      -- "how" under know/learn/see — negation absent from antecedent
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 4: New Words Subtypes (§5.4)
-- ============================================================================

/-- Subtypes of novel lexical material in sluice paraphrases (§5.4).

    These are cases where the paraphrase of the elided material contains
    words not present in the antecedent clause. -/
inductive NewWordsSubtype where
  | copularClause        -- Nominal antecedent → copular clause (46 cases)
  | existentialInterp    -- Existential interpretation in ellipsis site (17 cases)
  | strandedPreposition  -- Preposition in ellipsis with no antecedent source (17 cases)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 5: Corpus Summary Statistics
-- ============================================================================

/-- Summary statistics from the SCSS.

    Percentages are stored as tenths (655 = 65.5%) to avoid rationals
    while preserving the paper's reported precision. -/
structure CorpusSummary where
  totalSluices : Nat
  sproutingPctTenths : Nat    -- 655 = 65.5%
  mergerPctTenths : Nat       -- 345 = 34.5%
  rootPctTenths : Nat         -- 276 = 27.6%
  embeddedPctTenths : Nat     -- 724 = 72.4%
  whyCount : Nat
  whyPctTenths : Nat          -- 538 = 53.8%
  antecedentlessCount : Nat
  deriving Repr

/-- The SCSS corpus summary (Anand et al. 2021). -/
def scss : CorpusSummary where
  totalSluices := 4700
  sproutingPctTenths := 655
  mergerPctTenths := 345
  rootPctTenths := 276
  embeddedPctTenths := 724
  whyCount := 2529
  whyPctTenths := 538
  antecedentlessCount := 167

-- ============================================================================
-- § 6: Per-Datum Verification
-- ============================================================================

/-- Sprouting + merger = 100%. -/
theorem sprouting_merger_exhaustive :
    scss.sproutingPctTenths + scss.mergerPctTenths = 1000 := by native_decide

/-- Root + embedded = 100%. -/
theorem root_embedded_exhaustive :
    scss.rootPctTenths + scss.embeddedPctTenths = 1000 := by native_decide

/-- Sprouting is the majority kind. -/
theorem sprouting_majority :
    scss.sproutingPctTenths > scss.mergerPctTenths := by native_decide

/-- *Why* is the majority wh-remnant type. -/
theorem why_majority :
    scss.whyPctTenths > 500 := by native_decide

/-- Embedding is the majority context. -/
theorem embedded_majority :
    scss.embeddedPctTenths > scss.rootPctTenths := by native_decide

/-- Modality mismatches are the most frequent mismatch type. -/
theorem modality_most_frequent_mismatch :
    MismatchDimension.corpusCount .modality >
    MismatchDimension.corpusCount .tense ∧
    MismatchDimension.corpusCount .modality >
    MismatchDimension.corpusCount .polarity ∧
    MismatchDimension.corpusCount .modality >
    MismatchDimension.corpusCount .newWords :=
  ⟨by native_decide, by native_decide, by native_decide⟩

/-- Voice mismatches are absent. -/
theorem no_voice_mismatches :
    MismatchDimension.corpusCount .voice = 0 := rfl

/-- Argument structure mismatches are absent. -/
theorem no_argstructure_mismatches :
    MismatchDimension.corpusCount .argumentStructure = 0 := rfl

/-- Every attested dimension has a nonzero count;
    every unattested dimension has a zero count. -/
theorem attested_iff_nonzero (d : MismatchDimension) :
    d.attested = true ↔ d.corpusCount > 0 := by
  cases d <;> simp only [MismatchDimension.attested, MismatchDimension.corpusCount] <;> decide

end Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021.Data
