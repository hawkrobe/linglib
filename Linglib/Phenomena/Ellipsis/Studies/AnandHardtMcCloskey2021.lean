import Linglib.Core.Lexical.Word
import Linglib.Phenomena.Ellipsis.Sluicing
import Linglib.Theories.Syntax.Minimalism.Ellipsis.FormalMatching
import Linglib.Theories.Syntax.Minimalism.Ellipsis.DeletionDomain

/-!
# @cite{anand-hardt-mccloskey-2021} — Corpus Data

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

-/

namespace Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021

-- ============================================================================
-- § 1: Sluice Classification
-- ============================================================================

/-- Whether a sluice has an overt correlate in the antecedent.

    Merger: "Someone₁ left, but I don't know who₁" — *someone* is the correlate.
    Sprouting: "John left, but I don't know why" — no overt correlate. -/
inductive SluiceKind where
  | merger    -- Overt correlate (inner antecedent) present
  | sprouting -- No overt correlate; wh-phrase corresponds to an implicit argument
  deriving DecidableEq, Repr

/-- Embedding context of a sluice. -/
inductive EmbeddingContext where
  | root     -- Matrix clause: "Who did she see?"
  | embedded -- Subordinate: "I don't know who she saw"
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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

    Polarity reversal is pragmatically conditioned — it requires the
    discourse context to make the reversed polarity salient. -/
inductive PolarityReversalContext where
  | negRaising       -- "I don't think she'll pass, but I don't know why" (ex. 33)
  | withoutAdjunct   -- "without" phrases adjoin to VP (ex. 32)
  | disjunction      -- Disjunction/doubt/remember (ex. 34)
  | qudPartialAnswer -- Negative partial answer to a superordinate QUD (ex. 35)
  | howEmbedded      -- "how" under know/learn/see — negation absent from antecedent
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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

/-- The SCSS corpus summary. -/
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
    scss.sproutingPctTenths + scss.mergerPctTenths = 1000 := by decide

/-- Root + embedded = 100%. -/
theorem root_embedded_exhaustive :
    scss.rootPctTenths + scss.embeddedPctTenths = 1000 := by decide

/-- Sprouting is the majority kind. -/
theorem sprouting_majority :
    scss.sproutingPctTenths > scss.mergerPctTenths := by decide

/-- *Why* is the majority wh-remnant type. -/
theorem why_majority :
    scss.whyPctTenths > 500 := by decide

/-- Embedding is the majority context. -/
theorem embedded_majority :
    scss.embeddedPctTenths > scss.rootPctTenths := by decide

/-- Modality mismatches are the most frequent mismatch type. -/
theorem modality_most_frequent_mismatch :
    MismatchDimension.corpusCount .modality >
    MismatchDimension.corpusCount .tense ∧
    MismatchDimension.corpusCount .modality >
    MismatchDimension.corpusCount .polarity ∧
    MismatchDimension.corpusCount .modality >
    MismatchDimension.corpusCount .newWords :=
  ⟨by decide, by decide, by decide⟩

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

-- ============================================================================
-- § 7: Sluicing — Minimalist Bridge Theorems
-- ============================================================================
-- @cite{anand-hardt-mccloskey-2021} @cite{anand-hardt-mccloskey-2025}
-- Connects empirical sluicing data — both the individual examples in
-- `Phenomena.Ellipsis.Sluicing` and the corpus findings from
-- @cite{anand-hardt-mccloskey-2021} — to the Syntactic Isomorphism Condition
-- (SIC) formalized in
-- `Theories.Syntax.Minimalism.Ellipsis.FormalMatching`.

open Minimalism
open Minimalism.Ellipsis.FormalMatching
open Phenomena.Ellipsis.Sluicing

-- ============================================================================
-- § 7.1: Concrete SIC Licensing
-- ============================================================================

-- The argument domain of a full clause (CP) is vP, containing head pairs
-- ⟨v, V⟩ and ⟨V, D⟩ (v selects VP, V selects DP). When antecedent and
-- ellipsis site share the same verb, these head pairs are identical.

/-- Head pairs for a simple transitive vP: v selects V, V selects D.
    This is the argument domain structure of "someone left" / "John ate
    something" — any clause with a single verb and a DP argument. -/
def transitiveVP : List HeadPair := [⟨.v, .V, none, none, none⟩, ⟨.V, .D, none, none, none⟩]

/-- Head pairs for an intransitive vP: v selects V only.
    Used for the antecedent of sprouting examples like "John left." -/
def intransitiveVP : List HeadPair := [⟨.v, .V, none, none, none⟩]

/-- SIC licenses basic sluicing: "Someone left, but I don't know who."

    Antecedent "someone left" and ellipsis "[who] left" share the same
    verb, so their argument domains have identical head pairs. -/
theorem basic_sluice_licensed :
    structurallyIdentical transitiveVP transitiveVP = true := by
  decide

/-- SIC licenses object sluicing: "John ate something, but I don't know what."

    Same verb "ate" → same head pairs. -/
theorem object_sluice_licensed :
    structurallyIdentical transitiveVP transitiveVP = true := by
  decide

/-- A `SluicingLicense` for same-verb sluices is licensed. -/
theorem same_verb_license_is_licensed :
    (SluicingLicense.mk transitiveVP transitiveVP).isLicensed = true := by
  decide

/-- SIC correctly predicts `basicSluice` is grammatical. -/
theorem sic_predicts_basicSluice :
    basicSluice.grammatical = true ∧
    (SluicingLicense.mk transitiveVP transitiveVP).isLicensed = true :=
  ⟨rfl, by decide⟩

/-- SIC correctly predicts `objectSluice` is grammatical. -/
theorem sic_predicts_objectSluice :
    objectSluice.grammatical = true ∧
    (SluicingLicense.mk transitiveVP transitiveVP).isLicensed = true :=
  ⟨rfl, by decide⟩

-- Case matching: case is assigned within the argument domain, so the SIC
-- requires case to match between antecedent and ellipsis site.

/-- Head pairs for a dative-assigning transitive vP.
    V assigns dative case to its DP complement (e.g., German *helfen*). -/
def dativeVP : List HeadPair :=
  [⟨.v, .V, none, none, none⟩, ⟨.V, .D, some .Dat, none, none⟩]

/-- Head pairs for an accusative-assigning transitive vP.
    V assigns accusative case to its DP complement (e.g., German *sehen*). -/
def accusativeVP : List HeadPair :=
  [⟨.v, .V, none, none, none⟩, ⟨.V, .D, some .Acc, none, none⟩]

/-- Same-case head pairs are structurally identical (case match OK). -/
theorem case_match_licensed :
    structurallyIdentical dativeVP dativeVP = true := by
  decide

/-- Case mismatch blocks structural identity. -/
theorem case_mismatch_blocked :
    structurallyIdentical dativeVP accusativeVP = false := by
  decide

/-- SIC correctly predicts `germanCaseMatch` is grammatical:
    dative wh-phrase matches dative correlate. The SIC is licensed
    because the argument domains have structurally identical head pairs
    (both assign dative). -/
theorem sic_predicts_germanCaseMatch :
    germanCaseMatch.grammatical = true ∧
    structurallyIdentical dativeVP dativeVP = true :=
  ⟨rfl, by decide⟩

/-- SIC correctly predicts `germanCaseMismatch` is ungrammatical:
    accusative wh-phrase does not match dative correlate. The SIC
    blocks sluicing because dative ≠ accusative within the argument
    domain (@cite{merchant-2001}: German *wem*/*wen* data). -/
theorem sic_predicts_germanCaseMismatch :
    germanCaseMismatch.grammatical = false ∧
    structurallyIdentical dativeVP accusativeVP = false :=
  ⟨rfl, by decide⟩

-- ============================================================================
-- § 7.2: SIC Mismatch Predictions Confirmed by Corpus
-- ============================================================================

-- The SIC partitions categories into those inside and outside the
-- argument domain. Categories inside (V, v) must match; categories
-- outside (T, Mod, C) may differ freely.

/-- V and v are inside the argument domain: argument structure must match.
    The corpus confirms: zero argument structure mismatches. -/
theorem argstructure_inside_and_absent :
    isInArgumentDomain .V .C = true ∧
    isInArgumentDomain .v .C = true ∧
    MismatchDimension.corpusCount .argumentStructure = 0 :=
  ⟨by decide, by decide, rfl⟩

/-- T is outside the argument domain: tense mismatches are licit.
    The corpus confirms: 129 tense mismatches attested. -/
theorem tense_outside_and_attested :
    isInArgumentDomain .T .C = false ∧
    MismatchDimension.corpusCount .tense > 0 :=
  ⟨by decide, by decide⟩

/-- Mod is outside the argument domain: modal mismatches are licit.
    The corpus confirms: 394 modal mismatches — the most frequent type. -/
theorem modality_outside_and_attested :
    isInArgumentDomain .Mod .C = false ∧
    MismatchDimension.corpusCount .modality > 0 :=
  ⟨by decide, by decide⟩

/-- The SIC cleanly separates tolerated from untolerated mismatches:
    every mismatch dimension inside the argument domain has 0 corpus
    attestations; every dimension outside has nonzero attestations. -/
theorem sic_partition_confirmed :
    -- Inside arg domain → 0 mismatches
    MismatchDimension.corpusCount .argumentStructure = 0 ∧
    MismatchDimension.corpusCount .voice = 0 ∧
    -- Outside arg domain → mismatches attested
    MismatchDimension.corpusCount .tense > 0 ∧
    MismatchDimension.corpusCount .modality > 0 :=
  ⟨rfl, rfl, by decide, by decide⟩

-- ============================================================================
-- § 7.3: Voice Mismatch Resolution (@cite{anand-hardt-mccloskey-2021})
-- ============================================================================

-- @cite{anand-hardt-mccloskey-2021} resolves the voice puzzle: voice mismatches are correctly
-- blocked by the SIC because active v[agentive] ≠ passive v[nonThematic]
-- within the argument domain (v is F1, inside vP). The 0 corpus count
-- is predicted, not puzzling.

/-- The SIC correctly blocks voice mismatches in sluicing: active
    v[agentive] ≠ passive v[nonThematic], and both are within the
    argument domain (F1 ≤ F1). The corpus confirms: 0 voice mismatches.

    This resolves the voice puzzle from the earlier analysis. The puzzle
    arose from treating voice as outside the argument domain (like T/Mod),
    but @cite{anand-hardt-mccloskey-2021} shows that voice flavor is encoded on v, which IS inside
    the argument domain. Uses `activeVP`/`passiveVP` from FormalMatching. -/
theorem voice_correctly_blocked :
    structurallyIdentical activeVP passiveVP = false ∧
    MismatchDimension.corpusCount .voice = 0 :=
  ⟨by decide, rfl⟩

-- ============================================================================
-- § 7.4: Corpus Distributions
-- ============================================================================

/-- Sprouting is the dominant sluice kind (65.5%), overturning the
    literature's focus on merger. -/
theorem sprouting_is_default :
    scss.sproutingPctTenths > 500 := by decide

/-- *Why* accounts for the majority of sluicing. Since virtually all
    *why*-sluices are sprouting (reason adjuncts lack overt correlates),
    the prototypical sluice is "John left, but I don't know why"
    (sprouting, reason), not "Someone left, but I don't know who"
    (merger, entity). -/
theorem why_dominates :
    scss.whyCount > scss.totalSluices / 2 := by decide

-- ============================================================================
-- § 8: Merchant's Deletion Domain Predictions (@cite{merchant-2013})
-- ============================================================================

-- Merchant's [E]-feature theory provides a complementary explanation for
-- the corpus findings. The SIC (§ 7) explains voice mismatch blocking
-- via structural identity within the argument domain; Merchant's deletion
-- domain analysis explains it via the position of [E]: sluicing has C[E],
-- so everything below C (including Voice and v) is inside the deletion domain.

/-- Merchant's deletion domain theory converges with the corpus: sluicing
    (C[E]) predicts both voice and transitivity mismatches are blocked,
    and the SCSS finds exactly 0 attestations of each.

    This is a convergent prediction with the SIC (§ 7.2): both the SIC
    (structural identity within the argument domain) and the deletion
    domain analysis ([E] on C → Voice inside TP) independently predict
    that voice and argument structure mismatches are blocked in sluicing. -/
theorem merchant_deletion_domain_matches_corpus :
    -- Merchant predicts: voice mismatches blocked under sluicing
    Minimalism.Ellipsis.canMismatch Minimalism.Ellipsis.sluicing
      Minimalism.Ellipsis.voiceMismatch = false ∧
    -- Corpus confirms: 0 voice mismatches
    MismatchDimension.corpusCount .voice = 0 ∧
    -- Merchant predicts: transitivity mismatches blocked under sluicing
    Minimalism.Ellipsis.canMismatch Minimalism.Ellipsis.sluicing
      Minimalism.Ellipsis.transitivityMismatch = false ∧
    -- Corpus confirms: 0 argument structure mismatches
    MismatchDimension.corpusCount .argumentStructure = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.Ellipsis.Studies.AnandHardtMcCloskey2021
