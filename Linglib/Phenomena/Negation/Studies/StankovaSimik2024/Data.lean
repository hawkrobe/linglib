import Linglib.Phenomena.Negation.CzechThreeWayNegTypologyBridge

/-!
# Staňková & Šimík (2024): Negation in Czech Polar Questions

Experimental data from three naturalness judgment experiments on negation
in Czech polar questions (Staňková & Šimík, FASL 32 / JSL 33).

## Main experiment (§5)

2×2×2 within-subjects design manipulating:
- **Verb position**: V1 (interrogative) vs nonV1 (declarative)
- **Indefinite**: NCI (*žádný*) vs PPI (*nějaký*)
- **Context**: negative (implying ¬p) vs neutral

75 native Czech speakers, Likert 1–7, 32 items (4 per condition).

## Key findings

1. FALSUM is preferred in V1 (interrogative) PQs — PPIs preferred over NCIs
2. Declarative word order (nonV1) is preferred in negatively biased contexts
3. Czech FALSUM is compatible with any type of evidential bias (positive,
   negative, neutral) — broader than English
4. The particle *náhodou* is licensed by FALSUM — PPIs preferred (§6.1)
5. The particle *copak* requires contextual evidence — biased contexts
   preferred (§6.2)

## References

- Staňková, A. & Šimík, R. (2024). Negation in Czech polar questions.
  Journal of Slavic Linguistics 33. Proceedings of FASL 32.
-/

namespace Phenomena.Negation.Studies.StankovaSimik2024.Data

open Phenomena.Negation.CzechThreeWayNeg
open Semantics.Polarity.CzechNegation

-- ============================================================================
-- §1: CLMM Statistical Results
-- ============================================================================

/-- A Cumulative Link Mixed Model (CLMM) regression result.
z-values stored as Int × 1000 for precision without Float. -/
structure CLMMEffect where
  /-- Human-readable effect name -/
  name : String
  /-- z-value × 1000 (e.g., -15674 = z = -15.674) -/
  z1000 : Int
  /-- Whether the effect is statistically significant -/
  significant : Bool
  /-- p-value threshold (as string for display) -/
  pThreshold : String
  deriving Repr, BEq

/-- Whether a CLMM effect's z-value is positive (higher ratings in
the first level of the factor). -/
def CLMMEffect.isPositive (e : CLMMEffect) : Bool := e.z1000 > 0

/-- Whether a CLMM effect's z-value is negative. -/
def CLMMEffect.isNegative (e : CLMMEffect) : Bool := e.z1000 < 0

-- ============================================================================
-- §2: Main Experiment — V1 Results (§5.2, Figure 2a)
-- ============================================================================

/-- V1: Main effect of INDEFINITE (NCI < PPI).
PPIs (*nějaký*) are significantly more natural than NCIs (*žádný*) in V1 PQs.
z = −15.674, p < .001.

Interpretation: V1 negation is interpreted as FALSUM (outer negation),
which licenses PPIs but blocks NCIs. -/
def v1_indefinite : CLMMEffect :=
  { name := "V1: INDEFINITE"
  , z1000 := -15674
  , significant := true
  , pThreshold := "< .001" }

/-- V1: Main effect of CONTEXT (not significant).
z = −1.374, p = 0.169.

Interpretation: FALSUM/outer negation is insensitive to contextual
evidence — V1 PQs are equally natural in negative and neutral contexts.
This is because FALSUM conveys epistemic bias (speaker's possibility
assessment), not evidential bias. -/
def v1_context : CLMMEffect :=
  { name := "V1: CONTEXT"
  , z1000 := -1374
  , significant := false
  , pThreshold := "= 0.169" }

/-- V1: CONTEXT × INDEFINITE interaction.
z = 2.933, p < 0.01.

Post-hoc: the effect of INDEFINITE is more pronounced in neutral contexts.
Simple effect of CONTEXT within PPI: z = −3.522, p < .001.
Simple effect of CONTEXT within NCI: z = 1.104, p = .27 (n.s.). -/
def v1_interaction : CLMMEffect :=
  { name := "V1: CONTEXT × INDEFINITE"
  , z1000 := 2933
  , significant := true
  , pThreshold := "< 0.01" }

-- Post-hoc simple effects for V1

/-- Post-hoc: V1, simple effect of CONTEXT within PPI level.
z = −3.522, p < .001. PPI V1 PQs are more natural in neutral context. -/
def v1_context_within_ppi : CLMMEffect :=
  { name := "V1: CONTEXT | PPI"
  , z1000 := -3522
  , significant := true
  , pThreshold := "< .001" }

/-- Post-hoc: V1, simple effect of CONTEXT within NCI level.
z = 1.104, p = .27 (not significant). -/
def v1_context_within_nci : CLMMEffect :=
  { name := "V1: CONTEXT | NCI"
  , z1000 := 1104
  , significant := false
  , pThreshold := "= .27" }

-- ============================================================================
-- §3: Main Experiment — nonV1 Results (§5.2, Figure 2b)
-- ============================================================================

/-- nonV1: Main effect of CONTEXT.
Negative contexts rated significantly more natural than neutral contexts.
z = 8.674, p < 0.01.

Interpretation: nonV1 (declarative) PQs are sensitive to evidential bias
and preferred in negatively biased contexts. -/
def nonV1_context : CLMMEffect :=
  { name := "nonV1: CONTEXT"
  , z1000 := 8674
  , significant := true
  , pThreshold := "< 0.01" }

/-- nonV1: Main effect of INDEFINITE (NCI > PPI).
NCIs (*žádný*) rated higher than PPIs (*nějaký*) in nonV1 PQs.
z = 6.208, p < 0.01.

Interpretation: inner negation (Op¬) is the preferred reading for nonV1,
licensing NCIs. -/
def nonV1_indefinite : CLMMEffect :=
  { name := "nonV1: INDEFINITE"
  , z1000 := 6208
  , significant := true
  , pThreshold := "< 0.01" }

-- ============================================================================
-- §4: Experimental Predictions — Verification
-- ============================================================================

/-- V1 PQs: PPIs preferred over NCIs → outer (FALSUM) is the reading. -/
theorem v1_ppi_preferred :
    v1_indefinite.significant = true ∧ v1_indefinite.isNegative = true :=
  ⟨rfl, rfl⟩

/-- V1 PQs: No effect of context → FALSUM is insensitive to evidential bias. -/
theorem v1_context_insensitive_confirmed :
    v1_context.significant = false := rfl

/-- nonV1 PQs: Negative context preferred → sensitive to evidential bias. -/
theorem nonV1_context_sensitive_confirmed :
    nonV1_context.significant = true ∧ nonV1_context.isPositive = true :=
  ⟨rfl, rfl⟩

/-- nonV1 PQs: NCIs preferred → inner negation is the default reading. -/
theorem nonV1_nci_preferred :
    nonV1_indefinite.significant = true ∧ nonV1_indefinite.isPositive = true :=
  ⟨rfl, rfl⟩

/-- The key asymmetry: V1 is CONTEXT-insensitive (FALSUM = epistemic bias),
nonV1 is CONTEXT-sensitive (inner neg = evidential bias).

This matches Staňková (2026)'s claim that inner negation requires
contextual evidence while outer negation (FALSUM) does not, and
confirms the VerbPosition.requiresContextualEvidence classification. -/
theorem context_asymmetry :
    v1_context.significant = false ∧
    nonV1_context.significant = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §5: Bridge to CzechThreeWayNeg
-- ============================================================================

/-- V1 forces outer negation. Confirmed by experiment:
PPIs strongly preferred in V1 PQs, and only outer negation licenses PPIs. -/
theorem v1_confirms_outer_neg :
    v1_indefinite.significant = true ∧
    licenses .outer .ppiOutscoping = true ∧
    licenses .outer .nciLicensed = false := ⟨rfl, rfl, rfl⟩

/-- nonV1 defaults to inner negation. Confirmed by experiment:
NCIs preferred in nonV1 PQs, and only inner negation licenses NCIs. -/
theorem nonV1_confirms_inner_default :
    nonV1_indefinite.significant = true ∧
    licenses .inner .nciLicensed = true ∧
    licenses .inner .ppiOutscoping = false := ⟨rfl, rfl, rfl⟩

/-- Context sensitivity matches VerbPosition classification. -/
theorem experiment_matches_verb_position :
    VerbPosition.v1.requiresContextualEvidence = false ∧
    v1_context.significant = false ∧
    VerbPosition.nonV1.requiresContextualEvidence = true ∧
    nonV1_context.significant = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §6: Czech FALSUM with Positive Evidence (§5.3, ex. 14)
-- ============================================================================

/-- Czech FALSUM with positive evidential bias.

In a subexperiment, V1 PQs were tested in contexts with positive evidence
for p (e.g., Eva winning first place → "Didn't Eva win a prize?").
Median rating = 6 (biased) vs 5 (neutral), Likert 1–7.

This confirms Czech outer negation (FALSUM) is compatible with positive
evidential bias, unlike English HiNQs (Gärtner & Gyuris 2017). -/
structure PositiveEvidenceSubexp where
  /-- Median rating in positively biased context -/
  medianBiased : Nat
  /-- Median rating in neutral context -/
  medianNeutral : Nat

def positiveEvidence : PositiveEvidenceSubexp :=
  { medianBiased := 6, medianNeutral := 5 }

/-- V1 PQs with positive evidence rated at least as natural as neutral. -/
theorem positive_evidence_natural :
    positiveEvidence.medianBiased ≥ positiveEvidence.medianNeutral := by decide

/-- Czech FALSUM compatible with all three evidence types
(positive, negative, neutral). This matches the broad distribution
of InterNPQ in Šimík's bias profile table. -/
theorem falsum_evidence_compatible :
    positiveEvidence.medianBiased ≥ 5 ∧  -- positive evidence: natural
    v1_context.significant = false :=     -- neg vs neutral: no difference
  ⟨by decide, rfl⟩

-- ============================================================================
-- §7: náhodou Subexperiment (§6.1)
-- ============================================================================

/-! náhodou subexperiment: 2×2 design (Context × Indefinite).
All V1 PQs with *náhodou*. 8 items.

Tests whether *náhodou* requires FALSUM (outer negation).
If so, PPIs (*nějaký*) should be preferred over NCIs (*žádný*),
because FALSUM licenses PPIs but not NCIs. -/

/-- náhodou: Main effect of INDEFINITE (NCI < PPI).
PPIs strongly preferred with náhodou.
z = −12.845, p < .001.

Interpretation: náhodou requires FALSUM, which only licenses PPIs.
"based on this we suggest that náhodou could be used as an overt
indicator of the covert FALSUM operator" (S&Š §6.1). -/
def nahodou_indefinite : CLMMEffect :=
  { name := "náhodou: INDEFINITE"
  , z1000 := -12845
  , significant := true
  , pThreshold := "< .001" }

/-- náhodou requires FALSUM: confirmed by PPI preference. -/
theorem nahodou_requires_falsum :
    nahodou_indefinite.significant = true ∧
    nahodou_indefinite.isNegative = true ∧
    licenses .outer .nahodou = true := ⟨rfl, rfl, rfl⟩

/-- náhodou's INDEFINITE effect is in the same direction as V1's,
confirming both involve FALSUM (outer negation). -/
theorem nahodou_same_direction_as_v1 :
    nahodou_indefinite.isNegative = true ∧
    v1_indefinite.isNegative = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §8: copak Subexperiment (§6.2)
-- ============================================================================

/-! copak subexperiment: 2×2 design (Context × PQ Polarity).

- CONTEXT: biased (matching polarity) vs neutral
- PQ POLARITY: positive (copak + PPI) vs negative (copak + ne- + NCI)

For positive PQs: biased context has evidence for ¬p, speaker believed p.
For negative PQs: biased context has evidence for p, speaker believed ¬p.
In both cases, copak expresses surprise at the evidence conflicting with
the speaker's prior belief. -/

/-- copak: Main effect of CONTEXT.
Biased contexts significantly more natural than neutral.
z = 9.372, p < .001.

Interpretation: copak requires a conflict between speaker's prior belief
and current contextual evidence (evidential bias). "copak is a particle
which is used to express speaker's surprise about the current contextual
evidence" (S&Š §6.2). -/
def copak_context : CLMMEffect :=
  { name := "copak: CONTEXT"
  , z1000 := 9372
  , significant := true
  , pThreshold := "< .001" }

/-- copak requires evidential bias (biased context). -/
theorem copak_requires_evidential_bias :
    copak_context.significant = true ∧
    copak_context.isPositive = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §9: Key Contrasts
-- ============================================================================

/-- náhodou vs copak: opposite context sensitivity.

- náhodou (FALSUM-tied): context-insensitive. FALSUM conveys epistemic
  bias regardless of contextual evidence — V1 PQs are equally natural
  in any evidential context.
- copak (evidential-bias-tied): context-sensitive. Requires a biased
  context where speaker's prior belief conflicts with evidence.

This confirms they express different types of bias:
náhodou → epistemic bias; copak → evidential bias.
(Staňková & Šimík 2024 §6) -/
theorem nahodou_copak_contrast :
    v1_context.significant = false ∧     -- náhodou's licenser (FALSUM) is context-insensitive
    copak_context.significant = true :=   -- copak requires evidential bias
  ⟨rfl, rfl⟩

/-- The V1 context insensitivity and náhodou's FALSUM requirement converge:
both reflect that outer negation (FALSUM) is an epistemic-bias phenomenon,
not an evidential-bias phenomenon. Conversely, nonV1 context sensitivity
and copak's context requirement both reflect evidential bias sensitivity. -/
theorem epistemic_vs_evidential_coherence :
    -- Epistemic bias cluster: V1 context-insensitive, outer neg licenses náhodou
    v1_context.significant = false ∧
    licenses .outer .nahodou = true ∧
    -- Evidential bias cluster: nonV1 context-sensitive, copak context-sensitive
    nonV1_context.significant = true ∧
    copak_context.significant = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §10: Experiment Metadata
-- ============================================================================

structure ExperimentMetadata where
  nParticipants : Nat
  nItems : Nat
  scale : String
  method : String
  platform : String
  citation : String
  deriving Repr

def mainExperiment : ExperimentMetadata :=
  { nParticipants := 75
  , nItems := 32
  , scale := "Likert 1–7"
  , method := "CLMM (ordinal package in R; Christensen 2022)"
  , platform := "L-Rex (Starschenko & Wierzba 2022)"
  , citation := "Staňková & Šimík 2024, §5" }

def nahodouExperiment : ExperimentMetadata :=
  { nParticipants := 75
  , nItems := 8
  , scale := "Likert 1–7"
  , method := "CLMM (ordinal package in R)"
  , platform := "L-Rex"
  , citation := "Staňková & Šimík 2024, §6.1" }

def copakExperiment : ExperimentMetadata :=
  { nParticipants := 75
  , nItems := 8   -- 2×2 design, same setup as náhodou
  , scale := "Likert 1–7"
  , method := "CLMM (ordinal package in R)"
  , platform := "L-Rex"
  , citation := "Staňková & Šimík 2024, §6.2" }

end Phenomena.Negation.Studies.StankovaSimik2024.Data
