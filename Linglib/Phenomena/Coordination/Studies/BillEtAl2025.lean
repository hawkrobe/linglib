/-
# Bill, Gonzalez, Driemel, Makharoblidze & Pintér (2025)

"Is DP conjunction always complex? The view from child Georgian and Hungarian"
Semantics & Pragmatics 18, Article 5, 1-20.

## Main Question

Mitrović & Sauerland (2014, 2016) claim DP conjunction universally decomposes
into J (set intersection) + MU (subset) + ☉ (type-shifter). Combined with the
Transparency Principle (van Hout 1998) — children prefer 1-to-1 form-meaning
mappings — this predicts J-MU expressions (where all pieces are overt) should
be easier for children to comprehend than J-only or MU-only.

## Experiment

Act-out task: children and adults hear conjunctive sentences and manipulate
objects to match. Two DVs: accuracy and sentence-played-n (replay count).

## Key Findings

- Georgian children: J-MU sentences required significantly more replays than
  J or MU sentences (opposite of prediction). No difference between J and MU.
- Hungarian: no significant sentence-type effects detected on either measure.
  (Null result — could reflect ceiling effects or insufficient power.)
- Adults: near-ceiling in both languages.

## Theoretical Significance

Results challenge both Mitrović & Sauerland's universal decomposition and
alternative accounts (Szabolcsi 2015, Haslinger et al. 2019).

## Semantic Connection

The M&S decomposition maps directly onto Montague/Conjunction.lean:
- J = `genConj` (Partee & Rooth's generalized conjunction / set intersection)
- MU = `inclFunc` (INCL schema / subset relation)
- ☉ = `typeRaise` (individual → singleton set / generalized quantifier)

## References

- Mitrović & Sauerland (2014). Decomposing coordination. NELS 44.
- Mitrović & Sauerland (2016). Two conjunctions are better than one.
  Acta Linguistica Hungarica 63(4), 471-494.
- van Hout (1998). On the role of direct objects. BUCLD 22.
- Szabolcsi (2015). What do quantifier particles do? L&P 38(2).
- Haslinger et al. (2019). A plural analysis of distributive conjunctions.
-/

import Linglib.Core.Empirical

namespace Phenomena.Coordination.Studies.BillEtAl2025

open Phenomena

-- Conjunction Particle Typology

/--
Cross-linguistic conjunction strategy.

Mitrović & Sauerland (2014, 2016) decompose DP conjunction into three
semantic pieces: J (set intersection), MU (subset), ☉ (type-shifter).
Languages vary in which pieces are overtly realized.
-/
inductive ConjunctionStrategy where
  /-- Only J particle overt (e.g., English "and", Hungarian "és", Georgian "da") -/
  | jOnly
  /-- Only MU particles overt (e.g., Japanese "mo...mo", Hungarian "is...is",
      Georgian "-c...-c") -/
  | muOnly
  /-- Both J and MU overt (e.g., Hungarian "is és...is", Georgian "-c da...-c") -/
  | jMu
  deriving DecidableEq, BEq, Repr

/--
Number of overt functional morphemes per strategy.

Under M&S (2016), the underlying structure always has 3 semantic pieces
(J + MU₁ + MU₂). What varies is how many are pronounced.
-/
def ConjunctionStrategy.overtMorphemeCount : ConjunctionStrategy → Nat
  | .jOnly  => 1  -- only J pronounced
  | .muOnly => 2  -- both MUs pronounced
  | .jMu    => 3  -- J + both MUs pronounced

/--
Under M&S (2016), there are always 3 semantic pieces.
The transparency ratio measures how many are overtly realized.
-/
def ConjunctionStrategy.semanticPieceCount : Nat := 3

/--
M&S (2016) + Transparency Principle predicts: more overt morphemes → easier
to acquire (closer to 1-to-1 form-meaning mapping).
-/
def ConjunctionStrategy.predictedTransparency : ConjunctionStrategy → Nat :=
  ConjunctionStrategy.overtMorphemeCount

-- Georgian and Hungarian Conjunction Particles

/-- A conjunction particle in a specific language. -/
structure ConjParticle where
  language : String
  form : String
  gloss : String
  role : String  -- "J" or "MU"
  boundMorpheme : Bool  -- clitic/suffix vs free morpheme
  deriving Repr

/-- Georgian J particle -/
def georgian_da : ConjParticle :=
  { language := "Georgian", form := "da", gloss := "and"
  , role := "J", boundMorpheme := false }

/-- Georgian MU particle (clitic) -/
def georgian_c : ConjParticle :=
  { language := "Georgian", form := "-c", gloss := "MU/also"
  , role := "MU", boundMorpheme := true }

/-- Hungarian J particle -/
def hungarian_es : ConjParticle :=
  { language := "Hungarian", form := "és", gloss := "and"
  , role := "J", boundMorpheme := false }

/-- Hungarian MU particle -/
def hungarian_is : ConjParticle :=
  { language := "Hungarian", form := "is", gloss := "MU/also"
  , role := "MU", boundMorpheme := false }

/--
Both Georgian and Hungarian allow all three strategies.
This is typologically rare — most languages have only one or two.
-/
def georgianStrategies : List ConjunctionStrategy := [.jOnly, .muOnly, .jMu]
def hungarianStrategies : List ConjunctionStrategy := [.jOnly, .muOnly, .jMu]

/--
Key morphological difference: Georgian MU (-c) is a bound clitic,
Hungarian MU (is) is a free morpheme.
This may be relevant to the cross-linguistic difference in results
(Clark 2017: free morphemes may be acquired more readily than bound).
-/
theorem georgian_mu_bound : georgian_c.boundMorpheme = true := rfl
theorem hungarian_mu_free : hungarian_is.boundMorpheme = false := rfl

-- Experimental Design

def actOutMeasure : MeasureSpec :=
  { scale := .binary, task := .actOut, unit := "correct/incorrect" }

def sentencePlayedMeasure : MeasureSpec :=
  { scale := .continuous, task := .actOut, unit := "log(replay count)" }

inductive Group where
  | adult | child
  deriving DecidableEq, BEq, Repr

/-- Age range for a participant group, in months. -/
structure AgeRange where
  minMonths : Nat
  maxMonths : Nat
  meanMonths : Nat
  deriving Repr

/-- Participant group with demographics. -/
structure ParticipantGroup where
  language : String
  group : Group
  n : Nat
  ageRange : Option AgeRange  -- None for adults
  deriving Repr

def georgianChildren : ParticipantGroup :=
  { language := "Georgian", group := .child, n := 31
  , ageRange := some { minMonths := 45, maxMonths := 70, meanMonths := 57 } }  -- 3;9-5;10, M=4;9

def georgianAdults : ParticipantGroup :=
  { language := "Georgian", group := .adult, n := 41, ageRange := none }

def hungarianChildren : ParticipantGroup :=
  { language := "Hungarian", group := .child, n := 25
  , ageRange := some { minMonths := 36, maxMonths := 60, meanMonths := 50 } }  -- 3;0-5;0, M=4;2

def hungarianAdults : ParticipantGroup :=
  { language := "Hungarian", group := .adult, n := 30, ageRange := none }

/--
Age-accuracy correlation in Georgian children: medium positive.
r(525) = 0.31, p < 0.001 (footnote 8).
-/
def georgianAgeAccuracyCorrelation : Float := 0.31

/--
Age-sentencePlayedN correlation in Georgian children: small negative.
r(497) = -0.18, p < 0.001 (footnote 9). Older children needed fewer replays.
-/
def georgianAgeSentencePlayedCorrelation : Float := -0.18

/-- A single cell in the Group × SentenceType design. -/
structure ConditionResult where
  language : String
  group : Group
  sentenceType : ConjunctionStrategy
  /-- Accuracy (percentage 0-100) -/
  accuracyPct : Nat
  /-- Number of participants -/
  nParticipants : Nat
  deriving Repr

-- Georgian Data (Section 3.1)

/--
Georgian accuracy data (approximate from Figure 4).
Adults near ceiling across all conditions.
Children lower but no significant sentence-type effect on accuracy.
-/
def georgianAccuracy : List ConditionResult :=
  [ -- Adults (near ceiling)
    { language := "Georgian", group := .adult, sentenceType := .jOnly,  accuracyPct := 97, nParticipants := georgianAdults.n }
  , { language := "Georgian", group := .adult, sentenceType := .jMu,   accuracyPct := 97, nParticipants := georgianAdults.n }
  , { language := "Georgian", group := .adult, sentenceType := .muOnly, accuracyPct := 97, nParticipants := georgianAdults.n }
    -- Children
  , { language := "Georgian", group := .child, sentenceType := .jOnly,  accuracyPct := 78, nParticipants := georgianChildren.n }
  , { language := "Georgian", group := .child, sentenceType := .jMu,   accuracyPct := 78, nParticipants := georgianChildren.n }
  , { language := "Georgian", group := .child, sentenceType := .muOnly, accuracyPct := 80, nParticipants := georgianChildren.n }
  ]

-- Statistical Results

/--
Result of a Likelihood Ratio Test comparing nested models.

We encode statistical test results as data, not as theorems about
the underlying population. A non-significant result means the test
did not detect an effect — not that no effect exists.
-/
structure LRTResult where
  effect : String
  df : Nat
  chiSquared : Float
  pValue : Float
  /-- Whether p < .05 (conventional threshold) -/
  significant : Bool
  deriving Repr

/--
Table 1: LRT results for Georgian accuracy.

Only group is significant — sentence-type effect NOT detected.
NOTE: This is a null result. The act-out task allowed unlimited replays,
which may have washed out accuracy differences (see Section 3.1.2).
-/
def georgianAccuracyLRT : List LRTResult :=
  [ { effect := "group",            df := 1, chiSquared := 12.27, pValue := 0.001, significant := true }
  , { effect := "sentence",         df := 2, chiSquared := 2.24,  pValue := 0.327, significant := false }
  , { effect := "group:sentence",   df := 2, chiSquared := 1.95,  pValue := 0.377, significant := false }
  ]

/--
Table 2: LRT results for Georgian sentence-played-n.

All effects significant — this is where the key finding emerges.
-/
def georgianSentencePlayedLRT : List LRTResult :=
  [ { effect := "group",            df := 1, chiSquared := 35.88, pValue := 0.001, significant := true }
  , { effect := "sentence",         df := 2, chiSquared := 14.95, pValue := 0.001, significant := true }
  , { effect := "group:sentence",   df := 2, chiSquared := 23.89, pValue := 0.001, significant := true }
  ]

/--
Pairwise comparison for sentence-played-n (Table 3).
Tukey-adjusted p-values. Values on log scale, encoded as thousandths
(e.g., -176 = -0.176) so that comparisons are decidable.
-/
structure PairwiseComparison where
  group : Group
  contrast : String
  /-- Estimate on log scale, in thousandths (-176 = -0.176) -/
  estimate_thou : Int
  /-- Standard error in thousandths -/
  se_thou : Nat
  df : Nat
  /-- t-ratio in thousandths -/
  tRatio_thou : Int
  /-- p-value in ten-thousandths (1 = 0.0001, 670 = 0.067) -/
  pValue_tenThou : Nat
  significant : Bool
  deriving Repr

/-- Georgian children: J vs J-MU (p < .0001). Negative = J-MU harder. -/
def georgianChild_j_vs_jmu : PairwiseComparison :=
  { group := .child, contrast := "J vs J-MU"
  , estimate_thou := -176, se_thou := 31, df := 1121, tRatio_thou := -5681
  , pValue_tenThou := 1, significant := true }

/-- Georgian children: J vs MU (p = .067, marginal). -/
def georgianChild_j_vs_mu : PairwiseComparison :=
  { group := .child, contrast := "J vs MU"
  , estimate_thou := -69, se_thou := 31, df := 1121, tRatio_thou := -2230
  , pValue_tenThou := 670, significant := false }

/-- Georgian children: J-MU vs MU (p < .01). Positive = J-MU harder. -/
def georgianChild_jmu_vs_mu : PairwiseComparison :=
  { group := .child, contrast := "J-MU vs MU"
  , estimate_thou := 106, se_thou := 30, df := 1121, tRatio_thou := 3555
  , pValue_tenThou := 100, significant := true }

def georgianChildPairwise : List PairwiseComparison :=
  [georgianChild_j_vs_jmu, georgianChild_j_vs_mu, georgianChild_jmu_vs_mu]

/-- Adults show no pairwise differences (all p > .6). -/
def georgianAdultPairwise : List PairwiseComparison :=
  [ { group := .adult, contrast := "J vs J-MU"
    , estimate_thou := 19, se_thou := 26, df := 1120, tRatio_thou := 708
    , pValue_tenThou := 7590, significant := false }
  , { group := .adult, contrast := "J vs MU"
    , estimate_thou := -3, se_thou := 27, df := 1120, tRatio_thou := -102
    , pValue_tenThou := 9940, significant := false }
  , { group := .adult, contrast := "J-MU vs MU"
    , estimate_thou := -21, se_thou := 25, df := 1120, tRatio_thou := -850
    , pValue_tenThou := 6720, significant := false }
  ]

-- Hungarian Data (Section 3.2)

/--
Table 4: LRT results for Hungarian accuracy.

No significant effects detected.
NOTE: Null result — Hungarian children were somewhat older-behaving
than Georgian children despite being younger (see fn. 4).
-/
def hungarianAccuracyLRT : List LRTResult :=
  [ { effect := "group",            df := 1, chiSquared := 0.75,  pValue := 0.385, significant := false }
  , { effect := "sentence",         df := 2, chiSquared := 2.93,  pValue := 0.231, significant := false }
  , { effect := "group:sentence",   df := 2, chiSquared := 1.82,  pValue := 0.402, significant := false }
  ]

/--
Table 5: LRT results for Hungarian sentence-played-n.

Only group significant — sentence-type effect NOT detected.
NOTE: Null result for sentence-type. Could reflect: (a) no actual difference,
(b) insufficient power (n=25 children), (c) Hungarian MU (free morpheme "is")
being easier than Georgian MU (bound clitic "-c"), washing out complexity effects.
-/
def hungarianSentencePlayedLRT : List LRTResult :=
  [ { effect := "group",            df := 1, chiSquared := 6.54,  pValue := 0.05,  significant := true }
  , { effect := "sentence",         df := 2, chiSquared := 2.19,  pValue := 0.334, significant := false }
  , { effect := "group:sentence",   df := 2, chiSquared := 0.55,  pValue := 0.761, significant := false }
  ]

-- Verified Findings (significant results only)

/--
Georgian children replayed J-MU sentences significantly more than J sentences.

This is the OPPOSITE of what M&S (2016) + Transparency Principle predicts.
The prediction was that J-MU (most transparent) should be EASIEST.

Negative estimate means J < J-MU in replay count (J-MU harder).
-/
theorem georgian_child_jmu_harder_than_j :
    georgianChild_j_vs_jmu.significant = true ∧ georgianChild_j_vs_jmu.estimate_thou < 0 := by
  native_decide

/--
Georgian children replayed J-MU sentences significantly more than MU sentences.

Positive estimate means J-MU > MU in replay count (J-MU harder).
-/
theorem georgian_child_jmu_harder_than_mu :
    georgianChild_jmu_vs_mu.significant = true ∧ georgianChild_jmu_vs_mu.estimate_thou > 0 := by
  native_decide

/--
No significant difference between J and MU for Georgian children.

NOTE: This is a null result (p = .067, marginal). We record the
non-significance but do NOT assert that J and MU are equally difficult.
-/
theorem georgian_child_j_vs_mu_not_significant :
    georgianChild_j_vs_mu.significant = false := by
  native_decide

-- The Prediction and Its Failure

/--
The Transparency Principle (van Hout 1998):
Learning is easier for overt and unambiguous (1-to-1) form-meaning mappings
than for covert and/or conflated (many-to-1) mappings.
-/
def transparencyPredicts (s1 s2 : ConjunctionStrategy) : Bool :=
  s1.overtMorphemeCount > s2.overtMorphemeCount

/--
M&S (2016) + Transparency Principle predicts J-MU is more transparent
than both J-only and MU-only.
-/
theorem jmu_predicted_most_transparent :
    transparencyPredicts .jMu .jOnly = true ∧
    transparencyPredicts .jMu .muOnly = true := by
  native_decide

/--
The Georgian sentence-played-n data contradicts this prediction:
J-MU was HARDER (more replays), not easier.
The significant pairwise comparisons go in the wrong direction.
-/
theorem georgian_contradicts_transparency :
    -- The prediction says J-MU should be easier (fewer replays)
    transparencyPredicts .jMu .jOnly = true ∧
    -- But the data shows J-MU required MORE replays (negative estimate = J < J-MU)
    georgianChild_j_vs_jmu.estimate_thou < 0 := by
  native_decide

-- Connection to Form-Meaning Correspondences

/-!
## Link to Phenomena/Gradability/Imprecision/FormMeaning.lean

The Transparency Principle is the acquisition-side counterpart of
the No Needless Manner Violations principle formalized in FormMeaning.lean.

Both principles relate form complexity to meaning:
- NNMV: More complex form → more precise meaning
- Transparency: More overt form-meaning mapping → easier acquisition

The `andBoth` datum in FormMeaning.lean is particularly relevant:
"Ann and Bert" (J-only) vs "both Ann and Bert" (≈ J+MU).
"Both" adds precision (removes homogeneity gap) — it's arguably an
overt realization of MU/distributivity, paralleling the J-MU strategy.

Bill et al.'s finding complicates this picture: in Georgian, adding
overt MU+J (maximum transparency) made comprehension HARDER, suggesting
that morphological complexity can outweigh transparency benefits.
-/

-- Connection to Additive Particles

/-!
## Link to Phenomena/AdditiveParticles/Data.lean

Japanese "mo" (listed as an additive particle in AdditiveParticles/Data.lean)
is the canonical MU particle in Mitrović & Sauerland's framework.
In conjunction, "mo...mo" = MU-only strategy:

  Taroo-mo  Hanako-mo  neta
  Taro-MU   Hanako-MU  slept
  "Both Taro and Hanako slept"

Similarly, Hungarian "is" and Georgian "-c" serve as both additive
particles and conjunction MU particles — unifying two phenomena
under a single morpheme.
-/

end Phenomena.Coordination.Studies.BillEtAl2025
