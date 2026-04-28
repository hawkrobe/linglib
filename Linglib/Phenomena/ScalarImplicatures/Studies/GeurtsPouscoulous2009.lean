import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Phenomena.ScalarImplicatures.Embedded.Attitudes
import Linglib.Theories.Pragmatics.Implicature.Competence
import Linglib.Theories.Pragmatics.Implicature.Defs
import Linglib.Theories.Pragmatics.Implicature.Diagnostics
import Linglib.Theories.Semantics.Entailment.Polarity

/-!
# @cite{geurts-pouscoulous-2009} — Embedded Implicatures?!?
@cite{geurts-pouscoulous-2009}

Geurts, B. & Pouscoulous, N. (2009). Embedded implicatures?!?
*Semantics & Pragmatics*, 2(4), 1–34. https://doi.org/10.3765/sp.2.4

## Two threads

The paper makes two interlocking arguments, both formalized here:

1. **Empirical**: four experiments show that mainstream conventionalist
   theories of scalar implicature (@cite{landman-1998},
   @cite{levinson-2000}, @cite{recanati-2003}, @cite{chierchia-2004},
   @cite{chierchia-2006}, @cite{fox-2007},
   @cite{chierchia-fox-spector-2008}) — and even a *minimal*
   conventionalism that only claims local-SI readings exist — fail to
   predict the patterns observed. The embedded-implicature problem is
   traced back to @cite{cohen-1971}; @cite{landman-1998} is credited in
   the paper's footnote 2 with first noting the belief-report case.
2. **Methodological**: introspection systematically inflates SI rates
   (Worries §2 + Exp 2 + Exp 3); "subtle intuitions are best classified
   as ipso facto suspect" (page 4:18). The verification paradigm is the
   more reliable instrument.

## Paper structure (taxonomy followed by section blocks below)

| §  | Content                                                            |
|----|--------------------------------------------------------------------|
| §1 | **Experiments 1a and 1b** — embedding-type variation (Table 2)     |
| §2 | **Worries about the paradigm** — three a-priori concerns           |
| §3 | **Experiment 2** — paradigm bias on simple sentences               |
| §4 | **Monotonicity** — sentences (25)–(27) for Exp 3                   |
| §5 | **Experiment 3** — verification vs inference (Table 3)             |
| §6 | **Minimal conventionalism** — auxiliary-assumption argument        |
| §7 | **Experiment 4** — ambiguity-detection task (Tables 4, 5)          |
| §8 | **Meanwhile in the Gricean camp…** — competence-based explanation  |

## Empirical data captured

All numerical values in this file are taken directly from the paper's
Tables 2–5 and §1.4 / §3.2 / §5.2 / §7.2. Pages are cited in the
paper's article-prefixed format (`4:N`) used by S&P.

## Statistical-test attribution

The paper uses different statistical tests at different points:

- **Exp 1a–b overall**: Cochran's Q-test (UNVERIFIED: Q = 49.750 for
  Exp 1a, Q = 21.68 for Exp 1b; both p < .001 — exact Q-values
  reproduced from the paper but not externally cross-checked)
- **Exp 1a–b pairwise**: McNemar's test (specific p-values per pair)
- **Exp 2 inference vs verification**: McNemar's test (n = 29, p < .01)
- **Exp 2 order effects**: Fisher's Exact test (the paper writes
  "Fischer's", presumably a typo; inference p = .45, verification p = 1)
- **Exp 3 pairwise**: McNemar's with Bonferroni correction
- **Exp 4 critical vs ambiguous controls**: UNVERIFIED Wilcoxon's Exact
  test (W = 208, n = 20, p < .0001) — n=20 reflects 2 exclusions from
  the 22 UCL participants

## Linglib integration

The canonical *some*/*all* world model `SomeAllWorld` lives in
`Phenomena.ScalarImplicatures.Basic`; this file uses it for the
implicature-spine bridge. The §8 derivation routes through
`Implicature.Competence.processAlternative` (Sauerland-style competence
machinery). The `think` empirical condition is bridged to
`Embedded.Attitudes.AttitudeInterpretation.local_`.

## Subsequent literature (forward pointers)

The most-important post-publication replies and extensions, none yet
formalized in linglib:

- **Sauerland 2010** "Embedded implicatures and experimental
  constraints" (S&P 3:2) — paradigm-choice critique
- **Clifton & Dube 2010** S&P reply
- **Ippolito 2010** S&P reply
- **Chemla & Spector 2011** *J. of Semantics* 28:359–400 — the canonical
  empirical successor; uses graded truth-value judgments and finds
  ~73% local-SI in universal contexts, directly contesting this paper's
  Exp 4 null result. The most important reply.
- **Foppolo, Guasti & Chierchia 2012** — children's interpretation
- **Cremers, Tieu & Romoli** (2017–2018) — acquisition follow-ups

These belong in their own `Studies/` files; this paper's claims are
formalized as historical-state-of-knowledge claims, per linglib's
chronological-dependency rule.
-/

namespace Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009

open Semantics.Entailment.Polarity (ContextPolarity)
open Phenomena.ScalarImplicatures (SomeAllWorld)

-- ============================================================================
-- Shared types (paper-internal vocabulary)
-- ============================================================================

/-- Quantifier contexts tested in Experiments 3–4 (paper §4 sentences
(25)–(27) and §5 setup). -/
inductive QuantifierContext where
  | all              -- UE: "All the squares are connected with some of the circles"
  | moreThanOne      -- UE: "More than one square is connected with some..."
  | exactlyTwo       -- NM: "Exactly two squares are connected with some..."
  | notAll           -- DE: "Not all the squares are connected with some..."
  | notMoreThanOne   -- DE: "Not more than one square is connected with some..."
  deriving DecidableEq, Repr

/-- Map a quantifier context to its monotonicity using the canonical
`Semantics.Entailment.Polarity.ContextPolarity` enum. -/
def quantifierMonotonicity : QuantifierContext → ContextPolarity
  | .all              => .upward
  | .moreThanOne      => .upward
  | .exactlyTwo       => .nonMonotonic
  | .notAll           => .downward
  | .notMoreThanOne   => .downward

/-- Conventionalist variants distinguished by the paper. The paper
itself draws the **lexicalist vs syntax-based** dichotomy (page 4:3,
"Conventionalism comes in two main varieties: lexicalist and
syntax-based") and crosses it with a **mainstream vs minimal** axis
(page 4:24): mainstream variants commit to *preferring* the local SI in
non-DE contexts; minimal variants only claim local-SI readings *exist*.

Footnote 3 places Levinson 2000 with the lexicalists ("his position is
closer to that of Landman and Chierchia 2004 than it is to Horn's").

The file's three-way enum is the projection onto distinct *prediction
profiles*: both mainstream variants predict preference (collapsed here
into one prediction function); minimal makes no preference claim. The
paper's underlying 2×2 (lexicalist/syntactic × mainstream/minimal) can
be reconstructed from this projection plus the conventionalist
literature. -/
inductive ConventionalistVariant where
  | mainstreamLexicalist
  | mainstreamSyntactic
  | minimal
  deriving DecidableEq, Repr

/-- Does this variant predict a *preference* for local SIs in the given
context? Mainstream variants predict preference in non-DE; minimal
makes no preference claim.

**Caveat**: this is a flat Bool collapsing several distinctions the
paper preserves at page 4:5–4:6 and 4:19. Specifically: strong
defaultism (Levinson 2000) vs conditional preference (Landman 1998 /
Chierchia 2004) vs mere possibility (Chierchia 2004 on non-monotonic).
For non-monotonic *exactly two*, the paper notes Geurts 2009 says local
SI is *not* default, Van Rooij & Schulz 2004 say opinions are divided,
and Chierchia 2004 calls it "merely possible". The flat Bool above
collapses these to "non-DE → true". Refine if a downstream consumer
needs the finer-grained predictions. -/
def predictsLocalSI : ConventionalistVariant → QuantifierContext → Bool
  | .minimal, _ => false
  | _, q => quantifierMonotonicity q != .downward

/-- Convenience: the prediction shared by both mainstream variants
(paper's running "mainstream conventionalism" of §1). -/
def conventionalistPredictsLocalSI : QuantifierContext → Bool :=
  predictsLocalSI .mainstreamLexicalist


-- ============================================================================
-- §1  Experiments 1a and 1b — embedding-type variation (Table 2)
-- ============================================================================

section ExperimentsOneAOneB

/-! ## §1 Experiments 1a and 1b -/

/-- Embedding types tested in Experiments 1a and 1b (paper §1). -/
inductive EmbeddingType where
  | simple   -- "Fred heard some of the Verdi operas" (∅-condition)
  | think    -- "Betty thinks Fred heard some..."
  | want     -- "Betty wants Fred to hear some..."
  | must     -- "Fred has to hear some..."
  | all      -- "All students heard some..."
  deriving DecidableEq, Repr

/-- One row from Exp 1a-b results (paper Table 2). Rates are integer
percentages; the paper reports proportions (.93 = 93%). -/
structure EmbeddingResult where
  embedding : EmbeddingType
  /-- Percentage of participants endorsing the local-SI inference -/
  localSIRate : Nat
  n : Nat
  deriving Repr

/-- Look up the local-SI rate for a given embedding type. Returns
`none` if the embedding wasn't tested. Use this for queries where
non-existence should be observable. -/
def lookupRate? (results : List EmbeddingResult) (e : EmbeddingType) :
    Option Nat :=
  (results.find? (·.embedding == e)).map (·.localSIRate)

/-- Local-SI rate for an embedding type *known* to be present in
`results`, defaulting to `0` for untested embeddings. The 0-default is
deliberate for use in derived aggregates (`thinkAvgRate`,
`complexConditionRates`) where presence is ensured by the data tables;
for general queries use `lookupRate?`. -/
def lookupRate (results : List EmbeddingResult) (e : EmbeddingType) : Nat :=
  (lookupRate? results e).getD 0

/-! Method (paper §1.1–1.3): Exp 1a tested *some* embedded under *think*,
deontic *must*, and the universal quantifier *all*; Exp 1b under *think*
and *want*. Inference-task questionnaires; same design as Figure 1
("Emilie says: ‘Betty thinks that Fred heard some of the Verdi operas.'
Would you infer from this that Betty thinks that Fred didn't hear all
the Verdi operas?"). -/

/-- Experiment 1a results (paper Table 2, n = 30, French-speaking
students at the École Nationale des Arts Décoratifs in Paris). -/
def exp1aResults : List EmbeddingResult :=
  [ { embedding := .simple, localSIRate := 93, n := 30 }
  , { embedding := .think,  localSIRate := 50, n := 30 }
  , { embedding := .all,    localSIRate := 27, n := 30 }
  , { embedding := .must,   localSIRate := 3,  n := 30 } ]

/-- Experiment 1b results (paper Table 2, n = 31, same population). -/
def exp1bResults : List EmbeddingResult :=
  [ { embedding := .simple, localSIRate := 94, n := 31 }
  , { embedding := .think,  localSIRate := 65, n := 31 }
  , { embedding := .want,   localSIRate := 32, n := 31 } ]

/-- Cross-experiment average for *think* (paper §1.4 page 4:9): "local
SIs were relatively frequent with *think* (57.5% across the two
experiments)." Derived directly from Table 2 via `lookupRate`. -/
def thinkAvgRate : ℚ :=
  ((lookupRate exp1aResults .think + lookupRate exp1bResults .think : Nat) : ℚ)
    / 2

/-- All embedded (i.e. non-simple) condition rates from Exp 1a-b. -/
def complexConditionRates : List Nat :=
  (exp1aResults ++ exp1bResults).filter (·.embedding != .simple)
    |>.map (·.localSIRate)

/-- Mean rate across all complex (i.e. embedded) conditions in Exp 1a–b
(paper §1.4 page 4:9): "complex conditions yielded local SIs at a much
reduced mean rate of 35%." Derived from `complexConditionRates`:
(50 + 27 + 3 + 65 + 32) / 5 = 35.4. -/
def complexConditionsMean : ℚ :=
  (complexConditionRates.sum : ℚ) / complexConditionRates.length

/-- Paper's headline finding (page 4:9): SI rates vary from 3% (must,
Exp 1a) to 94% (simple, Exp 1b) — a 91-point range. Anchored in the
data tables rather than literal arithmetic. This contradicts the
conventionalist claim that local SIs occur "systematically and freely
in arbitrarily embedded positions." -/
theorem embedding_not_systematic :
    lookupRate exp1bResults .simple - lookupRate exp1aResults .must =
      (91 : Nat) := rfl

/-- Among embedded conditions, only *think* shows substantial local-SI
endorsement (averaging 57.5% across both experiments). Other embeddings
— *all* (27%), *must* (3%), *want* (32%) — fall below 35%, the
mean of complex-condition rates that the paper carries forward as the
disconfirmation baseline (page 4:9). -/
theorem think_above_35_others_below :
    thinkAvgRate = 575 / 10 ∧
    lookupRate exp1aResults .all  < (35 : Nat) ∧
    lookupRate exp1aResults .must < (35 : Nat) ∧
    lookupRate exp1bResults .want < (35 : Nat) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  have h : (lookupRate exp1aResults .think + lookupRate exp1bResults .think : Nat)
      = 115 := by decide
  unfold thinkAvgRate
  rw [h]; norm_num

end ExperimentsOneAOneB

-- ============================================================================
-- §1.4  Discussion — Objections #1, #2, #3 against the implausibility defense
-- ============================================================================

section ImplausibilityRefutation

/-! ## §1.4 Discussion: refuting the implausibility defense

Paper §1.4 (pages 4:9–4:13) anticipates the conventionalist response
that low embedded-SI rates are due to *implausibility* of the
strengthened readings, and refutes it with three objections:

- **Objection #1** (page 4:10): the implausibility argument doesn't
  work for *all* and *think* — paraphrases (8a-b)/(9a-b) show that the
  strengthened reading isn't markedly less plausible than the
  literal one. Footnote 7 makes the structural observation:
  asymmetric entailment (a) → (b) → (b) is at least as plausible as (a),
  so the implausibility defense cannot ground out at "(a) is implausible
  relative to (b)" (this is `mt` from Lean core).
- **Objection #2** (page 4:10–4:11): the argument might be restricted
  to *must*/*want*. Paper refutes with examples (12)–(14) — bona fide
  scalar implicatures that arise *despite* the strengthened reading
  being implausible.
- **Objection #3** (page 4:12): the gradient prediction
  (must < all < want < think correlating with implausibility ordering)
  is empirically false. Paper offers (18a)/(18b)/(18c) as a triple where
  the three readings are roughly equally plausible, contradicting the
  predicted gradient. -/

/-- A paper §1.4 example of a *bona fide* scalar implicature that
arises despite the strengthened reading being independently implausible
(i.e., the implausibility defense, if correct, would predict the SI
*not* to arise — but it does). Paper (12)–(14) and (15)–(17). -/
structure ImplausibilityCounterexample where
  /-- The utterance (verbatim from paper). -/
  utterance : String
  /-- The SI that arises despite implausibility. -/
  siInference : String
  /-- Why the SI's content is independently implausible. -/
  implausibilityReason : String
  /-- Paper claim: the SI nevertheless arises. -/
  siArises : Bool
  deriving Repr

/-- §1.4 Objection #2 counterexamples: SIs that arise despite their
strengthened readings being implausible. Page 4:11, examples (12)–(14)
plus the "Harry hopes" parallels (15)–(17). All five entries have
`siArises := true` — the data IS the refutation; no separate theorem
needed. -/
def objection2_counterexamples : List ImplausibilityCounterexample :=
  [ { utterance := "Some of the liberal MPs voted against the bill."
    , siInference := "the liberal MPs were divided"
    , implausibilityReason :=
        "Dutch parliamentary factions vote en bloc; SI implausible"
    , siArises := true }
  , { utterance :=
        "In order to prevent the rinderpest from spreading through his herd, " ++
        "some of Jones's cows were vaccinated."
    , siInference := "only some (not all) cows were vaccinated"
    , implausibilityReason :=
        "rinderpest is highly contagious; partial vaccination is irrational"
    , siArises := true }
  , { utterance := "Anna threw all her marbles in the swimming pool. " ++
                   "Some of them sank to the bottom."
    , siInference := "not all of the marbles sank"
    , implausibilityReason := "marbles are dense; all should sink"
    , siArises := true }
  , { utterance := "Harry hopes that some of the figures are correct."
    , siInference := "Harry doesn't hope that all are correct"
    , implausibilityReason :=
        "Harry presumably hopes for full correctness, not partial"
    , siArises := true }
  , { utterance := "Harry hopes that some of his grandchildren will be happy."
    , siInference := "Harry doesn't hope that all will be happy"
    , implausibilityReason := "Harry presumably hopes for all to be happy"
    , siArises := true } ]

/-- §1.4 Objection #3: the implausibility defense predicts a gradient
(must << all << want << think) of SI rates aligning with implausibility
ordering. Paper page 4:12 example (18) gives three readings (18a-c)
that, by the paper's intuitions, are roughly equally plausible — yet
their empirical SI rates differ markedly (think 57.5%, all 27%, must
3%): a 54.5pp spread the implausibility defense cannot ground. The data
itself is the refutation. -/
def objection3_data : List (String × Nat) :=
  [ ("Betty thinks that Fred read some but not all of the Harry Potter books.",
     575) -- think average, scaled by 10 to keep ℕ
  , ("All the students read some but not all of the Harry Potter books.",
     270) -- all
  , ("Fred has to read some but not all of the Harry Potter books.",
      30) -- must
  ]

end ImplausibilityRefutation

-- ============================================================================
-- §2  Worries about the paradigm
-- ============================================================================

section WorriesAboutParadigm

/-! ## §2 Worries about the paradigm

Paper §2 (pages 4:14–4:16) introduces three a-priori reasons to suspect
the inference paradigm exaggerates SI rates. These motivate Exp 2.

- **Worry #1** (page 4:14): the rate at which people spontaneously draw
  a conclusion ϕ from premises A is generally lower than the rate at
  which they endorse the corresponding argument "A, therefore ϕ" when
  asked explicitly (cf. @cite{evans-newstead-byrne-1993}).
- **Worry #2** (page 4:15): asking whether (b) might be implied by (a)
  changes the context: it makes the question of whether the speaker
  believes (b) contextually relevant. The inference paradigm thereby
  *creates* the relevance condition that makes the SI more likely.
- **Worry #3** (page 4:15): superficial similarity to valid syllogisms
  (@cite{chater-oaksford-1999}) may cause errors. SIs derived in the
  inference task may piggyback on this surface-similarity heuristic. -/

/-- Paper §1.4 page 4:13 informal follow-up: "we asked 31 Dutch
philosophy students to decide if the following inference is valid:
(19) Mary has to put some but not all of the stamps in a blue envelope.
SO: She may not put all the stamps in the blue envelope. 27 (or 89%) of
our students said that the inference was valid."

Function: shows that the *logical* form of the conventionalist
inferences is not intrinsically difficult to evaluate — so high
inference-task rates can't be dismissed as logical-difficulty
artifacts, and low inference-task rates aren't blocked by logical
form. -/
structure StampsFollowUp where
  n : Nat
  endorsementCount : Nat
  endorsementRate : Nat -- as integer percentage
  deriving Repr

/-- The Mary-stamps follow-up data (page 4:13). 27/31 = 89%
endorsement defuses the "logical-difficulty" alternative explanation
for the low embedded-SI rates of Exp 1a-b. -/
def maryStampsFollowUp : StampsFollowUp :=
  { n := 31, endorsementCount := 27, endorsementRate := 89 }

/-- @cite{chater-oaksford-1999}'s syllogism meta-analysis (paper §2
Worry #3, page 4:15): people endorse the valid `All A → All C`
syllogism ~90% of the time across independent experiments, and endorse
three superficially-similar *invalid* syllogisms ~63% on average. The
27pp valid-vs-invalid gap is the documented surface-similarity confound
that motivates the paradigm-bias hypothesis. -/
structure ChaterOaksfordDatum where
  validRate : Nat   -- % endorsement of valid syllogism
  invalidRate : Nat -- % endorsement of invalid syllogisms (averaged)
  deriving Repr

/-- The Chater-Oaksford data cited at page 4:15. -/
def chaterOaksfordSyllogisms : ChaterOaksfordDatum :=
  { validRate := 90, invalidRate := 63 }

end WorriesAboutParadigm

-- ============================================================================
-- §3  Experiment 2 — paradigm bias on simple sentences
-- ============================================================================

section ExperimentTwo

/-! ## §3 Experiment 2

Method (paper §3.1, page 4:16): 29 Dutch-speaking students at the
University of Nijmegen, within-subjects: same Dutch equivalent of
*Some of the B's are in the box on the left* (24) tested in both
inference and verification tasks (counterbalanced order: 15 inference-
first, 14 verification-first).

Stats (paper §3.2, page 4:17): no order effect (Fisher's Exact test,
inference p = .45, verification p = 1). Inference rate (62%) vs
verification rate (34%) significantly different (McNemar's test, n = 29,
p < .01). Filler control accuracy 97% (paper specifies this is for
*verification* fillers, ruling out positive response bias on the
verification side). -/

/-- Aggregate Exp 2 data (paper §3.2). -/
structure Exp2Data where
  inferenceRate : Nat            -- % deriving SI in inference task
  verificationRate : Nat         -- % deriving SI in verification task
  verificationFillerAccuracy : Nat  -- % correct on verification fillers
  n : Nat
  deriving Repr

/-- Exp 2 results from paper §3.2. The 28pp inference-vs-verification
gap (62% vs 34%) is the load-bearing inflation estimate the paper
carries into Exp 3; the 97% verification-filler accuracy rules out a
positive response bias on the verification side. The data IS the
finding — no separate trivial-arithmetic theorems are needed. -/
def exp2 : Exp2Data :=
  { inferenceRate := 62
  , verificationRate := 34
  , verificationFillerAccuracy := 97
  , n := 29 }

end ExperimentTwo

-- ============================================================================
-- §4  Monotonicity setup — predictions (25)–(27) for Exp 3
-- ============================================================================

/-! ## §4 Monotonicity setup

Paper §4 (pages 4:18–4:19) introduces the conventionalist predictions
tested in Exp 3:

- (25) DE contexts (`not all`, `not more than one`): no preference for
  local SIs — all theories agree (and `conventionalistPredictsLocalSI`
  returns `false` here).
- (26) UE contexts (`all`, `more than one`): mainstream conventionalism
  predicts local SIs are *preferred*.
- (27) NM context (`exactly two`): mainstream theories diverge here,
  none of them flatly predicting local SIs:
  - @cite{geurts-2009}: the default construal of (26) and (27) is
    *without* local SIs.
  - @cite{vanrooij-schulz-2004}: opinions are divided, but local SIs
    *can* occur in UE contexts.
  - @cite{chierchia-2004}: local SIs are *possible* in (26a,b) and
    (27), but not argued to be preferred.

`Exp3Row.verificationPred` and `inferencePred` encode the bracketed
predictions of Table 3 (page 4:22), which the paper attributes to the
*stronger* version of mainstream conventionalism (i.e. local SIs are
preferred in *all* non-DE environments). The flat
`conventionalistPredictsLocalSI` collapses the
"preferred"/"possible"/"divided"/"not default" distinctions the paper
preserves; consult the docstring on `predictsLocalSI` before reusing. -/

-- ============================================================================
-- §5  Experiment 3 — verification vs inference (Table 3)
-- ============================================================================

section ExperimentThree

/-! ## §5 Experiment 3

Method (paper §5.1, page 4:20): 26 first-year humanities students at
the University of Nijmegen, within-subjects: same five sentences (25)–(27)
tested in both verification and inference tasks. Verification block
first, then an unrelated experiment of about 20 minutes, then the
inference block. Verification used six items (since *exactly two* had
two verification conditions); inference used five.

Stats (paper §5.2, page 4:23): McNemar's with Bonferroni correction —
*all* p < .005, *not all* p < .001, *more than one* p < .0005, *not
more than one* p < .05, *exactly two* p < .005 (both conditions). -/

/-- One row of Exp 3 results (paper Table 3, page 4:22). The two
*exactly two* verification trials correspond to the two situations
described at page 4:21: one in which two squares are connected to
some-but-not-all of the circles while one square is connected to all
(mainstream conventionalism predicts "true"), and the converse
(mainstream predicts "false"). The bracketed numbers in Table 3 are
the *stronger*-version-of-mainstream-conventionalism trend predictions
captured here as `verificationPred` / `inferencePred`. -/
structure Exp3Row where
  quantifier : QuantifierContext
  /-- % saying "true" in verification task. -/
  verificationTrueRate : Nat
  /-- Conventionalist predicted trend for verification ("should say
  true"?) per Table 3. -/
  verificationPred : Bool
  /-- % endorsing local-SI inference task. -/
  inferenceRate : Nat
  /-- Conventionalist predicted trend for inference ("should endorse"?)
  per Table 3. -/
  inferencePred : Bool
  deriving Repr

/-- Experiment 3 results (paper Table 3, page 4:22, n = 26). -/
def exp3Results : List Exp3Row :=
  [ -- UE contexts
    { quantifier := .all,            verificationTrueRate := 100,
      verificationPred := false, inferenceRate := 46, inferencePred := true }
  , { quantifier := .moreThanOne,    verificationTrueRate := 100,
      verificationPred := false, inferenceRate := 62, inferencePred := true }
    -- NM context: two verification conditions, one inference
  , { quantifier := .exactlyTwo,     verificationTrueRate := 100,
      verificationPred := false, inferenceRate := 50, inferencePred := true }
  , { quantifier := .exactlyTwo,     verificationTrueRate := 0,
      verificationPred := true,  inferenceRate := 50, inferencePred := true }
    -- DE contexts
  , { quantifier := .notAll,         verificationTrueRate := 4,
      verificationPred := false, inferenceRate := 58, inferencePred := false }
  , { quantifier := .notMoreThanOne, verificationTrueRate := 4,
      verificationPred := false, inferenceRate := 46, inferencePred := false } ]

/-- Verification shows zero local SIs in UE contexts (100% "true",
accepting the classical reading), directly contradicting mainstream
conventionalism's prediction (Table 3 column predicts "false"). -/
theorem verification_no_local_SI_in_UE :
    exp3Results.filter (fun r => quantifierMonotonicity r.quantifier == .upward)
      |>.all (fun r => r.verificationTrueRate == 100) := by decide

/-- Verification rates perfectly track the *classical* (non-SI) truth
value: when the classical reading is true, verification ≥ 96%; when
false, ≤ 4%. Participants do not deploy the local-SI reading at all in
the verification task. -/
theorem verification_tracks_classical_reading :
    exp3Results.all
      (fun r => r.verificationTrueRate ≥ 96 ∨ r.verificationTrueRate ≤ 4) := by
  decide

/-- Conventionalism's predicted *trend* for verification is falsified
across all non-DE conditions: where Table 3 predicts "verification
should be 0" (i.e. "false"), the rate is overwhelmingly 100. -/
theorem verification_extremal_in_predicted_rows :
    exp3Results.all
      (fun r => r.verificationPred = false →
        r.verificationTrueRate ≥ 96 ∨ r.verificationTrueRate ≤ 4) := by
  decide

/-- Inference rates clustered around chance (paper §5.2 page 4:23: "all
rates, for DE and non-DE items alike, clustered around chance level,
give or take 12%" — i.e. roughly 38–62%). -/
theorem inference_clusters_around_chance :
    exp3Results.all
      (fun r => r.inferenceRate ≥ 38 ∧ r.inferenceRate ≤ 62) := by decide

/-- Inference rates from DE rows of `exp3Results`. -/
def deInferenceRates : List Nat :=
  (exp3Results.filter
    (fun r => quantifierMonotonicity r.quantifier == .downward)).map
      (·.inferenceRate)

/-- Inference rates from non-DE rows of `exp3Results`. -/
def nonDeInferenceRates : List Nat :=
  (exp3Results.filter
    (fun r => quantifierMonotonicity r.quantifier != .downward)).map
      (·.inferenceRate)

/-- Mean inference rate in DE conditions, derived from `exp3Results`.
Paper §5.2 reports 45% from raw counts; integer arithmetic over the
filtered rows gives `(58 + 46) / 2 = 52`. The discrepancy reflects
rounding in Table 3's reported proportions, not a substantive
difference. -/
def deInferenceMean : ℚ := (deInferenceRates.sum : ℚ) / deInferenceRates.length

/-- Mean inference rate in non-DE conditions, derived from
`exp3Results`. Paper §5.2 reports 51%; integer arithmetic yields 52
(see `deInferenceMean` docstring). -/
def nonDeInferenceMean : ℚ :=
  (nonDeInferenceRates.sum : ℚ) / nonDeInferenceRates.length

/-- Concrete numeric computation: non-DE conditions sum to 208 over
4 rows; DE conditions sum to 104 over 2 rows. Both yield mean 52. -/
private lemma exp3_sums :
    nonDeInferenceRates.sum = 208 ∧ deInferenceRates.sum = 104 ∧
    nonDeInferenceRates.length = 4 ∧ deInferenceRates.length = 2 := by decide

/-- The paper's "fails to coalesce into the predicted pattern"
disconfirmation (paper §5.2 page 4:23): both DE and non-DE inference
means lie within the "around 50%, give or take 12%" band the paper
explicitly delimits. The conventionalist-predicted pattern (non-DE
preference, DE no-preference) requires non-DE >> DE; instead both means
sit near chance. Note: paper reports 51%/45% from raw counts; this file
computes 52%/52% from rounded Table-3 percentages — the qualitative
"both within ±12 of 50%" claim survives either way. -/
theorem inference_means_within_chance_band :
    50 - 12 ≤ nonDeInferenceMean ∧ nonDeInferenceMean ≤ 50 + 12 ∧
    50 - 12 ≤ deInferenceMean   ∧ deInferenceMean   ≤ 50 + 12 := by
  obtain ⟨hN, hD, hLN, hLD⟩ := exp3_sums
  unfold nonDeInferenceMean deInferenceMean
  rw [hN, hD, hLN, hLD]; refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- After Exp 3 establishes the ~50% paradigm baseline in inference
tasks, the rates from Exp 1a–b for *all* (27%) and *want* (32%) are
*below* baseline — they may be entirely paradigm artifacts. Only
*think* (57.5% averaged) survives correction. -/
theorem think_above_50_others_below :
    lookupRate exp1aResults .all  ≤ (50 : Nat) ∧
    lookupRate exp1bResults .want ≤ (50 : Nat) ∧
    lookupRate exp1aResults .must ≤ (50 : Nat) ∧
    thinkAvgRate > (50 : ℚ) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  have h : (lookupRate exp1aResults .think + lookupRate exp1bResults .think : Nat)
      = 115 := by decide
  unfold thinkAvgRate
  rw [h]; norm_num

end ExperimentThree

-- ============================================================================
-- §6  Minimal conventionalism — auxiliary-assumption argument
-- ============================================================================

/-! ## §6 Minimal conventionalism setup

Paper §6 (pages 4:23–4:24) sets up Exp 4 by analyzing what *minimal*
conventionalism (the weakest form: "local-SI readings *exist*") would
predict. The argument:

1. In its bare form, minimal conventionalism makes no predictions
   (claim that (28a) "All the customers shot at some of the salesmen"
   may or may not be read as (28b) "All the customers shot at some but
   not all of the salesmen" cannot be falsified).
2. With the auxiliary assumption that native speakers can detect the
   readings their grammar makes available, minimal conventionalism
   *does* predict: in a situation that falsifies (28b), participants
   should claim either that (28a) is false or that it's ambiguous.
3. Exp 4 tests this by adding a "could be either" response option to
   Exp 3's verification task. -/

-- ============================================================================
-- §7  Experiment 4 — ambiguity-detection task (Tables 4, 5)
-- ============================================================================

section ExperimentFour

/-! ## §7 Experiment 4

Method (paper §7.1, pages 4:25–4:26): 22 first-year linguistics
students at University College London. Materials: Exp 3's verification
items translated to English, plus a third response option ("could be
either"), plus 5 ambiguous control sentences. 30 trials total in 10
pseudo-random orders. Conducted in a classroom with oral instructions
to ensure participants understood the notion of ambiguity (using
calibration items like "Visiting relatives can be boring" and "The
girl hit the boy with the telescope").

Stats (paper §7.2, page 4:26): Wilcoxon's Exact test W = 208, n = 20,
p < .0001 (n=20 reflects 2 exclusions from the 22 UCL participants)
for the difference between ambiguous-control rates (~70%) and critical
non-DE "could be either" rates (~6%). -/

/-- Response rates for critical and DE control items in Exp 4
(paper Table 4, page 4:27). The "either" rate is the load-bearing
diagnostic: minimal conventionalism predicts it should be high in
non-DE cases. -/
structure Exp4Row where
  quantifier : QuantifierContext
  /-- % saying "true" -/
  trueRate : Nat
  /-- % saying "false" -/
  falseRate : Nat
  /-- % saying "could be either" -/
  eitherRate : Nat
  deriving Repr

/-- Experiment 4 results (paper Table 4, page 4:27, n = 22). -/
def exp4Results : List Exp4Row :=
  [ -- UE contexts
    { quantifier := .all,            trueRate := 95,  falseRate := 5,  eitherRate := 0 }
  , { quantifier := .moreThanOne,    trueRate := 100, falseRate := 0,  eitherRate := 0 }
    -- NM context (two trials)
  , { quantifier := .exactlyTwo,     trueRate := 86,  falseRate := 5,  eitherRate := 9 }
  , { quantifier := .exactlyTwo,     trueRate := 9,   falseRate := 77, eitherRate := 14 }
    -- DE controls
  , { quantifier := .notAll,         trueRate := 9,   falseRate := 86, eitherRate := 5 }
  , { quantifier := .notMoreThanOne, trueRate := 9,   falseRate := 91, eitherRate := 0 } ]

/-- One ambiguous control item from Exp 4 (paper Table 5, page 4:27).
Sentences are quoted exactly as in the paper. -/
structure AmbiguityControl where
  sentence : String
  /-- % saying "could be either" -/
  eitherRate : Nat
  deriving Repr

/-- Ambiguous control items (paper Table 5, page 4:27). Sentences are
verbatim — note paper uses `the circles` and `the squares` with definite
articles in (29a), (29c)–(29e). -/
def genuineAmbiguityResults : List AmbiguityControl :=
  [ { sentence := "The circles and the squares are connected with each other"
    , eitherRate := 82 }
  , { sentence := "The green and the orange figures are connected with each other"
    , eitherRate := 73 }
  , { sentence := "All the figures are orange and green"
    , eitherRate := 59 }
  , { sentence := "There are green circles and squares"
    , eitherRate := 77 }
  , { sentence := "The circles and the squares have the same colour"
    , eitherRate := 59 } ]

/-- Either-rates from `genuineAmbiguityResults`, extracted for clean
arithmetic in `genuineAmbiguityMean`. -/
def genuineAmbiguityRates : List Nat :=
  genuineAmbiguityResults.map (·.eitherRate)

/-- Mean genuine-ambiguity detection across Table 5 items: (82+73+59+77+59)/5 = 70.
Paper §7.2 page 4:26 reports 70%. -/
def genuineAmbiguityMean : ℚ :=
  (genuineAmbiguityRates.sum : ℚ) / genuineAmbiguityRates.length

/-- Total non-DE trials in Exp 4: 4 critical items × 22 participants
(paper §7.2 page 4:26 footnote on the 9-of-88 calculation). -/
def exp4NonDeTotalResponses : Nat := 4 * 22

/-- Total non-DE trials in Exp 4 *consistent with minimal conventionalism*
(paper §7.2 page 4:26): "only 9 out of 88 responses". -/
def exp4NonDeConventionalistConsistent : Nat := 9

/-- The §7.2 disconfirmation of minimal conventionalism: critical-item
"either" rates (Table 4 non-DE rows) all sit at or below 14%, while
genuine-ambiguity controls (Table 5) average 70%. Participants reliably
detect *real* ambiguities but not the ones conventionalism predicts. -/
theorem either_rate_below_genuine_ambiguity :
    exp4Results.all (fun r => r.eitherRate ≤ 14) := by decide

/-- Total fraction of non-DE responses consistent with minimal
conventionalism (paper §7.2 page 4:26): "only 9 out of 88 responses
(i.e. 10%)". Stated as a ℚ inequality — the actual value is
9/88 ≈ 10.227%, which rounds to 10% per the paper's footnote 10. -/
theorem nonDe_consistent_with_minimal_at_10_percent :
    (exp4NonDeConventionalistConsistent : ℚ) / exp4NonDeTotalResponses
      < 11 / 100 := by
  unfold exp4NonDeConventionalistConsistent exp4NonDeTotalResponses
  norm_num

end ExperimentFour

-- ============================================================================
-- §8  Meanwhile in the Gricean camp — competence-based explanation
-- ============================================================================

section GriceanCamp

/-! ## §8 Gricean camp

Paper §8 (pages 4:28–4:29) sketches the Gricean explanation for the
one embedded condition that *did* yield elevated SI rates: *think*
(57.5%, the only one to survive Exp 3's paradigm correction).

The Gricean derivation proceeds in two steps. First, the global SI for
"Bob believes Anna ate some" yields the *primary* implicature (32):

  (32)  ¬K(Bob believes Anna ate all)

Second, if Bob is competent on whether Anna ate all (33):

  (33)  Bob believes all ∨ Bob believes ¬all

then (32) + (33) entail (34): "Bob believes Anna didn't eat all." This
*looks* like a local SI but is derived from global pragmatics +
competence. The same derivation does not generalize to universal
quantifiers (paper example (35)–(38)) because the analogous auxiliary
(38) is a *collective* uniformity assumption "considerably less
plausible" than (33).

Footnote 11 (page 4:28) lists the references for the Gricean
derivation of seemingly-embedded SIs that the §8 argument is built on:
@cite{recanati-2003}, @cite{sauerland-2004}, @cite{vanrooij-schulz-2004},
@cite{geurts-2006}, @cite{geurts-2009}, @cite{russell-2006},
@cite{spector-2006}. None of @cite{russell-2006}, @cite{spector-2006},
or @cite{geurts-2006} are formalized in linglib yet. -/

/-- The §8 derivation routed through the canonical Sauerland-style
competence machinery in `Implicature.Competence`. The paper's claim is
that *given* the speaker has a determinate negative stance about the
alternative (here `.disbelief` — speaker believes ¬(Bob-believes-all))
*and* the competence assumption (33), the strong implicature is
derived. The spine's `processAlternative true .disbelief` produces the
strong-derived flag exactly when these conditions hold; this theorem
exhibits the spine's `outcome_ii_strong` machinery applied to the §8
think-reading derivation. -/
theorem competence_explains_think_via_processAlternative :
    let p := Implicature.Competence.processAlternative true .disbelief
    p.weakHolds = true ∧ p.competenceAssumed = true ∧ p.strongDerived = true :=
  Implicature.Competence.outcome_ii_strong

/-- The same derivation chain *applied to universal quantifiers*
(paper §8 (35)–(38)). For "All the customers shot at some of the
salesmen" the Gricean primary implicature is (36) "Not all the
customers shot at all the salesmen", i.e. `¬ ∀ c s, Shot c s`. The
conventionalist construal (37) is "All the customers shot at some but
not all of the salesmen (hence, *none of the customers* shot at all the
salesmen)". The auxiliary needed to bridge (36) → (37)'s parenthetical
is (38):

  Either all the customers shot at all the salesmen, or none of the
  customers shot at all the salesmen.

This is a *collective uniformity* assumption — `(∀c∀s, Shot c s) ∨
(∀c, ¬∀s, Shot c s)` — not a per-customer competence. The paper's
substantive claim (page 4:29) is that (38) is "considerably less
plausible than (33)": (33) only stipulates that one opinion-holder
(Bob) has a determinate stance, whereas (38) requires that *every*
customer's behavior partition the same way (all-shot-all or
none-shot-all, with no in-between distribution). *Implausibility* is
not formalized; this theorem captures the formal half of the §8
argument, licensing the gap between "the inference goes through under
(38)" and "(38) is independently warranted." -/
theorem gricean_derivation_for_universals_requires_uniformity
    {Customer Salesman : Type} (Shot : Customer → Salesman → Prop)
    (globalSI : ¬ ∀ c s, Shot c s)
    (uniformity : (∀ c s, Shot c s) ∨ (∀ c, ¬ ∀ s, Shot c s)) :
    ∀ c, ¬ ∀ s, Shot c s :=
  uniformity.elim (fun h => absurd h globalSI) id

end GriceanCamp

-- ============================================================================
-- Bridge to Implicature spine + canonical SomeAllWorld model
-- ============================================================================

section ImplicatureSpineBridge

/-! ## Bridge: ∅-condition SI as `Implicature SomeAllWorld`

Wraps the canonical *some*-derived SI as an `Implicature` value over
the canonical `SomeAllWorld` model from `Phenomena.ScalarImplicatures.Basic`,
exercising the spine in `Defs.lean` and the diagnostics in
`Diagnostics.lean`. -/

open SomeAllWorld

/-- The neo-Gricean SI derived from *some students passed* in a UE
context (paper §1's ∅-condition). Mechanism is the Sauerland Standard
Recipe / neo-Gricean derivation; the SI content is `notUniversal`
(= the canonical "not all" inference from `SomeAllWorld`). -/
def somePassedSI : Implicature SomeAllWorld :=
  { kind := .scalar
  , content := notUniversal
  , altsUsed := {universal}
  , mechanism := .neoGricean }

/-- The SI is *reinforceable*: there's an assertion-world (`.all`)
where the assertion holds but the inferred content fails — so adding
"…but not all" is non-redundant. -/
theorem somePassedSI_isReinforceable :
    Implicature.IsReinforceable atLeastOne somePassedSI :=
  ⟨.all, trivial, fun h => h trivial⟩

/-- The SI is *cancellable* (Sadock 1978's diagnostic), via the
spine's `IsReinforceable.toCancellable`. -/
theorem somePassedSI_isCancellable :
    Implicature.IsCancellable atLeastOne somePassedSI :=
  Implicature.IsReinforceable.toCancellable somePassedSI_isReinforceable

/-- The neo-Gricean SI for `somePassedSI` corresponds to the
∅-condition tested in Experiments 1a-b, where the empirical SI
endorsement rate is 93% (Exp 1a) and 94% (Exp 1b). The spine bridge is
anchored in the data. -/
theorem somePassedSI_corresponds_to_unembedded_data :
    lookupRate exp1aResults .simple = 93 ∧
    lookupRate exp1bResults .simple = 94 := by decide

end ImplicatureSpineBridge

-- ============================================================================
-- Bridge to Embedded.Attitudes
-- ============================================================================

section AttitudesBridge

/-! ## Bridge: *think* condition ↔ `AttitudeInterpretation.local_`

The §1 *think* condition tests whether participants endorse the
attitude-embedded SI ("Betty thinks Fred didn't hear all the Verdi
operas" inferred from "Betty thinks Fred heard some of the Verdi
operas"). This is exactly the `AttitudeInterpretation.local_` reading
formalized in `Embedded/Attitudes.lean`: the strengthened *some* sits
inside Betty's belief-content. The cross-experiment 57.5% endorsement
rate measures how often participants compute `local_` rather than
`global`. -/

open Phenomena.ScalarImplicatures.Embedded.Attitudes

/-- The paper's *think* condition tests endorsement of the *local*
attitude reading, which `Embedded/Attitudes.lean` formalizes as
`AttitudeInterpretation.local_`. The empirical rate (57.5%) measures
the local-vs-global preference; the paper's §8 Gricean derivation
explains it via Bob-style competence on a single opinion-holder. -/
theorem think_condition_corresponds_to_local_attitude :
    -- empirical anchor
    thinkAvgRate = 575 / 10 ∧
    -- the local-attitude interpretation excludes the all-belief world
    -- (i.e., the Local interpretation strictly distinguishes
    -- "thinks-some" from "thinks-all")
    believesSomeMeaning .local_ ⟨.all, .all⟩ = false := by
  refine ⟨?_, ?_⟩
  · have h : (lookupRate exp1aResults .think + lookupRate exp1bResults .think : Nat)
        = 115 := by decide
    unfold thinkAvgRate; rw [h]; norm_num
  · rfl

end AttitudesBridge

/-! ## §Conclusion: Chierchia et al. (39)

Paper §Conclusion (page 4:30) example (39) is the marked contrastive
construction @cite{chierchia-fox-spector-2008} cite as evidence for
embedded SI: "If you take a salad OR desert, you pay $20; but if you
take BOTH there is a surcharge" (paper's typo "desert" preserved).
Geurts & Pouscoulous's punchline: such examples are *strongly marked*,
in which "the contrast between *or* and *both* is essential" — not
generic embedded-SI evidence. The paper's verdict (page 4:31) is that
mainstream conventionalism's defense "primarily relies on data that
are strongly marked, like (39), for example."

## Appendix

Sample stimulus pairs from Experiments 1a-b live in the paper's
appendix (page 4:31) and the separately available background-materials
file (doi:10.3765/sp.2.4a); they are not reproduced here. -/

end Phenomena.ScalarImplicatures.Studies.GeurtsPouscoulous2009
