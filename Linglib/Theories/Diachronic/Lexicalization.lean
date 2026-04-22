import Linglib.Core.Efficiency
import Linglib.Core.InformationTheory
import Linglib.Theories.Pragmatics.RSA.ConfigData

/-!
# Lexicalization: Efficient Encoding of Emerging Concepts
@cite{xu-etal-2024}

Inaugural module of `Theories/Diachronic/`: formal theories of language change.

Xu et al. (2024) unify word reuse and combination (compounding) under a single
information-theoretic account. Both strategies for encoding novel concepts are
shaped by the same tradeoff between minimizing speaker effort (word length)
and minimizing information loss (listener confusion). Attested encodings in
English, French, and Finnish sit near the Pareto frontier of this tradeoff.

## Architecture

The model extends RSA's speaker-listener framework to lexicon evolution:

- The **listener** uses prototype-based categorization (Eq. 1) — an L0
  whose meaning function is `exp(-γ · d(c, q_w))`.
- The **speaker** trades off informativity against word-length cost — an S1
  with `beliefAction` scoring where `cost(w) = β · l(w)`.
- The **encoding** E* is the set of (concept, form) pairs for emerging
  concepts. Its efficiency is measured against the Pareto frontier
  of possible encodings (`Core.Efficiency`).

## Connection to LCEC

The LCEC (`Morphology.WP.LCEC`) states that I-complexity (conditional entropy
across paradigm cells) is uniformly low despite high E-complexity. The analog
here: lexicons maintain low information loss despite high polysemy, because
reuse and compounding are informationally efficient. Both are instances of a
general principle: natural languages achieve low integrative complexity despite
high enumerative complexity, via structured redundancy.
-/

namespace Diachronic.Lexicalization

open Core.Efficiency Core.InformationTheory

-- ============================================================================
-- §1. Lexicalization Strategies
-- ============================================================================

/-- Strategy by which a novel concept enters the lexicon.
    @cite{xu-etal-2024} Table 1: reuse items (R) vs. compounds (C). -/
inductive Strategy where
  /-- Reuse an existing word for a new meaning.
      E.g., "mouse" (rodent → peripheral), "dish" (plate → antenna). -/
  | reuse
  /-- Combine existing words into a compound.
      E.g., "birthday card", "spreadsheet", "urban renewal". -/
  | combination
  deriving DecidableEq, Repr

/-- Literality of the form-meaning relationship.
    Literal items are semantically transparent and tend to be more
    communicatively efficient (@cite{xu-etal-2024} §Item-Level Variation). -/
inductive Literality where
  /-- Literal: form directly relates to the intended concept.
      - Reuse: intended meaning is a hyponym of the existing sense.
      - Combination: endocentric compound (head = superordinate). -/
  | literal
  /-- Nonliteral: metaphorical or metonymic relationship.
      - Reuse: e.g., "mouse" for computer peripheral.
      - Combination: exocentric, e.g., "boîte noire" = flight recorder. -/
  | nonliteral
  deriving DecidableEq, Repr

/-- A form-concept pair in an emerging encoding (one entry in E*). -/
structure FormConceptPair where
  form : String
  concept : String
  strategy : Strategy
  literality : Literality
  formLength : ℕ := form.length
  deriving Repr

-- ============================================================================
-- §2. Communicative Costs (Eqs. 2–3, 5)
-- ============================================================================

/-- Communicative costs of an encoding, parameterized by a listener model.

    `listenerScore concept form` is the probability that the listener
    recovers `concept` from `form`. In @cite{xu-etal-2024}, this is the
    prototype-based categorization model (Eq. 1):
      m̂_{w,L}(c) ∝ exp{-γ · d(c, q_w)}.

    Effort (Eq. 2) = expected word length.
    Information loss (Eq. 3) = expected surprisal under listener distribution.
    The aggregate is weighted by concept need probability. -/
noncomputable def encodingCosts
    (pairs : List FormConceptPair)
    (needProb : String → ℝ)
    (listenerScore : String → String → ℝ) : CostPair where
  cost₁ := (pairs.map fun p => needProb p.concept * (p.formLength : ℝ)).sum
  cost₂ := (pairs.map fun p =>
    let score := listenerScore p.concept p.form
    needProb p.concept * if score ≤ 0 then 20 else -Real.log score).sum

/-- Unified objective (Eq. 5): L_β = info_loss + β · effort.
    Parameterizes the Pareto frontier. Cost₂ is in nats; multiply by
    `1 / Real.log 2` to convert to bits. -/
noncomputable def unifiedObjective
    (pairs : List FormConceptPair)
    (needProb : String → ℝ)
    (listenerScore : String → String → ℝ)
    (β : ℝ) : ℝ :=
  weightedCost (encodingCosts pairs needProb listenerScore) β

-- ============================================================================
-- §3. RSA Connection
-- ============================================================================

/-- The prototype-based listener IS an RSA L0, and the unified objective
    IS an S1 with `beliefAction` scoring.

    To instantiate: set `RSAConfigData` with
    - `U := Form`, `W := Concept`
    - `meaning _ c w := exp(-γ · d(c, prototype(w)))`
    - `s1Spec := .beliefAction (fun w => β * length(w))`

    This function constructs the corresponding S1 scoring rule. -/
def asS1ScoreSpec (β : ℚ) (length : String → ℚ) :
    RSA.S1ScoreSpec String String Unit :=
  .beliefAction (fun w => β * length w)

-- ============================================================================
-- §4. Theoretical Claims
-- ============================================================================

/-- **Efficiency Claim** (Figs. 2–3): attested encodings are closer to the
    Pareto frontier than baseline encodings (random or near-synonym). -/
def moreEfficientThan (attested baseline : CostPair)
    (optimalAt : ℝ → CostPair) (βs : List ℝ) : Prop :=
  efficiencyLoss attested optimalAt βs < efficiencyLoss baseline optimalAt βs

/-- **Strategy Tradeoff** (§Strategy Comparison): reuse items tend shorter;
    compounds tend more informative. The two strategies occupy complementary
    regions of the effort-informativity space. -/
def strategyTradeoff (reuseCosts compoundCosts : CostPair) : Prop :=
  reuseCosts.cost₁ ≤ compoundCosts.cost₁ ∧
  compoundCosts.cost₂ ≤ reuseCosts.cost₂

/-- **Literal Advantage** (§Item-Level Variation): literal items (hyponymic
    reuse, endocentric compounds) are more efficient than nonliteral ones,
    because semantic transparency reduces information loss. -/
def literalAdvantage (literalCosts nonliteralCosts : CostPair)
    (optimalAt : ℝ → CostPair) (βs : List ℝ) : Prop :=
  efficiencyLoss literalCosts optimalAt βs ≤
  efficiencyLoss nonliteralCosts optimalAt βs

end Diachronic.Lexicalization
