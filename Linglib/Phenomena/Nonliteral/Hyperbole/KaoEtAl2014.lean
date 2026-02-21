import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Lexical.Numeral.Semantics
import Linglib.Theories.Semantics.Lexical.Numeral.Precision
import Linglib.Tactics.RSAPredict

/-!
# Kao et al. (2014) @cite{kao-etal-2014-hyperbole}

"Nonliteral understanding of number words"
PNAS 111(33): 12002-12007

## Experimental Design

Participants heard price utterances ("It cost $X") about items with known
typical prices (electric kettles, laptops, watches). Three experiments
measured: (3a) price priors, (3b) affect priors conditional on price,
(3c) listener interpretations of literal, hyperbolic, and round/sharp
utterances.

## The Model

Speakers may use literally false utterances to convey *affective* information
when the listener is uncertain about the speaker's communicative goal.

    S1(u|s,a,g) ∝ exp(α · [ln L0(g(s,a)|u) - C(u)])           [Eq. 5,7]

where g composes precision (exact vs approximate) with relevance (price,
affect, or both), yielding 5 distinct goals.

L1 marginalizes over goals:

    L1(s,a|u) ∝ P_S(s) · P_A(a|s) · Σ_g P_G(g) · S1(u|s,a,g)  [Eq. 10]

## Grounding

Price semantics is grounded in `HasDegree`. The literal meaning of
"fifty dollars" is `numeralExact 50 price` — the price equals $50.

## Qualitative Findings

Any model of hyperbole should account for these 6 findings:

| # | Finding | Theorem |
|---|---------|---------|
| 1 | At the inferred price, the listener infers notable affect | `hyperbole_affect_at_modal` |
| 2 | Marginal notable affect > no affect for hyperbolic utterances | `hyperbole_affect` |
| 3 | Listener infers speaker's QUD is valence, not price | `hyperbole_qud` |
| 4 | Literal utterance → listener infers correct price | `literal_correct` |
| 5 | Literal utterance is not interpreted hyperbolically | `literal_not_hyperbolic` |
| 6 | Sharp numbers interpreted more precisely than round | `halo_sharp_500` |
-/

set_option autoImplicit false

namespace Phenomena.Nonliteral.Hyperbole.KaoEtAl2014

open Core.Scale (HasDegree)
open Semantics.Lexical.Numeral (MeasurePredicate DegreePhrase measureSentence numeralExact)
open Real (exp log exp_pos)

-- ============================================================================
-- §1. Empirical Findings
-- ============================================================================

/-- The 6 qualitative findings from Kao et al. (2014) Experiments 3a–3c.
    Each model of hyperbole should formalize and prove all 6 findings. -/
inductive Finding where
  /-- Hearing "$10,000" for a kettle, the listener infers notable affect
      at the modal price (the most likely actual price under the posterior). -/
  | affect_at_modal
  /-- Marginalizing over all prices, notable affect dominates for "$10,000":
      Σ_s P(s, notable | "$10K") > Σ_s P(s, none | "$10K"). -/
  | affect_marginal
  /-- The listener infers the speaker's communicative goal (QUD) is to
      express valence/affect rather than to communicate exact price. -/
  | qud_valence
  /-- Hearing "$50" for a $50 kettle, the listener infers the correct price:
      P($50 | "$50") > P($500 | "$50"). -/
  | literal_correct
  /-- Literal utterances are not interpreted hyperbolically:
      P($50 | "$50") > P($10K | "$50"). -/
  | literal_not_hyperbolic
  /-- Sharp numbers are interpreted more precisely than round numbers:
      P(exact match | "$501") > P(exact match | "$500"). -/
  | halo_sharp_precise
  deriving DecidableEq, BEq, Repr

/-- All findings from the paper. -/
def findings : List Finding :=
  [.affect_at_modal, .affect_marginal, .qud_valence,
   .literal_correct, .literal_not_hyperbolic, .halo_sharp_precise]

-- ============================================================================
-- §2. Domain Types
-- ============================================================================

/-- Item types (Experiments 3a/3b): electric kettles, laptops, watches. -/
inductive Item where
  | electricKettle | laptop | watch
  deriving Repr, DecidableEq, BEq

/-- Price states: round/sharp pairs {50,51,500,501,...,10000,10001}. -/
inductive PriceState where
  | s50 | s51 | s500 | s501 | s1000 | s1001 | s5000 | s5001 | s10000 | s10001
  deriving Repr, DecidableEq, BEq

def PriceState.value : PriceState → ℚ
  | .s50 => 50 | .s51 => 51 | .s500 => 500 | .s501 => 501
  | .s1000 => 1000 | .s1001 => 1001 | .s5000 => 5000 | .s5001 => 5001
  | .s10000 => 10000 | .s10001 => 10001

instance : HasDegree PriceState where degree := PriceState.value

/-- Affect: no affect vs notable affect. -/
inductive Affect where
  | none | notable
  deriving Repr, DecidableEq, BEq

abbrev World := PriceState × Affect

/-- Communicative goals: 5 = (3 relevance × 2 precision) minus 1 collapse. -/
inductive Goal where
  | price | valence | priceValence | approxPrice | approxPriceValence
  deriving Repr, DecidableEq, BEq

instance : Fintype PriceState where
  elems := {.s50, .s51, .s500, .s501, .s1000, .s1001, .s5000, .s5001, .s10000, .s10001}
  complete := fun x => by cases x <;> simp

instance : Fintype Affect where
  elems := {.none, .notable}
  complete := fun x => by cases x <;> simp

instance : Fintype Goal where
  elems := {.price, .valence, .priceValence, .approxPrice, .approxPriceValence}
  complete := fun x => by cases x <;> simp

instance : Fintype Item where
  elems := {.electricKettle, .laptop, .watch}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Priors
-- ============================================================================

/-- Price prior P_S (Experiment 3a). Unnormalized. -/
def pricePrior (item : Item) : PriceState → ℝ
  | .s50    => match item with | .electricKettle => 4205 | .laptop => 1 | .watch => 3
  | .s51    => match item with | .electricKettle => 3865 | .laptop => 1 | .watch => 3
  | .s500   => match item with | .electricKettle => 533  | .laptop => 6 | .watch => 4
  | .s501   => match item with | .electricKettle => 538  | .laptop => 6 | .watch => 4
  | .s1000  => match item with | .electricKettle => 223  | .laptop => 4 | .watch => 3
  | .s1001  => match item with | .electricKettle => 211  | .laptop => 4 | .watch => 3
  | .s5000  => match item with | .electricKettle => 112  | .laptop => 3 | .watch => 3
  | .s5001  => match item with | .electricKettle => 111  | .laptop => 3 | .watch => 3
  | .s10000 => match item with | .electricKettle => 83   | .laptop => 2 | .watch => 3
  | .s10001 => match item with | .electricKettle => 120  | .laptop => 2 | .watch => 3

/-- Affect prior P_A(a|s) (Experiment 3b). Unnormalized (pairs sum to 10000). -/
def affectPrior : PriceState → Affect → ℝ
  | .s50,    .none => 6827 | .s50,    .notable => 3173
  | .s51,    .none => 6827 | .s51,    .notable => 3173
  | .s500,   .none => 2080 | .s500,   .notable => 7920
  | .s501,   .none => 2080 | .s501,   .notable => 7920
  | .s1000,  .none => 1067 | .s1000,  .notable => 8933
  | .s1001,  .none => 1067 | .s1001,  .notable => 8933
  | .s5000,  .none => 476  | .s5000,  .notable => 9524
  | .s5001,  .none => 476  | .s5001,  .notable => 9524
  | .s10000, .none => 136  | .s10000, .notable => 9864
  | .s10001, .none => 136  | .s10001, .notable => 9864

-- ============================================================================
-- §3. Utterance Cost
-- ============================================================================

def PriceState.isRound : PriceState → Bool
  | .s50 | .s500 | .s1000 | .s5000 | .s10000 => true
  | .s51 | .s501 | .s1001 | .s5001 | .s10001 => false

/-- C(round) = 0, C(sharp) = 1. -/
noncomputable def cost : PriceState → ℝ
  | u => if u.isRound then 0 else 1

-- ============================================================================
-- §4. Compositional Literal Semantics
-- ============================================================================

def costPredicate : MeasurePredicate PriceState :=
  MeasurePredicate.fromHasDegree PriceState "price (USD)"

def literalCompositional (u : PriceState) (world : PriceState) : Bool :=
  measureSentence costPredicate world (DegreePhrase.ofRat u.value "dollars")

def literal (u : PriceState) (world : PriceState) : Bool :=
  numeralExact u.value world

theorem literal_eq_compositional (u world : PriceState) :
    literal u world = literalCompositional u world := rfl

theorem literal_uses_degree (u world : PriceState) :
    literal u world = (HasDegree.degree world == u.value) := rfl

theorem costPredicate_is_hasDegree :
    costPredicate.μ = HasDegree.degree := rfl

-- ============================================================================
-- §5. Meaning & QUD Projection
-- ============================================================================

/-- L0(s,a|u) = P_A(a|s) if s = u, 0 otherwise. [Eq. 9] -/
def meaning (_q : Goal) (u : PriceState) (w : World) : ℝ :=
  if u == w.1 then affectPrior w.1 w.2 else 0

def PriceState.round : PriceState → PriceState
  | .s50 | .s51 => .s50 | .s500 | .s501 => .s500 | .s1000 | .s1001 => .s1000
  | .s5000 | .s5001 => .s5000 | .s10000 | .s10001 => .s10000

def PriceState.toIdx : PriceState → ℕ
  | .s50 => 0 | .s51 => 1 | .s500 => 2 | .s501 => 3 | .s1000 => 4
  | .s1001 => 5 | .s5000 => 6 | .s5001 => 7 | .s10000 => 8 | .s10001 => 9

def Affect.toIdx : Affect → ℕ
  | .none => 0 | .notable => 1

/-- QUD projection function [Eq. 6]: maps a world to its equivalence-class tag.
    Two worlds are QUD-equivalent iff `project w₁ q = project w₂ q`. -/
def project (w : World) (q : Goal) : ℕ :=
  match q with
  | .price              => w.1.toIdx
  | .valence            => w.2.toIdx
  | .priceValence       => w.1.toIdx * 2 + w.2.toIdx
  | .approxPrice        => w.1.round.toIdx
  | .approxPriceValence => w.1.round.toIdx * 2 + w.2.toIdx

/-- Sum L0 over the QUD equivalence class of w under goal q.
    The class is derived from `project`: {w' | project w' q = project w q}. -/
noncomputable def qudProject (q : Goal) (f : World → ℝ) (w : World) : ℝ :=
  (Finset.univ.filter (fun w' => project w' q = project w q)).sum f

-- ============================================================================
-- §6. RSAConfig
-- ============================================================================

/-- Kao et al. (2014) hyperbole model, parametric in item. -/
noncomputable def cfg (item : Item) : RSA.RSAConfig PriceState World where
  Latent := Goal
  meaning := meaning
  meaning_nonneg := by
    intro q u ⟨s, a⟩; simp only [meaning]
    split <;> (try exact le_refl 0)
    cases s <;> cases a <;> simp [affectPrior]
  s1Score l0 α q w u :=
    let projected := qudProject q (l0 u) w
    if projected = 0 then 0
    else exp (α * (log projected - cost u))
  s1Score_nonneg _ _ _ _ _ _ _ := by
    simp only; split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 1
  α_pos := one_pos
  worldPrior := fun ⟨s, a⟩ => pricePrior item s * affectPrior s a
  latentPrior_nonneg _ _ := by positivity
  worldPrior_nonneg := by
    intro ⟨s, a⟩; apply mul_nonneg
    · cases item <;> cases s <;> simp [pricePrior]
    · cases s <;> cases a <;> simp [affectPrior]

noncomputable abbrev kettleCfg := cfg .electricKettle

-- ============================================================================
-- §7. Bridge Theorems
-- ============================================================================

-- Hyperbole: "$10,000" for an electric kettle

set_option maxHeartbeats 400000 in
/-- At the modal price ($10K), notable affect > no affect.
    The speaker saying "$10K" about a kettle signals frustration. -/
theorem hyperbole_affect_at_modal :
    kettleCfg.L1 .s10000 (.s10000, .notable) >
    kettleCfg.L1 .s10000 (.s10000, .none) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Marginal: notable affect dominates overall for "$10K".
    Σ_s L1(s, notable | "$10K") > Σ_s L1(s, none | "$10K"). -/
theorem hyperbole_affect :
    kettleCfg.L1 .s10000 (.s50, .notable) + kettleCfg.L1 .s10000 (.s51, .notable) +
    kettleCfg.L1 .s10000 (.s500, .notable) + kettleCfg.L1 .s10000 (.s501, .notable) +
    kettleCfg.L1 .s10000 (.s1000, .notable) + kettleCfg.L1 .s10000 (.s1001, .notable) +
    kettleCfg.L1 .s10000 (.s5000, .notable) + kettleCfg.L1 .s10000 (.s5001, .notable) +
    kettleCfg.L1 .s10000 (.s10000, .notable) + kettleCfg.L1 .s10000 (.s10001, .notable) >
    kettleCfg.L1 .s10000 (.s50, .none) + kettleCfg.L1 .s10000 (.s51, .none) +
    kettleCfg.L1 .s10000 (.s500, .none) + kettleCfg.L1 .s10000 (.s501, .none) +
    kettleCfg.L1 .s10000 (.s1000, .none) + kettleCfg.L1 .s10000 (.s1001, .none) +
    kettleCfg.L1 .s10000 (.s5000, .none) + kettleCfg.L1 .s10000 (.s5001, .none) +
    kettleCfg.L1 .s10000 (.s10000, .none) + kettleCfg.L1 .s10000 (.s10001, .none) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- The listener infers valence QUD over price QUD. -/
theorem hyperbole_qud :
    kettleCfg.L1_latent .s10000 .valence >
    kettleCfg.L1_latent .s10000 .price := by
  rsa_predict

-- Literal: "$50" for an electric kettle

set_option maxHeartbeats 400000 in
/-- Hearing "$50", the listener infers $50 > $500. -/
theorem literal_correct :
    kettleCfg.L1 .s50 (.s50, .none) >
    kettleCfg.L1 .s50 (.s500, .none) := by
  rsa_predict

set_option maxHeartbeats 400000 in
/-- Literal utterances are not interpreted hyperbolically. -/
theorem literal_not_hyperbolic :
    kettleCfg.L1 .s50 (.s50, .none) >
    kettleCfg.L1 .s50 (.s10000, .none) := by
  rsa_predict

-- Pragmatic halo: round vs sharp numbers

set_option maxHeartbeats 400000 in
/-- Sharp "$501" is interpreted more precisely than round "$500". -/
theorem halo_sharp_500 :
    kettleCfg.L1 .s501 (.s501, .none) + kettleCfg.L1 .s501 (.s501, .notable) >
    kettleCfg.L1 .s500 (.s500, .none) + kettleCfg.L1 .s500 (.s500, .notable) := by
  rsa_predict

-- ============================================================================
-- §8. Verification: every finding from the paper is accounted for
-- ============================================================================

/-- Map each empirical finding to the RSA model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .affect_at_modal =>
      kettleCfg.L1 .s10000 (.s10000, .notable) >
      kettleCfg.L1 .s10000 (.s10000, .none)
  | .affect_marginal =>
      kettleCfg.L1 .s10000 (.s50, .notable) + kettleCfg.L1 .s10000 (.s51, .notable) +
      kettleCfg.L1 .s10000 (.s500, .notable) + kettleCfg.L1 .s10000 (.s501, .notable) +
      kettleCfg.L1 .s10000 (.s1000, .notable) + kettleCfg.L1 .s10000 (.s1001, .notable) +
      kettleCfg.L1 .s10000 (.s5000, .notable) + kettleCfg.L1 .s10000 (.s5001, .notable) +
      kettleCfg.L1 .s10000 (.s10000, .notable) + kettleCfg.L1 .s10000 (.s10001, .notable) >
      kettleCfg.L1 .s10000 (.s50, .none) + kettleCfg.L1 .s10000 (.s51, .none) +
      kettleCfg.L1 .s10000 (.s500, .none) + kettleCfg.L1 .s10000 (.s501, .none) +
      kettleCfg.L1 .s10000 (.s1000, .none) + kettleCfg.L1 .s10000 (.s1001, .none) +
      kettleCfg.L1 .s10000 (.s5000, .none) + kettleCfg.L1 .s10000 (.s5001, .none) +
      kettleCfg.L1 .s10000 (.s10000, .none) + kettleCfg.L1 .s10000 (.s10001, .none)
  | .qud_valence =>
      kettleCfg.L1_latent .s10000 .valence >
      kettleCfg.L1_latent .s10000 .price
  | .literal_correct =>
      kettleCfg.L1 .s50 (.s50, .none) >
      kettleCfg.L1 .s50 (.s500, .none)
  | .literal_not_hyperbolic =>
      kettleCfg.L1 .s50 (.s50, .none) >
      kettleCfg.L1 .s50 (.s10000, .none)
  | .halo_sharp_precise =>
      kettleCfg.L1 .s501 (.s501, .none) + kettleCfg.L1 .s501 (.s501, .notable) >
      kettleCfg.L1 .s500 (.s500, .none) + kettleCfg.L1 .s500 (.s500, .notable)

/-- The RSA model accounts for all 6 empirical findings from Kao et al. (2014). -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact hyperbole_affect_at_modal
  · exact hyperbole_affect
  · exact hyperbole_qud
  · exact literal_correct
  · exact literal_not_hyperbolic
  · exact halo_sharp_500

end Phenomena.Nonliteral.Hyperbole.KaoEtAl2014
