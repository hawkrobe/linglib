import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Semantics.PresuppositionContext
import Linglib.Phenomena.Plurals.Multiplicity
import Linglib.Phenomena.Plurals.Studies.Sauerland2003
import Linglib.Theories.Semantics.Presupposition.PhiFeatures
import Linglib.Theories.Semantics.Presupposition.MaximizePresupposition
import Linglib.Theories.Semantics.Exhaustification.PresuppositionalExhaustification
import Linglib.Theories.Semantics.Dynamic.Bilateral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Enguehard (2024): What Number Marking on Indefinites Means
@cite{enguehard-2024}

Enguehard, Émile. 2024. What number marking on indefinites means:
conceivability presuppositions and sensitivity to probabilities.
*Proceedings of Sinn und Bedeutung 28*, 289–302.

## Core Contributions

1. **Conceivability presupposition** (generalization 7): a sg (resp. pl)
   indefinite presupposes that it is conceivable the witness set has
   exactly one (resp. more than one) member. This presupposition projects
   under negation, questions, and conditionals — unlike scalar
   implicatures which are blocked in DE environments.

2. **Gradient sensitivity** (§3): an experiment shows that speakers'
   number choice on negated indefinites tracks the probability
   distribution over witness-set cardinalities, not a categorical
   presuppositional or MP-based boundary.

3. **Forward-looking cooperation** (§5.3, principle 23): speakers choose
   number to set up discourse referents whose number feature will be
   useful in potential continuations — a Manner-like maxim sensitive to
   prototypicality.

4. **Dynamic potential** (§5.1–5.2): negated indefinites introduce
   discourse referents accessible in bilateral dynamic semantics
   (@cite{elliott-2020}); the number feature on these referents constrains
   future pronoun binding, grounding the forward-looking principle.

## Integration Points

- `PhiFeatures.sgCardConceivable` / `plCardConceivable` — the
  conceivability presuppositions defined in §7 of `PhiFeatures.lean`
- `Sauerland2003` — challenges MP-derived complementary distribution
- `Multiplicity` — challenges the implicature theory's categorical
  predictions with gradient production data
- `MaximizePresupposition.phiMP` — MP is underdetermined when both
  conceivability presuppositions are satisfied
- `PresuppositionContext.presupSatisfiable` — conceivability =
  satisfiability in context

## Relation to Sauerland (2003)

@cite{sauerland-2003} treats `plSem` as vacuous (no presupposition).
Enguehard argues that **indefinite** plurals DO carry a non-trivial
conceivability presupposition — not about the entity but about the
*predicate's extension*. This refines rather than replaces Sauerland:
- For definites, `sgSem`/`plSem` with entity-level presuppositions remain
  appropriate (the referent is known).
- For indefinites (especially under negation), the conceivability
  presupposition governs number choice: the cardinality must be
  *conceivable*, not *actual*.
-/

set_option autoImplicit false

namespace Phenomena.Plurals.Studies.Enguehard2024

open Core.Presupposition (PrProp)
open Presupposition.PhiFeatures

-- ============================================================================
-- §1  Core Types
-- ============================================================================

/-- Indefinite number marking: the two-way contrast. -/
inductive IndefNumber where
  | sg | pl
  deriving DecidableEq, Repr, Inhabited

/-- Experimental conditions from §3.2: the probability that symbols of
    a given kind appear in multiples on a card (when present at all).
    Each condition determines a `pMultiple` value. -/
inductive Condition where
  /-- 0% chance of multiple symbols. -/
  | sg
  /-- 10% chance of multiple symbols. -/
  | sgPl
  /-- 50% chance of multiple symbols. -/
  | mix
  /-- 90% chance of multiple symbols. -/
  | plSg
  /-- 100% chance of multiple symbols. -/
  | pl
  deriving DecidableEq, Repr, Inhabited

/-- The probability of multiple symbols for each condition. -/
def Condition.pMultiple : Condition → ℚ
  | .sg   => 0
  | .sgPl => 1/10
  | .mix  => 1/2
  | .plSg => 9/10
  | .pl   => 1

/-- The probability of a unique symbol (complement). -/
def Condition.pUnique (c : Condition) : ℚ := 1 - c.pMultiple

-- ============================================================================
-- §2  Conceivability Presupposition Instances
-- ============================================================================

/-!
## §2: Book Examples — Conceivability in Action

@cite{enguehard-2024} examples (5)–(6) and @cite{farkas-de-swart-2010}
generalization (8) illustrate conceivability presuppositions via world
knowledge about books:

- Table of contents: prototypically unique → sg conceivable, pl not
- Chapter: prototypically multiple → sg not (prototypically), pl conceivable

We model this with `Bool` situations: `false` = prototypical, `true` = rare.
-/

section BookExamples

/-- A book's table-of-contents count in conceivable situations. -/
def tocCard : Bool → Nat
  | false => 1   -- prototypical: exactly one
  | true  => 0   -- rare: none (e.g., a pamphlet)

/-- All situations are conceivable for table of contents. -/
def allConceivable' : Bool → Prop := fun _ => True

/-- Table of contents: sg conceivable (prototypical situation has |C|=1). -/
theorem toc_sg_conceivable :
    sgCardConceivable tocCard allConceivable' :=
  ⟨false, trivial, rfl⟩

/-- Table of contents: pl NOT conceivable (no situation has |C|≥2). -/
theorem toc_pl_not_conceivable :
    ¬plCardConceivable tocCard allConceivable' := by
  intro ⟨w, _, h⟩
  cases w <;> simp [tocCard] at h

/-- A book's chapter count in conceivable situations. -/
def chapterCard : Bool → Nat
  | false => 5   -- prototypical: several chapters
  | true  => 1   -- rare: a single-chapter book

/-- Chapters: pl conceivable (prototypical situation has |C|=5 ≥ 2). -/
theorem chapter_pl_conceivable :
    plCardConceivable chapterCard allConceivable' :=
  ⟨false, trivial, by norm_num [chapterCard]⟩

/-- Chapters: sg also conceivable (rare situation has |C|=1), BUT
    @cite{farkas-de-swart-2010} argues this is prototypically
    dispreferred because unique-chapter books are rare. The
    conceivability presupposition per se is satisfied, but
    prototypicality (= frequency) governs actual use. -/
theorem chapter_sg_technically_conceivable :
    sgCardConceivable chapterCard allConceivable' :=
  ⟨true, trivial, rfl⟩

/-- Books: both conceivability presuppositions hold for chapters,
    but only sg holds for tables of contents. This contrast drives
    the felicity judgments in examples (5)–(6). -/
theorem book_contrast :
    (sgCardConceivable tocCard allConceivable' ∧
     ¬plCardConceivable tocCard allConceivable') ∧
    (sgCardConceivable chapterCard allConceivable' ∧
     plCardConceivable chapterCard allConceivable') :=
  ⟨⟨toc_sg_conceivable, toc_pl_not_conceivable⟩,
   ⟨chapter_sg_technically_conceivable, chapter_pl_conceivable⟩⟩

end BookExamples

-- ============================================================================
-- §3  Experimental Data
-- ============================================================================

/-!
## §3: Production Experiment (§3.2–3.3)

100 participants (Prolific). Each learned a probability distribution over
symbol cardinalities through a card-validity task. After 20 trials, they
described the rule by completing "the card is valid when..."

The result: SG productions decrease and PL productions increase
monotonically with `pMultiple`, consistent with H₂ (gradient sensitivity
to prototypicality/frequency).
-/

/-- Observed production proportions by condition (from Figure 2).
    Values are approximate readings from the published graph. -/
structure ProductionResult where
  condition : Condition
  sgRate : ℚ
  plRate : ℚ
  otherRate : ℚ
  deriving Repr

/-- Observed data: approximate proportions from Figure 2. -/
def sgResult : ProductionResult :=
  { condition := .sg, sgRate := 73/100, plRate := 3/100, otherRate := 24/100 }

def sgPlResult : ProductionResult :=
  { condition := .sgPl, sgRate := 63/100, plRate := 10/100, otherRate := 27/100 }

def mixResult : ProductionResult :=
  { condition := .mix, sgRate := 50/100, plRate := 25/100, otherRate := 25/100 }

def plSgResult : ProductionResult :=
  { condition := .plSg, sgRate := 30/100, plRate := 47/100, otherRate := 23/100 }

def plResult : ProductionResult :=
  { condition := .pl, sgRate := 0, plRate := 80/100, otherRate := 20/100 }

def allResults : List ProductionResult :=
  [sgResult, sgPlResult, mixResult, plSgResult, plResult]

/-- SG rate weakly decreases across conditions (monotonicity). -/
theorem sg_rate_monotone_decreasing :
    sgResult.sgRate ≥ sgPlResult.sgRate ∧
    sgPlResult.sgRate ≥ mixResult.sgRate ∧
    mixResult.sgRate ≥ plSgResult.sgRate ∧
    plSgResult.sgRate ≥ plResult.sgRate :=
  ⟨by norm_num [sgResult, sgPlResult],
   by norm_num [sgPlResult, mixResult],
   by norm_num [mixResult, plSgResult],
   by norm_num [plSgResult, plResult]⟩

/-- PL rate weakly increases across conditions (monotonicity). -/
theorem pl_rate_monotone_increasing :
    sgResult.plRate ≤ sgPlResult.plRate ∧
    sgPlResult.plRate ≤ mixResult.plRate ∧
    mixResult.plRate ≤ plSgResult.plRate ∧
    plSgResult.plRate ≤ plResult.plRate :=
  ⟨by norm_num [sgResult, sgPlResult],
   by norm_num [sgPlResult, mixResult],
   by norm_num [mixResult, plSgResult],
   by norm_num [plSgResult, plResult]⟩

/-- In the extreme Sg condition, SG dominates PL. -/
theorem sg_condition_sg_dominates : sgResult.sgRate > sgResult.plRate := by
  norm_num [sgResult]

/-- In the extreme Pl condition, PL dominates SG. -/
theorem pl_condition_pl_dominates : plResult.plRate > plResult.sgRate := by
  norm_num [plResult]

/-- In the Mix condition, BOTH SG and PL are used — production is NOT
    complementary. This is the central empirical challenge to MP and
    scalar implicature approaches. -/
theorem mix_condition_both_used :
    mixResult.sgRate > 0 ∧ mixResult.plRate > 0 :=
  ⟨by norm_num [mixResult], by norm_num [mixResult]⟩

/-- Asymmetry between Sg and Pl conditions: some pl productions in Sg
    but NO sg productions in Pl. This reflects the semantic weakness of
    plural ("one or more") vs singular ("exactly one"): pl can intrude
    into sg-biased conditions because it's semantically compatible, but
    sg cannot intrude into pl-biased conditions. -/
theorem sg_pl_production_asymmetry :
    sgResult.plRate > 0 ∧ plResult.sgRate = 0 :=
  ⟨by norm_num [sgResult], by norm_num [plResult]⟩

-- ============================================================================
-- §4  Challenge to Maximize Presupposition
-- ============================================================================

/-!
## §4: MP Underprediction

@cite{sauerland-2003}'s MP-based account (and all scalar-implicature
accounts) predicts **complementary distribution**: where sg's
presupposition is satisfied, use sg; elsewhere, use pl. The experiment
shows overlapping use in all intermediate conditions.

The structural diagnosis: conceivability presuppositions of sg and pl
are **incomparable** (`conceivability_presups_incomparable` in
`PhiFeatures.lean` §7). MP requires a strength ordering; when
presuppositions are not ordered, MP is silent.

This does NOT mean MP is wrong — it means MP underdetermines the choice
in intermediate cases, and the residual variation is governed by
probabilistic/prototypicality factors.
-/

/-- In the Mix condition, both conceivability presuppositions are
    satisfied: the card-validity task exposed participants to both
    unique and multiple symbols. The `both_sg_pl_conceivable` theorem
    from `PhiFeatures.lean` applies directly. -/
theorem mix_both_conceivable
    (witnessCard : Bool → Nat)
    (h₁ : witnessCard false = 1) (h₂ : witnessCard true ≥ 2) :
    sgCardConceivable witnessCard (fun _ => True) ∧
    plCardConceivable witnessCard (fun _ => True) :=
  both_sg_pl_conceivable witnessCard _ false trivial h₁ true trivial h₂

/-- The conceivability presuppositions have the same assertive
    content — both sg and pl indefinites contribute the same truth
    conditions (especially under negation: |C| = 0 for both).
    This mirrors `Sauerland2003.sg_pl_same_assertion` at the
    conceivability level: the competition is entirely presuppositional.
    But unlike Sauerland's entity-level presuppositions, the
    conceivability presuppositions are not ordered by strength. -/
theorem conceivability_same_assertion {W : Type*}
    (witnessCard : W → Nat) (conceivable : W → Prop) (w : W) :
    (⟨fun _ => sgCardConceivable witnessCard conceivable,
      fun _ => True⟩ : PrProp W).assertion w ↔
    (⟨fun _ => plCardConceivable witnessCard conceivable,
      fun _ => True⟩ : PrProp W).assertion w :=
  Iff.rfl

-- ============================================================================
-- §5  Challenge to the Implicature Theory
-- ============================================================================

/-!
## §5: Gradient Data vs Categorical Predictions

`Multiplicity.implicature_uniquely_predicts` asserts the implicature
theory uniquely predicts three patterns (children compute fewer,
correlation with SI rates, polarity asymmetry). Enguehard's experiment
reveals a fourth dimension where the implicature theory makes the wrong
prediction: it predicts categorical (complementary) distribution, but
production is gradient.

This does not refute the implicature theory for positive uses — the
multiplicity inference in UE contexts remains well-modeled as an
implicature/pex effect. But it shows the implicature theory is
incomplete for negative uses, where the conceivability presupposition
governs number choice.
-/

/-- The experimental data is inconsistent with H₀ (no effect of
    distribution): SG rate differs across extreme conditions. -/
theorem null_hypothesis_refuted :
    sgResult.sgRate ≠ plResult.sgRate := by
  norm_num [sgResult, plResult]

/-- The experimental data IS consistent with H₂ (gradient): SG rate
    monotonically decreases, PL rate monotonically increases, and
    intermediate conditions show overlap. -/
theorem gradient_hypothesis_supported :
    sgResult.sgRate > plResult.sgRate ∧
    mixResult.sgRate > 0 ∧ mixResult.plRate > 0 :=
  ⟨by norm_num [sgResult, plResult],
   mix_condition_both_used.1, mix_condition_both_used.2⟩

-- ============================================================================
-- §6  Forward-Looking Cooperation
-- ============================================================================

/-!
## §6: Provide Useful Referents (Principle 23)

@cite{enguehard-2024} proposes a forward-looking pragmatic principle:

> **Provide useful referents**: between utterances of equivalent
> acceptability as per other principles, prefer the one that sets up
> referents that can be used in well-formed continuations.

This is a Manner-like maxim: among truth-conditionally equivalent
alternatives, prefer the one that facilitates future discourse.

Under negation, indefinites introduce discourse referents bearing the
indefinite's number feature (cf. @cite{elliott-2020}'s bilateral
semantics). The number feature constrains future pronoun binding:

- "There is no blue circle₁ on the card. It₁ is hard to see." (sg → "it")
- "There are no blue circles₂ on the card. They₂ are hard to see."
  (pl → "they")

When the pronoun's number does not match the actual witness cardinality,
the continuation is infelicitous — the referent is "useless."

### Formalization as Production Utility

"Provide useful referents" reduces to a production utility function:
the speaker's expected payoff from choosing number `n` equals the
probability that a continuation requiring a referent of number `n`
would be well-formed. This probability tracks the distribution over
prototypical witness cardinalities.
-/

/-- Production utility for a number choice given a prototypicality
    distribution. The utility of sg = P(unique witness in prototypical
    situations); the utility of pl = P(multiple witnesses). -/
def productionUtility (pUnique : ℚ) : IndefNumber → ℚ
  | .sg => pUnique
  | .pl => 1 - pUnique

/-- Production utility for sg decreases with pMultiple. -/
theorem sg_utility_decreases (c₁ c₂ : Condition)
    (h : c₁.pMultiple ≤ c₂.pMultiple) :
    productionUtility c₂.pUnique .sg ≤ productionUtility c₁.pUnique .sg := by
  simp only [productionUtility, Condition.pUnique]; linarith

/-- Production utility for pl increases with pMultiple. -/
theorem pl_utility_increases (c₁ c₂ : Condition)
    (h : c₁.pMultiple ≤ c₂.pMultiple) :
    productionUtility c₁.pUnique .pl ≤ productionUtility c₂.pUnique .pl := by
  simp only [productionUtility, Condition.pUnique]; linarith

/-- At pMultiple = 0 (Sg condition), sg utility is maximal (= 1). -/
theorem sg_utility_maximal_at_zero :
    productionUtility (Condition.sg.pUnique) .sg = 1 := by
  simp [productionUtility, Condition.pUnique, Condition.pMultiple]

/-- At pMultiple = 1 (Pl condition), pl utility is maximal (= 1). -/
theorem pl_utility_maximal_at_one :
    productionUtility (Condition.pl.pUnique) .pl = 1 := by
  simp [productionUtility, Condition.pUnique, Condition.pMultiple]

/-- At pMultiple = 1/2 (Mix condition), both utilities are equal.
    This is the indifference point where both numbers are equally
    useful — explaining the overlap in production. -/
theorem mix_indifference :
    productionUtility (Condition.mix.pUnique) .sg =
    productionUtility (Condition.mix.pUnique) .pl := by
  norm_num [productionUtility, Condition.pUnique, Condition.pMultiple]

-- ============================================================================
-- §7  Conceivability as Constant Presupposition
-- ============================================================================

/-!
## §7: Why Conceivability Projects Universally

The conceivability presupposition is a **constant** presupposition: it
holds at all evaluation worlds or none, because it quantifies over
conceivable situations rather than testing the evaluation world. This
is the structural explanation for why it projects under negation,
questions, and conditionals — constant presuppositions are immune to
semantic operators that manipulate the evaluation world.

Contrast with standard `sgSem`: atomicity depends on the entity, so it
can fail at some entities but not others. The conceivability version
abstracts away from the actual entity.
-/

/-- The conceivability presupposition of a sg indefinite, packaged as
    a `PrProp` that is constant across evaluation worlds. -/
def sgIndefPresup {W : Type*} (witnessCard : W → Nat)
    (conceivable : W → Prop) : PrProp W where
  presup := fun _ => sgCardConceivable witnessCard conceivable
  assertion := fun _ => True

/-- The conceivability presupposition of a pl indefinite. -/
def plIndefPresup {W : Type*} (witnessCard : W → Nat)
    (conceivable : W → Prop) : PrProp W where
  presup := fun _ => plCardConceivable witnessCard conceivable
  assertion := fun _ => True

/-- Conceivability presuppositions are constant: they hold at all
    evaluation worlds or none. This is why they project under every
    semantic operator — negation, questions, conditionals, modals. -/
theorem sgIndefPresup_constant {W : Type*}
    (witnessCard : W → Nat) (conceivable : W → Prop) :
    ∀ w₁ w₂ : W,
      (sgIndefPresup witnessCard conceivable).defined w₁ ↔
      (sgIndefPresup witnessCard conceivable).defined w₂ :=
  fun _ _ => Iff.rfl

theorem plIndefPresup_constant {W : Type*}
    (witnessCard : W → Nat) (conceivable : W → Prop) :
    ∀ w₁ w₂ : W,
      (plIndefPresup witnessCard conceivable).defined w₁ ↔
      (plIndefPresup witnessCard conceivable).defined w₂ :=
  fun _ _ => Iff.rfl

-- ============================================================================
-- §8  Bridge to Presuppositional Exhaustification
-- ============================================================================

/-!
## §8: Conceivability is Weaker than Pex

@cite{delpinal-bassi-sauerland-2024}'s presuppositional exhaustification
(pex) derives the sharp multiplicity inference in positive contexts.
For plural indefinites:

- **pex(pl)** presupposes ¬sg-alternative — i.e., the singular alternative
  (which entails |C|=1) is false at the actual world. In a positive context
  where a witness exists, this yields |C|≥2 AT THE ACTUAL WORLD.
- **Conceivability(pl)** presupposes ∃ conceivable situation with |C|≥2 —
  much weaker, merely requiring that multiple witnesses be *possible*.

The structural relationship: actual non-atomicity (from pex) ENTAILS
conceivability of non-atomicity (by `actual_implies_conceivable` from
`PhiFeatures.lean`), but not vice versa.

This explains the empirical asymmetry:
- **Positive contexts**: pex applies, deriving |C|≥2 at the actual world.
  Conceivability is trivially satisfied (the actual world witnesses it).
  The sharp multiplicity inference comes from pex, not from conceivability.
- **Negative contexts**: pex is blocked (no exhaustification in DE
  environments), but the conceivability presupposition projects (it's
  constant — `sgIndefPresup_constant` / `plIndefPresup_constant`).
  Only the weaker, gradient conceivability pattern survives.

### Connection to pex infrastructure

`pexIEII` (from `PresuppositionalExhaustification.lean`) produces a
`PrProp` with:
- **assertion** = φ (the prejacent)
- **presupposition** = ¬IE ∧ homog(II)

For plural with the singular alternative as the only IE member, the
presupposition reduces to ¬sg. Under negation, `pex_neg_presup` proves
the presupposition projects unchanged.
-/

open Exhaustification.Presuppositional (pexIEII pex_assertion_eq pex_neg_presup)

/-- In a positive context where the actual witness set is non-empty,
    the actual situation witnesses sg conceivability (if |C|=1) or
    pl conceivability (if |C|≥2) — the presupposition is trivially
    satisfied and thus invisible. -/
theorem conceivability_trivial_in_positive {W : Type*}
    (witnessCard : W → Nat) (conceivable : W → Prop)
    (w₀ : W) (hw₀ : conceivable w₀) (hpos : witnessCard w₀ ≥ 1) :
    witnessCard w₀ = 1 ∧ sgCardConceivable witnessCard conceivable ∨
    witnessCard w₀ ≥ 2 ∧ plCardConceivable witnessCard conceivable := by
  by_cases h : witnessCard w₀ = 1
  · left; exact ⟨h, w₀, hw₀, h⟩
  · right; constructor
    · omega
    · exact ⟨w₀, hw₀, by omega⟩

/-- **Pex is stronger than conceivability**: if the actual witness set
    has |C|≥2 (the pex-derived inference), then pl conceivability holds.

    This follows directly from `actual_implies_conceivable`: the actual
    world is a conceivable world that witnesses |C|≥2.

    The converse fails: conceivability only requires SOME conceivable
    situation to have |C|≥2, while pex requires the ACTUAL situation to. -/
theorem pex_entails_conceivability {W : Type*}
    (witnessCard : W → Nat) (conceivable : W → Prop)
    (w₀ : W) (hw₀ : conceivable w₀) (hpex : witnessCard w₀ ≥ 2) :
    plCardConceivable witnessCard conceivable :=
  ⟨w₀, hw₀, hpex⟩

/-- The converse of `pex_entails_conceivability` fails: there exist
    models where pl is conceivable (some conceivable situation has |C|≥2)
    but the actual situation has |C|=0 or |C|=1.

    This is exactly the situation in negative contexts: "there are no
    blue circles" → |C|=0 at the actual world, but |C|≥2 may be
    conceivable. Pex would require |C|≥2 actually, which is false. -/
theorem conceivability_does_not_entail_pex :
    ∃ (witnessCard : Bool → Nat) (conceivable : Bool → Prop) (w₀ : Bool),
      conceivable w₀ ∧ witnessCard w₀ < 2 ∧
      plCardConceivable witnessCard conceivable :=
  ⟨fun | false => 0 | true => 3,
   fun _ => True,
   false, trivial, by norm_num,
   ⟨true, trivial, by norm_num⟩⟩

/-- The pex infrastructure confirms: negating a pex'd proposition
    preserves its presupposition but negates its assertion. For plural:
    ¬pex(∃x.P(x)) asserts ¬∃x.P(x) and presupposes ¬sg-alternative.
    The presupposition-assertion split is what enables the conceivability
    pattern under negation: the presupposition (about conceivable
    cardinalities) is independent of the assertion (about actual
    cardinality). -/
theorem pex_neg_preserves_presup {World : Type*}
    (ALT : Set (World → Prop)) (φ : World → Prop)
    (Rc : Set (World → Prop)) :
    ((pexIEII ALT φ Rc).neg).presup = (pexIEII ALT φ Rc).presup :=
  pex_neg_presup ALT φ Rc

-- ============================================================================
-- §9  Bridge to Multiplicity
-- ============================================================================

/-!
## §9: Refining the Implicature Theory

@cite{sauerland-2003}'s implicature theory (= `Multiplicity.PluralTheory.implicature`)
correctly predicts the multiplicity inference in positive UE contexts.
But it does not predict gradient production in negative contexts.

Enguehard's account is complementary: the conceivability presupposition
is the *underlying* inference that persists across all environments;
the sharp multiplicity inference in positive contexts is a *strengthened*
version derived by pex or MP.

This parallels the scalar implicature landscape:
- Some/all: the "not all" implicature is sharp in UE, absent in DE;
  but "some is conceivable" is always presupposed.
- Sg/pl: the multiplicity inference is sharp in UE, absent in DE;
  but "unique is conceivable" / "multiple is conceivable" persists.
-/

/-- The `productionUtility` model forms a probability distribution:
    sg and pl rates sum to 1 for any prototypicality parameter. -/
theorem productionUtility_normalized (pUnique : ℚ) :
    productionUtility pUnique .sg + productionUtility pUnique .pl = 1 := by
  simp only [productionUtility]; linarith

/-- Production utility is non-negative for all conditions. Combined
    with `productionUtility_normalized`, this makes `productionUtility
    c.pUnique` a probability distribution over `IndefNumber`. -/
theorem productionUtility_nonneg (c : Condition) (n : IndefNumber) :
    0 ≤ productionUtility c.pUnique n := by
  cases n <;> simp only [productionUtility, Condition.pUnique] <;>
    cases c <;> norm_num [Condition.pMultiple]

/-- The production utility model correctly predicts the dominance
    pattern in extreme conditions, matching the observed data
    (`sg_condition_sg_dominates`, `pl_condition_pl_dominates`). -/
theorem utility_predicts_extreme_dominance :
    productionUtility (Condition.sg.pUnique) .sg >
      productionUtility (Condition.sg.pUnique) .pl ∧
    productionUtility (Condition.pl.pUnique) .pl >
      productionUtility (Condition.pl.pUnique) .sg := by
  norm_num [productionUtility, Condition.pUnique, Condition.pMultiple]

/-- `productionUtility` is uniquely characterized by normalization
    (`f p .sg + f p .pl = 1`) and linearity (`f p .sg = p`). Any
    model satisfying both conditions IS `productionUtility` — it is
    not a free parameter but the unique solution. -/
theorem productionUtility_characterized (f : ℚ → IndefNumber → ℚ)
    (hNorm : ∀ p, f p .sg + f p .pl = 1)
    (hLinear : ∀ p, f p .sg = p) :
    ∀ p n, f p n = productionUtility p n := by
  intro p n; cases n
  · exact hLinear p
  · simp only [productionUtility]; linarith [hNorm p, hLinear p]

-- ============================================================================
-- §10  Bridge to PresuppositionContext
-- ============================================================================

/-!
## §10: Conceivability = Satisfiability in Context

`PresuppositionContext.presupSatisfiable c p` checks whether `p.presup`
is compatible with context set `c`. This is exactly Enguehard's
conceivability condition at the context-set level:

- A sg indefinite's conceivability presupposition is satisfied iff the
  common ground is compatible with a world where |C| = 1.
- A pl indefinite's conceivability presupposition is satisfied iff the
  common ground is compatible with a world where |C| ≥ 2.

When the common ground rules out one cardinality entirely (e.g., it's
common knowledge that books have exactly one table of contents), the
corresponding conceivability presupposition fails — yielding the
categorical judgments in examples (5)–(6).
-/

/-- Conceivability presuppositions are constant, so `presupSatisfied`
    and `presupSatisfiable` coincide for them (on non-empty contexts).
    Constant presuppositions are either entailed by every world or no
    world — there is no middle ground. -/
theorem constant_presup_satisfied_iff_satisfiable
    {W : Type*} (witnessCard : W → Nat) (conceivable : W → Prop)
    (c : Core.CommonGround.ContextSet W)
    (hne : c.nonEmpty) :
    Core.PresuppositionContext.presupSatisfied c
      (sgIndefPresup witnessCard conceivable) ↔
    Core.PresuppositionContext.presupSatisfiable c
      (sgIndefPresup witnessCard conceivable) := by
  constructor
  · intro hsat
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw, hsat w hw⟩
  · intro ⟨_, _, hdef⟩
    intro _ _
    exact hdef

-- ============================================================================
-- §11  Bilateral Dynamics Bridge
-- ============================================================================

/-!
## §11: Negated Indefinites in Bilateral Dynamic Semantics

@cite{enguehard-2024} §5.1–5.2 argues that negated indefinites introduce
discourse referents accessible for subsequent anaphora, following
@cite{elliott-2020}'s bilateral dynamic framework. The key mechanism:

1. `exists_ x domain φ` introduces a discourse referent `x` by random
   assignment into the positive update.
2. `neg` swaps positive and negative updates, so
   `neg (exists_ x domain φ)` has positive update:
   `{ p ∈ s | ∀ e ∈ domain, p.extend x e ∉ φ.positive (s.randomAssign x domain) }`
   The possibilities that survive are those from the INPUT state `s`
   where no witness satisfies `φ`.
3. The discourse referent `x` is introduced in the INNER computation but
   the output possibilities come from `s` — so `x` is available for
   subsequent anaphora (via composition with further updates).

The number feature on the discourse referent (sg/pl) constrains what
anaphoric continuations are felicitous. Enguehard argues that speakers
choose the number feature to maximize the utility of the discourse
referent for likely continuations — which reduces to the
`productionUtility` model in §4.

### The structural bridge

The bilateral `neg ∘ exists_` construction yields possibilities from `s`
that falsify the existential. These possibilities carry no witness in
their assignments — the key structural fact is that the OUTPUT state
preserves the input possibilities (those that survived universal
falsification). This means the discourse referent is "set up" by the
existential introduction but the output state is a subset of the input.
-/

section BilateralBridge

open Semantics.Dynamic.Core (BilateralDen Possibility InfoState)
open Semantics.Dynamic.Core.BilateralDen (neg exists_ atom)

variable {W E : Type*}

/-- A discourse referent paired with its indefinite number feature.
    This is the type-theoretic reflex of Enguehard's claim that number
    marking on indefinites is stored on the discourse referent. -/
structure NumberedDRef where
  /-- The variable index in the assignment function -/
  index : Nat
  /-- The number feature chosen by the speaker -/
  number : IndefNumber
  deriving DecidableEq, Repr

/-- The negative update of an existential keeps exactly those
    possibilities from `s` where no domain element witnesses `φ`. -/
theorem exists_negative_characterization
    (x : Nat) (domain : Set E) (φ : BilateralDen W E)
    (s : InfoState W E) (p : Possibility W E) :
    p ∈ (exists_ x domain φ).negative s ↔
    p ∈ s ∧ ∀ e ∈ domain, (p.extend x e) ∉
      φ.positive (s.randomAssign x domain) := by
  simp only [exists_, Set.mem_setOf_eq]

/-- Negating an existential: the positive update of `¬∃x.φ` collects
    exactly those input possibilities where no witness satisfies `φ`.
    This is the bilateral analog of universal falsification. -/
theorem neg_exists_positive
    (x : Nat) (domain : Set E) (φ : BilateralDen W E)
    (s : InfoState W E) (p : Possibility W E) :
    p ∈ (neg (exists_ x domain φ)).positive s ↔
    p ∈ s ∧ ∀ e ∈ domain, (p.extend x e) ∉
      φ.positive (s.randomAssign x domain) := by
  simp only [neg, exists_negative_characterization]

/-- The output of `¬∃x.φ` is a subset of the input state — negated
    existentials are eliminative. This is crucial for Enguehard's account:
    the surviving possibilities carry no witness, which is why the
    discourse referent's number feature matters for continuations
    (it encodes the speaker's expectation about the predicate's
    extension). -/
theorem neg_exists_eliminative
    (x : Nat) (domain : Set E) (φ : BilateralDen W E)
    (s : InfoState W E) :
    (neg (exists_ x domain φ)).positive s ⊆ s := by
  intro p hp
  rw [neg_exists_positive] at hp
  exact hp.1

/-- Double negation elimination for the existential: ¬¬∃x.φ has the
    same positive update as ∃x.φ. This is definitional in bilateral
    semantics — `neg` swaps, so two swaps restore the original. -/
theorem neg_neg_exists
    (x : Nat) (domain : Set E) (φ : BilateralDen W E)
    (s : InfoState W E) :
    (neg (neg
      (exists_ x domain φ))).positive s =
    (exists_ x domain φ).positive s := rfl

/-- Agreement constraint: a continuation sentence with pronoun `y`
    agreeing in number with discourse referent `dref` is felicitous
    only when the number feature matches the conceivability pattern.

    When `dref.number = .sg`, continuations presuppose `|C| = 1` is
    conceivable; when `dref.number = .pl`, they presuppose `|C| ≥ 2`.
    This connects back to `sgCardConceivable`/`plCardConceivable`. -/
def agreementFelicitous (dref : NumberedDRef)
    (witnessCard : W → Nat) (conceivable : W → Prop) : Prop :=
  match dref.number with
  | .sg => sgCardConceivable witnessCard conceivable
  | .pl => plCardConceivable witnessCard conceivable

/-- The bilateral bridge: for the book examples, the agreement
    constraint on discourse referents matches the conceivability
    presupposition pattern. Table of contents: sg-marked dref is
    felicitous (sg conceivable), pl-marked is not. -/
theorem toc_agreement_matches_conceivability :
    agreementFelicitous ⟨0, .sg⟩ tocCard allConceivable' ∧
    ¬agreementFelicitous ⟨0, .pl⟩ tocCard allConceivable' := by
  constructor
  · exact toc_sg_conceivable
  · exact toc_pl_not_conceivable

/-- Chapters: both sg and pl discourse referents are felicitous
    (both conceivability presuppositions hold), matching the
    underdetermination that Enguehard argues requires gradient
    utility to resolve. -/
theorem chapter_agreement_underdetermined :
    agreementFelicitous ⟨0, .sg⟩ chapterCard allConceivable' ∧
    agreementFelicitous ⟨0, .pl⟩ chapterCard allConceivable' := by
  exact ⟨chapter_sg_technically_conceivable, chapter_pl_conceivable⟩

/-- The full pipeline from bilateral dynamics to production data:

    1. Negated indefinites introduce discourse referents (`neg_exists_eliminative`)
    2. The dref carries a number feature (`NumberedDRef`)
    3. Agreement constrains continuations (`agreementFelicitous`)
    4. When both sg and pl are felicitous (underdetermined), the speaker
       chooses number to maximize `productionUtility`
    5. At pMultiple = 1/2, both utilities are equal (`mix_indifference`)

    This theorem ties together steps 3-4: when agreement is underdetermined,
    production utility determines the choice, and the utility values track
    the observed production rates (sg dominates when pMultiple is low,
    pl dominates when pMultiple is high). -/
theorem underdetermined_implies_gradient
    (witnessCard : Bool → Nat) (hsg : witnessCard true = 1) (hpl : witnessCard false ≥ 2)
    (c₁ c₂ : Condition) (h : c₁.pMultiple ≤ c₂.pMultiple) :
    -- Agreement is underdetermined (both conceivability presups hold)
    agreementFelicitous ⟨0, .sg⟩ witnessCard (fun _ => True) ∧
    agreementFelicitous ⟨0, .pl⟩ witnessCard (fun _ => True) ∧
    -- AND production utility for sg decreases with pMultiple
    productionUtility c₂.pUnique .sg ≤ productionUtility c₁.pUnique .sg ∧
    -- AND production utility for pl increases with pMultiple
    productionUtility c₁.pUnique .pl ≤ productionUtility c₂.pUnique .pl := by
  refine ⟨⟨true, trivial, hsg⟩, ⟨false, trivial, hpl⟩, ?_, ?_⟩
  · exact sg_utility_decreases c₁ c₂ h
  · exact pl_utility_increases c₁ c₂ h

end BilateralBridge

end Phenomena.Plurals.Studies.Enguehard2024
