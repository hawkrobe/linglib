import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Copular
import Linglib.Core.Order.Rat01
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-!
# [degen-tonhauser-2021]: Prior Beliefs Modulate Projection

Does a listener's prior belief about a content modulate how strongly that content
*projects* — i.e., how committed the speaker is taken to be to it when it sits
under an entailment-canceling operator? The prior literature conflicted:
[mahler-2020] found that politically charged complements project more when a
priori more plausible, while [lorson-2018] found no effect of world knowledge on
the projection of the prestate of *stop*. [degen-tonhauser-2021] resolve the
conflict in favor of modulation: across 20 clause-embedding predicates and 20
contents, higher-prior content projects more, at the group and the individual
level.

A *prior-sensitive* account is one monotone in prior credence (`PriorSensitive`);
it predicts the modulation by its shape (`sensitive_predicts_modulation`), while
the prior-*insensitive* null account predicts none (`priorInsensitive_not_sensitive`).
This is the account family the paper argues for — projection as a posterior
credence in a Bayesian / RSA listener ([qing-goodman-lassiter-2016],
[goodman-frank-2016]) — and the prior analogue of the at-issueness predictor of
[tonhauser-beaver-degen-2018]. The experiment 1 by-predicate means realize the
modulation for every predicate (`prior_modulates_projection`), and the predicates
are bridged to their Fragment entries (`all_predicates_take_clause_complement`).

The regression coefficients are recorded as prose, not theorems. Experiment 1
(within-participant, N = 286): the prior manipulation was successful (β = 0.45,
SE = 0.01, t = 31.12), and prior probability predicted projection at every level —
categorical high/low fact (β = 0.14, t = 12.24), group-level continuous prior
(β = 0.31, t = 12.58), and the participant's own continuous prior (β = 0.28,
t = 13.85). Model comparison favored the individual-level predictor decisively
(BIC 2291 < group-level 2586 < categorical 2654). The by-predicate projection
ranking was highly stable (Spearman r = .991 with prior work), reproducing the
predicate-level projection variability documented by [tonhauser-beaver-degen-2018].
Experiment 2 (between-participant) replicated the effect: prior manipulation
β = 0.54 (t = 15.07; Exp 2a, N = 75; prior ratings r = .977 with Exp 1) and
projection β = 0.18 categorical / β = 0.34 group-level (t = 12.81 / 13.27; Exp 2b,
N = 266). The main-clause control projected at floor (mean certainty 0.21).
-/

namespace DegenTonhauser2021

open Core.Order

/-! ### The 20 clause-embedding predicates -/

/-- The 20 clause-embedding predicates of [degen-tonhauser-2021], listed
    alphabetically as in Figure 1C. For the traditional classification see
    `DegenTonhauser2022.traditionalClass`. -/
inductive Predicate where
  | acknowledge | admit | announce | beAnnoyed | beRight
  | confess | confirm | demonstrate | discover | establish
  | hear | inform | know | pretend | prove
  | reveal | say | see | suggest | think
  deriving DecidableEq, Fintype, Repr

/-! ### Projection as a function of prior credence -/

/-- A predictor of projection strength from prior credence in the complement. -/
abbrev PriorAccount := Rat01 → Rat01

/-- The prior-insensitive null account: projection is constant in prior credence. -/
def priorInsensitive (c : Rat01) : PriorAccount := fun _ => c

/-- An account is prior-sensitive when projection is strictly monotone in prior
    credence. -/
def PriorSensitive (acc : PriorAccount) : Prop := StrictMono acc

/-- The null account predicts identical projection for any two priors. -/
theorem priorInsensitive_no_modulation (c p q : Rat01) :
    priorInsensitive c p = priorInsensitive c q := rfl

/-- The null account is not prior-sensitive. -/
theorem priorInsensitive_not_sensitive (c : Rat01) :
    ¬ PriorSensitive (priorInsensitive c) :=
  fun h => lt_irrefl c (h Rat01.zero_lt_one)

/-- A prior-sensitive account predicts stronger projection for higher-prior content. -/
theorem sensitive_predicts_modulation {acc : PriorAccount} (h : PriorSensitive acc)
    {p q : Rat01} (hpq : p < q) : acc p < acc q := h hpq

/-! ### Data: prior modulates projection for every predicate

Experiment 1 by-predicate means from `results/9-prior-projection/data/cd.csv` at
github.com/judith-tonhauser/projective-probability (n = 286), rounded to two decimals;
prior means average over the contents each predicate was randomly paired with. -/

/-- Mean certainty rating (projection) under the higher-probability fact
    (Figure 3; nonprojective main-clause control mean 0.21). -/
def certaintyHigh : Predicate → ℚ
  | .acknowledge => 0.65
  | .admit => 0.60
  | .announce => 0.53
  | .beAnnoyed => 0.80
  | .beRight => 0.34
  | .confess => 0.58
  | .confirm => 0.37
  | .demonstrate => 0.48
  | .discover => 0.69
  | .establish => 0.43
  | .hear => 0.72
  | .inform => 0.76
  | .know => 0.74
  | .pretend => 0.31
  | .prove => 0.41
  | .reveal => 0.62
  | .say => 0.38
  | .see => 0.69
  | .suggest => 0.32
  | .think => 0.40

/-- Mean certainty rating under the lower-probability fact. -/
def certaintyLow : Predicate → ℚ
  | .acknowledge => 0.49
  | .admit => 0.43
  | .announce => 0.41
  | .beAnnoyed => 0.68
  | .beRight => 0.20
  | .confess => 0.45
  | .confirm => 0.28
  | .demonstrate => 0.33
  | .discover => 0.55
  | .establish => 0.27
  | .hear => 0.57
  | .inform => 0.57
  | .know => 0.68
  | .pretend => 0.21
  | .prove => 0.25
  | .reveal => 0.47
  | .say => 0.22
  | .see => 0.60
  | .suggest => 0.24
  | .think => 0.20

/-- Mean prior probability rating of the complement content given the
    higher-probability fact. -/
def priorHigh : Predicate → ℚ
  | .acknowledge => 0.67
  | .admit => 0.68
  | .announce => 0.72
  | .beAnnoyed => 0.71
  | .beRight => 0.69
  | .confess => 0.69
  | .confirm => 0.68
  | .demonstrate => 0.62
  | .discover => 0.72
  | .establish => 0.69
  | .hear => 0.69
  | .inform => 0.72
  | .know => 0.68
  | .pretend => 0.70
  | .prove => 0.67
  | .reveal => 0.69
  | .say => 0.69
  | .see => 0.67
  | .suggest => 0.69
  | .think => 0.66

/-- Mean prior probability rating given the lower-probability fact. -/
def priorLow : Predicate → ℚ
  | .acknowledge => 0.24
  | .admit => 0.24
  | .announce => 0.26
  | .beAnnoyed => 0.23
  | .beRight => 0.26
  | .confess => 0.20
  | .confirm => 0.21
  | .demonstrate => 0.26
  | .discover => 0.26
  | .establish => 0.23
  | .hear => 0.24
  | .inform => 0.25
  | .know => 0.25
  | .pretend => 0.20
  | .prove => 0.24
  | .reveal => 0.25
  | .say => 0.22
  | .see => 0.21
  | .suggest => 0.22
  | .think => 0.19

/-- Prior credence and certainty are both higher under the higher-probability fact
    for every predicate (Figure 3) — the pattern a prior-sensitive account predicts
    and the null account rules out. -/
theorem prior_modulates_projection (p : Predicate) :
    priorLow p < priorHigh p ∧ certaintyLow p < certaintyHigh p := by
  cases p <;> exact ⟨by norm_num [priorLow, priorHigh],
    by norm_num [certaintyLow, certaintyHigh]⟩

/-- The observed certainties differ across the manipulation, contra the null
    account (`priorInsensitive_no_modulation`). -/
theorem certaintyLow_ne_certaintyHigh (p : Predicate) :
    certaintyLow p ≠ certaintyHigh p :=
  (prior_modulates_projection p).2.ne

/-! ### Fragment bridge -/

section FragmentBridge

open English.Predicates.Verbal
open English.Predicates.Copular

/-- Map each predicate to its Fragment verb entry (18 of 20; `beAnnoyed` and
    `beRight` are copular — use `toPredicateCore` for full coverage). -/
def toVerbEntry : Predicate → Option VerbEntry
  | .know => some know
  | .think => some think
  | .discover => some discover
  | .see => some see
  | .say => some say
  | .hear => some hear
  | .reveal => some reveal
  | .acknowledge => some acknowledge
  | .admit => some admit
  | .announce => some announce
  | .confess => some confess
  | .inform => some inform
  | .suggest => some suggest
  | .pretend => some pretend
  | .confirm => some confirm
  | .demonstrate => some demonstrate
  | .establish => some establish
  | .prove => some prove
  | .beAnnoyed => none
  | .beRight => none

/-- The two copular predicates are exactly the ones without a `VerbEntry`. -/
theorem toVerbEntry_eq_none_iff (p : Predicate) :
    toVerbEntry p = none ↔ p = .beAnnoyed ∨ p = .beRight := by
  cases p <;> simp [toVerbEntry]

/-- Map each predicate to its `Verb` — the semantic spine shared by verbal and
    copular entries. Covers all 20; copular entries go through
    `ClauseEmbeddingAdj.toVerb`. -/
def toPredicateCore : Predicate → Verb
  | .know => know.toVerb
  | .think => think.toVerb
  | .discover => discover.toVerb
  | .see => see.toVerb
  | .say => say.toVerb
  | .hear => hear.toVerb
  | .reveal => reveal.toVerb
  | .acknowledge => acknowledge.toVerb
  | .admit => admit.toVerb
  | .announce => announce.toVerb
  | .confess => confess.toVerb
  | .inform => inform.toVerb
  | .suggest => suggest.toVerb
  | .pretend => pretend.toVerb
  | .confirm => confirm.toVerb
  | .demonstrate => demonstrate.toVerb
  | .establish => establish.toVerb
  | .prove => prove.toVerb
  | .beAnnoyed => beAnnoyed.toVerb
  | .beRight => beRight.toVerb

/-- Every predicate takes a finite clause complement (as primary or alternate
    frame), matching the experimental design. -/
theorem all_predicates_take_clause_complement (p : Predicate) :
    (toPredicateCore p).complementType = .finiteClause ∨
    (toPredicateCore p).altComplementType = some .finiteClause := by
  cases p <;>
    simp [toPredicateCore, Semantics.Attitudes.ClauseEmbeddingAdj.toVerb,
          beAnnoyed, beRight] <;>
    first | left; rfl | right; rfl

end FragmentBridge

end DegenTonhauser2021
