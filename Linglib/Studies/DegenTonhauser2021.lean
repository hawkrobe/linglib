import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Copular
import Linglib.Core.Order.Rat01
import Linglib.Data.Examples.DegenTonhauser2021
import Mathlib.Order.Monotone.Basic
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
contents, higher-prior content projects more, at the group **and** the individual
level.

The deep claim is structural: projection tracks prior credence *monotonically*.
We make that the pivot. An account is **prior-sensitive** when it is monotone in
prior credence (`PriorSensitive`); such an account predicts the observed
per-content modulation by its very shape (`sensitive_predicts_modulation`),
whereas the prior-*insensitive* null account predicts no modulation at all
(`priorInsensitive_not_sensitive`). This is the account family the paper argues
for — projection as a posterior credence in a Bayesian / RSA listener
([qing-goodman-lassiter-2016], [goodman-frank-2016]). It is the *prior* analogue
of the at-issueness predictor of projection in [tonhauser-beaver-degen-2018]:
both are gradient `Rat01 → Rat01` maps into the same projection space.

## Main definitions
* `Predicate` — the 20 clause-embedding predicates (Figure 1C).
* `PriorAccount := Rat01 → Rat01` — predict projection strength from prior credence.
* `PriorSensitive` / `priorInsensitive` — the monotone account family vs. the
  constant null.
* `ProjectionByPrior` — a per-predicate datum (high/low-prior mean certainty and
  prior credence), lifted from `Data.Examples.DegenTonhauser2021`.

## Main results
* `sensitive_predicts_modulation`, `priorInsensitive_not_sensitive`,
  `priorInsensitive_no_modulation` — the modulation is derived from account shape.
* `#guard`s over `Examples.all` build-check that every predicate shows higher
  prior **and** higher projection in the high condition (the core finding).
* `all_predicates_take_clause_complement` and the coverage lemmas — every
  predicate is realized by a Fragment entry taking a finite clause.

## Empirical findings (prose, per [degen-tonhauser-2021])
Regression coefficients are documented here, not encoded as theorems. Experiment 1
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

## Implementation notes
Per-predicate mean certainty (projection) and prior credence are computed from the
authors' data (`results/9-prior-projection/data/cd.csv` at
github.com/judith-tonhauser/projective-probability, n = 286) and stored in
`Data.Examples.DegenTonhauser2021`; degrees use the shared `Core.Order.Rat01`
projection space. The continuous data is checked by `#guard` (string-keyed
`paperFeatures` do not kernel-reduce); the provable content is the account-shape
theorems. Predicates are bridged to their Fragment lexical entries.
-/

namespace DegenTonhauser2021

open Core.Order
open Data.Examples (LinguisticExample)

/-! ### The 20 clause-embedding predicates -/

/-- The 20 clause-embedding predicates investigated in [degen-tonhauser-2021],
    listed alphabetically as in Figure 1C. The set spans cognitive (`know`),
    emotive (`beAnnoyed`), communication (`announce`), and inferential (`prove`)
    predicates. For the traditional factive/nonfactive classification see
    `DegenTonhauser2022.traditionalClass`. -/
inductive Predicate where
  | acknowledge | admit | announce | beAnnoyed | beRight
  | confess | confirm | demonstrate | discover | establish
  | hear | inform | know | pretend | prove
  | reveal | say | see | suggest | think
  deriving DecidableEq, Repr

/-! ### Projection as a function of prior credence

The account family the paper argues for: projection strength is a function of the
listener's prior credence in the content. A *prior-sensitive* account is monotone
in that credence; the null account is constant (prior-insensitive). The monotone
shape alone predicts the modulation; the constant one cannot. -/

/-- A predictor of projection strength from prior credence in the complement —
    the same gradient shape as the at-issueness predictor of
    [tonhauser-beaver-degen-2018]. -/
abbrev PriorAccount := Rat01 → Rat01

/-- The prior-insensitive null account: projection is constant in prior credence. -/
def priorInsensitive (c : Rat01) : PriorAccount := fun _ => c

/-- An account is prior-sensitive when projection is strictly monotone in prior
    credence — the structural form of the paper's positive prior coefficient. -/
def PriorSensitive (acc : PriorAccount) : Prop := StrictMono acc

/-- The endpoints of the prior scale are distinct, so a constant account is
    detectably non-modulating. -/
theorem rat01_zero_lt_one : (Rat01.zero : Rat01) < Rat01.one := by
  rw [Rat01.zero, Rat01.one, Subtype.mk_lt_mk]; norm_num

/-- The null account predicts identical projection for any two priors. -/
theorem priorInsensitive_no_modulation (c p q : Rat01) :
    priorInsensitive c p = priorInsensitive c q := rfl

/-- The null account is not prior-sensitive: it cannot produce the observed gap. -/
theorem priorInsensitive_not_sensitive (c : Rat01) :
    ¬ PriorSensitive (priorInsensitive c) :=
  fun h => lt_irrefl c (h rat01_zero_lt_one)

/-- A prior-sensitive account predicts stronger projection for higher-prior
    content — the modulation, derived from the account's shape, not stipulated. -/
theorem sensitive_predicts_modulation {acc : PriorAccount} (h : PriorSensitive acc)
    {p q : Rat01} (hpq : p < q) : acc p < acc q := h hpq

/-! ### Data: prior modulates projection for every predicate

The per-predicate means (`Data.Examples.DegenTonhauser2021`) show, for all 20
predicates, both a higher prior credence and a higher projection in the high
condition — the joint pattern a prior-sensitive account predicts and the null
account rules out. -/

/-- Parse a percent-integer string (e.g. `"69"`) into a `Rat01`. -/
private def parsePct (s : String) : Option Rat01 :=
  match s.toNat? with
  | some n =>
      if h : n ≤ 100 then
        some ⟨(n : ℚ) / 100, by positivity,
          by rw [div_le_one (by norm_num)]; exact_mod_cast h⟩
      else none
  | none => none

/-- A per-predicate projection datum: mean certainty (projection) and prior
    credence in the higher- vs. lower-probability conditions. -/
structure ProjectionByPrior where
  predicate     : String
  certaintyHigh : Rat01
  certaintyLow  : Rat01
  priorHigh     : Rat01
  priorLow      : Rat01
  deriving Repr

/-- Lift a `LinguisticExample` row to a `ProjectionByPrior`. -/
def fromExample (e : LinguisticExample) : Option ProjectionByPrior :=
  match e.paperFeatures.lookup "predicate",
        (e.paperFeatures.lookup "certaintyHigh").bind parsePct,
        (e.paperFeatures.lookup "certaintyLow").bind parsePct,
        (e.paperFeatures.lookup "priorHigh").bind parsePct,
        (e.paperFeatures.lookup "priorLow").bind parsePct with
  | some p, some ch, some cl, some ph, some pl =>
      some { predicate := p, certaintyHigh := ch, certaintyLow := cl,
             priorHigh := ph, priorLow := pl }
  | _, _, _, _, _ => none

/-- The pooled per-predicate data. -/
def allData : List ProjectionByPrior := Examples.all.filterMap fromExample

/-- Higher prior credence in the high condition (the manipulation held). -/
def priorIsHigher (d : ProjectionByPrior) : Bool := decide (d.priorLow.val < d.priorHigh.val)

/-- Higher projection in the high condition (the modulation). -/
def priorModulates (d : ProjectionByPrior) : Bool :=
  decide (d.certaintyLow.val < d.certaintyHigh.val)

-- Build-checked: all 20 predicates parse, and each shows both a higher prior
-- credence and a higher projection in the high-probability condition.
#guard allData.length = 20
#guard allData.all (fun d => priorIsHigher d && priorModulates d)

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

/-- All 20 predicates (alphabetical). -/
def allPredicates : List Predicate :=
  [.acknowledge, .admit, .announce, .beAnnoyed, .beRight,
   .confess, .confirm, .demonstrate, .discover, .establish,
   .hear, .inform, .know, .pretend, .prove,
   .reveal, .say, .see, .suggest, .think]

/-- All 20 predicates are listed. -/
theorem full_coverage : allPredicates.length = 20 := rfl

/-- 18 of 20 predicates have `VerbEntry` entries (all except copular
    `beAnnoyed` and `beRight`). -/
theorem verbEntry_coverage :
    (allPredicates.filter (fun p => (toVerbEntry p).isSome)).length = 18 := by
  decide

/-- Every predicate takes a finite clause complement (as primary or alternate
    frame), matching the experimental design. -/
theorem all_predicates_take_clause_complement (p : Predicate) :
    (toPredicateCore p).complementType = .finiteClause ∨
    (toPredicateCore p).altComplementType = some .finiteClause := by
  cases p <;>
    simp [toPredicateCore, Semantics.Gradability.ClauseEmbeddingAdj.toVerb,
          beAnnoyed, beRight] <;>
    first | left; rfl | right; rfl

end FragmentBridge

end DegenTonhauser2021
