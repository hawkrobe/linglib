/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.Comparison
import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Semantics.Exhaustification.Chain
import Linglib.Semantics.Exhaustification.PreExhaustified
import Linglib.Discourse.CommonGround
import Mathlib.Data.Fintype.Powerset

/-!
# [mihoc-2019]: Decomposing Modified Numerals
[mihoc-2019] [hackl-2000] [kennedy-2015] [horn-1972] [geurts-nouwen-2007]
[nouwen-2010] [fox-hackl-2006] [spector-2014] [chierchia-2013]
[sauerland-stateva-2011] [krifka-2007]

[mihoc-2019] (Ch. 2) decomposes bare (BN), comparative-modified (CMN), and
superlative-modified (SMN) numerals into *extent indicators* — `much`/`little`
denote positive/negative extents on the cardinality scale, transposing
Kennedy's earlier extent algebra (her §2.5) — and two operators: [comp]
places the maximum of the degree predicate in the *complement* of the extent,
[at-sup] inside it. The four modified forms are cross-pairings (*more than* =
[comp]+much, *less than* = [comp]+little, *at least* = [at-sup]+**little**,
*at most* = [at-sup]+**much**), and the truth conditions provably reduce to
the Hackl/Kennedy meanings — here the named meanings of `Semantics.Numerals`,
so the reduction theorems double as bridges to the [kennedy-2015] spine.
Alternatives fall out of the truth conditions: σA replaces the numeral with a
scalemate; DA replaces the set the maximum is asserted to fall in — the
complement of the extent for [comp] forms (her Ch. 2 (38c)), the extent for
[at-sup] forms (her Ch. 2 (39c)) — with its proper subsets. Bare numerals
generate *no* DA, since their (Hornian, lower-bounded) truth conditions
reference no degree-set domain (her Ch. 2 (37c)).

Ch. 3 defends classical scalar implicatures for all three classes and locates
the failures: σA-exhaustification at scale granularity 1 produces an
'exactly' meaning for *every* form — welcome for bare numerals ([horn-1972],
her Ch. 3 (2)), unwelcome for CMNs/SMNs (her Ch. 3 (24)–(27)) — while coarser
granularities avoid it (her §3.7; [spector-2014]'s grade context, her §3.6
(33), is the granularity-4 instance). The scale and its granularity are
contextual ([sauerland-stateva-2011]'s granularity functions; rounder
numerals select coarser scales, [krifka-2007] and her pp. 110–111), not
universally dense — contra [fox-hackl-2006] (her fn. 8). On discrete scales
the two accounts agree (`FoxHackl2006Numerals.moreThan_has_maxInf_nat` is
the g = 1 'exactly n+1' rescue); they part on whether density ever
obliterates the next-stronger alternative.

## Main definitions

- `much`, `little`: the extent indicators, as `Core.Order.Comparison.interval`s
- `compTC`, `atSupTC`: the [comp]/[at-sup] truth conditions on the maximum
- `Form`: BN/CMN/SMN assertion forms; `Form.toComparison` factors them
  through the `Comparison` spine; `Form.tc`, `Form.domainAlts`,
  `Form.strongerAlt`, `Form.exhSigma`

## Main results

- `compTC_much_iff` … `atSupTC_much_iff`: the reductions to the
  `Semantics.Numerals` named meanings (her Ch. 2 (32)–(33))
- `Form.tc_iff_rel`: the Op × Extent factorization lands on `Comparison.rel`
- `comp_excludes_boundary` / `atSup_includes_boundary`: the Class A/B
  strict/non-strict split ([geurts-nouwen-2007], [nouwen-2010]) as
  corollaries of `Comparison.boundary_mem`
- `exhSigma_bare_eq_exhNumeral`: at granularity 1 her `O_σA` *is* the spine's
  `exhNumeral` (hence, via `Spector2013.exhNumeral_eq_innocent_exh`, Fox-2007
  innocent exclusion); `exhSigma` is its granularity/direction generalization
- `exhSigma_*_g1`: 'exactly' meanings for all five forms at granularity 1
  (her Ch. 3 (2), (24)–(27)); `exhSigma_moreThan_proper`: the strengthening
  is non-vacuous — deriving an implicature exactly where [kennedy-2015]'s
  neo-Gricean account derives none (`Kennedy2015.classA_moreThan3_no_primary`)
- `exhSigma_moreThan_coarse_not_exactly`, `spector_grade_context`: coarser
  granularity avoids the 'exactly' overgeneration (her §3.6–3.7)
- `exhSigma_moreThan_eq_exhChain` / `exhSigma_atMost_eq_exhChain`: the
  one-scalemate operator equals whole-scale chain-exhaustification
  (`Exhaustification.exhChain_iff_succ`)
- `Ignorance.parse_sg_total`: unpruned parses force total ignorance —
  the structural core of her Tables 4.1/4.3, via
  `Exhaustification.forall_not_preExh_iff`; `winner0_blocked`,
  `sg_accommodates_loser`, `db_blocks_loser`: the residual table cells
- `AntiNegativity.negation_fails_PS`: `O_ExhDA` is vacuous under negation
  (her Ch. 5 (9)), so the SMN's Proper Strengthening requirement fails;
  `NumeralClass`: her [±prune DA, ±PS] parameter pair
-/

namespace Mihoc2019

open Core.Order

/-! ### Extent indicators (her §2.5, Ch. 2 (27)–(28)) -/

/-- ⟦much⟧(n) = {d | d ≤ n}: the positive extent of `n` on the cardinality
scale — `Comparison.le.interval n`. -/
def much (n : ℕ) : Set ℕ := Comparison.le.interval n

/-- ⟦little⟧(n) = {d | d ≥ n}: the negative extent —
`Comparison.ge.interval n`. -/
def little (n : ℕ) : Set ℕ := Comparison.ge.interval n

@[simp] theorem mem_much {d n : ℕ} : d ∈ much n ↔ d ≤ n := by
  simp [much, Comparison.rel]

@[simp] theorem mem_little {d n : ℕ} : d ∈ little n ↔ n ≤ d := by
  simp [little, Comparison.rel]

/-! ### The modifiers [comp] and [at-sup] (her Ch. 2 (30)–(31))

Both take an extent indicator `f` and the numeral `n`, and locate the maximum
of the degree predicate — abstracted here as its value `maxD` — relative to
the extent `f n`: [comp] in its complement, [at-sup] inside it. -/

/-- [comp] (her Ch. 2 (30)): `max(D) ∈ complement of f(n)`. -/
def compTC (f : ℕ → Set ℕ) (n maxD : ℕ) : Prop := maxD ∈ (f n)ᶜ

/-- [at-sup] (her Ch. 2 (31)): `max(D) ∈ f(n)`. -/
def atSupTC (f : ℕ → Set ℕ) (n maxD : ℕ) : Prop := maxD ∈ f n

/-! ### Reduction to the Kennedy spine (her Ch. 2 (32)–(33))

The four cross-pairings recover exactly the named meanings of
`Semantics.Numerals`. That *at least* pairs with `little` and *at most* with
`much` — inverting the pairing of the comparatives — is what captures the
shared `much`/`little` morphology across CMNs and SMNs. -/

theorem compTC_much_iff (n maxD : ℕ) :
    compTC much n maxD ↔ Semantics.Numerals.moreThanMeaning n maxD := by
  simp [compTC, Semantics.Numerals.moreThanMeaning, Comparison.rel]

theorem compTC_little_iff (n maxD : ℕ) :
    compTC little n maxD ↔ Semantics.Numerals.fewerThanMeaning n maxD := by
  simp [compTC, Semantics.Numerals.fewerThanMeaning, Comparison.rel]

theorem atSupTC_little_iff (n maxD : ℕ) :
    atSupTC little n maxD ↔ Semantics.Numerals.atLeastMeaning n maxD := by
  simp [atSupTC, Semantics.Numerals.atLeastMeaning, Comparison.rel]

theorem atSupTC_much_iff (n maxD : ℕ) :
    atSupTC much n maxD ↔ Semantics.Numerals.atMostMeaning n maxD := by
  simp [atSupTC, Semantics.Numerals.atMostMeaning, Comparison.rel]

/-! ### Assertion forms (her §2.6)

Truth conditions of all three classes expose a scalar element (the numeral);
those of CMNs/SMNs additionally expose a degree-set domain. -/

/-- The two extent indicators as data. -/
inductive Extent where
  /-- Positive extent: `⟦much⟧(n) = {d | d ≤ n}`. -/
  | much
  /-- Negative extent: `⟦little⟧(n) = {d | n ≤ d}`. -/
  | little
  deriving DecidableEq, Repr

/-- The extent an `Extent` denotes. -/
def Extent.set : Extent → ℕ → Set ℕ
  | .much => Mihoc2019.much
  | .little => Mihoc2019.little

/-- The [comp]/[at-sup] operators as data. -/
inductive Op where
  /-- [comp]: maximum in the complement of the extent (strict, Class A). -/
  | comp
  /-- [at-sup]: maximum inside the extent (non-strict, Class B). -/
  | atSup
  deriving DecidableEq, Repr

/-- BN/CMN/SMN assertion forms. -/
inductive Form where
  /-- A bare numeral (Hornian lower-bounded basic meaning, her §2.3). -/
  | bare (n : ℕ)
  /-- An extent indicator under [comp] or [at-sup]. -/
  | modified (op : Op) (f : Extent) (n : ℕ)
  deriving DecidableEq, Repr

/-- *more than n* = [comp]+much. -/
abbrev Form.moreThan (n : ℕ) : Form := .modified .comp .much n

/-- *less than n* = [comp]+little. -/
abbrev Form.lessThan (n : ℕ) : Form := .modified .comp .little n

/-- *at least n* = [at-sup]+little. -/
abbrev Form.atLeast (n : ℕ) : Form := .modified .atSup .little n

/-- *at most n* = [at-sup]+much. -/
abbrev Form.atMost (n : ℕ) : Form := .modified .atSup .much n

/-- Truth conditions of a form, as a predicate on the maximum of the degree
predicate. Bare numerals get the lower-bounded Horn meaning
(`Semantics.Numerals.atLeastMeaning`; her §2.3, following [horn-1972]). -/
def Form.tc : Form → ℕ → Prop
  | .bare n, maxD => Semantics.Numerals.atLeastMeaning n maxD
  | .modified .comp f n, maxD => compTC f.set n maxD
  | .modified .atSup f n, maxD => atSupTC f.set n maxD

instance (φ : Form) (maxD : ℕ) : Decidable (φ.tc maxD) := by
  obtain ⟨n⟩ | ⟨op, f, n⟩ := φ
  · exact inferInstanceAs (Decidable (maxD ≥ n))
  · cases op <;> cases f
    · exact inferInstanceAs (Decidable ¬(maxD ≤ n))
    · exact inferInstanceAs (Decidable ¬(n ≤ maxD))
    · exact inferInstanceAs (Decidable (maxD ≤ n))
    · exact inferInstanceAs (Decidable (n ≤ maxD))

/-! ### The Op × Extent factorization of the `Comparison` spine

The four modified forms are a coordinate system on the four non-`eq`
`Core.Order.Comparison`s: the operator carries strictness (Class A/B,
`Comparison.isStrict`), the extent and operator jointly fix the bound
direction. `Form.tc_iff_rel` makes the factorization first-class; the Class
A/B boundary facts then follow from `Comparison.boundary_mem` rather than
being re-proved. -/

/-- The comparison a form's truth conditions instantiate. -/
def Form.toComparison : Form → Comparison
  | .bare _ => .ge
  | .modified .comp .much _ => .gt
  | .modified .comp .little _ => .lt
  | .modified .atSup .little _ => .ge
  | .modified .atSup .much _ => .le

/-- The numeral argument of a form. -/
def Form.arg : Form → ℕ
  | .bare n => n
  | .modified _ _ n => n

/-- The factorization theorem: every form's truth conditions are its
comparison's relation at its numeral argument. -/
theorem Form.tc_iff_rel (φ : Form) (maxD : ℕ) :
    φ.tc maxD ↔ φ.toComparison.rel maxD φ.arg := by
  obtain ⟨n⟩ | ⟨op, f, n⟩ := φ
  · exact Iff.rfl
  · cases op <;> cases f <;>
      simp only [Form.tc, Form.toComparison, Form.arg, compTC, atSupTC,
        Set.mem_compl_iff, mem_much, mem_little, Extent.set, Comparison.rel] <;>
      omega

@[simp] theorem tc_bare (n maxD : ℕ) : (Form.bare n).tc maxD ↔ n ≤ maxD := by
  simp [Form.tc, Semantics.Numerals.atLeastMeaning, Comparison.rel]

@[simp] theorem tc_moreThan (n maxD : ℕ) :
    (Form.moreThan n).tc maxD ↔ n < maxD := by
  simp [Form.tc_iff_rel, Form.toComparison, Form.arg, Comparison.rel]

@[simp] theorem tc_lessThan (n maxD : ℕ) :
    (Form.lessThan n).tc maxD ↔ maxD < n := by
  simp [Form.tc_iff_rel, Form.toComparison, Form.arg, Comparison.rel]

@[simp] theorem tc_atLeast (n maxD : ℕ) :
    (Form.atLeast n).tc maxD ↔ n ≤ maxD := by
  simp [Form.tc_iff_rel, Form.toComparison, Form.arg, Comparison.rel]

@[simp] theorem tc_atMost (n maxD : ℕ) :
    (Form.atMost n).tc maxD ↔ maxD ≤ n := by
  simp [Form.tc_iff_rel, Form.toComparison, Form.arg, Comparison.rel]

/-! ### Class A/B strictness from the decomposition

The Class A (strict) / Class B (non-strict) split of [geurts-nouwen-2007]
and [nouwen-2010] — `Semantics.Numerals.ModifierClass` — derived from
complement-vs-extent through `Comparison.boundary_mem`, rather than
stipulated per modifier. -/

theorem comp_excludes_boundary (f : Extent) (n : ℕ) :
    ¬ (Form.modified .comp f n).tc n := by
  rw [Form.tc_iff_rel]
  simp only [Form.arg]
  rw [← Comparison.mem_interval, Comparison.boundary_mem]
  cases f <;> simp [Form.toComparison, Comparison.isStrict]

theorem atSup_includes_boundary (f : Extent) (n : ℕ) :
    (Form.modified .atSup f n).tc n := by
  rw [Form.tc_iff_rel]
  simp only [Form.arg]
  rw [← Comparison.mem_interval, Comparison.boundary_mem]
  cases f <;> simp [Form.toComparison, Comparison.isStrict]

/-! ### Domain alternatives (her Ch. 2 (37)–(39))

σA replaces the numeral with a scalemate. DA replaces the set the maximum is
asserted to fall in — the *complement* of the extent for [comp] forms (her
(38c)), the extent itself for [at-sup] forms (her (39c)) — with its proper
subsets; uniformly, the proper subsets of the form's truth-condition set.
Bare numerals reference no degree-set domain and generate no DA (her (37c)):
the structural asymmetry that drives the ignorance and polarity results of
her Chs. 4–5. -/

/-- The degree-set domains a form makes available for subdomain
alternatives. -/
def Form.domainAlts : Form → Set (Set ℕ)
  | .bare _ => ∅
  | φ@(.modified _ _ _) => {D' | D' ⊂ {d | φ.tc d}}

/-- Every domain alternative strengthens the assertion: membership of the
maximum in a DA entails the form's truth conditions — the premise of her
Ch. 4 pre-exhaustification. -/
theorem Form.tc_of_mem_domainAlt {φ : Form} {D' : Set ℕ}
    (h : D' ∈ φ.domainAlts) {maxD : ℕ} (hm : maxD ∈ D') : φ.tc maxD := by
  obtain ⟨n⟩ | ⟨op, f, n⟩ := φ
  · exact absurd h (Set.notMem_empty _)
  · simp only [Form.domainAlts, Set.mem_setOf_eq] at h
    exact h.subset hm

/-! ### σA-exhaustification and 'exactly' overgeneration (her Ch. 3)

`O_σA` asserts the prejacent and negates its next-stronger scalar alternative
on a scale of granularity `g` (stronger = larger numeral for lower-bounding
forms, smaller for upper-bounding). Negating the next-stronger scalemate is
her own computation shape (Ch. 3 (2), (24)–(27)) and coincides with full
innocent-exclusion exhaustification for these monotone forms, whose stronger
alternatives form an entailment chain.

At `g = 1` the result is an 'exactly' meaning for *every* form: welcome for
bare numerals (her Ch. 3 (2)), the unwelcome overgeneration of her Ch. 3
(24)–(27) for CMNs/SMNs. Coarser granularity yields a non-singleton interval
instead (her §3.6–3.7). The scale and its granularity are contextual
([sauerland-stateva-2011]'s granularity functions; rounder numerals select
coarser scales, [krifka-2007], her pp. 110–111) rather than universally
dense (her fn. 8, contra [fox-hackl-2006] — though on discrete ℕ the
accounts agree: cf. `FoxHackl2006Numerals.moreThan_has_maxInf_nat`). -/

/-- The next-stronger σA scalemate of a form at granularity `g`. -/
def Form.strongerAlt (g : ℕ) : Form → Form
  | .bare n => .bare (n + g)
  | .modified .comp .much n => .moreThan (n + g)
  | .modified .comp .little n => .lessThan (n - g)
  | .modified .atSup .little n => .atLeast (n + g)
  | .modified .atSup .much n => .atMost (n - g)

/-- `O_σA` at granularity `g`: assert the prejacent, negate the next-stronger
scalemate. -/
def Form.exhSigma (g : ℕ) (φ : Form) (maxD : ℕ) : Prop :=
  φ.tc maxD ∧ ¬ (φ.strongerAlt g).tc maxD

instance (g : ℕ) (φ : Form) (maxD : ℕ) : Decidable (φ.exhSigma g maxD) :=
  inferInstanceAs (Decidable (φ.tc maxD ∧ ¬ (φ.strongerAlt g).tc maxD))

/-- At granularity 1 on a bare numeral, her `O_σA` *is* the spine's
`Semantics.Numerals.exhNumeral` — and hence, via
`Spector2013.exhNumeral_eq_innocent_exh`, Fox-2007 innocent exclusion.
`exhSigma` is its generalization to arbitrary granularity and to the
upper-bounding scalemate direction. -/
theorem exhSigma_bare_eq_exhNumeral (n maxD : ℕ) :
    (Form.bare n).exhSigma 1 maxD ↔ Semantics.Numerals.exhNumeral n maxD :=
  Iff.rfl

/-- The *at least* form agrees with the bare form under `O_σA` at
granularity 1 — both are `exhNumeral`. -/
theorem exhSigma_atLeast_eq_exhNumeral (n maxD : ℕ) :
    (Form.atLeast n).exhSigma 1 maxD ↔ Semantics.Numerals.exhNumeral n maxD := by
  simp [Form.exhSigma, Form.strongerAlt, Semantics.Numerals.exhNumeral,
    Semantics.Numerals.atLeastMeaning, Comparison.rel]

/-- Her Ch. 3 (2): `O_σA`(bare n) = 'exactly n' — the classical Horn
derivation. -/
theorem exhSigma_bare_g1 (n maxD : ℕ) :
    (Form.bare n).exhSigma 1 maxD ↔ maxD = n := by
  rw [exhSigma_bare_eq_exhNumeral, Semantics.Numerals.exhNumeral_iff_bare,
    Semantics.Numerals.bareMeaning_def]

/-- Her Ch. 3 (24): `O_σA`(more than n) = 'exactly n+1' — unwelcome. -/
theorem exhSigma_moreThan_g1 (n maxD : ℕ) :
    (Form.moreThan n).exhSigma 1 maxD ↔ maxD = n + 1 := by
  simp only [Form.exhSigma, Form.strongerAlt, tc_moreThan]; omega

/-- Her Ch. 3 (25): `O_σA`(less than n) = 'exactly n−1' — unwelcome. -/
theorem exhSigma_lessThan_g1 (n maxD : ℕ) (hn : 1 ≤ n) :
    (Form.lessThan n).exhSigma 1 maxD ↔ maxD = n - 1 := by
  simp only [Form.exhSigma, Form.strongerAlt, tc_lessThan]; omega

/-- Her Ch. 3 (26): `O_σA`(at least n) = 'exactly n' — unwelcome. -/
theorem exhSigma_atLeast_g1 (n maxD : ℕ) :
    (Form.atLeast n).exhSigma 1 maxD ↔ maxD = n := by
  simp only [Form.exhSigma, Form.strongerAlt, tc_atLeast]; omega

/-- Her Ch. 3 (27): `O_σA`(at most n) = 'exactly n' — unwelcome. -/
theorem exhSigma_atMost_g1 (n maxD : ℕ) (hn : 1 ≤ n) :
    (Form.atMost n).exhSigma 1 maxD ↔ maxD = n := by
  simp only [Form.exhSigma, Form.strongerAlt, tc_atMost]; omega

/-- The granularity-1 strengthening is *non-vacuous*: some worlds verify the
CMN's truth conditions but not its exhaustification. Mihoc thus derives a
scalar implicature for Class A forms exactly where [kennedy-2015]'s
neo-Gricean account derives none (`Kennedy2015.classA_moreThan3_no_primary`)
— same truth conditions, opposite pragmatic verdict, reconciled only by the
granularity parameter (coarse scales recover the weaker effect,
`exhSigma_moreThan_coarse_not_exactly`). -/
theorem exhSigma_moreThan_proper (n : ℕ) :
    ∃ maxD, (Form.moreThan n).tc maxD ∧ ¬ (Form.moreThan n).exhSigma 1 maxD :=
  ⟨n + 2, by simp, by rw [exhSigma_moreThan_g1]; omega⟩

/-- Her §3.7: at granularity ≥ 2 the exhaustified CMN is no longer an
'exactly' meaning — two distinct values survive. -/
theorem exhSigma_moreThan_coarse_not_exactly (n g : ℕ) (hg : 2 ≤ g) :
    ∃ d₁ d₂, d₁ ≠ d₂ ∧
      (Form.moreThan n).exhSigma g d₁ ∧ (Form.moreThan n).exhSigma g d₂ := by
  refine ⟨n + 1, n + 2, by omega, ?_, ?_⟩ <;>
    · simp only [Form.exhSigma, Form.strongerAlt, tc_moreThan]
      omega

/-- [spector-2014]'s grade context (her §3.6 (33)): with the contextually
salient scale ⟨…, more than 5, more than 9, …⟩ (granularity 4), *John solved
more than five problems* implicates *not more than nine* — the surviving
meaning is the interval {6, …, 9} she glosses as "a B", not an 'exactly'. -/
theorem spector_grade_context (maxD : ℕ) :
    (Form.moreThan 5).exhSigma 4 maxD ↔ 5 < maxD ∧ maxD ≤ 9 := by
  simp only [Form.exhSigma, Form.strongerAlt, tc_moreThan]; omega

-- Verification: the five 'exactly' verdicts at granularity 1, on her values
#guard (Form.bare 3).exhSigma 1 3
#guard (Form.moreThan 3).exhSigma 1 4 ∧ ¬ (Form.moreThan 3).exhSigma 1 5
#guard (Form.lessThan 3).exhSigma 1 2 ∧ ¬ (Form.lessThan 3).exhSigma 1 1
#guard (Form.atLeast 3).exhSigma 1 3 ∧ ¬ (Form.atLeast 3).exhSigma 1 4
#guard (Form.atMost 3).exhSigma 1 3 ∧ ¬ (Form.atMost 3).exhSigma 1 2


/-! ### σA scales as entailment chains

`exhSigma` negates one next-stronger scalemate; the substrate keystone
`Exhaustification.exhChain_iff_succ` shows this equals exhaustification
against the *whole* granularity-`g` scale, since the scale is an entailment
chain. (Dually, `Exhaustification.exhChain_not_of_dense` is the
[fox-hackl-2006] crash that this file's contextual-granularity scales
avoid: cf. `FoxHackl2006Numerals.moreThan_exhChain_crash`.) -/

theorem exhSigma_moreThan_eq_exhChain (n g maxD : ℕ) :
    (Form.moreThan n).exhSigma g maxD ↔
      Exhaustification.exhChain (fun k => (Form.moreThan (n + k * g)).tc) 0 maxD := by
  rw [Exhaustification.exhChain_iff_succ
      (fun j k hjk d hd => by
        simp only [tc_moreThan] at hd ⊢
        have := Nat.mul_le_mul_right g hjk
        omega)
      Nat.zero_lt_one fun j hj => hj]
  simp only [Form.exhSigma, Form.strongerAlt, tc_moreThan, Nat.zero_mul,
    Nat.add_zero, Nat.one_mul]

theorem exhSigma_atMost_eq_exhChain (n g maxD : ℕ) :
    (Form.atMost n).exhSigma g maxD ↔
      Exhaustification.exhChain (fun k => (Form.atMost (n - k * g)).tc) 0 maxD := by
  rw [Exhaustification.exhChain_iff_succ
      (fun j k hjk d hd => by
        simp only [tc_atMost] at hd ⊢
        have := Nat.mul_le_mul_right g hjk
        omega)
      Nat.zero_lt_one fun j hj => hj]
  simp only [Form.exhSigma, Form.strongerAlt, tc_atMost, Nat.zero_mul,
    Nat.sub_zero, Nat.one_mul]

/-! ### Ignorance (her Ch. 4)

Assertions carry a null epistemic necessity modal `□_S`; `O` applies above
it, negating pre-exhaustified domain alternatives
(`Exhaustification.preExh`) and the stronger σA. Her running model: the CMN
*less than three* / SMN *at most two*, worlds = candidate maxima 0–3,
`□_S` = `ContextSet.entails` over a nonempty epistemic state
(`boxS_iff_entails`). The DA are the value-regions inside the prejacent set
{0, 1, 2}: singletons and doubletons.

The load-bearing structure: negating the pre-exhaustified singleton DA says
no region is settled *uniquely* (`Exhaustification.forall_not_preExh_iff`),
and a nonempty state settles at most one of the disjoint regions
(`sgDA_subsingleton`) — so none is settled: **total ignorance**, her Tables
4.1/4.3, derived structurally. The residual table cells (loser/winner
accommodation and blocking) are checked exhaustively over all epistemic
states. -/

namespace Ignorance

/-- Worlds: the candidate maximum, values 0–3. -/
abbrev EWorld := Fin 4

/-- `□_S` over a finite epistemic state — `ContextSet.entails` in
computable clothing (`boxS_iff_entails`). -/
def boxS (E : Finset EWorld) (p : EWorld → Prop) : Prop := ∀ w ∈ E, p w

instance (E : Finset EWorld) (p : EWorld → Prop) [DecidablePred p] :
    Decidable (boxS E p) :=
  inferInstanceAs (Decidable (∀ w ∈ E, p w))

theorem boxS_iff_entails (E : Finset EWorld) (p : EWorld → Prop) :
    boxS E p ↔ CommonGround.ContextSet.entails (↑E : Set EWorld) {w | p w} := by
  simp [boxS, CommonGround.ContextSet.entails, Set.subset_def]

/-- The asserted prejacent: `□_S`(*less than three*). -/
def prejacent (E : Finset EWorld) : Prop :=
  boxS E fun w => (Form.lessThan 3).tc w.val

instance (E : Finset EWorld) : Decidable (prejacent E) :=
  inferInstanceAs (Decidable (boxS E fun w => (Form.lessThan 3).tc w.val))

/-- Singleton domain alternatives: `□_S(max = i)` for `i < 3`. -/
def sgDA (E : Finset EWorld) (i : Fin 3) : Prop :=
  boxS E fun w => w.val = i.val

/-- Doubleton domain alternatives: `□_S` of the prejacent region minus
value `i`. -/
def dbDA (E : Finset EWorld) (i : Fin 3) : Prop :=
  boxS E fun w => w.val < 3 ∧ w.val ≠ i.val

instance (E : Finset EWorld) (i : Fin 3) : Decidable (sgDA E i) :=
  inferInstanceAs (Decidable (boxS E fun w => w.val = i.val))

instance (E : Finset EWorld) (i : Fin 3) : Decidable (dbDA E i) :=
  inferInstanceAs (Decidable (boxS E fun w => w.val < 3 ∧ w.val ≠ i.val))

/-- A nonempty state settles at most one singleton region. -/
theorem sgDA_subsingleton {E : Finset EWorld} (hE : E.Nonempty) {i j : Fin 3}
    (hi : sgDA E i) (hj : sgDA E j) : i = j := by
  obtain ⟨w, hw⟩ := hE
  have h1 := hi w hw
  have h2 := hj w hw
  exact Fin.ext (by omega)

/-- **Total ignorance from unique-truth failure**: negating every
pre-exhaustified singleton DA leaves no settled region at all — the
'total' verdicts of her Tables 4.1/4.3, structurally. -/
theorem total_ignorance_of_not_preExh {E : Finset EWorld} (hE : E.Nonempty)
    (h : ∀ i, ¬ Exhaustification.preExh (sgDA E) i) (i : Fin 3) :
    ¬ sgDA E i := by
  intro hi
  rw [Exhaustification.forall_not_preExh_iff] at h
  exact h ⟨i, hi, fun j hj => sgDA_subsingleton hE hj hi⟩

/-- The `O_ExhDA+σA` parse of `□_S`(*less than three*) (her (12)/(14)/(16)),
with her DA-pruning parameter: `sg`/`db` select which DA sizes survive
pruning. -/
def parse (sg db : Bool) (E : Finset EWorld) : Prop :=
  prejacent E ∧
  (sg = true → ∀ i, ¬ Exhaustification.preExh (sgDA E) i) ∧
  (db = true → ∀ i, ¬ Exhaustification.preExh (dbDA E) i) ∧
  ¬ boxS E (fun w => w.val < 2) ∧ ¬ boxS E (fun w => w.val < 1)

instance (sg db : Bool) (E : Finset EWorld) : Decidable (parse sg db E) :=
  inferInstanceAs (Decidable (prejacent E ∧ _ ∧ _ ∧ _ ∧ _))

/-- Total ignorance (her total row): no value-region is settled. -/
def TotalIgnorance (E : Finset EWorld) : Prop := ∀ i, ¬ sgDA E i

/-- Her canonical 'winner' scenario: `□_S 0`. -/
def winner0 (E : Finset EWorld) : Prop := sgDA E 0

/-- Her canonical 'loser' scenario: `□_S ¬0 ∧ ¬□_S 1 ∧ ¬□_S 2` — one region
excluded, the rest unsettled. -/
def loser0 (E : Finset EWorld) : Prop :=
  (boxS E fun w => w.val ≠ 0) ∧ ¬ sgDA E 1 ∧ ¬ sgDA E 2

instance (E : Finset EWorld) : Decidable (loser0 E) :=
  inferInstanceAs (Decidable ((boxS E fun w => w.val ≠ 0) ∧ _ ∧ _))

/-- Any parse that keeps the singleton DA forces total ignorance — her
Table 4.1 and 4.3 sum-ups, including the SMN (no-pruning) verdict. -/
theorem parse_sg_total {db : Bool} {E : Finset EWorld} (hE : E.Nonempty)
    (h : parse true db E) : TotalIgnorance E :=
  fun i => total_ignorance_of_not_preExh hE (h.2.1 rfl) i

/-- The 'winner' scenario clashes with the σA-implicature — the ✗ cells of
her Tables 4.1/4.2: `□_S 0` entails `□_S`(*less than one*). -/
theorem winner0_blocked {sg db : Bool} {E : Finset EWorld}
    (h : parse sg db E) : ¬ winner0 E := by
  intro hw
  exact h.2.2.2.2 fun w hwE => by have := hw w hwE; omega

/-- The singleton-DA regime accommodates the 'loser' scenario — Table 4.1's
✓ cell (CMNs, which may prune, admit partial ignorance). -/
theorem sg_accommodates_loser :
    ∃ E : Finset EWorld, E.Nonempty ∧ parse true false E ∧ loser0 E := by
  exact ⟨{1, 2}, by decide, by decide, by decide⟩

/-- The doubleton-DA regime blocks the 'loser' scenario — Table 4.2's ✗
cell — checked over every epistemic state. -/
theorem db_blocks_loser :
    ∀ E : Finset EWorld, E.Nonempty → parse false true E → ¬ loser0 E := by
  decide

end Ignorance

/-! ### Anti-negativity (her Ch. 5)

Under clausemate negation each pre-exhaustified DA is individually
inconsistent with the prejacent, so `O_ExhDA` is vacuous (her (9)) — and
the Proper Strengthening requirement
(`Exhaustification.ProperlyStrengthens`) fails. Her parameter pair: SMNs
keep all DA (hence episodic total ignorance, `Ignorance.parse_sg_total`)
and require PS (hence deviance under negation, `negation_fails_PS`); CMNs
may prune and impose no PS requirement, escaping both. -/

namespace AntiNegativity

/-- Worlds for the negated case: candidate maxima 0–2. -/
abbrev NWorld := Fin 3

/-- *John didn't call less than two people*: the negated prejacent. -/
def negPrejacent (w : NWorld) : Prop := ¬ (Form.lessThan 2).tc w.val

/-- The embedded numeral's DA as propositions at `w`: `max = i`, `i < 2`. -/
def negDA (w : NWorld) (i : Fin 2) : Prop := w.val = i.val

/-- The `O_ExhDA` parse of the negated sentence (her (8)–(9)). -/
def oParse (w : NWorld) : Prop :=
  negPrejacent w ∧ ∀ i, ¬ Exhaustification.preExh (negDA w) i

/-- Her (9): every pre-exhaustified DA contradicts the negated prejacent,
so negating them adds nothing — `O_ExhDA` is vacuous. -/
theorem oParse_iff_negPrejacent (w : NWorld) : oParse w ↔ negPrejacent w := by
  constructor
  · exact And.left
  · intro h
    refine ⟨h, fun i hpe => h ((tc_lessThan 2 w.val).mpr ?_)⟩
    have hi := hpe.1
    simp only [negDA] at hi
    omega

/-- Vacuous exhaustification fails Proper Strengthening — the SMN
anti-negativity verdict (her §5.1); CMNs, lacking the requirement, are
fine under negation. -/
theorem negation_fails_PS :
    ¬ Exhaustification.ProperlyStrengthens oParse negPrejacent :=
  Exhaustification.not_properlyStrengthens_of_iff oParse_iff_negPrejacent

/-- Her Ch. 4–5 lexical parameter pair for modified numerals. -/
inductive NumeralClass where
  /-- Comparative-modified: may prune DA; no PS requirement. -/
  | cmn
  /-- Superlative-modified: full DA; PS required. -/
  | smn
  deriving DecidableEq, Repr

/-- Whether the class licenses DA pruning (her Ch. 4). -/
def NumeralClass.canPruneDA : NumeralClass → Prop
  | .cmn => True
  | .smn => False

/-- Whether the class requires Proper Strengthening (her Ch. 5). -/
def NumeralClass.requiresPS : NumeralClass → Prop
  | .cmn => False
  | .smn => True

end AntiNegativity

end Mihoc2019
