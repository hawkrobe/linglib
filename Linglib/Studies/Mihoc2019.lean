import Linglib.Core.Order.Comparison
import Linglib.Semantics.Quantification.Numerals.Basic

/-!
# [mihoc-2019]: Decomposing Modified Numerals
[mihoc-2019] [hackl-2000] [kennedy-2015] [horn-1972] [geurts-nouwen-2007]
[nouwen-2010] [fox-hackl-2006] [spector-2014] [chierchia-2013]

[mihoc-2019] (Ch. 2) decomposes bare (BN), comparative-modified (CMN), and
superlative-modified (SMN) numerals into *extent indicators* — `much`/`little`
denote Kennedy-style positive/negative extents on the cardinality scale — and
two operators: [comp] places the maximum of the degree predicate in the
*complement* of the extent, [at-sup] inside it. The four modified forms are
cross-pairings (*more than* = [comp]+much, *less than* = [comp]+little,
*at least* = [at-sup]+**little**, *at most* = [at-sup]+**much**), and the
truth conditions provably reduce to the Hackl/Kennedy meanings — here the
named meanings of `Semantics.Numerals`, so the reduction theorems double as
bridges to the [kennedy-2015] spine. Alternatives fall out of the truth
conditions: σA replaces the numeral with a scalemate, DA replaces the extent
with its subsets — and bare numerals generate *no* DA, since their (Hornian,
lower-bounded) truth conditions reference no degree-set domain (her (37)).

Ch. 3 defends classical scalar implicatures for all three classes and locates
the failures: σA-exhaustification at scale granularity 1 produces an
'exactly' meaning for *every* form — welcome for bare numerals ([horn-1972]),
unwelcome for CMNs/SMNs (her (24)–(27)) — while coarser granularities avoid
it (§3.7; [spector-2014]'s grade context is the granularity-4 instance).
The scale's granularity is contextual rather than universally dense, contra
[fox-hackl-2006] (her fn. 8).

## Main definitions

- `much`, `little`: the extent indicators, as `Core.Order.Comparison.interval`s
- `compTC`, `atSupTC`: the [comp]/[at-sup] truth conditions on the maximum
- `Form`: BN/CMN/SMN assertion forms; `Form.tc`, `Form.strongerAlt`,
  `Form.exhSigma`: truth conditions, next-stronger σA scalemate at
  granularity `g`, and σA-exhaustification

## Main results

- `compTC_much_iff` … `atSupTC_much_iff`: the reductions to the
  `Semantics.Numerals` named meanings (her (32)–(33))
- `comp_excludes_boundary` / `atSup_includes_boundary`: the Class A/B
  strict/non-strict split derived from complement-vs-extent
  ([geurts-nouwen-2007], [nouwen-2010])
- `exhSigma_*_g1`: 'exactly' meanings for all five forms at granularity 1
  (her (2), (24)–(27)); `exhSigma_moreThan_coarse_not_exactly` and
  `spector_grade_context`: coarser granularity avoids them (§3.7, (33))
-/

namespace Mihoc2019

open Core.Order

/-! ### Extent indicators (her §2.5, (27)–(28)) -/

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

/-! ### The modifiers [comp] and [at-sup] (her (30)–(31))

Both take an extent indicator `f` and the numeral `n`, and locate the maximum
of the degree predicate — abstracted here as its value `maxD` — relative to
the extent `f n`: [comp] in its complement, [at-sup] inside it. -/

/-- [comp] (her (30)): `max(D) ∈ complement of f(n)`. -/
def compTC (f : ℕ → Set ℕ) (n maxD : ℕ) : Prop := maxD ∈ (f n)ᶜ

/-- [at-sup] (her (31)): `max(D) ∈ f(n)`. -/
def atSupTC (f : ℕ → Set ℕ) (n maxD : ℕ) : Prop := maxD ∈ f n

/-! ### Reduction to the Kennedy spine (her (32)–(33))

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

/-! ### Class A/B strictness from the decomposition

The boundary value `n` always lies in its own extent, so [comp]-built
meanings exclude it and [at-sup]-built meanings include it: the Class A
(strict) / Class B (non-strict) split of [geurts-nouwen-2007] and
[nouwen-2010] — `Semantics.Numerals.ModifierClass`, truth-conditionally
`Comparison.boundary_mem` — derived from complement-vs-extent rather than
stipulated per modifier. -/

/-- The two extent indicators as data (for stating form-level facts). -/
inductive Extent where
  | much
  | little
  deriving DecidableEq, Repr

/-- The extent an `Extent` denotes. -/
def Extent.set : Extent → ℕ → Set ℕ
  | .much => Mihoc2019.much
  | .little => Mihoc2019.little

theorem comp_excludes_boundary (f : Extent) (n : ℕ) : ¬ compTC f.set n n := by
  cases f <;> simp [compTC, Extent.set]

theorem atSup_includes_boundary (f : Extent) (n : ℕ) : atSupTC f.set n n := by
  cases f <;> simp [atSupTC, Extent.set]

/-! ### Assertion forms and their alternatives (her §2.6, (37)–(39))

Truth conditions of all three classes expose a scalar element (the numeral);
those of CMNs/SMNs additionally expose a degree-set domain (the extent).
σA replaces the numeral, DA replaces the extent with its proper subsets —
so bare numerals, whose truth conditions reference no extent, generate no DA
(her (37c)): the structural asymmetry that drives the ignorance and
polarity results of her Chs. 4–5. -/

/-- The [comp]/[at-sup] operators as data. -/
inductive Op where
  | comp
  | atSup
  deriving DecidableEq, Repr

/-- BN/CMN/SMN assertion forms: a bare numeral, or an extent indicator under
[comp] or [at-sup]. -/
inductive Form where
  | bare (n : ℕ)
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
  · cases op <;> cases f <;>
      · simp only [Form.tc, compTC, atSupTC, Extent.set, Set.mem_compl_iff,
          mem_much, mem_little]
        infer_instance

/-- The degree-set domains a form makes available for DA: the proper subsets
of the extent for modified forms; none for bare numerals (her (37c)). -/
def Form.domainAlts : Form → Set (Set ℕ)
  | .bare _ => ∅
  | .modified _ f n => {D' | D' ⊂ f.set n}

/-! ### σA-exhaustification and 'exactly' overgeneration (her Ch. 3)

`O_σA` asserts the prejacent and negates its next-stronger scalar alternative
on a scale of granularity `g` (stronger = larger numeral for lower-bounding
forms, smaller for upper-bounding). At `g = 1` the result is an 'exactly'
meaning for *every* form: welcome for bare numerals (her (2)), the unwelcome
overgeneration of her (24)–(27) for CMNs/SMNs. Coarser granularity yields a
non-singleton interval instead (§3.7, her (44)); the scale and its
granularity are contextual, not universally dense (her fn. 8, contra
[fox-hackl-2006]). -/

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

/-- Her (2): `O_σA`(bare n) = 'exactly n' — the classical Horn derivation. -/
theorem exhSigma_bare_g1 (n maxD : ℕ) :
    (Form.bare n).exhSigma 1 maxD ↔ maxD = n := by
  simp only [Form.exhSigma, Form.strongerAlt, Form.tc,
    Semantics.Numerals.atLeastMeaning_def, ge_iff_le]
  omega

/-- Her (24): `O_σA`(more than n) = 'exactly n+1' — unwelcome. -/
theorem exhSigma_moreThan_g1 (n maxD : ℕ) :
    (Form.moreThan n).exhSigma 1 maxD ↔ maxD = n + 1 := by
  simp only [Form.exhSigma, Form.strongerAlt, Form.tc, compTC, Set.mem_compl_iff,
    mem_much, Extent.set]
  omega

/-- Her (25): `O_σA`(less than n) = 'exactly n−1' — unwelcome. -/
theorem exhSigma_lessThan_g1 (n maxD : ℕ) (hn : 1 ≤ n) :
    (Form.lessThan n).exhSigma 1 maxD ↔ maxD = n - 1 := by
  simp only [Form.exhSigma, Form.strongerAlt, Form.tc, compTC, Set.mem_compl_iff,
    mem_little, Extent.set]
  omega

/-- Her (26): `O_σA`(at least n) = 'exactly n' — unwelcome. -/
theorem exhSigma_atLeast_g1 (n maxD : ℕ) :
    (Form.atLeast n).exhSigma 1 maxD ↔ maxD = n := by
  simp only [Form.exhSigma, Form.strongerAlt, Form.tc, atSupTC, mem_little,
    Extent.set]
  omega

/-- Her (27): `O_σA`(at most n) = 'exactly n' — unwelcome. -/
theorem exhSigma_atMost_g1 (n maxD : ℕ) (hn : 1 ≤ n) :
    (Form.atMost n).exhSigma 1 maxD ↔ maxD = n := by
  simp only [Form.exhSigma, Form.strongerAlt, Form.tc, atSupTC, mem_much,
    Extent.set]
  omega

/-- §3.7: at granularity ≥ 2 the exhaustified CMN is no longer an 'exactly'
meaning — two distinct values survive. -/
theorem exhSigma_moreThan_coarse_not_exactly (n g : ℕ) (hg : 2 ≤ g) :
    ∃ d₁ d₂, d₁ ≠ d₂ ∧
      (Form.moreThan n).exhSigma g d₁ ∧ (Form.moreThan n).exhSigma g d₂ := by
  refine ⟨n + 1, n + 2, by omega, ?_, ?_⟩ <;>
    simp only [Form.exhSigma, Form.strongerAlt, Form.tc, compTC, Set.mem_compl_iff,
      mem_much, Extent.set] <;>
    omega

/-- [spector-2014]'s grade context (her (33)): with the contextually salient
scale ⟨…, more than 5, more than 9, …⟩ (granularity 4), *John solved more
than five problems* implicates *not more than nine* — the surviving meaning
is the B-grade band {6, …, 9}, not an 'exactly'. -/
theorem spector_grade_context (maxD : ℕ) :
    (Form.moreThan 5).exhSigma 4 maxD ↔ 5 < maxD ∧ maxD ≤ 9 := by
  simp only [Form.exhSigma, Form.strongerAlt, Form.tc, compTC, Set.mem_compl_iff,
    mem_much, Extent.set]
  omega

-- Verification: the five 'exactly' verdicts at granularity 1, on her values
#guard (Form.bare 3).exhSigma 1 3
#guard (Form.moreThan 3).exhSigma 1 4 ∧ ¬ (Form.moreThan 3).exhSigma 1 5
#guard (Form.lessThan 3).exhSigma 1 2 ∧ ¬ (Form.lessThan 3).exhSigma 1 1
#guard (Form.atLeast 3).exhSigma 1 3 ∧ ¬ (Form.atLeast 3).exhSigma 1 4
#guard (Form.atMost 3).exhSigma 1 3 ∧ ¬ (Form.atMost 3).exhSigma 1 2

end Mihoc2019
