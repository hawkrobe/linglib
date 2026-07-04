import Linglib.Core.Probability.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Algebra.BigOperators.Field

/-!
# PMFs from rational score vectors

RSA-style models compute unnormalized scores in `ℚ≥0` — exact, computable,
and with order decidable by kernel reduction — and state predictions about
the normalized distributions. This file provides the constructor and its
comparison calculus.

`Fallback σ` completes zero-mass score rows: a study declares one fallback
per normalization site, and *both* faces read it — the ℚ≥0 values through
`scoresWith`, the distribution through `ofScores` — so the two cannot
diverge and the bridge `ofScores_apply` is total (a `rfl`). Comparison,
threshold, product, and event lemmas then reduce every prediction to a
`ℚ≥0` inequality between `scoresWith` values, closed by `decide +kernel`.

`normalizeOrUniform` is the generic `ℝ≥0∞` total normalizer (the total
sibling of `PMF.normalize`); `[UPSTREAM]` candidate.

## Main definitions

* `PMF.Fallback` — total fallback distribution (value + nonzero-mass witness)
  with smart constructors `pure`, `uniform`, `uniformOn`.
* `PMF.normalizeScores f` — `f x / ∑ f`, the ℚ≥0 shadow of `PMF.normalize`.
* `PMF.scoresWith fb f` — the normalized `ℚ≥0` score function both faces read.
* `PMF.ofScores fb f` — the induced PMF; `ofScores_apply` is `rfl`.
* `QDist` — bundled exact-rational distribution (`FunLike` into ℚ≥0,
  `toPMF` into the mathlib face); `QDist.ofScores` is the one-step
  constructor for RSA-style agents.
* `PMF.normalizeOrUniform` — total `ℝ≥0∞` normalization.

## Main results

* `ofScores_lt` / `ofScores_lt_cross` / `_le` / `_eq` — predictions from
  `scoresWith` comparisons.
* `ofScores_lt_ratCast` and companions — thresholds against `ℚ≥0` literals.
* `prod_ofScores_apply`, `prod_ofScores_lt` — chain-rule trajectory products.
* `eventMass`, `ofScores_event_eq`, `ofScores_event_lt` — event marginals.
-/

open scoped NNRat NNReal ENNReal

namespace PMF

variable {σ τ : Type*} [Fintype σ]

/-! ### Total normalization -/

variable [Nonempty σ] in
/-- Total normalization: normalize `f` when it has positive finite mass,
else fall back to the uniform distribution. Unlike `PMF.normalize`, no
positivity witness is needed at the definition site, so
`u ↦ normalizeOrUniform (score u)` is a well-defined kernel even when some
rows are dead. `[UPSTREAM]` candidate (total sibling of `PMF.normalize`). -/
noncomputable def normalizeOrUniform (f : σ → ℝ≥0∞) : PMF σ :=
  if h : (∑' x, f x) ≠ 0 ∧ (∑' x, f x) ≠ ∞ then PMF.normalize f h.1 h.2
  else PMF.uniformOfFintype σ

variable [Nonempty σ] in
theorem normalizeOrUniform_apply {f : σ → ℝ≥0∞} (h0 : (∑' x, f x) ≠ 0)
    (hT : (∑' x, f x) ≠ ∞) (x : σ) :
    normalizeOrUniform f x = f x * (∑' x', f x')⁻¹ := by
  rw [normalizeOrUniform, dif_pos ⟨h0, hT⟩, PMF.normalize_apply]

/-! ### Fallbacks -/

/-- A total fallback distribution completing a zero-mass score row: a `ℚ≥0`
weight vector with nonzero mass. A study declares one fallback per
normalization site; `scoresWith` and `ofScores` both read it, so the ℚ≥0
and PMF faces agree by construction. -/
structure Fallback (σ : Type*) [Fintype σ] where
  /-- The fallback weights (normalized by `scoresWith`). -/
  dist : σ → ℚ≥0
  /-- The weights carry mass. -/
  ne_zero : ∑ x, dist x ≠ 0

/-- Point-mass fallback (e.g. a designated null utterance). -/
def Fallback.pure [DecidableEq σ] (a : σ) : Fallback σ where
  dist x := if x = a then 1 else 0
  ne_zero := by simp

/-- Uniform fallback. -/
def Fallback.uniform [Nonempty σ] : Fallback σ where
  dist _ := 1
  ne_zero := by simp

/-- Uniform fallback over a nonempty subset (e.g. words with viable
continuations, scene members). -/
def Fallback.uniformOn [DecidableEq σ] (S : Finset σ) (hS : S.Nonempty) : Fallback σ where
  dist x := if x ∈ S then 1 else 0
  ne_zero := by
    obtain ⟨a, ha⟩ := hS
    intro h
    have := Finset.sum_eq_zero_iff.mp h a (Finset.mem_univ a)
    simp [ha] at this

/-! ### Scores -/

/-- Normalize a score vector into a distribution function (`÷0 = 0` gives
the zero function on a dead vector) — the ℚ≥0 shadow of `PMF.normalize`.
Studies define each agent of a model tower as one `normalizeScores`
application over the agents below it. -/
def normalizeScores (f : σ → ℚ≥0) (x : σ) : ℚ≥0 := f x / ∑ y, f y

/-- The normalized score function both faces read: `f` normalized when it
has mass, else the fallback normalized.

Kernel hygiene: comparisons of `scoresWith` values reduce under
`decide +kernel` provided the score chain's *base tables* are pattern
matches or `Bool`-valued tables — a propositional `if x = y then … else …`
over a derived `DecidableEq` anywhere in the chain blocks kernel reduction
of order comparisons (equalities still reduce). -/
def scoresWith (fb : Fallback σ) (f : σ → ℚ≥0) (x : σ) : ℚ≥0 :=
  if 0 < ∑ y, f y then normalizeScores f x else normalizeScores fb.dist x

theorem scoresWith_sum_eq_one (fb : Fallback σ) (f : σ → ℚ≥0) :
    ∑ x, scoresWith fb f x = 1 := by
  unfold scoresWith normalizeScores
  split
  · rw [← Finset.sum_div, div_self (by positivity)]
  · rw [← Finset.sum_div, div_self fb.ne_zero]

theorem scoresWith_of_pos (fb : Fallback σ) {f : σ → ℚ≥0}
    (h : 0 < ∑ y, f y) (x : σ) : scoresWith fb f x = f x / ∑ y, f y := by
  rw [scoresWith, if_pos h, normalizeScores]

/-- The PMF induced by a score vector and a fallback: pointwise the
coercion of `scoresWith`, so the ℚ≥0 face and the PMF face agree
definitionally. -/
noncomputable def ofScores (fb : Fallback σ) (f : σ → ℚ≥0) : PMF σ :=
  ⟨fun x => ((scoresWith fb f x : ℝ≥0) : ℝ≥0∞), by
    have h : ((1 : ℝ≥0) : ℝ≥0∞) = 1 := rfl
    rw [← h, ← show ((∑ x, scoresWith fb f x : ℚ≥0) : ℝ≥0) = 1 by
        rw [scoresWith_sum_eq_one]; norm_num,
      NNRat.cast_sum]
    exact_mod_cast hasSum_fintype fun x => ((scoresWith fb f x : ℝ≥0) : ℝ≥0∞)⟩

/-- The total bridge: `ofScores` values are exactly the coerced `scoresWith`
values — no hypotheses, by definition. -/
theorem ofScores_apply (fb : Fallback σ) (f : σ → ℚ≥0) (x : σ) :
    ofScores fb f x = ((scoresWith fb f x : ℝ≥0) : ℝ≥0∞) := rfl

/-! ### Comparisons

Each lemma reduces a PMF-level prediction to a `ℚ≥0` inequality between
`scoresWith` values, which `decide +kernel` closes. -/

theorem ofScores_lt_cross {τ : Type*} [Fintype τ]
    (fb₁ : Fallback σ) (fb₂ : Fallback τ) {f : σ → ℚ≥0} {g : τ → ℚ≥0}
    {a : σ} {b : τ} (h : scoresWith fb₁ f a < scoresWith fb₂ g b) :
    ofScores fb₁ f a < ofScores fb₂ g b := by
  rw [ofScores_apply, ofScores_apply]
  exact_mod_cast h

theorem ofScores_lt (fb : Fallback σ) {f : σ → ℚ≥0} {a b : σ}
    (h : scoresWith fb f a < scoresWith fb f b) :
    ofScores fb f a < ofScores fb f b :=
  ofScores_lt_cross fb fb h

theorem ofScores_le_cross {τ : Type*} [Fintype τ]
    (fb₁ : Fallback σ) (fb₂ : Fallback τ) {f : σ → ℚ≥0} {g : τ → ℚ≥0}
    {a : σ} {b : τ} (h : scoresWith fb₁ f a ≤ scoresWith fb₂ g b) :
    ofScores fb₁ f a ≤ ofScores fb₂ g b := by
  rw [ofScores_apply, ofScores_apply]
  exact_mod_cast h

theorem ofScores_eq_cross {τ : Type*} [Fintype τ]
    (fb₁ : Fallback σ) (fb₂ : Fallback τ) {f : σ → ℚ≥0} {g : τ → ℚ≥0}
    {a : σ} {b : τ} (h : scoresWith fb₁ f a = scoresWith fb₂ g b) :
    ofScores fb₁ f a = ofScores fb₂ g b := by
  rw [ofScores_apply, ofScores_apply, h]

/-! ### Thresholds against rational literals -/

theorem ofScores_lt_ratCast (fb : Fallback σ) {f : σ → ℚ≥0} {a : σ} {t : ℚ≥0}
    (h : scoresWith fb f a < t) : ofScores fb f a < ((t : ℝ≥0) : ℝ≥0∞) := by
  rw [ofScores_apply]
  exact_mod_cast h

theorem ratCast_lt_ofScores (fb : Fallback σ) {f : σ → ℚ≥0} {a : σ} {t : ℚ≥0}
    (h : t < scoresWith fb f a) : ((t : ℝ≥0) : ℝ≥0∞) < ofScores fb f a := by
  rw [ofScores_apply]
  exact_mod_cast h

theorem ofScores_eq_ratCast (fb : Fallback σ) {f : σ → ℚ≥0} {a : σ} {t : ℚ≥0}
    (h : scoresWith fb f a = t) : ofScores fb f a = ((t : ℝ≥0) : ℝ≥0∞) := by
  rw [ofScores_apply, h]

/-! ### Chain-rule products -/

theorem prod_ofScores_apply {ι : Type*} (s : Finset ι) (fb : ι → Fallback σ)
    (f : ι → σ → ℚ≥0) (a : ι → σ) :
    (∏ i ∈ s, ofScores (fb i) (f i) (a i))
      = (((∏ i ∈ s, scoresWith (fb i) (f i) (a i) : ℚ≥0) : ℝ≥0) : ℝ≥0∞) := by
  simp only [ofScores_apply]
  push_cast
  rfl

theorem prod_ofScores_lt {ι : Type*} (s : Finset ι) (fb₁ fb₂ : ι → Fallback σ)
    {f g : ι → σ → ℚ≥0} {a b : ι → σ}
    (h : (∏ i ∈ s, scoresWith (fb₁ i) (f i) (a i)) <
      ∏ i ∈ s, scoresWith (fb₂ i) (g i) (b i)) :
    (∏ i ∈ s, ofScores (fb₁ i) (f i) (a i)) <
      ∏ i ∈ s, ofScores (fb₂ i) (g i) (b i) := by
  rw [prod_ofScores_apply, prod_ofScores_apply]
  exact_mod_cast h

/-! ### Event marginals -/

/-- Mass of a decidable event under a `ℚ≥0` weight vector. -/
def eventMass (g : σ → ℚ≥0) (P : σ → Bool) : ℚ≥0 :=
  ∑ x, if P x then g x else 0

theorem ofScores_event_eq (fb : Fallback σ) (f : σ → ℚ≥0) (P : σ → Bool) :
    (∑' x, if P x then ofScores fb f x else 0)
      = ((eventMass (scoresWith fb f) P : ℝ≥0) : ℝ≥0∞) := by
  rw [tsum_fintype, eventMass, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl fun x _ => by
    by_cases h : P x <;> simp [h, ofScores_apply]

theorem ofScores_event_lt (fb : Fallback σ) (f : σ → ℚ≥0) {P Q : σ → Bool}
    (h : eventMass (scoresWith fb f) P < eventMass (scoresWith fb f) Q) :
    (∑' x, if P x then ofScores fb f x else 0)
      < ∑' x, if Q x then ofScores fb f x else 0 := by
  rw [ofScores_event_eq, ofScores_event_eq]
  exact_mod_cast h

end PMF

/-! ### Bundled exact-rational distributions -/

/-- An exact rational distribution on a finite type: a `ℚ≥0` mass function
summing to one. Applies like a function (into ℚ≥0, where `decide +kernel`
computes) and coerces to the mathlib face by `toPMF` (a pointwise cast, by
`rfl`). An agent tower is one `QDist.ofScores` definition per agent, each
consuming the applications of the agents below it. -/
structure QDist (σ : Type*) [Fintype σ] where
  /-- The mass function. -/
  toFun : σ → ℚ≥0
  /-- Total mass one. -/
  sum_eq_one : ∑ x, toFun x = 1

namespace QDist

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

instance : FunLike (QDist σ) σ ℚ≥0 where
  coe := toFun
  coe_injective := fun d e h => by cases d; cases e; congr

/-- Normalize a score vector into a distribution, falling back to `fb` on a
zero-mass vector (`PMF.scoresWith` bundled with its total-mass proof). -/
def ofScores (fb : PMF.Fallback σ) (f : σ → ℚ≥0) : QDist σ :=
  ⟨PMF.scoresWith fb f, PMF.scoresWith_sum_eq_one fb f⟩

theorem ofScores_apply (fb : PMF.Fallback σ) (f : σ → ℚ≥0) (x : σ) :
    ofScores fb f x = PMF.scoresWith fb f x := rfl

/-- The mathlib face: the same masses, cast into `ℝ≥0∞`. -/
noncomputable def toPMF (d : QDist σ) : PMF σ :=
  ⟨fun x => ((d x : ℝ≥0) : ℝ≥0∞), by
    have key : ((∑ x, d.toFun x : ℚ≥0) : ℝ≥0) = 1 := by rw [d.sum_eq_one]; norm_num
    rw [show (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) from rfl, ← key, NNRat.cast_sum]
    exact_mod_cast hasSum_fintype fun x => ((d x : ℝ≥0) : ℝ≥0∞)⟩

theorem toPMF_apply (d : QDist σ) (x : σ) :
    d.toPMF x = ((d x : ℝ≥0) : ℝ≥0∞) := rfl

/-- `PMF.ofScores` factors through the bundled face. -/
theorem _root_.PMF.ofScores_eq_toPMF (fb : PMF.Fallback σ) (f : σ → ℚ≥0) :
    PMF.ofScores fb f = (ofScores fb f).toPMF := rfl

/-! Comparisons: a PMF-level prediction from a `ℚ≥0` mass comparison, the
latter closed by `decide +kernel`. -/

theorem toPMF_lt {d : QDist σ} {e : QDist τ} {a : σ} {b : τ} (h : d a < e b) :
    d.toPMF a < e.toPMF b := by
  rw [toPMF_apply, toPMF_apply]; exact_mod_cast h

theorem toPMF_le {d : QDist σ} {e : QDist τ} {a : σ} {b : τ} (h : d a ≤ e b) :
    d.toPMF a ≤ e.toPMF b := by
  rw [toPMF_apply, toPMF_apply]; exact_mod_cast h

theorem toPMF_eq {d : QDist σ} {e : QDist τ} {a : σ} {b : τ} (h : d a = e b) :
    d.toPMF a = e.toPMF b := by
  rw [toPMF_apply, toPMF_apply, h]

theorem toPMF_lt_ratCast {d : QDist σ} {a : σ} {t : ℚ≥0} (h : d a < t) :
    d.toPMF a < ((t : ℝ≥0) : ℝ≥0∞) := by
  rw [toPMF_apply]; exact_mod_cast h

theorem ratCast_lt_toPMF {d : QDist σ} {a : σ} {t : ℚ≥0} (h : t < d a) :
    ((t : ℝ≥0) : ℝ≥0∞) < d.toPMF a := by
  rw [toPMF_apply]; exact_mod_cast h

end QDist
