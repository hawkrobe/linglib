import Linglib.Semantics.Numerals.Basic
import Linglib.Pragmatics.Implicature.EpistemicBlocking
import Linglib.Semantics.Entailment.AsymStronger
import Mathlib.Data.Rat.Defs
import Linglib.Pragmatics.RSA.Operators
import Mathlib.Probability.Distributions.Uniform

/-!
# [kennedy-2015]: De-Fregean numerals — neo-Gricean derivation
[kennedy-2015] [sauerland-2004] [nouwen-2010]
[geurts-nouwen-2007] [frank-goodman-2012] [franke-2011]

[kennedy-2015] replaces the Horn scale `⟨1, 2, 3, …⟩` with a single
**lexically-grouped alternative set** containing the bare numeral together
with all of its surface modifications:

```
  ALT(n) = {bare n, more than n, fewer than n, at least n, at most n}
```

The point is **anti-Horn-scale**: there is no fixed scale direction. The
asymmetric-entailment filter of [sauerland-2004]'s primary-implicature
operator does the work that a pre-categorized "lower" or "upper" scale
would otherwise do. Asserting "at least n" makes only the lower-direction
alternatives (bare n, more than n) asymmetrically stronger; the
upper-direction alternatives (fewer than n, at most n) are not — they're
disjoint or overlapping but not subsets — so they don't trigger primary
implicatures. The Class A / Class B distinction (labels from
[nouwen-2010], which [kennedy-2015] *contests* by replacing
Nouwen's lexical bifurcation with one denotation + asymmetric entailment)
falls out as a structural property of the modifier's relation:

- **Class B (`≥`, `≤`)** — the bare numeral is asymmetrically stronger
  than the asserted form (and so is the strict modifier on the same
  side); two primary implicatures, hence ignorance.
- **Class A (`>`, `<`)** — *no* alternative in the full set is
  asymmetrically stronger than the asserted form; no primary implicature.

We formalize both routes:

- §2 derives the predictions **symbolically** via `asymStrongerOn`
  (the polymorphic primitive from
  `Semantics/Entailment/AsymStronger.lean`).
- §3 derives the same direction probabilistically through RSA L1.

§3 is our own integration contribution, not Kennedy's — Kennedy's paper
discusses [franke-2011]'s IBR as the probabilistic counterpart, not
[frank-goodman-2012]-style RSA. The two routes are theoretically
distinct: §2 follows Kennedy directly; §3 shows the same qualitative
predictions emerge from a soft-max listener over the same alternative set
and bare-numeral semantics.

The formalization consumes `Numeral.Entry.denoteUnder` from
`Semantics/Numerals/Basic.lean` directly — there is no separate
"Kennedy meaning" function (Kennedy's alternative set is *which* numeral
words to consider, not *what they mean*).

Domain: cardinality 0–5 (`Fin 6`, wide enough that Class A "more than 3"
needs `w = 4` to be non-trivial).
-/

namespace Kennedy2015

open Semantics.Numerals
open Semantics.Entailment (asymStrongerOn)

-- ============================================================================
-- §1: Cardinality worlds and Kennedy's single alternative set
-- ============================================================================

/-- Cardinality worlds 0–5. We use `Fin 6` directly: `decide` runs over
    the type-class-derived `Fintype`, and the six-element domain is wide
    enough that Class A "more than 3" needs `w = 4` to be non-trivial. -/
abbrev KCard : Type := Fin 6

/-- Kennedy's alternative set members for `n = 3`. One enum unifying
    bare and all four modifications — Class A vs Class B is read off
    asymmetric-entailment, not from membership in a pre-split sublist.
    The RSA analysis is §3 below. -/
inductive KUtt where
  | bare3 | moreThan3 | fewerThan3 | atLeast3 | atMost3
  deriving DecidableEq, Repr, Fintype

/-- The numeral word (`Numeral.Entry`) a Kennedy alternative is — all at
    argument 3, with their surface forms. -/
def KUtt.entry : KUtt → Numeral.Entry
  | .bare3      => ⟨"three", .eq, 3⟩
  | .moreThan3  => ⟨"more than three", .gt, 3⟩
  | .fewerThan3 => ⟨"fewer than three", .lt, 3⟩
  | .atLeast3   => ⟨"at least three", .ge, 3⟩
  | .atMost3    => ⟨"at most three", .le, 3⟩

/-- Prop-valued meaning of any Kennedy alternative under bilateral (exact) bare
    semantics — `Numeral.Entry.denoteUnder` with `bare := bareMeaning`. -/
def kMean (u : KUtt) (w : KCard) : Prop :=
  u.entry.denoteUnder bareMeaning w.val

noncomputable instance (u : KUtt) : DecidablePred (kMean u) :=
  fun w => inferInstanceAs (Decidable (u.entry.denoteUnder bareMeaning w.val))

-- ============================================================================
-- §2: Symbolic neo-Gricean derivation ([sauerland-2004] on Kennedy's alts)
-- ============================================================================

/-! Sauerland's primary-implicature schema applied to Kennedy's single
alternative set distinguishes Class A from Class B with no probability:

For asserted φ and alternative set ALT, the primary implicatures are
`{¬Kψ | ψ ∈ ALT, ψ asymmetrically entails φ over the speaker's worlds}`.

Over the six-world domain, the meanings at `n = 3` are:

| Expr             | True at        |
|------------------|----------------|
| `bare 3`         | `{3}`          |
| `more than 3`    | `{4, 5}`       |
| `fewer than 3`   | `{0, 1, 2}`    |
| `at least 3`     | `{3, 4, 5}`    |
| `at most 3`      | `{0, 1, 2, 3}` |

Asserting "at least 3": `bare 3 ⊊ at least 3` and `more than 3 ⊊
at least 3` — both asymmetrically stronger. The upper-direction
alternatives `fewer than 3` and `at most 3` are not subsets (the former
is disjoint, the latter overlaps but extends below). So 2 primary
implicatures fire.

Asserting "more than 3": `bare 3` is *disjoint* (rules out subset
relation in either direction); `at least 3` is a *weaker* alternative
(superset, not subset); `at most 3` and `fewer than 3` are also not
subsets. So 0 primary implicatures fire — exactly Kennedy's Class A
prediction.

The alternative set is `Finset.univ : Finset KUtt` (all 5 KUtt
constructors); the world domain is `Finset.univ : Finset KCard` (Fin 6
via Fintype). -/

/-- **Class B (lower-bound) triggers two primary implicatures**.
    Asserting "at least 3" makes both "bare 3" and "more than 3"
    asymmetrically stronger over the six-world domain; the
    upper-direction alternatives are not. -/
theorem classB_atLeast3_two_primary :
    (Finset.univ.filter
      (fun u : KUtt => asymStrongerOn Finset.univ (kMean u) (kMean .atLeast3))).card
      = 2 := by
  decide

/-- **Class A (lower-bound) triggers no primary implicatures**.
    Asserting "more than 3" makes *no* alternative in Kennedy's full
    set — neither bare-direction nor cross-direction — asymmetrically
    stronger. -/
theorem classA_moreThan3_no_primary :
    (Finset.univ.filter
      (fun u : KUtt => asymStrongerOn Finset.univ (kMean u) (kMean .moreThan3))).card
      = 0 := by
  decide

/-- Mirror image: **Class B (upper-bound) triggers two primary implicatures**. -/
theorem classB_atMost3_two_primary :
    (Finset.univ.filter
      (fun u : KUtt => asymStrongerOn Finset.univ (kMean u) (kMean .atMost3))).card
      = 2 := by
  decide

/-- Mirror image: **Class A (upper-bound) triggers no primary implicatures**. -/
theorem classA_fewerThan3_no_primary :
    (Finset.univ.filter
      (fun u : KUtt => asymStrongerOn Finset.univ (kMean u) (kMean .fewerThan3))).card
      = 0 := by
  decide

end Kennedy2015

/-! ## §3. RSA analysis on the PMF shell (merged from the former Kennedy2015PMF) -/

namespace Kennedy2015.PMF

open scoped ENNReal

instance : Nonempty KCard := ⟨0⟩
instance : Nonempty KUtt := ⟨.bare3⟩

/-- Boolean meaning, derived from `kMean` via `decide`. -/
noncomputable def kMeanBool (u : KUtt) (w : KCard) : Bool := decide (kMean u w)

/-- The Bool form agrees with the Prop form. -/
theorem kMeanBool_iff (u : KUtt) (w : KCard) : kMeanBool u w = true ↔ kMean u w :=
  decide_eq_true_iff

/-! ## §1. L0 — uniform on extension via `RSA.L0OfBoolMeaning` -/

noncomputable abbrev extension (u : KUtt) : Finset KCard :=
  RSA.extensionOf kMeanBool u

theorem extension_nonempty (u : KUtt) : (extension u).Nonempty := by
  cases u
  · exact ⟨3, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨4, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨2, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨3, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨3, RSA.mem_extensionOf.mpr (by decide)⟩

noncomputable def L0 (u : KUtt) : PMF KCard :=
  RSA.L0OfBoolMeaning kMeanBool u (extension_nonempty u)

@[simp] theorem mem_support_L0_iff (u : KUtt) (w : KCard) :
    w ∈ (L0 u).support ↔ kMeanBool u w = true :=
  RSA.mem_support_L0OfBoolMeaning_iff _ _

theorem L0_apply_of_true {u : KUtt} {w : KCard} (h : kMeanBool u w = true) :
    L0 u w = ((extension u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_apply_of_false {u : KUtt} {w : KCard} (h : kMeanBool u w ≠ true) :
    L0 u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

private theorem L0_apply_ne_zero {u : KUtt} {w : KCard} (h : kMeanBool u w = true) :
    L0 u w ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_L0_iff]; exact h

/-! ## §2. S1 — speaker as `PMF.normalize` of L0 with conditional fallback

At every world in 0..5, at least one utterance applies (e.g. .atMost3 applies
at 0..3, .atLeast3 applies at 3..5). So S1 is well-defined everywhere — no
fallback needed in this domain (all worlds have a witness).

Still using the conditional pattern for compatibility with the Shape A
template. -/

theorem L0_tsum_utterance_ne_top (w : KCard) : ∑' u, (L0 u w : ℝ≥0∞) ≠ ∞ :=
  PMF.tsum_apply_ne_top (fun u => L0 u) w

private theorem tsum_L0_ne_zero_at {u : KUtt} {w : KCard} (h : kMeanBool u w = true) :
    (∑' u', (L0 u' w : ℝ≥0∞)) ≠ 0 :=
  PMF.tsum_apply_ne_zero L0 (a := u) (L0_apply_ne_zero h)

noncomputable def S1 (w : KCard) : PMF KUtt :=
  if h : (∑' u, (L0 u w : ℝ≥0∞)) ≠ 0 then
    PMF.normalize (fun u => L0 u w) h (L0_tsum_utterance_ne_top w)
  else
    PMF.pure .bare3  -- vacuous fallback; not reached in 0..5 domain

theorem S1_eq_normalize {w : KCard}
    (h : (∑' u, (L0 u w : ℝ≥0∞)) ≠ 0) :
    S1 w = PMF.normalize (fun u => L0 u w) h (L0_tsum_utterance_ne_top w) :=
  dif_pos h

/-! ## §3. L1 — Bayesian inversion against the uniform world prior -/

noncomputable def worldPrior : PMF KCard := PMF.uniformOfFintype KCard

theorem worldPrior_ne_zero (w : KCard) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

private theorem S1_ne_zero_at {u : KUtt} {w : KCard} (h : kMeanBool u w = true) :
    S1 w u ≠ 0 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at h), ← PMF.mem_support_iff,
      PMF.mem_support_normalize_iff]
  exact L0_apply_ne_zero h

theorem L1_marginal_ne_zero (u : KUtt) :
    PMF.marginal S1 worldPrior u ≠ 0 := by
  -- Pick a world where the utterance applies.
  cases u
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 3) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 4) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 2) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 3) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 3) (S1_ne_zero_at (by decide))

noncomputable def L1 (u : KUtt) : PMF KCard :=
  PMF.posterior S1 worldPrior u (L1_marginal_ne_zero u)

/-! ## §4. Findings — vacuous-zero discharges -/

/-- "moreThan3" doesn't apply at .3 → S1 .3 .moreThan3 = 0 (vacuous-zero). -/
theorem S1_3_lt_S1_4_for_moreThan3 :
    S1 (3 : KCard) .moreThan3 < S1 (4 : KCard) .moreThan3 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .bare3) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .moreThan3) (by decide))]
  exact PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ _
    (L0_apply_of_false (by decide : kMeanBool .moreThan3 (3 : KCard) ≠ true))
    (L0_apply_ne_zero (by decide : kMeanBool .moreThan3 (4 : KCard) = true))

/-- L1("moreThan3") prefers .4 over .3 — Class A excludes the boundary semantically. -/
theorem classA_no_competition_at_boundary :
    L1 .moreThan3 (4 : KCard) > L1 .moreThan3 (3 : KCard) := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_3_lt_S1_4_for_moreThan3

/-- "bare3" doesn't apply at .4 → S1 .4 .bare3 = 0 (vacuous-zero). -/
theorem S1_4_lt_S1_3_for_bare3 :
    S1 (4 : KCard) .bare3 < S1 (3 : KCard) .bare3 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .moreThan3) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .bare3) (by decide))]
  exact PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ _
    (L0_apply_of_false (by decide : kMeanBool .bare3 (4 : KCard) ≠ true))
    (L0_apply_ne_zero (by decide : kMeanBool .bare3 (3 : KCard) = true))

/-- L1("bare 3") peaked at .3 — bare numeral exact reading. -/
theorem bare_peaked_with_kennedy_alternatives :
    L1 .bare3 (3 : KCard) > L1 .bare3 (4 : KCard) := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_4_lt_S1_3_for_bare3

/-- "fewerThan3" doesn't apply at .3 → S1 .3 .fewerThan3 = 0 (vacuous-zero, mirror of moreThan3). -/
theorem S1_3_lt_S1_2_for_fewerThan3 :
    S1 (3 : KCard) .fewerThan3 < S1 (2 : KCard) .fewerThan3 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .bare3) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .fewerThan3) (by decide))]
  exact PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ _
    (L0_apply_of_false (by decide : kMeanBool .fewerThan3 (3 : KCard) ≠ true))
    (L0_apply_ne_zero (by decide : kMeanBool .fewerThan3 (2 : KCard) = true))

/-- L1("fewerThan3") prefers .2 over .3 — upper Class A excludes boundary. -/
theorem upper_classA_no_competition :
    L1 .fewerThan3 (2 : KCard) > L1 .fewerThan3 (3 : KCard) := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_3_lt_S1_2_for_fewerThan3

/-! ## §5. Findings — partition-dominance leaves

The S1 partition `Z(w) = ∑_u L0(u)(w)` differs across worlds; with equal
numerators, `L1` favours the world with the smaller partition. We evaluate the
partitions FG12-style and cancel the shared alternatives — no reflection. -/

private theorem univ_KUtt :
    (Finset.univ : Finset KUtt) = {.bare3, .moreThan3, .fewerThan3, .atLeast3, .atMost3} := by
  decide

private theorem Z3 : (∑' u : KUtt, L0 u (3 : KCard)) = 1 + 3⁻¹ + 4⁻¹ := by
  rw [tsum_fintype, univ_KUtt, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      L0_apply_of_true (show kMeanBool .bare3 (3 : KCard) = true by decide),
      L0_apply_of_false (show kMeanBool .moreThan3 (3 : KCard) ≠ true by decide),
      L0_apply_of_false (show kMeanBool .fewerThan3 (3 : KCard) ≠ true by decide),
      L0_apply_of_true (show kMeanBool .atLeast3 (3 : KCard) = true by decide),
      L0_apply_of_true (show kMeanBool .atMost3 (3 : KCard) = true by decide),
      show (extension .bare3).card = 1 from by decide,
      show (extension .atLeast3).card = 3 from by decide,
      show (extension .atMost3).card = 4 from by decide]
  simp only [Nat.cast_one, inv_one, Nat.cast_ofNat, zero_add]
  ring

private theorem Z4 : (∑' u : KUtt, L0 u (4 : KCard)) = 2⁻¹ + 3⁻¹ := by
  rw [tsum_fintype, univ_KUtt, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      L0_apply_of_false (show kMeanBool .bare3 (4 : KCard) ≠ true by decide),
      L0_apply_of_true (show kMeanBool .moreThan3 (4 : KCard) = true by decide),
      L0_apply_of_false (show kMeanBool .fewerThan3 (4 : KCard) ≠ true by decide),
      L0_apply_of_true (show kMeanBool .atLeast3 (4 : KCard) = true by decide),
      L0_apply_of_false (show kMeanBool .atMost3 (4 : KCard) ≠ true by decide),
      show (extension .moreThan3).card = 2 from by decide,
      show (extension .atLeast3).card = 3 from by decide]
  simp only [Nat.cast_ofNat, zero_add, add_zero]

private theorem Z2 : (∑' u : KUtt, L0 u (2 : KCard)) = 3⁻¹ + 4⁻¹ := by
  rw [tsum_fintype, univ_KUtt, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      L0_apply_of_false (show kMeanBool .bare3 (2 : KCard) ≠ true by decide),
      L0_apply_of_false (show kMeanBool .moreThan3 (2 : KCard) ≠ true by decide),
      L0_apply_of_true (show kMeanBool .fewerThan3 (2 : KCard) = true by decide),
      L0_apply_of_false (show kMeanBool .atLeast3 (2 : KCard) ≠ true by decide),
      L0_apply_of_true (show kMeanBool .atMost3 (2 : KCard) = true by decide),
      show (extension .fewerThan3).card = 3 from by decide,
      show (extension .atMost3).card = 4 from by decide]
  simp only [Nat.cast_ofNat, zero_add, add_zero]

private theorem Z4_lt_Z3 :
    (∑' u : KUtt, L0 u (4 : KCard)) < ∑' u : KUtt, L0 u (3 : KCard) := by
  rw [Z3, Z4, show (1 : ℝ≥0∞) + 3⁻¹ + 4⁻¹ = 3⁻¹ + (1 + 4⁻¹) from by ring,
      show (2 : ℝ≥0∞)⁻¹ + 3⁻¹ = 3⁻¹ + 2⁻¹ from by ring,
      ENNReal.add_lt_add_iff_left (ENNReal.inv_ne_top.mpr (by norm_num))]
  exact lt_of_lt_of_le (ENNReal.inv_lt_one.mpr (by norm_num)) le_self_add

private theorem Z2_lt_Z3 :
    (∑' u : KUtt, L0 u (2 : KCard)) < ∑' u : KUtt, L0 u (3 : KCard) := by
  rw [Z3, Z2, show (1 : ℝ≥0∞) + 3⁻¹ + 4⁻¹ = (3⁻¹ + 4⁻¹) + 1 from by ring]
  exact ENNReal.lt_add_right (by rw [← Z2]; exact PMF.tsum_apply_ne_top L0 _) one_ne_zero

/-- Class B: L1 of "atLeast3" prefers .4 over .3. Equal numerators (1/3); world 3
has the larger partition (more competing alternatives), so L1 shifts toward .4. -/
theorem classB_strengthened_above_bare :
    L1 .atLeast3 (4 : KCard) > L1 .atLeast3 (3 : KCard) := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      S1_eq_normalize (tsum_L0_ne_zero_at (show kMeanBool .atLeast3 (3 : KCard) = true by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (show kMeanBool .atLeast3 (4 : KCard) = true by decide))]
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt
  · rw [L0_apply_of_true (show kMeanBool .atLeast3 (3 : KCard) = true by decide),
        L0_apply_of_true (show kMeanBool .atLeast3 (4 : KCard) = true by decide)]
  · rw [L0_apply_of_true (show kMeanBool .atLeast3 (4 : KCard) = true by decide)]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · exact PMF.apply_ne_top _ _
  · exact Z4_lt_Z3

/-- Upper Class B: L1 of "atMost3" prefers .2 over .3 (mirror of
`classB_strengthened_above_bare`). -/
theorem upper_classB_strengthened_below_bare :
    L1 .atMost3 (2 : KCard) > L1 .atMost3 (3 : KCard) := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform,
      S1_eq_normalize (tsum_L0_ne_zero_at (show kMeanBool .atMost3 (3 : KCard) = true by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (show kMeanBool .atMost3 (2 : KCard) = true by decide))]
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt
  · rw [L0_apply_of_true (show kMeanBool .atMost3 (3 : KCard) = true by decide),
        L0_apply_of_true (show kMeanBool .atMost3 (2 : KCard) = true by decide)]
  · rw [L0_apply_of_true (show kMeanBool .atMost3 (2 : KCard) = true by decide)]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · exact PMF.apply_ne_top _ _
  · exact Z2_lt_Z3

/-! ## §6. Findings — cross-observation (different utterance, same world) -/

/-- Class B competition at the boundary: L1("bare 3" | .3) > L1("at least 3" | .3).

**Structural discharge** (post-0.230.409 lemma `posterior_lt_of_score_cross_lt`):
1. `gt_iff_lt` flips to `<` shape
2. `unfold L1`, `posterior_lt_of_score_cross_lt`
3. Reduces to cross-multiplied score comparison:
   `S1 .3 .atLeast3 * marginal .bare3 < S1 .3 .bare3 * marginal .atLeast3`

**Remaining leaf**: the cross-multiplied numeric inequality requires
computing `marginal .bare3` and `marginal .atLeast3` (each a tsum over
Fin 6). Same partition-computation friction as `classB_strengthened_above_bare`
— would close once a `pmf_partition_compute` helper exists. -/
theorem classB_competition_at_boundary :
    L1 .bare3 (3 : KCard) > L1 .atLeast3 (3 : KCard) := by
  unfold L1
  rw [gt_iff_lt]
  apply PMF.posterior_lt_of_score_cross_lt
  · -- μ a ≠ 0 (worldPrior at .3)
    exact worldPrior_ne_zero 3
  · -- μ a ≠ ⊤
    exact PMF.apply_ne_top _ _
  · -- Cross-multiplied score inequality (partition-function computation)
    sorry  -- numeric leaf: needs marginal value computation

/-- Upper Class B competition. Same shape as `classB_competition_at_boundary`. -/
theorem upper_classB_competition :
    L1 .bare3 (3 : KCard) > L1 .atMost3 (3 : KCard) := by
  unfold L1
  rw [gt_iff_lt]
  apply PMF.posterior_lt_of_score_cross_lt
  · exact worldPrior_ne_zero 3
  · exact PMF.apply_ne_top _ _
  · sorry  -- numeric leaf

end Kennedy2015.PMF
