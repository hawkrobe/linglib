import Linglib.Pragmatics.RSA.Canonical

/-!
# [champollion-alsop-grosu-2019] — Free choice disjunction as a rational speech act

RSA model of [champollion-alsop-grosu-2019] (SALT 29): free choice ("You may
take an apple or a pear" ⤳ "You may take an apple") emerges from RSA once
**semantic uncertainty** ([bergen-levy-goodman-2016]) is added: agents reason
over two interpretation functions — ℐ₁ (classical modal logic) and ℐ₂
(strengthened via [fox-2007]-style exhaustification) — so a bare disjunct
risks the "Only A" reading; the disjunction avoids that risk and the listener
inverts the avoidance. States and utterances extend [franke-2011]'s IBR
model; the recursion is [frank-goodman-2012]'s, with
`P_L0(w|u,ℐ) ∝ ℐ(u,w)·P(w)`, `P_S1(u|w,ℐ) ∝ [P_L0]^α`, and
`P_L1(w|u) ∝ P(w)·Σ_ℐ P_S1(u|w,ℐ)`.

Instantiated on the canonical pipeline: the speaker is `RSA.Canonical.S1` at
the natural-exponent informativity utility (`RSA.Canonical.powUtility` with
`α = 2`, i.e. `rsaUtility` at zero cost), the listener `RSA.Canonical.L1`
(the joint posterior over `FCState × Interp`). Findings are posterior-mass
comparisons closed by dominance *bounds* on softmax weights — no numeric
reflection. Since the FCI/EI events constrain only the world coordinate and
the interpretation prior is uniform, joint-posterior event masses coincide
with the paper's ℐ-marginalised L1. The paper's tables use `α = 100`; at the
`α = 2` used here the paper notes L1 assigns "only 70%" to the FCI states
given Or (our exact masses give ≈ 70.2%).

## Main statements

* `fci_derived` — given Or, L1 favours the FCI states (Only One,
  Any Number) under a uniform prior; `ei_uniform` — at α = 2 the EI states
  also carry more mass (a low-α observation of ours: at the paper's α = 100
  the EI split is exactly ½/½, and the paper derives EI from priors only).
* `ei_defeated_by_prior` — with the paper's 75%-Any-Number prior the EI
  comparison reverses: EI tracks world knowledge.
* `speaker_or_onlyOne_exh` / `speaker_prefers_a_at_onlyA_exh` — the
  avoidance mechanism at S1.

## Implementation notes

The paper's FCI-robustness claim (75% prior on Only A leaves FCI intact at
`α = 100`) is parameter-dependent: at `α = 2` it *reverses* (the non-FCI
score sum ≈ 0.32 dominates ≈ 0.065 — the low-α speaker does not reliably
avoid Or at Only A, and the 12× prior swamps the avoidance; at `α = 100` the
Only-A terms decay like (15/16)^α). The reversal qualifies the paper's
generally-worded robustness conclusion, which is stated without an α-caveat.
Per the library's policy on findings whose truth depends on an exact
parameter value, it is recorded as prose, not as a theorem. The paper's Table-8 null-utterance robustness check is
recorded as prose for space (its α = 2 values are documented in the final
section), and the §4 negation model is not formalised.
-/

set_option autoImplicit false

namespace ChampollionAlsopGrosu2019

open scoped ENNReal
open RSA.Canonical

/-! ### States, utterances, interpretation functions (Table 2, (5), (6), (7)) -/

/-- Permission states (Table 2): Franke's All True split into Any Number
and Only Both. -/
inductive FCState where
  | onlyA | onlyB
  | onlyOne   -- either fruit, not both (FCI + EI)
  | anyNumber -- any combination (FCI, no EI)
  | onlyBoth  -- only both together (no FCI, no EI)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The four utterances of (5). -/
inductive Utterance where
  | a | b | or_ | and_
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- ℐ₁ literal vs ℐ₂ exhaustified ([fox-2007] innocent exclusion). -/
inductive Interp where
  | literal | exhaustified
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Free choice: each item individually permitted, `◇(A∧¬B) ∧ ◇(B∧¬A)`. -/
def HasFCI : FCState → Prop
  | .onlyOne | .anyNumber => True
  | _ => False

instance : DecidablePred HasFCI
  | .onlyA | .onlyB | .onlyBoth => .isFalse id
  | .onlyOne | .anyNumber => .isTrue trivial

/-- Exclusivity: taking both is not permitted, `¬◇(A∧B)`. -/
def HasEI : FCState → Prop
  | .onlyA | .onlyB | .onlyOne => True
  | _ => False

instance : DecidablePred HasEI
  | .onlyA | .onlyB | .onlyOne => .isTrue trivial
  | .anyNumber | .onlyBoth => .isFalse id

/-- Interpretation function ℐ₁ (the paper's (6)). -/
def I1 : Utterance → FCState → Prop
  | .a, .onlyB => False
  | .a, _ => True
  | .b, .onlyA => False
  | .b, _ => True
  | .or_, _ => True
  | .and_, .anyNumber | .and_, .onlyBoth => True
  | .and_, _ => False

instance : ∀ u, DecidablePred (I1 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- Interpretation function ℐ₂ (the paper's (7)). -/
def I2 : Utterance → FCState → Prop
  | .a, .onlyA => True
  | .a, _ => False
  | .b, .onlyB => True
  | .b, _ => False
  | .or_, .onlyBoth => False
  | .or_, _ => True
  | .and_, .onlyBoth => True
  | .and_, _ => False

instance : ∀ u, DecidablePred (I2 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- Meaning indexed by interpretation function. -/
def interpMeaning : Interp → Utterance → FCState → Prop
  | .literal => I1
  | .exhaustified => I2

instance : ∀ i u, DecidablePred (interpMeaning i u)
  | .literal, u => inferInstanceAs (DecidablePred (I1 u))
  | .exhaustified, u => inferInstanceAs (DecidablePred (I2 u))

/-- ℐ₂ refines ℐ₁: exhaustification only strengthens. -/
theorem I2_refines_I1 : ∀ u w, I2 u w → I1 u w := by decide

/-- ℐ₁(Or) is literally true everywhere — maximally uninformative. -/
theorem I1_or_everywhere : ∀ w, I1 .or_ w := by decide

/-- ℐ₂(Or) excludes exactly Only Both. -/
theorem I2_or_excludes_onlyBoth : ∀ w, I2 .or_ w ↔ w ≠ .onlyBoth := by decide

/-- ℐ₂(A) singles out exactly Only A — the risk the speaker avoids. -/
theorem I2_a_singleton : ∀ w, I2 .a w ↔ w = .onlyA := by decide

/-! ### ENNReal budget helpers -/

private theorem two_mul_inv_add {c : ℝ≥0∞} (hT : c ≠ ∞) :
    (2 * c)⁻¹ + (2 * c)⁻¹ = c⁻¹ := by
  rw [← two_mul, ENNReal.mul_inv (Or.inr hT) (Or.inl ENNReal.ofNat_ne_top),
      ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

private theorem quarter_add_quarter : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ = 2⁻¹ := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 from by norm_num, two_mul_inv_add ENNReal.ofNat_ne_top]

/-! ### The FCI / EI events -/

/-- The free-choice event of the joint listener (any interpretation). -/
def fciPairs : Finset (FCState × Interp) := Finset.univ.filter (fun p => HasFCI p.1)

/-- The complement of `fciPairs`. -/
def nonFciPairs : Finset (FCState × Interp) := Finset.univ.filter (fun p => ¬ HasFCI p.1)

/-- The exclusivity event of the joint listener. -/
def eiPairs : Finset (FCState × Interp) := Finset.univ.filter (fun p => HasEI p.1)

/-- The complement of `eiPairs`. -/
def nonEiPairs : Finset (FCState × Interp) := Finset.univ.filter (fun p => ¬ HasEI p.1)

/-! ### The basic model, uniform prior

At a uniform world prior the paper's `P_L0(w|u,ℐ) ∝ ℐ(u,w)·P(w)` is uniform
on the extension, i.e. `RSA.Canonical.L0OfPred`. Exact S1(Or) values at
α = 2, for reference: ℐ₁ row 16/41, 16/41, 8/33, 8/83, 8/83; ℐ₂ row 1/17,
1/17, 1, 1, 0 (states in Table-2 order). -/

theorem ext_nonempty (i : Interp) (u : Utterance) :
    (RSA.extensionOf (interpMeaning i) u).Nonempty := by
  cases i <;> cases u <;>
    first
      | exact ⟨.onlyA, by decide⟩
      | exact ⟨.onlyB, by decide⟩
      | exact ⟨.anyNumber, by decide⟩
      | exact ⟨.onlyBoth, by decide⟩

/-- Literal listener of the basic model. -/
noncomputable abbrev l0 : Interp → Utterance → PMF FCState :=
  L0OfPred interpMeaning ext_nonempty

instance : ViableSpeaker (powUtility 2 l0) :=
  viableSpeaker_powUtility_of_witness 2 l0 fun s => by
    obtain ⟨w, i⟩ := s
    cases i <;> cases w <;>
      first
        | exact ⟨.or_, L0OfPred_ne_zero _ _ (by decide)⟩
        | exact ⟨.and_, L0OfPred_ne_zero _ _ (by decide)⟩

/-- The pragmatic speaker of the basic model (the paper's `P_S1`, α = 2). -/
noncomputable abbrev speaker : FCState × Interp → PMF Utterance :=
  S1 (powUtility 2 l0)

/-- Uniform joint prior over `state × interpretation`. -/
noncomputable abbrev prior : PMF (FCState × Interp) := PMF.uniformOfFintype _

/-- Under ℐ₂ at Only One, Or is the *only* applicable utterance — the heart
of the avoidance mechanism (paper §3.3). -/
theorem speaker_or_onlyOne_exh : speaker (.onlyOne, .exhaustified) .or_ = 1 :=
  S1_powUtility_eq_one 2 l0 two_ne_zero .or_ fun u' hu' => by
    cases u' <;> first | exact absurd rfl hu' | exact L0OfPred_eq_zero _ _ (by decide)

/-- Under ℐ₂ at Any Number, Or is the only applicable utterance. -/
theorem speaker_or_anyNumber_exh : speaker (.anyNumber, .exhaustified) .or_ = 1 :=
  S1_powUtility_eq_one 2 l0 two_ne_zero .or_ fun u' hu' => by
    cases u' <;> first | exact absurd rfl hu' | exact L0OfPred_eq_zero _ _ (by decide)

/-- Under ℐ₂ at Only Both, Or is inapplicable. -/
theorem speaker_or_onlyBoth_exh : speaker (.onlyBoth, .exhaustified) .or_ = 0 :=
  S1_powUtility_eq_zero 2 l0 two_ne_zero (L0OfPred_eq_zero _ _ (by decide))

/-- The avoidance mechanism at S1: under ℐ₂ at Only A the bare disjunct
strictly beats the disjunction (16/17 vs 1/17). -/
theorem speaker_prefers_a_at_onlyA_exh :
    speaker (.onlyA, .exhaustified) .or_ < speaker (.onlyA, .exhaustified) .a := by
  show S1 (powUtility 2 l0) (.onlyA, .exhaustified) .or_
    < S1 (powUtility 2 l0) (.onlyA, .exhaustified) .a
  rw [S1_powUtility_eq_normalize, PMF.normalize_lt_iff_lt,
      powWeight_L0OfPred_of_mem _ _ 4 (by decide) (by decide),
      powWeight_L0OfPred_of_mem _ _ 1 (by decide) (by decide)]
  exact ENNReal.pow_lt_pow_left two_ne_zero
    (ENNReal.inv_lt_inv.mpr (Nat.cast_lt.mpr (by norm_num)))

theorem marginal_or_ne_zero : PMF.marginal speaker prior .or_ ≠ 0 :=
  PMF.marginal_ne_zero _ _ _
    ((prior.mem_support_iff _).mp
      (PMF.mem_support_uniformOfFintype (.onlyOne, .exhaustified)))
    (by rw [speaker_or_onlyOne_exh]; exact one_ne_zero)

/-- The pragmatic listener of the basic model (the paper's `P_L1`). -/
noncomputable abbrev listener (u : Utterance)
    (h : PMF.marginal speaker prior u ≠ 0) : PMF (FCState × Interp) :=
  L1 speaker prior u h

private theorem speaker_or_onlyA_lit_lt_half : speaker (.onlyA, .literal) .or_ < 2⁻¹ :=
  (S1_L0OfPred_lt_inv_succ_of_dominator _ _ (u' := .a) (n := 1) (k := 5) (k' := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) two_ne_zero
    (by norm_num)).trans_le (by norm_num)

private theorem speaker_or_onlyB_lit_lt_half : speaker (.onlyB, .literal) .or_ < 2⁻¹ :=
  (S1_L0OfPred_lt_inv_succ_of_dominator _ _ (u' := .b) (n := 1) (k := 5) (k' := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) two_ne_zero
    (by norm_num)).trans_le (by norm_num)

private theorem speaker_or_anyNumber_lit_lt_quarter : speaker (.anyNumber, .literal) .or_ < 4⁻¹ :=
  (S1_L0OfPred_lt_inv_succ_of_dominator _ _ (u' := .and_) (n := 3) (k := 5) (k' := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) two_ne_zero
    (by norm_num)).trans_le (by norm_num)

private theorem speaker_or_onlyBoth_lit_lt_quarter : speaker (.onlyBoth, .literal) .or_ < 4⁻¹ :=
  (S1_L0OfPred_lt_inv_succ_of_dominator _ _ (u' := .and_) (n := 3) (k := 5) (k' := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) two_ne_zero
    (by norm_num)).trans_le (by norm_num)

private theorem speaker_or_onlyA_exh_lt_quarter : speaker (.onlyA, .exhaustified) .or_ < 4⁻¹ :=
  (S1_L0OfPred_lt_inv_succ_of_dominator _ _ (u' := .a) (n := 3) (k := 4) (k' := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) two_ne_zero
    (by norm_num)).trans_le (by norm_num)

private theorem speaker_or_onlyB_exh_lt_quarter : speaker (.onlyB, .exhaustified) .or_ < 4⁻¹ :=
  (S1_L0OfPred_lt_inv_succ_of_dominator _ _ (u' := .b) (n := 3) (k := 4) (k' := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) two_ne_zero
    (by norm_num)).trans_le (by norm_num)

private theorem speaker_or_onlyA_lit_gt_quarter : 4⁻¹ < speaker (.onlyA, .literal) .or_ :=
  (inv_succ_lt_S1_powUtility 2 l0 (n := 3) <| by
    rw [show (Finset.univ.erase Utterance.or_) = {.a, .b, .and_} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton,
        powWeight_L0OfPred_of_mem _ _ 4 (by decide) (by decide),
        powWeight_L0OfPred_of_not_mem _ _ two_ne_zero (by decide),
        powWeight_L0OfPred_of_not_mem _ _ two_ne_zero (by decide),
        powWeight_L0OfPred_of_mem _ _ 5 (by decide) (by decide),
        add_zero, add_zero]
    exact ENNReal.inv_pow_lt_natCast_mul_inv_pow (by norm_num) (by norm_num)
      (by norm_num)).trans_le' (by norm_num)

private theorem speaker_or_onlyB_lit_gt_quarter : 4⁻¹ < speaker (.onlyB, .literal) .or_ :=
  (inv_succ_lt_S1_powUtility 2 l0 (n := 3) <| by
    rw [show (Finset.univ.erase Utterance.or_) = {.a, .b, .and_} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton,
        powWeight_L0OfPred_of_not_mem _ _ two_ne_zero (by decide),
        powWeight_L0OfPred_of_mem _ _ 4 (by decide) (by decide),
        powWeight_L0OfPred_of_not_mem _ _ two_ne_zero (by decide),
        powWeight_L0OfPred_of_mem _ _ 5 (by decide) (by decide),
        zero_add, add_zero]
    exact ENNReal.inv_pow_lt_natCast_mul_inv_pow (by norm_num) (by norm_num)
      (by norm_num)).trans_le' (by norm_num)

/-- **Free choice derived** (paper §3.3; uniform prior, α = 2): given Or, L1
puts strictly more posterior mass on the FCI states than on the rest (the
exact split is the ≈ 70% / 30% the paper reports for α = 2). -/
theorem fci_derived :
    (listener .or_ marginal_or_ne_zero).toOuterMeasure ↑nonFciPairs
      < (listener .or_ marginal_or_ne_zero).toOuterMeasure ↑fciPairs := by
  rw [L1_uniform_event_lt_iff]
  have hub : (∑ p ∈ nonFciPairs, speaker p .or_) < 2 := by
    rw [show nonFciPairs = {(.onlyA, .literal), (.onlyA, .exhaustified),
          (.onlyB, .literal), (.onlyB, .exhaustified),
          (.onlyBoth, .literal), (.onlyBoth, .exhaustified)} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton,
        speaker_or_onlyBoth_exh, add_zero]
    refine (ENNReal.add_lt_add speaker_or_onlyA_lit_lt_half
      (ENNReal.add_lt_add speaker_or_onlyA_exh_lt_quarter
        (ENNReal.add_lt_add speaker_or_onlyB_lit_lt_half
          (ENNReal.add_lt_add speaker_or_onlyB_exh_lt_quarter
            speaker_or_onlyBoth_lit_lt_quarter)))).trans ?_
    rw [show (2 : ℝ≥0∞)⁻¹ + (4⁻¹ + (2⁻¹ + (4⁻¹ + 4⁻¹)))
          = (2⁻¹ + 2⁻¹) + ((4⁻¹ + 4⁻¹) + 4⁻¹) from by ring,
        ENNReal.inv_two_add_inv_two, quarter_add_quarter]
    calc (1 : ℝ≥0∞) + (2⁻¹ + 4⁻¹) < 1 + (2⁻¹ + 2⁻¹) := by
          refine (ENNReal.add_lt_add_iff_left ENNReal.one_ne_top).mpr ?_
          exact (ENNReal.add_lt_add_iff_left (ENNReal.inv_ne_top.mpr two_ne_zero)).mpr
            (ENNReal.inv_lt_inv.mpr (by norm_num))
      _ = 2 := by rw [ENNReal.inv_two_add_inv_two]; exact one_add_one_eq_two
  have hlb : (2 : ℝ≥0∞) ≤ ∑ p ∈ fciPairs, speaker p .or_ := by
    refine le_trans ?_ (Finset.sum_le_sum_of_subset
      (by decide : ({(.onlyOne, .exhaustified), (.anyNumber, .exhaustified)} :
        Finset (FCState × Interp)) ⊆ fciPairs))
    rw [Finset.sum_insert (by decide), Finset.sum_singleton,
        speaker_or_onlyOne_exh, speaker_or_anyNumber_exh, one_add_one_eq_two]
  exact hub.trans_le hlb

/-- **Exclusivity at a uniform prior, α = 2** — a formalizer's observation,
*not* the paper's claim: at the paper's α = 100 the split given Or is exactly
0.5/0.5 ("fully half of it is on the non-EI state Any Number"); the paper
derives EI from prior beliefs, claiming only that FCI is the *stronger*
inference under uniform priors. At α = 2 the low-α speaker leaks Or-mass to
the literal-ℐ Only A / Only B states (both EI states), so the EI event
carries strictly more mass (≈ 64% / 36%) — strictness is an α = 2 artifact.
Contrast `ei_defeated_by_prior`. -/
theorem ei_uniform :
    (listener .or_ marginal_or_ne_zero).toOuterMeasure ↑nonEiPairs
      < (listener .or_ marginal_or_ne_zero).toOuterMeasure ↑eiPairs := by
  rw [L1_uniform_event_lt_iff]
  have hub : (∑ p ∈ nonEiPairs, speaker p .or_) < 1 + 2⁻¹ := by
    rw [show nonEiPairs = {(.anyNumber, .literal), (.anyNumber, .exhaustified),
          (.onlyBoth, .literal), (.onlyBoth, .exhaustified)} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton,
        speaker_or_anyNumber_exh, speaker_or_onlyBoth_exh, add_zero]
    refine (ENNReal.add_lt_add speaker_or_anyNumber_lit_lt_quarter
      ((ENNReal.add_lt_add_iff_left ENNReal.one_ne_top).mpr
        speaker_or_onlyBoth_lit_lt_quarter)).trans_eq ?_
    rw [show (4 : ℝ≥0∞)⁻¹ + (1 + 4⁻¹) = 1 + (4⁻¹ + 4⁻¹) from by ring,
        quarter_add_quarter]
  have hlb : (1 : ℝ≥0∞) + 2⁻¹ ≤ ∑ p ∈ eiPairs, speaker p .or_ := by
    refine le_trans ?_ (Finset.sum_le_sum_of_subset
      (by decide : ({(.onlyA, .literal), (.onlyB, .literal),
        (.onlyOne, .exhaustified)} : Finset (FCState × Interp)) ⊆ eiPairs))
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton, speaker_or_onlyOne_exh]
    refine le_of_lt (lt_of_eq_of_lt ?_ (ENNReal.add_lt_add speaker_or_onlyA_lit_gt_quarter
      ((ENNReal.add_lt_add_iff_right ENNReal.one_ne_top).mpr
        speaker_or_onlyB_lit_gt_quarter)))
    rw [show (4 : ℝ≥0∞)⁻¹ + (4⁻¹ + 1) = (4⁻¹ + 4⁻¹) + 1 from by ring,
        quarter_add_quarter, add_comm]
  exact hub.trans_le hlb

/-! ### Prior sensitivity: the asymmetric-prior model

The paper shows EI, unlike FCI, tracks world knowledge: with 75% prior on
Any Number, L1 given Or concentrates on Any Number (92% at α = 100, Table 6).
Following `P_L0(w|u,ℐ) ∝ ℐ(u,w)·P(w)`, the prior enters the literal
listener. The complementary FCI-robustness claim (75% on Only A) is
`α = 100`-dependent and reverses at α = 2 (module docstring): prose only. -/

/-- Asymmetric prior weights: 75% on Any Number (12 : 1 : 1 : 1 : 1). -/
def biasedWeight : FCState → ℕ
  | .anyNumber => 12
  | _ => 1

private theorem wB_tsum_ne_zero (i : Interp) (u : Utterance) :
    (∑' w, if interpMeaning i u w then (biasedWeight w : ℝ≥0∞) else 0) ≠ 0 := by
  intro hz
  have key : ∀ w : FCState, interpMeaning i u w → False := fun w hw => by
    have h := ENNReal.tsum_eq_zero.mp hz w
    rw [if_pos hw, Nat.cast_eq_zero] at h
    exact absurd h (by cases w <;> simp [biasedWeight])
  cases i <;> cases u <;>
    first
      | exact key .onlyA (by decide)
      | exact key .onlyB (by decide)
      | exact key .anyNumber (by decide)
      | exact key .onlyBoth (by decide)

private theorem wB_tsum_ne_top (i : Interp) (u : Utterance) :
    (∑' w, if interpMeaning i u w then (biasedWeight w : ℝ≥0∞) else 0) ≠ ∞ := by
  rw [tsum_fintype]
  refine ENNReal.sum_ne_top.mpr fun w _ => ?_
  split
  · exact ENNReal.natCast_ne_top _
  · exact ENNReal.zero_ne_top

/-- Literal listener with the asymmetric prior (the paper's `P_L0`). -/
noncomputable abbrev l0B (i : Interp) (u : Utterance) : PMF FCState :=
  PMF.normalize _ (wB_tsum_ne_zero i u) (wB_tsum_ne_top i u)

private theorem l0B_ne_zero {i : Interp} {u : Utterance} {w : FCState}
    (h : interpMeaning i u w) : l0B i u w ≠ 0 := by
  rw [PMF.normalize_apply, if_pos h]
  exact mul_ne_zero (by rw [Nat.cast_ne_zero]; cases w <;> simp [biasedWeight])
    (ENNReal.inv_ne_zero.mpr (wB_tsum_ne_top i u))

private theorem l0B_eq_zero {i : Interp} {u : Utterance} {w : FCState}
    (h : ¬ interpMeaning i u w) : l0B i u w = 0 := by
  rw [PMF.normalize_apply, if_neg h, zero_mul]

instance : ViableSpeaker (powUtility 2 l0B) :=
  viableSpeaker_powUtility_of_witness 2 l0B fun s => by
    obtain ⟨w, i⟩ := s
    cases i <;> cases w <;>
      first
        | exact ⟨.or_, l0B_ne_zero (by decide)⟩
        | exact ⟨.and_, l0B_ne_zero (by decide)⟩

/-- The pragmatic speaker of the asymmetric-prior model. -/
noncomputable abbrev speakerB : FCState × Interp → PMF Utterance :=
  S1 (powUtility 2 l0B)

/-- Or is still the only applicable utterance at (Any Number, ℐ₂),
independently of the prior weighting. -/
theorem speakerB_or_anyNumber_exh : speakerB (.anyNumber, .exhaustified) .or_ = 1 :=
  S1_powUtility_eq_one 2 l0B two_ne_zero .or_ fun u' hu' => by
    cases u' <;> first | exact absurd rfl hu' | exact l0B_eq_zero (by decide)

/-- The asymmetric joint prior `P(w) · 1/2` (weights 12 : 1 : 1 : 1 : 1,
halved per interpretation; total 32). -/
noncomputable def priorB : PMF (FCState × Interp) :=
  PMF.ofFintype (fun p => (biasedWeight p.1 : ℝ≥0∞) * 32⁻¹) (by
    rw [← Finset.sum_mul, ← Nat.cast_sum,
        show (∑ p : FCState × Interp, biasedWeight p.1) = 32 from by decide]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

theorem marginalB_or_ne_zero : PMF.marginal speakerB priorB .or_ ≠ 0 :=
  PMF.marginal_ne_zero (a := (FCState.anyNumber, Interp.exhaustified)) speakerB priorB .or_
    (mul_ne_zero (by norm_num [biasedWeight]) (ENNReal.inv_ne_zero.mpr (by norm_num)))
    (by rw [speakerB_or_anyNumber_exh]; exact one_ne_zero)

/-- The pragmatic listener of the asymmetric-prior model. -/
noncomputable abbrev listenerB (u : Utterance)
    (h : PMF.marginal speakerB priorB u ≠ 0) : PMF (FCState × Interp) :=
  L1 speakerB priorB u h

/-- **Exclusivity is defeated by world knowledge** (paper §3.3, Table 6
direction, α = 2): with 75% prior on Any Number, L1 given Or favours the
non-EI states. The prior's 12/32 share at (Any Number, ℐ₂), where Or is
produced with certainty, outweighs the EI event's entire 6/32 prior mass. -/
theorem ei_defeated_by_prior :
    (listenerB .or_ marginalB_or_ne_zero).toOuterMeasure ↑eiPairs
      < (listenerB .or_ marginalB_or_ne_zero).toOuterMeasure ↑nonEiPairs := by
  rw [L1_event_lt_iff]
  have hL : (∑ p ∈ eiPairs, priorB p * speakerB p .or_) ≤ 6 * 32⁻¹ := by
    calc ∑ p ∈ eiPairs, priorB p * speakerB p .or_
        ≤ ∑ p ∈ eiPairs, priorB p * 1 :=
          Finset.sum_le_sum fun p _ => mul_le_mul_right (PMF.coe_le_one _ _) _
      _ = 6 * 32⁻¹ := by
          simp only [mul_one, show ∀ p : FCState × Interp,
            priorB p = (biasedWeight p.1 : ℝ≥0∞) * 32⁻¹ from fun _ => rfl]
          rw [← Finset.sum_mul, ← Nat.cast_sum,
              show (∑ p ∈ eiPairs, biasedWeight p.1) = 6 from by decide]
          norm_num
  have hR : (12 : ℝ≥0∞) * 32⁻¹ ≤ ∑ p ∈ nonEiPairs, priorB p * speakerB p .or_ := by
    have hmem : ((.anyNumber, .exhaustified) : FCState × Interp) ∈ nonEiPairs := by
      decide
    calc (12 : ℝ≥0∞) * 32⁻¹
        = priorB (.anyNumber, .exhaustified)
            * speakerB (.anyNumber, .exhaustified) .or_ := by
          rw [speakerB_or_anyNumber_exh, mul_one,
              show priorB (.anyNumber, .exhaustified)
                = (biasedWeight FCState.anyNumber : ℝ≥0∞) * 32⁻¹ from rfl]
          norm_num [biasedWeight]
      _ ≤ ∑ p ∈ nonEiPairs, priorB p * speakerB p .or_ :=
          Finset.single_le_sum (f := fun p => priorB p * speakerB p .or_)
            (fun p _ => zero_le') hmem
  refine lt_of_le_of_lt hL (lt_of_lt_of_le ?_ hR)
  exact (ENNReal.mul_lt_mul_iff_left (ENNReal.inv_ne_zero.mpr (by norm_num))
    (ENNReal.inv_ne_top.mpr (by norm_num))).mpr (by norm_num)

/-! ### Without the conjunctive alternative (prose)

The paper's Tables 7–8 show FCI is robust to dropping the conjunctive
alternative. Table 7 removes the Only Both state along with And; in the
Table-8 variant described here, And is replaced by a null utterance (saying
nothing, true at every state under both interpretations) and FCI still
arises — the null
utterance also restores well-definedness at Only Both under ℐ₂, where no
other utterance is true. At α = 2 the S1(Or) values of that model are
16/57, 16/57, 8/41, 8/41, 8/41 under ℐ₁ and 25/441, 25/441, 25/41, 25/41, 0
under ℐ₂ (states in Table-2 order), so given Or the FCI score sum 66/41
again dominates the non-FCI sum ≈ 0.87: the avoidance mechanism between the
bare disjuncts and Or does not depend on And. The formalisation is omitted
for space; it instantiates the same `RSA.Canonical.powUtility` pipeline over
the four-utterance meaning table with `.null` mapped to `fun _ => True`. -/

end ChampollionAlsopGrosu2019
