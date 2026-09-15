import Linglib.Phonology.HarmonicGrammar.Separability
import Linglib.Studies.Zuraw2010

/-!
# Zuraw and Hayes (2017): Intersecting Constraint Families

This file formalizes the Tagalog case of [zuraw-hayes-2017]'s argument for Harmonic Grammar.
When variation is governed by two independent families of constraints, here the
consonant-sensitive markedness constraints and the prefix-indexed faithfulness constraints of
nasal substitution, the rates of application show across-the-board effects in both dimensions,
restrained by floor and ceiling effects: differences in one family appear only at medial values
of the other. Harmonic Grammar predicts the pattern because constraint effects add, so that
the logit rates differ by a constant along each dimension and the sigmoid compresses the
constant difference at both extremes, whereas a decision-tree model multiplies factors and so
pinches at one end only, the paper's claws. The constraints are those of §2.4, adapted from
[zuraw-2010]: `NASSUB` of (3), *NC̥ of (4), the prefix-indexed `UNIFORMITY` constraints of (5)
and the root-initial nasal constraints of (6). On a square of two prefixes and two stems, the
violation differences of each constraint are insensitive to one dimension
(`violDiff_independence`), so any MaxEnt weighting satisfies the constant logit difference
(`maxent_predicts_hz_tagalog`, `hz_constant_value_tagalog`), and any Noisy Harmonic Grammar
with positive noise orders the cells consistently (`nhg_tagalog_consistent`); the multiplicative
model's differences instead grow with the other factor (`decision_tree_monotonic_diff`). The four
constraints shared with [zuraw-2010] are its constraints pulled back along the projection of the
square onto its stem and decision (`nasSub_eq_zuraw_under_projection`), and the two prefix
`UNIFORMITY` constraints sum to its *ASSOCIATE on the square (`unif_sum_eq_assoc`).

## Implementation notes

* The square fixes the extreme prefixes *maŋ-* and *paŋ-res* of the paper's six and the stems
  /b/ and /k/; the two `UNIFORMITY` constraints are the restriction of the six-way family of
  (5) to these prefixes.
* The paper's fitted models, their log likelihoods and the empirical rates are not represented.

## References

* [zuraw-hayes-2017]
* [zuraw-2010]
* [pater-1999]
* [mccarthy-prince-1995]
-/

namespace ZurawHayes2017

open Constraints HarmonicGrammar Core.Optimization OptimalityTheory

/-! ### The square of underlying forms -/

/-- The four underlying concatenations: the prefixes *maŋ-* and *paŋ-res* crossed with the stems
/b/ and /k/. -/
inductive NasalSubInput
  | mang_b
  | mang_k
  | pang_b
  | pang_k
  deriving DecidableEq, Repr, Fintype

/-- The two surface variants: the coalesced nasal, or the assimilated cluster. -/
inductive NasalSubOutput
  | yes
  | no
  deriving DecidableEq, Repr, Fintype

/-- An input paired with an output. -/
abbrev NasalSubCandidate := NasalSubInput × NasalSubOutput

/-- The square, prefix by stem. -/
def nasalSubSquare : Square NasalSubInput where
  tl := .mang_b
  tr := .mang_k
  bl := .pang_b
  br := .pang_k

/-- The stem of an input. -/
def NasalSubInput.toStemC : NasalSubInput → Zuraw2010.StemC
  | .mang_b | .pang_b => .b
  | .mang_k | .pang_k => .k

/-- The decision of an output. -/
def NasalSubOutput.toSubSt : NasalSubOutput → Zuraw2010.SubSt
  | .yes => .yes
  | .no => .no

/-- The projection of a candidate onto [zuraw-2010]'s stem and decision. -/
def NasalSubCandidate.project (c : NasalSubCandidate) : Zuraw2010.NSCand :=
  (c.1.toStemC, c.2.toSubSt)

/-! ### The constraints -/

/-- `NASSUB` of (3): one violation for a nasal followed by an obstruent across a morpheme
boundary. -/
def nasSub : Constraint NasalSubCandidate :=
  Zuraw2010.nasSub.comap NasalSubCandidate.project

/-- *NC̥ of (4): one violation for a nasal followed by a voiceless obstruent. -/
def starNC : Constraint NasalSubCandidate :=
  Zuraw2010.starNC.comap NasalSubCandidate.project

/-- *[root ŋ of (6c): a root must not begin with a velar nasal. -/
def starStemVelar : Constraint NasalSubCandidate :=
  Zuraw2010.starInitVelar.comap NasalSubCandidate.project

/-- *[root n/ŋ of (6b): a root must not begin with a coronal or velar nasal. -/
def starStemVelarCoronal : Constraint NasalSubCandidate :=
  Zuraw2010.starInitCorVel.comap NasalSubCandidate.project

/-- `UNIF-maŋ-OTHER` of (5a): a segment of *maŋ-* and a distinct input segment must not
correspond to one output segment. -/
def unifMang : Constraint NasalSubCandidate :=
  λ
    | (.mang_b, .yes) | (.mang_k, .yes) => 1
    | _ => 0

/-- `UNIF-paŋ-RES` of (5f). -/
def unifPang : Constraint NasalSubCandidate :=
  λ
    | (.pang_b, .yes) | (.pang_k, .yes) => 1
    | _ => 0

/-- The six constraints. -/
def constraints : Fin 6 → Constraint NasalSubCandidate
  | ⟨0, _⟩ => nasSub
  | ⟨1, _⟩ => starNC
  | ⟨2, _⟩ => starStemVelar
  | ⟨3, _⟩ => starStemVelarCoronal
  | ⟨4, _⟩ => unifMang
  | ⟨5, _⟩ => unifPang

/-! ### Violation differences -/

/-- The violation difference `Cₖ(x, no) − Cₖ(x, yes)` of each constraint at each input;
positive differences favour substitution. -/
def violDiffProfile : Fin 6 → NasalSubInput → ℤ
  | ⟨0, _⟩, _ => 1
  | ⟨1, _⟩, .mang_k | ⟨1, _⟩, .pang_k => 1
  | ⟨1, _⟩, _ => 0
  | ⟨2, _⟩, .mang_k | ⟨2, _⟩, .pang_k => -1
  | ⟨2, _⟩, _ => 0
  | ⟨3, _⟩, .mang_k | ⟨3, _⟩, .pang_k => -1
  | ⟨3, _⟩, _ => 0
  | ⟨4, _⟩, .mang_b | ⟨4, _⟩, .mang_k => -1
  | ⟨4, _⟩, _ => 0
  | ⟨5, _⟩, .pang_b | ⟨5, _⟩, .pang_k => -1
  | ⟨5, _⟩, _ => 0

/-- The violation differences as reals. -/
def deltaR : Fin 6 → NasalSubInput → ℝ :=
  λ k x => (violDiffProfile k x : ℝ)

/-- Each constraint's violation difference is insensitive to one dimension of the square: the
consonant-sensitive constraints to the prefix, the prefix-indexed ones to the stem. -/
theorem violDiff_independence : ViolDiffIndependence deltaR nasalSubSquare := by
  intro k
  simp only [deltaR, violDiffProfile, nasalSubSquare]
  fin_cases k <;> simp

/-! ### Additive and multiplicative models -/

/-- Across-the-board consistency: the effect of one dimension has the same sign at both values
of the other. -/
def ConsistentOrdering {α : Type*} [Mul α] [Sub α] [Zero α] [LT α] (r : Square α) : Prop :=
  (r.tl - r.bl) * (r.tr - r.br) > 0

/-- In a multiplicative model `p(x, y) = g(x) · h(y)`, the difference between two `h`-values
grows with `g`: it vanishes at the floor and is largest at the ceiling, the paper's claws. -/
theorem decision_tree_monotonic_diff (g₁ g₂ h₁ h₂ : ℚ) (hg : g₁ < g₂) (hh : h₁ < h₂) :
    g₁ * h₂ - g₁ * h₁ < g₂ * h₂ - g₂ * h₁ := by
  have key : g₁ * (h₂ - h₁) < g₂ * (h₂ - h₁) := mul_lt_mul_of_pos_right hg (by linarith)
  linarith [mul_sub g₁ h₂ h₁, mul_sub g₂ h₂ h₁]

/-- In a multiplicative model the ratio of `h`-differences across two `g`-values is the ratio
of the `g`-values. -/
theorem decision_tree_diff_proportional (g₁ g₂ h₁ h₂ : ℚ) :
    (g₂ * h₂ - g₂ * h₁) * g₁ = (g₁ * h₂ - g₁ * h₁) * g₂ := by
  ring

/-- Any MaxEnt weighting of the six constraints satisfies the constant logit difference on the
square. -/
theorem maxent_predicts_hz_tagalog (w : Fin 6 → ℝ) :
    ConstantLogitDiff (λ x => ∑ k : Fin 6, w k * deltaR k x) nasalSubSquare :=
  me_predicts_hz w deltaR nasalSubSquare violDiff_independence

/-- The constant difference between the /b/ and /k/ columns in the *maŋ-* row is
`−w₂ + w₃ + w₄`: the prefix constraints cancel. -/
theorem hz_constant_value_tagalog (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
      (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) = -w 1 + w 2 + w 3 := by
  simp only [Fin.sum_univ_six, violDiffProfile]
  ring

/-- The same difference in the *paŋ-res* row. -/
theorem hz_constant_value_tagalog' (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) -
      (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) = -w 1 + w 2 + w 3 := by
  simp only [Fin.sum_univ_six, violDiffProfile]
  ring

/-- The two row differences coincide. -/
theorem hz_identity_concrete (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
      (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) -
      (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) := by
  rw [hz_constant_value_tagalog, hz_constant_value_tagalog']

/-- Under a constant logit difference, Noisy Harmonic Grammar with noise `σ` orders the square
consistently, since the normal distribution function is strictly monotone. -/
theorem nhg_consistent_ordering {X : Type} (d : X → ℝ) (σ : ℝ) (hσ : 0 < σ) (sq : Square X)
    (hcld : ConstantLogitDiff d sq) (hne : d sq.tl ≠ d sq.bl) :
    ConsistentOrdering ⟨Core.normalCDF (d sq.tl / σ), Core.normalCDF (d sq.tr / σ),
      Core.normalCDF (d sq.bl / σ), Core.normalCDF (d sq.br / σ)⟩ :=
  constantLogitDiff_mono_consistent d (λ x => Core.normalCDF (x / σ))
    (Core.normalCDF_strictMono.comp λ _ _ h => (div_lt_div_iff_of_pos_right hσ).mpr h)
    sq hcld hne

/-- For any weighting and noise, Noisy Harmonic Grammar orders the Tagalog square consistently
whenever the two prefixes differ on /b/. -/
theorem nhg_tagalog_consistent (w : Fin 6 → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hne : (∑ k : Fin 6, w k * deltaR k .mang_b) ≠ (∑ k : Fin 6, w k * deltaR k .pang_b)) :
    ConsistentOrdering ⟨Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .mang_b) / σ),
      Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .mang_k) / σ),
      Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .pang_b) / σ),
      Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .pang_k) / σ)⟩ :=
  nhg_consistent_ordering (λ x => ∑ k : Fin 6, w k * deltaR k x) σ hσ nasalSubSquare
    (maxent_predicts_hz_tagalog w) hne

/-! ### The constraints of Zuraw 2010 under the projection -/

theorem nasSub_eq_zuraw_under_projection :
    nasSub = Zuraw2010.nasSub ∘ NasalSubCandidate.project := rfl

theorem starNC_eq_zuraw_under_projection :
    starNC = Zuraw2010.starNC ∘ NasalSubCandidate.project := rfl

theorem starStemVelar_eq_zuraw_under_projection :
    starStemVelar = Zuraw2010.starInitVelar ∘ NasalSubCandidate.project := rfl

theorem starStemVelarCoronal_eq_zuraw_under_projection :
    starStemVelarCoronal = Zuraw2010.starInitCorVel ∘ NasalSubCandidate.project := rfl

/-- On the square the two prefix-indexed `UNIFORMITY` constraints sum to [zuraw-2010]'s
*ASSOCIATE: each coalescing candidate is hit by exactly one of them. -/
theorem unif_sum_eq_assoc (c : NasalSubCandidate) :
    unifMang c + unifPang c = Zuraw2010.starAssoc (NasalSubCandidate.project c) := by
  rcases c with ⟨i, o⟩
  cases i <;> cases o <;> decide

end ZurawHayes2017
