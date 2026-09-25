module

public import Linglib.Phonology.HarmonicGrammar.IntersectingFamilies
public import Linglib.Phonology.HarmonicGrammar.Noise
public import Linglib.Studies.Zuraw2010

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
and the root-initial nasal constraints of (6). On a square of two prefixes and two stems, each
constraint is insensitive to the prefix or to the stem (`independent`), so every MaxEnt
weighting has constant logit differences (`maxent_predicts_hz_tagalog`,
`hz_constant_value_tagalog`). Noisy Harmonic Grammar orders the cells consistently for every
noise and every weighting that distinguishes the prefixes (`nhg_tagalog_consistent`): its noise
grows with the violation differences, but these depend on the stem alone. The multiplicative
model's differences instead grow with the other factor (`decision_tree_monotonic_diff`). The two
prefix `UNIFORMITY` constraints sum to [zuraw-2010]'s *ASSOCIATE on the square
(`unif_sum_eq_assoc`).

## Implementation notes

* The square fixes the extreme prefixes *maŋ-* and *paŋ-res* of the paper's six and the stems
  /b/ and /k/; the two `UNIFORMITY` constraints are the restriction of the six-way family of
  (5) to these prefixes.
* The four constraints shared with [zuraw-2010] are its constraints pulled back along the
  projection of a candidate onto its stem and decision.
* The paper's fitted models, their log likelihoods and the empirical rates are not represented.

## References

* [zuraw-hayes-2017]
* [zuraw-2010]
* [pater-1999]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace ZurawHayes2017

open Real Constraints HarmonicGrammar ProbabilityTheory

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
def unifMang : Constraint NasalSubCandidate
  | (.mang_b, .yes) | (.mang_k, .yes) => 1
  | _ => 0

/-- `UNIF-paŋ-RES` of (5f). -/
def unifPang : Constraint NasalSubCandidate
  | (.pang_b, .yes) | (.pang_k, .yes) => 1
  | _ => 0

/-- The six constraints. -/
def constraints : CON NasalSubCandidate 6 :=
  ![nasSub, starNC, starStemVelar, starStemVelarCoronal, unifMang, unifPang]

attribute [local simp] constraints nasSub starNC starStemVelar starStemVelarCoronal unifMang
  unifPang Zuraw2010.nasSub Zuraw2010.starNC Zuraw2010.starInitVelar Zuraw2010.starInitCorVel
  NasalSubCandidate.project NasalSubInput.toStemC NasalSubOutput.toSubSt

/-- The prefix and the stem intersect: the consonant-sensitive constraints are insensitive to
the prefix, the prefix-indexed ones to the stem. -/
theorem independent : nasalSubSquare.Independent constraints := by
  intro k
  simp only [Square.InsensitiveToRow, Square.InsensitiveToCol, nasalSubSquare]
  fin_cases k <;> decide

/-! ### Additive and multiplicative models -/

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

/-- Any MaxEnt weighting of the six constraints has constant logit differences on the square,
whatever the other candidates. -/
theorem maxent_predicts_hz_tagalog (w : Fin 6 → ℝ) :
    nasalSubSquare.interaction (fun x ↦
      log (softmax (fun y ↦ harmonyScore constraints w (x, y)) .yes /
        softmax (fun y ↦ harmonyScore constraints w (x, y)) .no)) = 0 :=
  independent.interaction_logOdds_softmax w .yes .no

/-- The constant difference between the /b/ and /k/ columns is `w 2 + w 3 - w 1`: the prefix
constraints cancel. -/
theorem hz_constant_value_tagalog (w : Fin 6 → ℝ) :
    harmonyScore constraints w (.mang_b, .yes) - harmonyScore constraints w (.mang_b, .no) -
      (harmonyScore constraints w (.mang_k, .yes) - harmonyScore constraints w (.mang_k, .no)) =
    w 2 + w 3 - w 1 := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_six]
  ring

/-! ### Consistent ordering under noise -/

/-- Across-the-board consistency of `p` on a square: the effect of the rows has the same sign in
both columns. -/
def ConsistentOrdering {X : Type*} (sq : Square X) (p : X → ℝ) : Prop :=
  0 < (p sq.tl - p sq.bl) * (p sq.tr - p sq.br)

/-- A score with zero interaction, passed through a strictly increasing link whose other argument
(a noise scale, say) is insensitive to the rows, orders the square consistently whenever the rows
differ. -/
theorem consistentOrdering_of_interaction_eq_zero {X S : Type*} {sq : Square X} {d : X → ℝ}
    {s : X → S} {F : S → ℝ → ℝ} (hF : ∀ x, StrictMono (F (s x))) (hd : sq.interaction d = 0)
    (hs : sq.InsensitiveToRow s) (hne : d sq.tl ≠ d sq.bl) :
    ConsistentOrdering sq fun x ↦ F (s x) (d x) := by
  rw [Square.interaction_eq_zero_iff'] at hd
  rw [ConsistentOrdering, ← hs.1, ← hs.2]
  rcases hne.lt_or_gt with h | h
  · exact mul_pos_of_neg_of_neg (sub_neg.2 (hF _ h)) (sub_neg.2 (hF _ (by linarith)))
  · exact mul_pos (sub_pos.2 (hF _ h)) (sub_pos.2 (hF _ (by linarith)))

/-- The summed squared violation differences between substitution and its absence, which scale
the Noisy Harmonic Grammar noise: 2 on the /b/ stems and 5 on the /k/ stems, whatever the
prefix. -/
theorem violationDiffSqSum_eq (x : NasalSubInput) :
    violationDiffSqSum constraints (x, .yes) (x, .no) = if x.toStemC = .b then 2 else 5 := by
  cases x <;>
  simp [violationDiffSqSum, Fin.sum_univ_six] <;>
  norm_num

/-- Noisy Harmonic Grammar orders the Tagalog square consistently for every weighting and noise
under which the two prefixes differ. -/
theorem nhg_tagalog_consistent (w : Fin 6 → ℝ) {σ : ℝ} (hσ : 0 < σ) (hw : w 4 ≠ w 5) :
    ConsistentOrdering nasalSubSquare
      fun x ↦ nhgChoiceProb constraints w σ (x, .yes) (x, .no) := by
  have hs (x : NasalSubInput) : nhgSigmaD constraints σ (x, .yes) (x, .no) =
      σ * √(if x.toStemC = .b then 2 else 5) := by
    rw [nhgSigmaD, violationDiffSqSum_eq]
  refine consistentOrdering_of_interaction_eq_zero (F := fun s Δ ↦ gaussianChoiceProb Δ s)
    (fun x ↦ gaussianChoiceProb_strictMono ?_) (independent.interaction_harmonyScore_sub w _ _)
    ⟨by simp only [hs]; rfl, by simp only [hs]; rfl⟩ fun h ↦ hw ?_
  · rw [hs]
    split_ifs <;> positivity
  · simp [nasalSubSquare, harmonyScore_eq_neg_sum, Fin.sum_univ_six] at h
    linarith

/-! ### The *ASSOCIATE constraint of Zuraw 2010 -/

/-- On the square the two prefix-indexed `UNIFORMITY` constraints sum to [zuraw-2010]'s
*ASSOCIATE: each coalescing candidate is hit by exactly one of them. -/
theorem unif_sum_eq_assoc (c : NasalSubCandidate) :
    unifMang c + unifPang c = Zuraw2010.starAssoc (NasalSubCandidate.project c) := by
  rcases c with ⟨i, o⟩
  cases i <;> cases o <;> decide

end ZurawHayes2017
