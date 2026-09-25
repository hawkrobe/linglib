module

public import Linglib.Phonology.HarmonicGrammar.IntersectingFamilies
public import Linglib.Phonology.HarmonicGrammar.Noise
public import Linglib.Studies.Zuraw2010

/-!
# Zuraw and Hayes (2017): Intersecting Constraint Families

This file formalizes the Tagalog case of [zuraw-hayes-2017]'s argument for Harmonic Grammar.
Nasal substitution is conditioned by two families of constraints (§2.4): the consonant-sensitive
markedness constraints (3), (4), (6), and the Uniformity constraints (5), one for each of the six
prefix constructions. Every square crossing two prefixes with two stems is independent in the
sense of the substrate: each constraint is insensitive to the prefix or to the stem
(`independent`). The rates of application show across-the-board effects in both dimensions,
restrained by floor and ceiling effects (§2.3); Harmonic Grammar predicts the pattern because
constraint effects add.

In MaxEnt the probability of substitution is logistic in the harmony difference (13)
(`maxentSubst_eq`), the logit rates have constant differences on every square
(`maxent_predicts_hz`), and so the effects of prefixes and of stems are across the board on
every square, for every weighting (`maxent_acrossTheBoard`). In Noisy Harmonic Grammar the noise
on a comparison grows with the number of constraints that distinguish the candidates, four for
/p/ as in (15) (`violationDiffSqSum_p`); since that number depends on the stem alone, the
effects of the prefixes are across the board on every square, for every weighting and noise
(`nhg_acrossTheBoard`). A decision-tree model instead multiplies a prefix probability by a stem
probability, so the stem differences grow with the prefix probability, the paper's claws
(`decision_tree_monotonic_diff`).

## Implementation notes

* The inputs are the thirty-six crossings of the six prefix constructions of Figure 3 with the
  six stem-initial consonants of [zuraw-2010]; its /t/ stands for the paper's t/s class.
* The constraints are those of Table 1, in its order, the consonant-sensitive ones pulled back
  from [zuraw-2010] along the projection of a candidate onto its stem and decision.
* The paper's fitted weights, their log likelihoods, the empirical rates, and the stochastic OT
  and partial-ordering models are not represented.

## References

* [zuraw-hayes-2017]
* [zuraw-2010]
* [pater-1999]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace ZurawHayes2017

open Real Constraints HarmonicGrammar ProbabilityTheory Finset
open Zuraw2010 (StemC SubSt NSCand)

/-! ### Inputs and candidates -/

/-- The six most type-frequent prefix constructions of Figure 3, in the order of Table 1. -/
inductive Prefix
  /-- *maŋ-* OTHER, nonadversative verbs. -/
  | mangOther
  /-- *paŋ-* RED-, mainly gerunds. -/
  | pangRed
  /-- *maŋ-* ADV, adversative verbs. -/
  | mangAdv
  /-- *maŋ-* RED-, professional or habitual nouns. -/
  | mangRed
  /-- *paŋ-* NOUN, various nominalizations. -/
  | pangNoun
  /-- *paŋ-* RES, reservational adjectives. -/
  | pangRes
  deriving DecidableEq, Repr, Fintype

/-- A candidate: a prefix construction and a stem-initial consonant, with or without
substitution. -/
abbrev Candidate := (Prefix × StemC) × SubSt

/-- The projection of a candidate onto [zuraw-2010]'s stem and decision. -/
def project (c : Candidate) : NSCand := (c.1.2, c.2)

/-- The square crossing the prefixes `p` and `p'` (rows) with the stems `c` and `c'` (columns). -/
def square (p p' : Prefix) (c c' : StemC) : Square (Prefix × StemC) :=
  ⟨(p, c), (p, c'), (p', c), (p', c')⟩

/-! ### The constraints -/

/-- `NasSub` of (3): one violation for a nasal followed by an obstruent across a morpheme
boundary. -/
def nasSub : Constraint Candidate := Zuraw2010.nasSub.comap project

/-- *NC̥ of (4): one violation for a nasal followed by a voiceless obstruent. -/
def starNC : Constraint Candidate := Zuraw2010.starNC.comap project

/-- *[root m/n/ŋ of (6a): a root must not begin with a nasal. -/
def starRootNasal : Constraint Candidate := Zuraw2010.starInitAll.comap project

/-- *[root n/ŋ of (6b): a root must not begin with a coronal or velar nasal. -/
def starRootCorVel : Constraint Candidate := Zuraw2010.starInitCorVel.comap project

/-- *[root ŋ of (6c): a root must not begin with a velar nasal. -/
def starRootVelar : Constraint Candidate := Zuraw2010.starInitVelar.comap project

/-- The Uniformity constraint of (5) indexed to prefix construction `q`: a segment of the prefix
and a distinct input segment must not correspond to one output segment. -/
def unif (q : Prefix) : Constraint Candidate :=
  Constraint.binary fun c ↦ c.1.1 = q ∧ c.2 = .yes

/-- The eleven constraints, in the order of Table 1. -/
def constraints : CON Candidate 11 :=
  ![nasSub, starNC, starRootNasal, starRootCorVel, starRootVelar, unif .mangOther, unif .pangRed,
    unif .mangAdv, unif .mangRed, unif .pangNoun, unif .pangRes]

attribute [local simp] constraints nasSub starNC starRootNasal starRootCorVel starRootVelar unif
  Zuraw2010.nasSub Zuraw2010.starNC Zuraw2010.starInitAll Zuraw2010.starInitCorVel
  Zuraw2010.starInitVelar project

/-- The two families intersect: on every square the consonant-sensitive constraints are
insensitive to the prefix and the Uniformity constraints to the stem. -/
theorem independent (p p' : Prefix) (c c' : StemC) :
    (square p p' c c').Independent constraints := by
  intro k
  fin_cases k <;> first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩

/-- The Uniformity family sums to *[root m/n/ŋ: a substituted candidate violates exactly the
Uniformity constraint of its prefix. -/
theorem sum_unif_eq_starRootNasal (c : Candidate) : ∑ q, unif q c = starRootNasal c := by
  revert c
  decide +kernel

/-! ### Across-the-board effects -/

/-- The effect of the rows of a square is across the board (§2.3): it has the same direction in
both columns, so that the lines of Figure 4 do not cross. -/
def AcrossTheBoard {X : Type*} (sq : Square X) (r : X → ℝ) : Prop :=
  0 ≤ (r sq.tl - r sq.bl) * (r sq.tr - r sq.br)

/-- A score with zero interaction, passed through a monotone link whose other argument (a noise
scale, say) is insensitive to the rows, has across-the-board row effects. -/
theorem acrossTheBoard_of_interaction_eq_zero {X S : Type*} {sq : Square X} {d : X → ℝ}
    {s : X → S} {F : S → ℝ → ℝ} (hF : ∀ x, Monotone (F (s x))) (hd : sq.interaction d = 0)
    (hs : sq.InsensitiveToRow s) : AcrossTheBoard sq fun x ↦ F (s x) (d x) := by
  rw [Square.interaction_eq_zero_iff'] at hd
  rw [AcrossTheBoard, ← hs.1, ← hs.2]
  rcases le_total (d sq.tl) (d sq.bl) with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hF _ h)) (sub_nonpos.2 (hF _ (by linarith)))
  · exact mul_nonneg (sub_nonneg.2 (hF _ h)) (sub_nonneg.2 (hF _ (by linarith)))

/-! ### Maximum entropy -/

/-- The MaxEnt probability of substitution for an input. -/
noncomputable def maxentSubst (w : Fin 11 → ℝ) (x : Prefix × StemC) : ℝ :=
  softmax (fun y ↦ harmonyScore constraints w (x, y)) .yes

/-- The MaxEnt probability of substitution is logistic in the harmony difference between the
substituted and unsubstituted candidates (13). -/
theorem maxentSubst_eq (w : Fin 11 → ℝ) (x : Prefix × StemC) :
    maxentSubst w x =
      sigmoid (harmonyScore constraints w (x, .yes) - harmonyScore constraints w (x, .no)) := by
  rw [maxentSubst, softmax_def, show (univ : Finset SubSt) = {.yes, .no} by decide,
    sum_pair (by decide), sigmoid_def, neg_sub, exp_sub, ← div_self (exp_pos _).ne', ← add_div,
    inv_div]

/-- Any MaxEnt weighting has constant logit differences on every square, whatever the other
candidates. -/
theorem maxent_predicts_hz (w : Fin 11 → ℝ) (p p' : Prefix) (c c' : StemC) :
    (square p p' c c').interaction (fun x ↦
      log (softmax (fun y ↦ harmonyScore constraints w (x, y)) .yes /
        softmax (fun y ↦ harmonyScore constraints w (x, y)) .no)) = 0 :=
  (independent p p' c c').interaction_logOdds_softmax w .yes .no

/-- The logit of substitution for /b/ exceeds that for /k/ by the weights of *[root n/ŋ and
*[root ŋ less that of *NC̥, whatever the prefix. -/
theorem harmony_b_sub_harmony_k (w : Fin 11 → ℝ) (p : Prefix) :
    harmonyScore constraints w ((p, .b), .yes) - harmonyScore constraints w ((p, .b), .no) -
      (harmonyScore constraints w ((p, .k), .yes) - harmonyScore constraints w ((p, .k), .no)) =
    w 3 + w 4 - w 1 := by
  cases p <;> simp [harmonyScore_eq_neg_sum, Fin.sum_univ_succ] <;> ring

/-- MaxEnt's effects are across the board on every square, for every weighting: those of the
prefixes at every pair of stems, and those of the stems at every pair of prefixes. -/
theorem maxent_acrossTheBoard (w : Fin 11 → ℝ) (p p' : Prefix) (c c' : StemC) :
    AcrossTheBoard (square p p' c c') (maxentSubst w) ∧
      AcrossTheBoard (square p p' c c').transpose (maxentSubst w) := by
  have hd := (independent p p' c c').interaction_harmonyScore_sub w .yes .no
  rw [funext (maxentSubst_eq w)]
  exact ⟨acrossTheBoard_of_interaction_eq_zero (s := fun _ ↦ ()) (F := fun _ ↦ sigmoid)
      (fun _ ↦ sigmoid_strictMono.monotone) hd ⟨rfl, rfl⟩,
    acrossTheBoard_of_interaction_eq_zero (s := fun _ ↦ ()) (F := fun _ ↦ sigmoid)
      (fun _ ↦ sigmoid_strictMono.monotone) (by rwa [Square.interaction_transpose]) ⟨rfl, rfl⟩⟩

/-! ### Noisy Harmonic Grammar -/

/-- The number of constraints that distinguish substitution from its absence, each counted with
its squared violation difference. -/
private def diffSq (x : Prefix × StemC) : ℤ :=
  ∑ i, ((constraints i (x, .yes) : ℤ) - constraints i (x, .no)) ^ 2

private theorem violationDiffSqSum_eq_diffSq (x : Prefix × StemC) :
    violationDiffSqSum constraints (x, .yes) (x, .no) = diffSq x := by
  simp [violationDiffSqSum, diffSq]

private theorem diffSq_eq (q : Prefix) (c : StemC) : diffSq (q, c) = diffSq (.mangOther, c) := by
  revert q c
  decide +kernel

private theorem diffSq_pos (x : Prefix × StemC) : 0 < diffSq x := by
  revert x
  decide +kernel

/-- The Noisy HG noise on /p/ is the sum of four Gaussians, one for each constraint that
distinguishes substitution from its absence, whatever the prefix (15). -/
theorem violationDiffSqSum_p (q : Prefix) :
    violationDiffSqSum constraints ((q, .p), .yes) ((q, .p), .no) = 4 := by
  rw [violationDiffSqSum_eq_diffSq]
  exact_mod_cast (show diffSq (q, .p) = 4 by cases q <;> decide +kernel)

/-- Noisy Harmonic Grammar's prefix effects are across the board on every square, for every
weighting and noise: its noise depends on the stem alone. -/
theorem nhg_acrossTheBoard (w : Fin 11 → ℝ) {σ : ℝ} (hσ : 0 < σ) (p p' : Prefix)
    (c c' : StemC) :
    AcrossTheBoard (square p p' c c')
      fun x ↦ nhgChoiceProb constraints w σ (x, .yes) (x, .no) := by
  have hs (x : Prefix × StemC) :
      nhgSigmaD constraints σ (x, .yes) (x, .no) = σ * √(diffSq (.mangOther, x.2)) := by
    rw [nhgSigmaD, violationDiffSqSum_eq_diffSq, ← diffSq_eq x.1]
  refine acrossTheBoard_of_interaction_eq_zero (F := fun s Δ ↦ gaussianChoiceProb Δ s)
    (fun x ↦ (gaussianChoiceProb_strictMono ?_).monotone)
    ((independent p p' c c').interaction_harmonyScore_sub w _ _)
    ⟨by simp only [hs, square], by simp only [hs, square]⟩
  rw [hs]
  have := diffSq_pos (.mangOther, x.2)
  have : (0 : ℝ) < diffSq (.mangOther, x.2) := by exact_mod_cast this
  positivity

/-! ### The decision-tree model -/

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

end ZurawHayes2017
