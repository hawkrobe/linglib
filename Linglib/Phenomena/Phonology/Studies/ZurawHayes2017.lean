import Linglib.Core.Constraint.Separability
import Linglib.Phenomena.Phonology.Studies.Zuraw2010

/-!
# @cite{zuraw-hayes-2017}: Intersecting Constraint Families
@cite{zuraw-hayes-2017}

@cite{zuraw-hayes-2017} "Intersecting Constraint Families: An Argument
for Harmonic Grammar" (Language 93(3): 497–546).

## Main claims

1. When phonological variation is governed by two independent families
   of constraints, the data exhibits **across-the-board effects** with
   **floor and ceiling compression** — a family of sigmoid curves.

2. This pattern is naturally predicted by Harmonic Grammar (MaxEnt and
   Noisy HG) because constraint effects are *additive*.

3. **Decision-tree models** fail because their *multiplicative*
   decomposition produces "claws" (monotonically increasing
   differentiation), not sigmoid families.

4. **Stochastic OT** fails because ranking paradoxes prevent fitting
   structured constraint sets to the observed pattern.

## Formalization

This file develops the 2×2 sub-square of Z&H 2017's Tagalog data and
proves the decision-tree failure theorem, the across-the-board
consistency property of the empirical rates, and the bridge from
constraint independence to the Hayes-Zuraw constant-logit-difference
identity (which Z&H argue is the diagnostic of additive constraint
interaction).

The 2×2 sub-square fixes two extreme cells of Z&H's full 6×6 grid
(maŋ-other = highest substitution rate, paŋ-res = lowest) crossed with
two of the six stem obstruents (/b/ vs /k/, voicing contrast at
non-coronal places). This sub-square suffices for the mathematical
content of the family-interaction argument.

The 2-way UNIFORMITY split here (`unifMang`, `unifPang`) is a
restriction of Z&H's 6-way prefix-indexed UNIFORMITY constraint set
(Unif-maŋ-other / Unif-maŋ-RED / Unif-maŋ-ADV / Unif-paŋ-RED /
Unif-paŋ-NOUN / Unif-paŋ-RES) projected onto the maŋ-other × paŋ-res
sub-grid.

## Case studies (full paper)

- **Tagalog nasal substitution**: nearly synergistic families
  (both markedness and prefix UNIFORMITY constraints mostly penalize
  substitution; only \*NC̥ favors it on the consonant side)
- **French liaison/elision**: synergistic families
  (word2 ALIGN + word1 USE both favor non-alignment)
- **Hungarian vowel harmony**: mixed families
  (stem vowel AGREE + final consonant BILABIAL/SIBILANT/etc.)
-/

namespace ZurawHayes2017

open Core.Constraint Core.Constraint.OT Phonology.Constraints

/-! ## § 1: 2×2 Square — Underlying Forms -/

/-- The four underlying concatenations populating the 2×2 sub-square:
    two prefix constructions (maŋ-other, paŋ-res — the extreme rows
    of Z&H's 6-prefix grid) crossed with two stem obstruents (/b/, /k/
    — the voicing contrast at non-coronal places). -/
inductive NasalSubInput where
  | mang_b  -- /maŋ-other + b/  (top-left)
  | mang_k  -- /maŋ-other + k/  (top-right)
  | pang_b  -- /paŋ-res + b/    (bottom-left)
  | pang_k  -- /paŋ-res + k/    (bottom-right)
  deriving DecidableEq, Repr, Fintype

/-- The two surface variants for each underlying form. -/
inductive NasalSubOutput where
  /-- YES: nasal substitution applies — nasal and obstruent coalesce. -/
  | yes
  /-- NO: nasal substitution does not apply — place assimilation only. -/
  | no
  deriving DecidableEq, Repr, Fintype

/-- Input–output pair for constraint evaluation. -/
abbrev NasalSubCandidate := NasalSubInput × NasalSubOutput

/-- The 2×2 square of underlying forms: prefix × stem-initial obstruent. -/
def nasalSubSquare : Square NasalSubInput where
  tl := .mang_b
  tr := .mang_k
  bl := .pang_b
  br := .pang_k

/-! ## § 2: Projection to Zuraw 2010's six-stem candidate space

Z&H §2.4 explicitly says their constraint set is "adapted from Zuraw 2010".
The 4 of 6 constraints they share with Zuraw (NasSub, \*NC, \*[stemŋ], and
the *[stemŋ]/n stringent step) are not redefined here — they're lifted
from `Zuraw2010` via projection. The 2 prefix-indexed UNIFORMITY constraints
are Z&H's substitute for Zuraw's \*ASSOC and are defined locally.

The projection maps the 4-cell sub-square onto the corresponding cells of
Zuraw 2010's 6-stem × 2-decision space:
- maŋ-other + b, paŋ-res + b → (b, _)
- maŋ-other + k, paŋ-res + k → (k, _)

The prefix dimension is collapsed; the stem and yes/no dimensions are
preserved. -/

/-- Project a 2×2 input onto Zuraw 2010's stem consonant. -/
def NasalSubInput.toStemC : NasalSubInput → Zuraw2010.StemC
  | .mang_b | .pang_b => .b
  | .mang_k | .pang_k => .k

/-- Project a 2-cell output onto Zuraw 2010's substitution decision. -/
def NasalSubOutput.toSubSt : NasalSubOutput → Zuraw2010.SubSt
  | .yes => .yes
  | .no  => .no

/-- Project a Z&H candidate onto a Zuraw 2010 candidate. -/
def NasalSubCandidate.project (c : NasalSubCandidate) : Zuraw2010.NSCand :=
  (c.1.toStemC, c.2.toSubSt)

/-! ## § 3: Constraint Inventory

The 4 shared constraints come from Zuraw 2010 via `comap` along the
projection. The 2 prefix-indexed UNIFORMITY constraints are local. -/

/-- C₁ = NasSub (markedness): per @cite{zuraw-hayes-2017} ex. (3),
    "Assess one violation for any nasal + obstruent sequence, where + is
    a morpheme boundary within a word." Lifted from `Zuraw2010.nasSub`. -/
def nasSub : NamedConstraint NasalSubCandidate :=
  Zuraw2010.nasSub.comap NasalSubCandidate.project

/-- C₂ = \*NC: per @cite{zuraw-2010} ex. (17), "A [+nasal] segment must
    not be immediately followed by a [-voice, -sonorant] segment". Lifted
    from `Zuraw2010.starNC`. Violated by NO only for voiceless stems (k). -/
def starNC : NamedConstraint NasalSubCandidate :=
  Zuraw2010.starNC.comap NasalSubCandidate.project

/-- C₃ = \*[stemŋ]: penalizes stem-initial velar nasal. Lifted from
    `Zuraw2010.starInitVelar`. Violated by YES for k-initial stems
    (coalesced ŋ is velar). Z&H ex. (6c). -/
def starStemVelar : NamedConstraint NasalSubCandidate :=
  Zuraw2010.starInitVelar.comap NasalSubCandidate.project

/-- C₄ = \*[stemŋ]/n: penalizes stem-initial velar or coronal nasal.
    Lifted from `Zuraw2010.starInitCorVel`. In the b vs k square, this
    coincides with C₃ (bilabial m is neither velar nor coronal), so on
    the restricted domain `(c.eval ∘ project)` is identical for C₃ and C₄.
    Z&H ex. (6b). -/
def starStemVelarCoronal : NamedConstraint NasalSubCandidate :=
  Zuraw2010.starInitCorVel.comap NasalSubCandidate.project

/-- C₅ = Unif-maŋ-other (faithfulness): one violation when the maŋ-other
    prefix coalesces with the stem-initial obstruent. Per Z&H ex. (5a),
    "One segment from input maŋ-other and a distinct input segment must
    not correspond to the same output segment." Restriction of Z&H's
    6-way prefix-indexed UNIFORMITY family to the maŋ-other cell.
    Z&H-local; replaces Zuraw 2010's \*ASSOC. -/
def unifMang : NamedConstraint NasalSubCandidate :=
  mkFaithGrad "Unif-maŋ-other" fun
    | (.mang_b, .yes) | (.mang_k, .yes) => 1
    | _ => 0

/-- C₆ = Unif-paŋ-res (faithfulness): one violation when the paŋ-res
    prefix coalesces with the stem-initial obstruent. Per Z&H ex. (5f),
    similar to Unif-maŋ-other but for paŋ-res. Restriction of Z&H's
    6-way prefix-indexed UNIFORMITY family to the paŋ-res cell. -/
def unifPang : NamedConstraint NasalSubCandidate :=
  mkFaithGrad "Unif-paŋ-res" fun
    | (.pang_b, .yes) | (.pang_k, .yes) => 1
    | _ => 0

/-- The six constraints as a `Fin 6`-indexed family. -/
def constraints : Fin 6 → NamedConstraint NasalSubCandidate
  | ⟨0, _⟩ => nasSub
  | ⟨1, _⟩ => starNC
  | ⟨2, _⟩ => starStemVelar
  | ⟨3, _⟩ => starStemVelarCoronal
  | ⟨4, _⟩ => unifMang
  | ⟨5, _⟩ => unifPang

/-! ## § 4: Violation Differences (Δₖ) -/

/-- Violation difference `Δₖ(x) = Cₖ(x, NO) − Cₖ(x, YES)` for each
    underlying form x and constraint k. Positive Δ favors YES. -/
def violDiffProfile : Fin 6 → NasalSubInput → ℤ
  -- C₁ = NasSub: Δ₁ = 1 for all forms (NO always has a nasal+obstruent sequence)
  | ⟨0, _⟩, _ => 1
  -- C₂ = *NC: Δ₂ = 1 for /k/ forms, 0 for /b/ forms
  | ⟨1, _⟩, .mang_k | ⟨1, _⟩, .pang_k => 1
  | ⟨1, _⟩, _ => 0
  -- C₃ = *[stemŋ]: Δ₃ = −1 for /k/ forms (YES has velar nasal), 0 for /b/
  | ⟨2, _⟩, .mang_k | ⟨2, _⟩, .pang_k => -1
  | ⟨2, _⟩, _ => 0
  -- C₄ = *[stemŋ]/n: same as C₃ in the /b/ vs /k/ case
  | ⟨3, _⟩, .mang_k | ⟨3, _⟩, .pang_k => -1
  | ⟨3, _⟩, _ => 0
  -- C₅ = UNIF(maŋ-other): Δ₅ = −1 for /maŋ/ forms, 0 for /paŋ/
  | ⟨4, _⟩, .mang_b | ⟨4, _⟩, .mang_k => -1
  | ⟨4, _⟩, _ => 0
  -- C₆ = UNIF(paŋ-res): Δ₆ = −1 for /paŋ/ forms, 0 for /maŋ/
  | ⟨5, _⟩, .pang_b | ⟨5, _⟩, .pang_k => -1
  | ⟨5, _⟩, _ => 0

/-- The violation differences cast to ℝ, for use with `me_predicts_hz`. -/
def deltaR : Fin 6 → NasalSubInput → ℝ :=
  fun k x => (violDiffProfile k x : ℝ)

/-- **Violation difference independence**: the violation differences Δₖ
    satisfy `ViolDiffIndependence` on the nasal substitution square.

    - C₁–C₄ (markedness): Δₖ is the same for /maŋ-other+X/ and
      /paŋ-res+X/ (insensitive to prefix = row)
    - C₅–C₆ (faithfulness): Δₖ is the same for /X+b/ and /X+k/
      (insensitive to stem = column)

    This is a data-level property of the constraint violation profiles,
    used by both Z&H's family-interaction argument and Magri 2025's
    MaxEnt-on-square deduction. -/
theorem violDiff_independence :
    ViolDiffIndependence deltaR nasalSubSquare := by
  intro k
  simp only [deltaR, violDiffProfile, nasalSubSquare]
  fin_cases k <;> simp

/-! ## § 5: Empirical Rates (2×2 square) -/

/-- Empirical rates of nasal substitution from @cite{zuraw-2010}'s
    Tagalog dictionary type frequencies, arranged per the
    @cite{zuraw-hayes-2017} 2×2 sub-square. The four cells correspond
    to the two extreme prefixes (maŋ-other = highest rate,
    paŋ-res = lowest) crossed with /b/ (voiced) and /k/ (voiceless).

    UNVERIFIED: bottom-row rates (0.434, 0.909) extracted from Z&H's
    fitted-MaxEnt tableau; should be cross-checked against the paper's
    Table 6 or supplementary materials before being treated as
    paper-citable. -/
def nasalSubRate : NasalSubInput → ℚ
  | .mang_b => 916 / 1000  -- 0.916
  | .mang_k => 993 / 1000  -- 0.993
  | .pang_b => 434 / 1000  -- 0.434
  | .pang_k => 909 / 1000  -- 0.909

/-! ## § 6: Across-the-Board Consistency -/

/-- **Across-the-board consistency**: one dimension's effect has the same
    sign regardless of the other dimension's value. Formally: the product
    of row-wise rate differences across columns is positive (same sign). -/
def ConsistentOrdering (r : Square ℚ) : Prop :=
  (r.tl - r.bl) * (r.tr - r.br) > 0

/-- Tagalog nasal substitution rates exhibit across-the-board consistency:
    maŋ- prefixes have higher substitution than paŋ- prefixes for both
    voiced (/b/) and voiceless (/k/) stem-initial consonants. -/
theorem tagalog_consistent_ordering :
    ConsistentOrdering
      { tl := nasalSubRate .mang_b   -- 0.916
        tr := nasalSubRate .mang_k   -- 0.993
        bl := nasalSubRate .pang_b   -- 0.434
        br := nasalSubRate .pang_k } -- 0.909
    := by
  simp only [ConsistentOrdering, nasalSubRate]; norm_num

/-! ## § 7: Decision-Tree Models Fail -/

/-- **Decision-tree models predict monotonic differentiation**:
    In a multiplicative model `P(x,y) = g(x) · h(y)`, the difference
    between two h-values is *proportional* to g:

      `g(x) · h(y₂) - g(x) · h(y₁) = g(x) · (h(y₂) - h(y₁))`

    So at the floor (g → 0), all h-differences vanish, and at the
    ceiling (g → 1), h-differences are maximal. Differences grow
    **monotonically** from floor to ceiling.

    This is the "claws" pattern: pinching at one end
    only. In contrast, MaxEnt predicts humped differentiation: sigmoid
    families compressed at *both* extremes — the observed pattern. -/
theorem decision_tree_monotonic_diff (g₁ g₂ h₁ h₂ : ℚ)
    (hg : g₁ < g₂)
    (hh : h₁ < h₂) :
    g₁ * h₂ - g₁ * h₁ < g₂ * h₂ - g₂ * h₁ := by
  have key : g₁ * (h₂ - h₁) < g₂ * (h₂ - h₁) :=
    mul_lt_mul_of_pos_right hg (by linarith)
  linarith [mul_sub g₁ h₂ h₁, mul_sub g₂ h₂ h₁]

/-- In a multiplicative model, the ratio of differences across two
    g-values exactly equals the ratio of those g-values.
    Cross-multiplied form (avoids division): -/
theorem decision_tree_diff_proportional (g₁ g₂ h₁ h₂ : ℚ) :
    (g₂ * h₂ - g₂ * h₁) * g₁ = (g₁ * h₂ - g₁ * h₁) * g₂ := by ring

/-- **Decision-tree ceiling bound**: in a multiplicative model with both
    factors in [0,1], the product is bounded above by both factors.

    This is the mathematical core of why decision trees produce "claws"
    instead of sigmoid families: probabilities can never exceed either
    component probability. At the floor (g → 0), all products vanish
    regardless of h — explaining the pinch at one end. But at the
    ceiling (g → 1), differences are preserved — so there is NO
    compression at the top. MaxEnt, by contrast, compresses at BOTH
    extremes via the sigmoid function `1/(1 + eⁿ)`. -/
theorem decision_tree_product_bound (g h : ℚ)
    (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    g * h ≤ g ∧ g * h ≤ h :=
  ⟨mul_le_of_le_one_right hg hh1, mul_le_of_le_one_left hh hg1⟩

/-! ## § 8: Model Comparison (Table 7, Table 17) -/

-- Log likelihoods from Z&H Table 7 (Tagalog) and Table 17 (French).
-- Closer to 0 is better. The paper's central empirical argument is
-- that BOTH harmonic grammar variants succeed (MaxEnt AND Noisy HG)
-- while ALL ranking-based models fail.

/-- MaxEnt achieves the best fit for Tagalog (Table 7). -/
theorem tagalog_maxent_best :
    (-28482 : ℚ) / 100 > -29231 / 100 ∧   -- ME > Decision tree
    (-28482 : ℚ) / 100 > -29448 / 100 ∧   -- ME > Noisy HG
    (-28482 : ℚ) / 100 > -31464 / 100 ∧   -- ME > Stochastic OT
    (-28482 : ℚ) / 100 > -64572 / 100     -- ME > Stratified OT
    := by constructor <;> norm_num

/-- Both HG variants beat both ranking models for Tagalog (Table 7).
    This is the paper's core claim: constraint weighting consistently
    outperforms constraint ranking. -/
theorem tagalog_hg_beats_ranking :
    (-29448 : ℚ) / 100 > -31464 / 100 ∧   -- NHG > Stochastic OT
    (-29448 : ℚ) / 100 > -64572 / 100     -- NHG > Stratified OT
    := by constructor <;> norm_num

/-- MaxEnt and Noisy HG achieve the best fits for French (Table 17). -/
theorem french_maxent_best :
    (-19771 : ℚ) / 100 > -19880 / 100 ∧   -- ME > Noisy HG
    (-19771 : ℚ) / 100 > -20795 / 100 ∧   -- ME > Decision tree
    (-19771 : ℚ) / 100 > -23361 / 100 ∧   -- ME > Stochastic OT
    (-19771 : ℚ) / 100 > -41064 / 100     -- ME > Stratified OT
    := by constructor <;> norm_num

/-- Both HG variants beat both ranking models for French (Table 17). -/
theorem french_hg_beats_ranking :
    (-19880 : ℚ) / 100 > -23361 / 100 ∧   -- NHG > Stochastic OT
    (-19880 : ℚ) / 100 > -41064 / 100     -- NHG > Stratified OT
    := by constructor <;> norm_num

/-! ## § 9: MaxEnt Predicts the Sigmoid Family Pattern -/

/-- **MaxEnt predicts HZ's generalization for Tagalog nasal substitution**:
    for *any* weight assignment `w : Fin 6 → ℝ`, the MaxEnt logit rates
    satisfy the constant-difference identity.

    `LR(/maŋb/) − LR(/maŋk/) = LR(/paŋb/) − LR(/paŋk/)`

    The proof instantiates `me_predicts_hz` (Separability.lean) with the
    Tagalog violation differences and their independence. -/
theorem maxent_predicts_hz_tagalog (w : Fin 6 → ℝ) :
    ConstantLogitDiff
      (fun x => ∑ k : Fin 6, w k * deltaR k x)
      nasalSubSquare :=
  me_predicts_hz w deltaR nasalSubSquare violDiff_independence

/-! ## § 10: Closed-Form Logit-Rate Difference -/

/-- The constant logit-rate difference equals `−w₂ + w₃ + w₄`
    for both rows, regardless of weights. This follows from the
    insensitivity structure of the six constraints: markedness
    constraints (C₁–C₄) are insensitive to prefix, so their
    contributions cancel in the row difference, while faithfulness
    constraints (C₅–C₆) are insensitive to stem consonant, so they
    cancel in the column difference. -/
theorem hz_constant_value_tagalog (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    -w 1 + w 2 + w 3 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

theorem hz_constant_value_tagalog' (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) =
    -w 1 + w 2 + w 3 := by
  simp only [Fin.sum_univ_six, violDiffProfile]; ring

/-- The HZ identity verified concretely: both row-differences are equal. -/
theorem hz_identity_concrete (w : Fin 6 → ℚ) :
    (∑ k : Fin 6, w k * violDiffProfile k .mang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .mang_k : ℚ) =
    (∑ k : Fin 6, w k * violDiffProfile k .pang_b : ℚ) -
    (∑ k : Fin 6, w k * violDiffProfile k .pang_k : ℚ) := by
  rw [hz_constant_value_tagalog, hz_constant_value_tagalog']

/-! ## § 11: NHG Produces Consistent Ordering -/

/-- **NHG produces consistent ordering** (@cite{zuraw-hayes-2017}):
    when the harmony scores satisfy `ConstantLogitDiff`, NHG
    probabilities `Φ(d(x)/σ)` exhibit across-the-board consistency.

    Composes `constantLogitDiff_mono_consistent` (CLD + strict monotonicity
    ⟹ consistent ordering) with `normalCDF_strictMono`. Since
    `x ↦ Φ(x/σ)` is strictly monotone for `σ > 0`, the result follows.
    This is the formal version of Z&H's argument that NHG produces sigmoid
    families (not claws) because the normal CDF compresses at both
    extremes. -/
theorem nhg_consistent_ordering {X : Type} (d : X → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (sq : Square X)
    (hcld : ConstantLogitDiff d sq)
    (hne : d sq.tl ≠ d sq.bl) :
    (Core.normalCDF (d sq.tl / σ) - Core.normalCDF (d sq.bl / σ)) *
    (Core.normalCDF (d sq.tr / σ) - Core.normalCDF (d sq.br / σ)) > 0 :=
  constantLogitDiff_mono_consistent d (fun x => Core.normalCDF (x / σ))
    (Core.normalCDF_strictMono.comp (fun _ _ h => (div_lt_div_iff_of_pos_right hσ).mpr h))
    sq hcld hne

/-- **NHG predicts consistent ordering for Tagalog nasal substitution**:
    for any weight assignment and noise level, the NHG probabilities of
    nasal substitution exhibit across-the-board consistency whenever the
    mang- and pang- prefixes have different logit rates for b-initial stems.

    End-to-end chain: Tagalog violation differences →
    `violDiff_independence` → `maxent_predicts_hz_tagalog` (CLD) →
    `nhg_consistent_ordering` (CDF monotonicity) → consistent ordering. -/
theorem nhg_tagalog_consistent (w : Fin 6 → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hne : (∑ k : Fin 6, w k * deltaR k .mang_b) ≠
           (∑ k : Fin 6, w k * deltaR k .pang_b)) :
    (Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .mang_b) / σ) -
     Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .pang_b) / σ)) *
    (Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .mang_k) / σ) -
     Core.normalCDF ((∑ k : Fin 6, w k * deltaR k .pang_k) / σ)) > 0 :=
  nhg_consistent_ordering (fun x => ∑ k : Fin 6, w k * deltaR k x)
    σ hσ nasalSubSquare (maxent_predicts_hz_tagalog w) hne

/-! ## § 12: Cross-Reference to Zuraw 2010

Z&H §2.4 says their constraint set is "adapted from Zuraw 2010". The
projection-based defs in § 3 make that adaptation precise: 4 of 6
constraints are literally `comap`'d from Zuraw, so equality with
Zuraw's constraints under projection holds by definition. The 2 prefix-
indexed UNIFORMITY constraints replace Zuraw's single \*ASSOC — but they
turn out to be a *decomposition* of \*ASSOC on this restricted square,
not a substitution by something incompatible.
-/

/-- C₁ = NasSub agrees with Zuraw 2010 under the candidate projection.
    Holds by definition (`comap` is `eval ∘ project` and `nasSub` is
    defined as `Zuraw2010.nasSub.comap NasalSubCandidate.project`). -/
theorem nasSub_eq_zuraw_under_projection :
    nasSub.eval = Zuraw2010.nasSub.eval ∘ NasalSubCandidate.project := rfl

/-- C₂ = \*NC agrees with Zuraw 2010 under the projection. -/
theorem starNC_eq_zuraw_under_projection :
    starNC.eval = Zuraw2010.starNC.eval ∘ NasalSubCandidate.project := rfl

/-- C₃ = \*[stemŋ] agrees with Zuraw's `starInitVelar` under the projection. -/
theorem starStemVelar_eq_zuraw_under_projection :
    starStemVelar.eval = Zuraw2010.starInitVelar.eval ∘ NasalSubCandidate.project := rfl

/-- C₄ = \*[stemŋ]/n agrees with Zuraw's `starInitCorVel` under the projection. -/
theorem starStemVelarCoronal_eq_zuraw_under_projection :
    starStemVelarCoronal.eval = Zuraw2010.starInitCorVel.eval ∘ NasalSubCandidate.project := rfl

/-- **Cross-paper structural insight**: Z&H's prefix-indexed UNIFORMITY pair
    (`unifMang + unifPang`) is an additive *decomposition* of Zuraw 2010's
    single \*ASSOC constraint on this 2×2 sub-square.

    Zuraw's \*ASSOC fires on every YES candidate (penalty 1) regardless of
    prefix. Z&H's `unifMang` fires on YES only for maŋ-other inputs;
    `unifPang` fires on YES only for paŋ-res inputs. On the 2×2 square,
    every YES cell is hit by exactly one of them, so their sum equals
    Zuraw's \*ASSOC under the candidate projection. Under any HG/ME
    analysis, the sum of the two prefix-UNIF weights `w₅ + w₆` plays the
    role Zuraw's single \*ASSOC weight plays in her grammar. -/
theorem unif_sum_eq_assoc (c : NasalSubCandidate) :
    unifMang.eval c + unifPang.eval c =
    Zuraw2010.starAssoc.eval (NasalSubCandidate.project c) := by
  rcases c with ⟨i, o⟩
  cases i <;> cases o <;> decide

end ZurawHayes2017
