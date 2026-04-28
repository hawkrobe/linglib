import Linglib.Core.Constraint.Separability

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

open Core.Constraint

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

/-! ## § 2: Constraint Violation Profiles -/

/-- C₁ = DEP-C: one violation per surface segment without an input
    correspondent. Violated by NO (the faithful candidate keeps the
    cluster — the YES candidate's coalesced nasal has no input pair).
    Following @cite{zuraw-2010}'s discussion of DEP-C as the constraint
    violated by non-substitution. -/
def depC : NasalSubCandidate → ℕ
  | (_, .no) => 1
  | (_, .yes) => 0

/-- C₂ = \*NC: one violation for nasal followed by voiceless obstruent.
    Violated by NO only for voiceless stems (k). Per @cite{zuraw-2010}
    (17): "\*NC: A [+nasal] segment must not be immediately followed by
    a [-voice, -sonorant] segment". -/
def starNC : NasalSubCandidate → ℕ
  | (.mang_k, .no) | (.pang_k, .no) => 1
  | _ => 0

/-- C₃ = \*[stemŋ]: one violation when stem starts with a velar nasal.
    Violated by YES for k-initial stems (coalesced ŋ is velar). -/
def starStemVelar : NasalSubCandidate → ℕ
  | (.mang_k, .yes) | (.pang_k, .yes) => 1
  | _ => 0

/-- C₄ = \*[stemŋ]/n: one violation when stem starts with a velar or
    coronal nasal. In the b vs k square, this coincides with C₃
    (bilabial m is neither velar nor coronal). -/
def starStemVelarCoronal : NasalSubCandidate → ℕ
  | (.mang_k, .yes) | (.pang_k, .yes) => 1
  | _ => 0

/-- C₅ = UNIFORMITY(maŋ-other): one violation when the maŋ-other prefix
    coalesces with the stem-initial obstruent. Restriction of Z&H's
    6-way prefix-indexed UNIFORMITY constraint set to the maŋ-other
    cell. -/
def unifMang : NasalSubCandidate → ℕ
  | (.mang_b, .yes) | (.mang_k, .yes) => 1
  | _ => 0

/-- C₆ = UNIFORMITY(paŋ-res): one violation when the paŋ-res prefix
    coalesces with the stem-initial obstruent. Restriction of Z&H's
    6-way prefix-indexed UNIFORMITY constraint set to the paŋ-res
    cell. -/
def unifPang : NasalSubCandidate → ℕ
  | (.pang_b, .yes) | (.pang_k, .yes) => 1
  | _ => 0

/-- The six constraints as a `Fin 6`-indexed family. -/
def constraints : Fin 6 → NasalSubCandidate → ℕ
  | ⟨0, _⟩ => depC
  | ⟨1, _⟩ => starNC
  | ⟨2, _⟩ => starStemVelar
  | ⟨3, _⟩ => starStemVelarCoronal
  | ⟨4, _⟩ => unifMang
  | ⟨5, _⟩ => unifPang

/-! ## § 3: Violation Differences (Δₖ) -/

/-- Violation difference `Δₖ(x) = Cₖ(x, NO) − Cₖ(x, YES)` for each
    underlying form x and constraint k. Positive Δ favors YES. -/
def violDiffProfile : Fin 6 → NasalSubInput → ℤ
  -- C₁ = DEP-C: Δ₁ = 1 for all forms (NO always violates DEP-C)
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

/-! ## § 4: Empirical Rates (2×2 square) -/

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

/-! ## § 5: Across-the-Board Consistency -/

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

/-! ## § 6: Decision-Tree Models Fail -/

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

/-! ## § 7: Model Comparison (Table 7, Table 17) -/

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

/-! ## § 8: MaxEnt Predicts the Sigmoid Family Pattern -/

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

/-! ## § 9: Closed-Form Logit-Rate Difference -/

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

/-! ## § 10: NHG Produces Consistent Ordering -/

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

end ZurawHayes2017
