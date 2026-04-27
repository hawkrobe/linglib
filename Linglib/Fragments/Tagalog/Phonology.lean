import Linglib.Core.Constraint.Separability

/-!
# Tagalog Nasal Substitution Data @cite{zuraw-2010}

Empirical data for Tagalog nasal substitution (@cite{zuraw-2010}),
the running case study in @cite{magri-2025}'s analysis of constraint
interaction in probabilistic phonology.

## The process

When a nasal-final prefix (maŋ- or paŋ-) is concatenated with an
obstruent-initial stem, the nasal and the obstruent may **coalesce** into
a single consonant retaining the nasality of the former and the place of
the latter (@cite{zuraw-2010}):

- `maŋ+bigáj` → `mamigáj` 'to distribute' (nasal substitution)
- `paŋ+tabój` → `pantabój` 'to goad' (place assimilation, no substitution)

## Data organization

This Fragment houses **two distinct formal setups** for the same empirical
phenomenon, addressing different theoretical questions:

- **§ 1–2: @cite{zuraw-2010} setup** — `StemC` (six stem-initial obstruents:
  p, t, k, b, d, g) × `SubSt` (yes/no substitution). Used by
  `Phenomena/Phonology/Studies/Zuraw2010.lean` for the factorial typology
  analysis (720 rankings → 10 distinct patterns + per-consonant percentages).
- **§ 3–7: @cite{magri-2025} 2×2 square setup** — `NasalSubInput` (four
  underlying concatenations: maŋ/paŋ × b/k) × `NasalSubOutput`. Used by
  `Phenomena/Phonology/Studies/Magri2025.lean` for the MaxEnt-on-square
  analysis (Hayes-Zuraw shifted-sigmoids generalization).

The two setups are **complementary, not redundant**. They share data
(both encode Zuraw's empirical claims about Tagalog) but differ in formal
structure: the Zuraw setup is wider (6 stems, no prefix dimension), the
Magri setup is narrower (only b, k stems) but adds the maŋ/paŋ prefix
dimension needed for the 2×2 square. The constraint sets also differ —
Zuraw's analysis uses the stringent *\[N hierarchy + *ASSOC; Magri's
analysis uses prefix-specific UNIFORMITY constraints. Neither is wrong
relative to Zuraw 2010; they're picking out different sub-phenomena.

Cross-reference theorem `magri_input_corresponds_to_stem` (§7) makes the
overlap explicit at the data level: each `NasalSubInput` projects to the
corresponding `StemC` (b or k) in Zuraw's encoding.
-/

open Core.Constraint

namespace Fragments.Tagalog.Phonology

-- ============================================================================
-- § 1: Stem Consonants (@cite{zuraw-2010})
-- ============================================================================

/-- The six stem-initial obstruents in the nasal substitution typology.
    Coalescence maps each to its homorganic nasal: p→m, t→n, k→ŋ,
    b→m, d→n, g→ŋ. -/
inductive StemC where
  | p | t | k   -- voiceless
  | b | d | g   -- voiced
  deriving DecidableEq, Repr

/-- Whether nasal substitution applies. -/
inductive SubSt where
  | yes  -- coalescence: nasal + obstruent → nasal
  | no   -- faithful: nasal cluster preserved
  deriving DecidableEq, Repr

/-- A candidate is a stem consonant paired with a substitution decision. -/
abbrev NSCand := StemC × SubSt

-- ============================================================================
-- § 2: Dictionary Rates (@cite{zuraw-2010})
-- ============================================================================

/-- Dictionary substitution rate for voiceless labial p (253/263 ≈ 96.2%).
    Text-verified from @cite{zuraw-2010}'s discussion of the Tagalog
    dictionary study. -/
def dictRate_p : ℚ := 253 / 263

/-- Dictionary substitution rate for voiced labial b (177/277 ≈ 63.9%).
    Text-verified from @cite{zuraw-2010}'s discussion of the Tagalog
    dictionary study. -/
def dictRate_b : ℚ := 177 / 277

/-- **Voicing effect in dictionary data** (labial place): voiceless p
    has a higher substitution rate than voiced b. -/
theorem dict_voicing_labial : dictRate_p > dictRate_b := by native_decide

-- ============================================================================
-- § 3: 2×2 Square — Underlying Forms (@cite{magri-2025})
-- ============================================================================

/-- The four underlying concatenations from @cite{magri-2025}'s
    2×2 square arrangement. These cross two prefixes (maŋ-, paŋ-)
    with two of the six stem consonants (b, k). -/
inductive NasalSubInput where
  | mang_b  -- /maŋ+b/  (top-left)
  | mang_k  -- /maŋ+k/  (top-right)
  | pang_b  -- /paŋ+b/  (bottom-left)
  | pang_k  -- /paŋ+k/  (bottom-right)
  deriving DecidableEq, Repr

/-- The two surface variants for each underlying form. -/
inductive NasalSubOutput where
  /-- YES: nasal substitution applies — nasal and obstruent coalesce. -/
  | yes
  /-- NO: nasal substitution does not apply — place assimilation only. -/
  | no
  deriving DecidableEq, Repr

instance : Fintype NasalSubInput where
  elems := {.mang_b, .mang_k, .pang_b, .pang_k}
  complete := fun x => by cases x <;> simp

instance : Fintype NasalSubOutput where
  elems := {.yes, .no}
  complete := fun x => by cases x <;> simp

/-- Input–output pair for constraint evaluation. -/
abbrev NasalSubCandidate := NasalSubInput × NasalSubOutput

-- ============================================================================
-- § 4: The Square
-- ============================================================================

/-- The 2×2 square of underlying forms: prefix × stem-initial obstruent. -/
def nasalSubSquare : Square NasalSubInput where
  tl := .mang_b
  tr := .mang_k
  bl := .pang_b
  br := .pang_k

-- ============================================================================
-- § 5: Constraint Violation Profiles
-- ============================================================================

/-- C₁ = DEP-C: one violation per surface segment without an input
    correspondent. Violated by NO (the faithful candidate keeps the
    cluster — the YES candidate's coalesced nasal has no input pair).
    Per @cite{zuraw-2010} (16): "DEP-C is violated by non-substitution".
    NB: previously labeled \*NC in earlier commits; renamed for fidelity
    to the paper, where \*NC is reserved for the voiceless-only constraint
    (see `starNC` below). -/
def depC : NasalSubCandidate → ℕ
  | (_, .no) => 1
  | (_, .yes) => 0

/-- C₂ = \*NC: one violation for nasal followed by voiceless obstruent.
    Violated by NO only for voiceless stems (k). Per @cite{zuraw-2010}
    (17): "*NC: A [+nasal] segment must not be immediately followed by
    a [-voice, -sonorant] segment". -/
def starNC : NasalSubCandidate → ℕ
  | (.mang_k, .no) | (.pang_k, .no) => 1
  | _ => 0

/-- C₃ = *[stemη]: one violation when stem starts with a velar nasal.
    Violated by YES for k-initial stems (coalesced ŋ is velar). -/
def starStemVelar : NasalSubCandidate → ℕ
  | (.mang_k, .yes) | (.pang_k, .yes) => 1
  | _ => 0

/-- C₄ = *[stemη]∕n: one violation when stem starts with a velar or
    coronal nasal. In the b vs k square, this coincides with C₃
    (bilabial m is neither velar nor coronal). -/
def starStemVelarCoronal : NasalSubCandidate → ℕ
  | (.mang_k, .yes) | (.pang_k, .yes) => 1
  | _ => 0

/-- C₅ = UNIFORMITY(maŋ): one violation when the maŋ- prefix coalesces
    with the stem-initial obstruent. Only relevant for maŋ- forms. -/
def unifMang : NasalSubCandidate → ℕ
  | (.mang_b, .yes) | (.mang_k, .yes) => 1
  | _ => 0

/-- C₆ = UNIFORMITY(paŋ): one violation when the paŋ- prefix coalesces.
    Only relevant for paŋ- forms. -/
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

-- ============================================================================
-- § 6: Violation Differences (Δₖ)
-- ============================================================================

/-- Violation difference `Δₖ(x) = Cₖ(x, NO) − Cₖ(x, YES)` for each
    underlying form x and constraint k. Positive Δ favors YES. -/
def violDiffProfile : Fin 6 → NasalSubInput → ℤ
  -- C₁ = *NC: Δ₁ = 1 for all forms (NO always has NC)
  | ⟨0, _⟩, _ => 1
  -- C₂ = *NC̥: Δ₂ = 1 for /k/ forms, 0 for /b/ forms
  | ⟨1, _⟩, .mang_k | ⟨1, _⟩, .pang_k => 1
  | ⟨1, _⟩, _ => 0
  -- C₃ = *[stem]: Δ₃ = −1 for /k/ forms (YES has velar nasal), 0 for /b/
  | ⟨2, _⟩, .mang_k | ⟨2, _⟩, .pang_k => -1
  | ⟨2, _⟩, _ => 0
  -- C₄ = *[stem]/n: same as C₃ in the /b/ vs /k/ case
  | ⟨3, _⟩, .mang_k | ⟨3, _⟩, .pang_k => -1
  | ⟨3, _⟩, _ => 0
  -- C₅ = UNIF(maŋ): Δ₅ = −1 for /maŋ/ forms, 0 for /paŋ/
  | ⟨4, _⟩, .mang_b | ⟨4, _⟩, .mang_k => -1
  | ⟨4, _⟩, _ => 0
  -- C₆ = UNIF(paŋ): Δ₆ = −1 for /paŋ/ forms, 0 for /maŋ/
  | ⟨5, _⟩, .pang_b | ⟨5, _⟩, .pang_k => -1
  | ⟨5, _⟩, _ => 0

-- ============================================================================
-- § 7: Empirical Rates (2×2 square)
-- ============================================================================

/-- Empirical rates of nasal substitution from @cite{zuraw-2010} type
    frequencies, arranged per @cite{magri-2025}'s 2×2 square
    (@cite{zuraw-hayes-2017}). The four cells correspond to the two
    extreme prefixes (maŋ-other = highest rate, paŋ-res = lowest)
    crossed with /b/ (voiced) and /k/ (voiceless). -/
def nasalSubRate : NasalSubInput → ℚ
  | .mang_b => 916 / 1000  -- 0.916
  | .mang_k => 993 / 1000  -- 0.993
  | .pang_b => 434 / 1000  -- 0.434
  | .pang_k => 909 / 1000  -- 0.909

-- ============================================================================
-- § 8: Violation Difference Independence
-- ============================================================================

/-- The violation differences cast to ℝ, for use with `me_predicts_hz`. -/
def deltaR : Fin 6 → NasalSubInput → ℝ :=
  fun k x => (violDiffProfile k x : ℝ)

/-- **Violation difference independence**: the violation differences Δₖ
    satisfy `ViolDiffIndependence` on the nasal substitution square.

    - C₁–C₄ (markedness): Δₖ is the same for /maŋ+X/ and /paŋ+X/
      (insensitive to prefix = row)
    - C₅–C₆ (faithfulness): Δₖ is the same for /X+b/ and /X+k/
      (insensitive to stem = column)

    This is a data-level property of the constraint violation profiles,
    used by both @cite{zuraw-hayes-2017} and @cite{magri-2025}. -/
theorem violDiff_independence :
    ViolDiffIndependence deltaR nasalSubSquare := by
  intro k
  simp only [deltaR, violDiffProfile, nasalSubSquare]
  fin_cases k <;> simp

-- ============================================================================
-- § 9: Cross-reference — Magri's `NasalSubInput` ↔ Zuraw's `StemC`
-- ============================================================================

/-- Project a Magri 2025 input (maŋ/paŋ × b/k) to its Zuraw 2010 stem
    consonant. The prefix dimension is collapsed; the stem dimension is
    preserved. -/
def NasalSubInput.toStemC : NasalSubInput → StemC
  | .mang_b => .b
  | .pang_b => .b
  | .mang_k => .k
  | .pang_k => .k

/-- The four Magri inputs project onto exactly the two Zuraw stems
    relevant to the 2×2 square: `b` and `k`. The Magri analysis is a
    **prefix-aware narrowing** of the Zuraw factorial typology to the
    voicing-contrast subset {b, k}. -/
theorem magri_input_corresponds_to_stem :
    (Finset.univ : Finset NasalSubInput).image NasalSubInput.toStemC =
    ({StemC.b, StemC.k} : Finset StemC) := by
  decide

end Fragments.Tagalog.Phonology
