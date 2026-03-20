import Linglib.Theories.Phonology.HarmonicGrammar.Separability

/-!
# Tagalog Nasal Substitution Data @cite{zuraw-2010}

Empirical data for Tagalog nasal substitution, the running case study in
@cite{magri-2025}'s analysis of constraint interaction in probabilistic
phonology.

## The process

When a nasal-final prefix (maŋ- or paŋ-) is concatenated with an
obstruent-initial stem, the nasal and the obstruent may **coalesce** into
a single consonant retaining the nasality of the former and the place of
the latter (@cite{zuraw-2010}):

- `maŋ+bigáj` → `mamigáj` 'to distribute' (nasal substitution)
- `paŋ+tabój` → `pantabój` 'to goad' (place assimilation, no substitution)

## The 2×2 square

@cite{magri-2025} §2.1 arranges four underlying concatenations in a
square, with prefix identity as the row dimension and
stem-initial obstruent quality as the column dimension:

```
         b (voiced)     k (voiceless)
maŋ-     maŋb            maŋk
paŋ-     paŋb            paŋk
```

Each form has two surface variants: YES (nasal substitution applies) and
NO (place assimilation only).
-/

namespace Fragments.Tagalog.Phonology

open Theories.Phonology.HarmonicGrammar

-- ============================================================================
-- § 1: Underlying Forms
-- ============================================================================

/-- The four underlying concatenations from @cite{magri-2025}'s
    2×2 square arrangement. -/
inductive NasalSubInput where
  | mang_b  -- /maŋ+b/  (top-left)
  | mang_k  -- /maŋ+k/  (top-right)
  | pang_b  -- /paŋ+b/  (bottom-left)
  | pang_k  -- /paŋ+k/  (bottom-right)
  deriving DecidableEq, BEq, Repr

/-- The two surface variants for each underlying form. -/
inductive NasalSubOutput where
  /-- YES: nasal substitution applies — nasal and obstruent coalesce. -/
  | yes
  /-- NO: nasal substitution does not apply — place assimilation only. -/
  | no
  deriving DecidableEq, BEq, Repr

instance : Fintype NasalSubInput where
  elems := {.mang_b, .mang_k, .pang_b, .pang_k}
  complete := fun x => by cases x <;> simp

instance : Fintype NasalSubOutput where
  elems := {.yes, .no}
  complete := fun x => by cases x <;> simp

/-- Input–output pair for constraint evaluation. -/
abbrev NasalSubCandidate := NasalSubInput × NasalSubOutput

-- ============================================================================
-- § 2: The Square
-- ============================================================================

/-- The 2×2 square of underlying forms: prefix × stem-initial obstruent. -/
def nasalSubSquare : Square NasalSubInput where
  tl := .mang_b
  tr := .mang_k
  bl := .pang_b
  br := .pang_k

-- ============================================================================
-- § 3: Constraint Violation Profiles (Figure 3)
-- ============================================================================

/-- C₁ = \*NC: one violation for every nasal–obstruent sequence.
    Violated by NO (place assimilation preserves the NC sequence). -/
def starNC : NasalSubCandidate → ℕ
  | (_, .no) => 1
  | (_, .yes) => 0

/-- C₂ = \*NC̥: one violation for nasal followed by voiceless obstruent.
    Violated by NO only for voiceless stems (k). -/
def starNCvoiceless : NasalSubCandidate → ℕ
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
  | ⟨0, _⟩ => starNC
  | ⟨1, _⟩ => starNCvoiceless
  | ⟨2, _⟩ => starStemVelar
  | ⟨3, _⟩ => starStemVelarCoronal
  | ⟨4, _⟩ => unifMang
  | ⟨5, _⟩ => unifPang

-- ============================================================================
-- § 4: Violation Differences (Δₖ)
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
-- § 5: Empirical Rates
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
-- § 6: Violation Difference Independence
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

end Fragments.Tagalog.Phonology
