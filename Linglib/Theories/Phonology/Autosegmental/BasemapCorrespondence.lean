import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone
import Linglib.Core.Logic.OT

/-!
# Matrix-Basemap Correspondence (MxBM-C)
@cite{rolle-2018} @cite{benua-1997}

Matrix-Basemap Correspondence is @cite{rolle-2018}'s central theoretical
contribution (Ch 5). It extends Output-Output Correspondence
(@cite{benua-1997}) to explain **dominant grammatical tone** as a special
type of faithfulness rather than markedness.

## The three problems

Any theory of dominant vs. non-dominant GT must address:
1. **Origin problem**: where does the grammatical tune come from?
2. **Erasure problem**: why do the target's underlying tones go unrealized?
3. **Scope problem**: what determines the domain of the GT operation?

MxBM-C addresses the erasure problem. The origin problem is solved by
floating tone representation (the tune is part of the trigger's UR);
the scope problem by CoP-scope (`CoPScope.lean`).

## Key insight: dominance as transparadigmatic uniformity

A **basemap** is an abstract I/O mapping derived from a "deficient
projection" of the input: all valued (lexical) tones on the target
are stripped, leaving only floating (grammatical) tones. The basemap
output shows what the form would look like if the target had no
underlying tones.

**Dominant GT** = faithfulness to the basemap output. The matrix
(actual) output must correspond to the basemap output. Since the
basemap has no valued tones to preserve, its output is determined
entirely by the grammatical tune. The matrix output must match,
so the target's underlying tones are forced to go unrealized.

**Non-dominant GT** = no basemap faithfulness. The matrix output
is determined by the default constraint ranking, which may preserve
underlying tones.

## Connection to `tonalOverwrite`

`tonalOverwrite` in `GrammaticalTone.lean` directly implements the
computational result of replacive-dominant GT. Under MxBM-C, this
result *emerges* from basemap faithfulness: `tonalOverwrite_basemap_faithful`
proves that the overwrite function produces the same tonal output as
basemap-faithful evaluation.
-/

namespace Theories.Phonology.Autosegmental.BasemapCorrespondence

open Theories.Phonology.Autosegmental.GrammaticalTone
open Theories.Phonology.Autosegmental.RegisterTier (ToneFeature)
open Core.OT (NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: Basemap — Deficient Projection
-- ============================================================================

/-- Strip all tones from a host word, replacing them with a default tone.
    This is the **deficient projection** of @cite{rolle-2018} Ch 5:
    the input with all valued (lexical) tones removed, leaving only the
    segmental skeleton ready to receive floating (grammatical) tones.

    The `defaultTone` is the tone assigned to "unvalued" TBUs —
    language-specific (often L in African tone languages). -/
def deficientProjection {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (defaultTone : ToneFeature) : List (TBU S) :=
  host.map (λ tbu => { tbu with tone := defaultTone })

/-- Deficient projection produces uniform tone: every TBU gets the
    default tone. -/
theorem deficientProjection_uniform {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (defaultTone : ToneFeature) :
    (deficientProjection host defaultTone).map TBU.tone =
    host.map (λ _ => defaultTone) := by
  simp [deficientProjection, List.map_map]

-- ============================================================================
-- § 2: Basemap Output
-- ============================================================================

/-- Compute the basemap output: apply the grammatical tune to the
    deficient projection. This represents what the output would look
    like if the target had no underlying tones — only the floating
    tones from the trigger determine the surface pattern.

    For replacive-dominant GT with a whole-word melody, the basemap
    output has the grammatical tune on every TBU. -/
def basemapOutput {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (spec : Spec)
    (defaultTone : ToneFeature) : List (TBU S) :=
  tonalOverwrite (deficientProjection host defaultTone) spec

-- ============================================================================
-- § 3: Tonal Tier Extraction
-- ============================================================================

/-- Extract the tonal tier from a list of TBUs. -/
def tonalTier {S : Type} (tbus : List (TBU S)) : List ToneFeature :=
  tbus.map TBU.tone

-- ============================================================================
-- § 4: Matrix-Basemap Correspondence Constraint
-- ============================================================================

/-- Count violations of Matrix-Basemap Correspondence: the number of
    positions where two tonal tiers differ.

    In @cite{rolle-2018}'s analysis, dominant GT triggers have a
    cophonology that ranks this constraint high — forcing the matrix
    output to match the basemap, which erases the target's underlying
    tones. Non-dominant triggers leave this constraint low-ranked,
    so underlying tones can surface. -/
def basemapViolations (tier₁ tier₂ : List ToneFeature) : Nat :=
  (tier₁.zip tier₂).foldl
    (λ count (m, b) => if m == b then count else count + 1) 0

/-- Basemap violations on empty tiers is zero. -/
theorem basemapViolations_nil : basemapViolations [] [] = 0 := rfl

/-- The fold accumulator in `basemapViolations` never decreases. -/
private theorem foldl_mismatch_mono
    (pairs : List (ToneFeature × ToneFeature)) (acc : Nat) :
    (pairs.foldl (λ count (m, b) => if m == b then count else count + 1) acc) ≥ acc := by
  induction pairs generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have h_step : (if p.1 == p.2 then acc else acc + 1) ≥ acc := by
      split <;> omega
    exact Nat.le_trans h_step (ih _)

/-- Removing matching heads doesn't change violation count. -/
private theorem basemapViolations_cons_eq (x : ToneFeature) (xs ys : List ToneFeature) :
    basemapViolations (x :: xs) (x :: ys) = basemapViolations xs ys := by
  unfold basemapViolations
  rw [List.zip_cons_cons, List.foldl_cons]
  congr 1
  cases x <;> rfl

/-- Mismatching heads contribute at least one violation. -/
private theorem basemapViolations_cons_ne (x y : ToneFeature) (xs ys : List ToneFeature)
    (hne : x ≠ y) :
    basemapViolations (x :: xs) (y :: ys) ≥ 1 := by
  unfold basemapViolations
  rw [List.zip_cons_cons, List.foldl_cons]
  have : ∀ (acc : Nat), acc ≥ 1 →
      (xs.zip ys).foldl (λ count (m, b) => if m == b then count else count + 1) acc ≥ 1 :=
    fun acc hacc => Nat.le_trans hacc (foldl_mismatch_mono _ _)
  apply this
  cases x <;> cases y <;> (first | exact absurd rfl hne | decide)

/-- Self-comparison has zero basemap violations: a tonal tier is
    perfectly faithful to itself. -/
theorem basemapViolations_self_eq_zero (t : List ToneFeature) :
    basemapViolations t t = 0 := by
  induction t with
  | nil => rfl
  | cons x xs ih =>
    rw [basemapViolations_cons_eq]
    exact ih

/-- Zero basemap violations with equal-length tiers implies the tiers
    are identical.

    This is the inverse of `basemapViolations_self_eq_zero`: if two
    tiers of the same length have no mismatches, they must be equal
    element-by-element. The equal-length hypothesis is necessary because
    `List.zip` silently drops elements from the longer list. -/
theorem basemapViolations_eq_zero_imp
    (t₁ t₂ : List ToneFeature) (hLen : t₁.length = t₂.length)
    (hZero : basemapViolations t₁ t₂ = 0) : t₁ = t₂ := by
  induction t₁ generalizing t₂ with
  | nil =>
    cases t₂ with
    | nil => rfl
    | cons _ _ => simp at hLen
  | cons x xs ih =>
    cases t₂ with
    | nil => simp at hLen
    | cons y ys =>
      have hLen' : xs.length = ys.length := by simpa using hLen
      have hxy : x = y := by
        rcases Decidable.em (x = y) with rfl | hne
        · rfl
        · exact absurd hZero (by have := basemapViolations_cons_ne x y xs ys hne; omega)
      rw [hxy] at hZero
      rw [basemapViolations_cons_eq] at hZero
      rw [hxy]
      exact congrArg (y :: ·) (ih ys hLen' hZero)

/-- Wrap `basemapViolations` as a `NamedConstraint` for use in OT
    tableaux and cophonological evaluation.

    Given a fixed basemap output (the tonal tier of the basemap-faithful
    form), this constraint evaluates each candidate by comparing its
    tonal tier against the basemap. In @cite{rolle-2018}'s analysis,
    dominant triggers promote this constraint above default markedness
    in their cophonology's subranking.

    `extractTier` converts a candidate to its tonal tier for comparison.
    This allows the constraint to work with any candidate type, not
    just raw `List ToneFeature`. -/
def mkBasemapConstraint {C : Type}
    (basemapTier : List ToneFeature)
    (extractTier : C → List ToneFeature) : NamedConstraint C :=
  { name := "BM-FAITH"
  , family := .faithfulness
  , eval := λ c => basemapViolations (extractTier c) basemapTier }

-- ============================================================================
-- § 5: Dominance as Basemap Faithfulness
-- ============================================================================

/-- Helper: whole-word tonalOverwrite reduces to map. -/
private theorem tonalOverwrite_whole_eq_map {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t : ToneFeature) :
    tonalOverwrite host ⟨"", [t], .whole⟩ =
    host.map (λ tbu => { tbu with tone := t }) := rfl

/-- Helper: whole-word tonalOverwrite tonal tier is constant. -/
private theorem tonalTier_overwrite_whole {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t : ToneFeature) :
    tonalTier (tonalOverwrite host ⟨"", [t], .whole⟩) =
    host.map (λ _ => t) := by
  simp [tonalTier, tonalOverwrite, List.map_map]

/-- The central theorem of MxBM-C: for replacive-dominant GT with a
    whole-word single-tone melody, the matrix output's tonal tier
    equals the basemap output's tonal tier.

    This captures @cite{rolle-2018}'s key insight: dominant GT is not
    a special deletion rule or markedness constraint, but faithfulness
    to an abstract basemap. The target's underlying tones go unrealized
    because the output must match what would happen if those tones
    were never there.

    Both `tonalOverwrite host spec` and `basemapOutput host spec dt`
    produce the tonal tier `[t, t, ..., t]` when `spec` has a
    whole-word single-tone melody `[t]`, because `tonalOverwrite`
    replaces all tones regardless of input — and the basemap's
    deficient projection changes input tones before the same overwrite. -/
theorem tonalOverwrite_basemap_faithful {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t : ToneFeature) (defaultTone : ToneFeature) :
    let spec : Spec := ⟨"", [t], .whole⟩
    tonalTier (tonalOverwrite host spec) =
    tonalTier (basemapOutput host spec defaultTone) := by
  simp only [tonalTier, basemapOutput, deficientProjection]
  rw [tonalOverwrite_whole_eq_map, tonalOverwrite_whole_eq_map]
  simp only [List.map_map]
  congr 1

/-- The basemap output's tonal tier is independent of the host's
    underlying tones: for whole-word replacement, two hosts with
    different lexical tones but identical segmental content produce
    the same basemap tonal tier.

    This is the formal content of "transparadigmatic uniformity"
    (@cite{rolle-2018} Ch 5): the basemap abstracts away from the
    paradigmatic tonal variation of the target. -/
theorem basemapOutput_tone_independent_whole {S : Type} [DecidableEq S] [BEq S] [Repr S]
    (host₁ host₂ : List (TBU S)) (t defaultTone : ToneFeature)
    (hLen : host₁.length = host₂.length) :
    let spec : Spec := ⟨"", [t], .whole⟩
    tonalTier (basemapOutput host₁ spec defaultTone) =
    tonalTier (basemapOutput host₂ spec defaultTone) := by
  simp only [tonalTier, basemapOutput, deficientProjection]
  rw [tonalOverwrite_whole_eq_map, tonalOverwrite_whole_eq_map]
  simp only [List.map_map]
  -- Both sides reduce to host.map (f ∘ g ∘ ...), where f ∘ g ∘ ... = (λ _ => t).
  -- Constant maps over lists of equal length produce equal lists.
  have mapConst : ∀ (xs : List (TBU S)),
      List.map (TBU.tone ∘ (λ tbu : TBU S => { tbu with tone := t }) ∘
        λ tbu : TBU S => { tbu with tone := defaultTone }) xs =
      List.replicate xs.length t := by
    intro xs; induction xs with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, Function.comp, List.length_cons,
                                 List.replicate_succ]; exact congrArg _ ih
  rw [mapConst, mapConst, hLen]

end Theories.Phonology.Autosegmental.BasemapCorrespondence
