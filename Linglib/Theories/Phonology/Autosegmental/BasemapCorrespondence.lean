import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone
import Linglib.Theories.Phonology.Tier
import Linglib.Theories.Phonology.OptimalityTheory.Correspondence
import Linglib.Core.Constraint.OT.Basic

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

## Key insight: dominance as basemap faithfulness

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

## Connection to `Correspondence.lean`

Matrix-Basemap Correspondence is the IDENT-OO correspondence relation of
@cite{mccarthy-prince-1995} / @cite{benua-1997} specialized to the tonal
tier. `basemapViolations` is defined as `Corr.identViol` on the
`(matrix, basemap)` edge of a binary correspondence diagram between the
two tonal tiers — making the connection true by construction rather than
via a separate Hamming-distance implementation.
-/

namespace Phonology.Autosegmental.BasemapCorrespondence

open Phonology.Autosegmental.GrammaticalTone
open Phonology.Autosegmental.RegisterTier (TRN)
open Phonology.Correspondence (Corr)
open Core.Constraint.OT (NamedConstraint ConstraintFamily)

-- ============================================================================
-- § 1: Basemap — Deficient Projection
-- ============================================================================

/-- Strip all tones from a host word, replacing them with a default tone.
    The **deficient projection** of @cite{rolle-2018} Ch 5: the input with
    all valued (lexical) tones removed, leaving only the segmental skeleton
    ready to receive floating (grammatical) tones.

    The `defaultTone` is the tone assigned to "unvalued" TBUs —
    language-specific (often L in African tone languages). -/
def deficientProjection {S : Type} (host : List (TBU S)) (defaultTone : TRN) :
    List (TBU S) :=
  host.map fun tbu => { tbu with tone := defaultTone }

/-- Deficient projection produces uniform tone: every TBU gets the
    default tone. -/
theorem deficientProjection_uniform {S : Type}
    (host : List (TBU S)) (defaultTone : TRN) :
    (deficientProjection host defaultTone).map TBU.tone =
    host.map fun _ => defaultTone := by
  simp only [deficientProjection, List.map_map]; congr 1

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
    (host : List (TBU S)) (spec : Spec) (defaultTone : TRN) : List (TBU S) :=
  tonalOverwrite (deficientProjection host defaultTone) spec

-- ============================================================================
-- § 3: Tonal Tier Extraction
-- ============================================================================

/-- Extract the tonal tier from a list of TBUs.

    Grounded in the unified `Phonology.Tier` abstraction
    (`Tier.apply Tier.tonal`): an erasing string homomorphism
    `(TBU S)* → TRN*` in the Kleisli category of `Option`. The
    tonal tier is the `total` (no-erasure) case @cite{goldsmith-1976}. -/
def tonalTier {S : Type} (tbus : List (TBU S)) : List TRN :=
  Core.Tier.apply Phonology.Tier.tonal tbus

/-- The tonal tier reduces to `List.map TBU.tone` (the historical
    formulation), via `Tier.total`'s length-preservation property. -/
@[simp] theorem tonalTier_eq_map {S : Type} (tbus : List (TBU S)) :
    tonalTier tbus = tbus.map TBU.tone :=
  Phonology.Tier.apply_tonal tbus

-- ============================================================================
-- § 4: Matrix-Basemap Correspondence — derived from `Corr`
-- ============================================================================

/-- Matrix-Basemap Correspondence violation count: Hamming distance between
    the matrix tonal tier and the basemap tonal tier.

    **Derived from `Corr.identViol`** on the `(false, true)` edge of the
    binary parallel-pair correspondence between the two tiers. This
    structurally identifies MxBM-C as IDENT-OO of @cite{mccarthy-prince-1995}
    / @cite{benua-1997} specialized to the tonal tier — no separate Hamming
    implementation, no bridge theorem required.

    On unequal-length tiers, the underlying `Corr.parallel` truncates to the
    shorter prefix (matching `List.zip` semantics). -/
def basemapViolations (tier₁ tier₂ : List TRN) : Nat :=
  (Corr.parallel tier₁ tier₂).identViol .lhs .rhs

/-- Self-comparison has zero basemap violations: a tonal tier is
    perfectly faithful to itself. Derived from `Corr.identity_ident_zero`. -/
theorem basemapViolations_self_eq_zero (t : List TRN) :
    basemapViolations t t = 0 :=
  Corr.identity_ident_zero t

/-- Zero basemap violations with equal-length tiers implies the tiers are
    identical. The equal-length hypothesis is necessary because the
    underlying `Corr.parallel` truncates to `min`. -/
theorem basemapViolations_eq_zero_imp
    (t₁ t₂ : List TRN) (hLen : t₁.length = t₂.length)
    (hZero : basemapViolations t₁ t₂ = 0) : t₁ = t₂ := by
  unfold basemapViolations Corr.identViol at hZero
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hZero
  apply List.ext_getElem hLen
  intro n hn₁ hn₂
  have hmem : (n, n) ∈ (Corr.parallel t₁ t₂).edge .lhs .rhs := by
    rw [Corr.parallel_edge_lhs_rhs, Finset.mem_image]
    refine ⟨n, ?_, rfl⟩
    rw [Finset.mem_range, Nat.lt_min]
    exact ⟨hn₁, hn₂⟩
  have := hZero hmem
  simp only [Corr.parallel_form_lhs, Corr.parallel_form_rhs,
             not_not] at this
  rw [List.getElem?_eq_getElem hn₁, List.getElem?_eq_getElem hn₂] at this
  exact Option.some_inj.mp this

-- ============================================================================
-- § 5: NamedConstraint Bridge
-- ============================================================================

/-- Wrap `basemapViolations` as a `NamedConstraint` for use in OT
    tableaux and cophonological evaluation.

    Given a fixed basemap output (the tonal tier of the basemap-faithful
    form), this constraint evaluates each candidate by comparing its
    tonal tier against the basemap. In @cite{rolle-2018}'s analysis,
    dominant triggers promote this constraint above default markedness
    in their cophonology's subranking.

    `extractTier` converts a candidate to its tonal tier for comparison.
    This allows the constraint to work with any candidate type, not
    just raw `List TRN`. -/
def mkBasemapConstraint {C : Type}
    (basemapTier : List TRN)
    (extractTier : C → List TRN) : NamedConstraint C where
  name := "BM-FAITH"
  family := .faithfulness
  eval c := basemapViolations (extractTier c) basemapTier

-- ============================================================================
-- § 6: Dominance as Basemap Faithfulness
-- ============================================================================

/-- Helper: whole-word `tonalOverwrite` reduces to `List.map`. -/
private theorem tonalOverwrite_whole_eq_map {S : Type}
    [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t : TRN) :
    tonalOverwrite host ⟨"", [t], .whole⟩ =
    host.map fun tbu => { tbu with tone := t } := rfl

/-- The central theorem of MxBM-C: for replacive-dominant GT with a
    whole-word single-tone melody, the matrix output's tonal tier
    equals the basemap output's tonal tier.

    This captures @cite{rolle-2018}'s key insight: dominant GT is not
    a special deletion rule or markedness constraint, but faithfulness
    to an abstract basemap. The target's underlying tones go unrealized
    because the output must match what would happen if those tones
    were never there. -/
theorem tonalOverwrite_basemap_faithful {S : Type}
    [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t : TRN) (defaultTone : TRN) :
    let spec : Spec := ⟨"", [t], .whole⟩
    tonalTier (tonalOverwrite host spec) =
    tonalTier (basemapOutput host spec defaultTone) := by
  simp only [tonalTier_eq_map, basemapOutput, deficientProjection]
  rw [tonalOverwrite_whole_eq_map, tonalOverwrite_whole_eq_map]
  simp only [List.map_map]
  congr 1

/-- The basemap output's tonal tier is independent of the host's
    underlying tones: for whole-word replacement, two hosts with
    different lexical tones but identical segmental content produce
    the same basemap tonal tier.

    The formal content of "transparadigmatic uniformity"
    (@cite{rolle-2018} Ch 5): the basemap abstracts away from the
    paradigmatic tonal variation of the target. -/
theorem basemapOutput_tone_independent_whole {S : Type}
    [DecidableEq S] [BEq S] [Repr S]
    (host₁ host₂ : List (TBU S)) (t defaultTone : TRN)
    (hLen : host₁.length = host₂.length) :
    let spec : Spec := ⟨"", [t], .whole⟩
    tonalTier (basemapOutput host₁ spec defaultTone) =
    tonalTier (basemapOutput host₂ spec defaultTone) := by
  simp only [tonalTier_eq_map, basemapOutput, deficientProjection]
  rw [tonalOverwrite_whole_eq_map, tonalOverwrite_whole_eq_map]
  simp only [List.map_map]
  have mapConst : ∀ xs : List (TBU S),
      List.map (TBU.tone ∘ (fun tbu : TBU S => { tbu with tone := t }) ∘
        fun tbu : TBU S => { tbu with tone := defaultTone }) xs =
      List.replicate xs.length t := by
    intro xs
    induction xs with
    | nil => rfl
    | cons _ _ ih =>
      simp only [List.map_cons, Function.comp_def, List.length_cons,
                 List.replicate_succ]
      exact congrArg _ ih
  rw [mapConst, mapConst, hLen]

end Phonology.Autosegmental.BasemapCorrespondence
