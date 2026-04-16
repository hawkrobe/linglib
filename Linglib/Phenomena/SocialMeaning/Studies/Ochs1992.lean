import Linglib.Core.SocialMeaning
import Mathlib.Data.Fintype.Basic

/-!
# @cite{ochs-1992} — Indexing Gender

## Overview

@cite{ochs-1992} argues that the relation between language and gender is
almost never a direct mapping from linguistic form to gender category.
Instead, linguistic forms index *stances* and *speech acts*, which in turn
*constitutively* relate to gender identity. Three properties characterize
this relation:

1. **Non-exclusivity**: few features of language directly and exclusively
   index gender. The association is probabilistic, not categorical.
2. **Constitutivity**: using certain linguistic forms helps *constitute*
   gender identity, not merely reflect it (cf. "doing gender,"
   @cite{west-zimmerman-1987}).
3. **Mediation**: the relation is indirect — form → stance/act → gender.
   Direct indexical relations (e.g., "he"/"she") are rare; mediated
   relations (e.g., *ze* → coarse intensity → masculinity) are the norm.

## Formalization

The core formal contribution is modeling indirect indexicality as
**composition of association maps** (@cite{ochs-1992} Figure 14.2):

- **Field 1** (`formStanceAssoc`): maps sentence-final particles to
  the interactional stances they directly index (categorical 0/1)
- **Field 2** (`stanceGenderAssoc`): maps interactional stances to
  gender identity poles, with graded (non-exclusive) associations
- **Composition** (`composedAssoc`): the matrix product of the two
  fields via `Core.SocialMeaning.composeIndex`, deriving the indirect
  form–gender association

Non-exclusivity is then a *theorem* about the composed field: when
stances have mixed gender associations, forms that index those stances
inherit the non-exclusivity.

## Cross-linguistic data

Japanese sentence-final particles (@cite{uyeno-1971}) illustrate the
mediation thesis (Figure 14.1):
- *ze/zo* directly index **coarse intensity**, which constitutively
  indexes masculinity
- *wa* directly indexes **delicate intensity**, which constitutively
  indexes femininity — but both genders use *wa*, confirming
  non-exclusivity
- *yo* (emphatic) and *ne* (confirmation-seeking) have weak,
  gender-neutral stance associations

## Connections

* `Core.SocialMeaning.composeIndex`: the composition operation
  formalized as a general primitive for indirect indexicality
* `Core.SocialMeaning.IndexicalField`: the composed field is lifted
  to an `IndexicalField`, connecting to @cite{eckert-2008}'s framework
  which explicitly builds on @cite{ochs-1992} and @cite{silverstein-1976}
* `Burnett2019`: RSA model of persona
  inference from variant choice — the computational realization of
  Ochs's indirect indexicality thesis via @cite{burnett-2019}'s SMG
-/

set_option autoImplicit false

namespace Ochs1992

open Core.SocialMeaning

-- ============================================================================
-- §1. Types
-- ============================================================================

/-- Interactional stances that sentence-final particles directly index.
    These are the intermediate meanings through which gender is indirectly
    indexed (@cite{ochs-1992} Figure 14.2).

    @cite{ochs-1992} identifies two key poles of *intensity* in Japanese:
    "coarse intensity" (indexed by *ze/zo*) and "delicate intensity"
    (indexed by *wa*). These stance categories are distinct from
    `Semantics.Lexical.Expressives.OutlookMarker.StanceType`, which
    classifies evaluative stances in @cite{kubota-2026}'s theory. -/
inductive Stance where
  /-- Coarse intensity — rough, forceful interactional style.
      Indexed by *ze*, *zo*. -/
  | coarse
  /-- Delicate intensity — gentle, refined interactional style.
      Indexed by *wa*. -/
  | delicate
  /-- Emphatic assertion — strong commitment without coarseness.
      Indexed by *yo*. -/
  | emphatic
  /-- Seeking confirmation or agreement from the addressee.
      Indexed by *ne*. -/
  | confirmSeeking
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Stance where
  elems := {.coarse, .delicate, .emphatic, .confirmSeeking}
  complete := by intro x; cases x <;> simp

/-- All stances as a list (for `composeIndex`). -/
def Stance.all : List Stance :=
  [.coarse, .delicate, .emphatic, .confirmSeeking]

/-- Gender identity poles — the endpoints of the social gender dimension.
    Not grammatical gender (masc/fem noun class) but the social identity
    dimension that linguistic forms can index
    (@cite{west-zimmerman-1987}). -/
inductive GenderPole where
  | masculine
  | feminine
  deriving DecidableEq, Repr, Inhabited

instance : Fintype GenderPole where
  elems := {.masculine, .feminine}
  complete := by intro x; cases x <;> simp

/-- Japanese sentence-final particles discussed in @cite{ochs-1992}.
    See @cite{uyeno-1971} for the foundational study. -/
inductive SFP where
  | ze   -- ぜ: coarse intensity
  | zo   -- ぞ: coarse intensity (stronger)
  | wa   -- わ: delicate intensity
  | yo   -- よ: emphatic
  | ne   -- ね: confirmation-seeking
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SFP where
  elems := {.ze, .zo, .wa, .yo, .ne}
  complete := by intro x; cases x <;> simp

-- ============================================================================
-- §2. The two association maps — the indirect indexicality chain
-- ============================================================================

/-- Field 1: SFP → Stance (direct index).

    Each particle directly indexes exactly one interactional stance.
    The mapping is categorical (0/1) — a particle either does or does
    not index a stance. The probabilistic gradient enters in Field 2. -/
def formStanceAssoc : SFP → Stance → ℚ
  | .ze, .coarse         => 1
  | .zo, .coarse         => 1
  | .wa, .delicate       => 1
  | .yo, .emphatic       => 1
  | .ne, .confirmSeeking => 1
  | _,   _               => 0

/-- Field 2: Stance → GenderPole (constitutive relation).

    Captures how habitual use of certain stances constitutes gender
    identity. Values are association strengths — positive for BOTH poles
    on every stance, encoding @cite{ochs-1992}'s non-exclusivity.

    The two intensity stances are mirror images on the gender axis:
    coarse is 3/4 masculine, delicate is 3/4 feminine. The remaining
    stances (emphatic, confirmation-seeking) are gender-neutral. -/
def stanceGenderAssoc : Stance → GenderPole → ℚ
  | .coarse,         .masculine => 3/4
  | .coarse,         .feminine  => 1/4
  | .delicate,       .masculine => 1/4
  | .delicate,       .feminine  => 3/4
  | .emphatic,       .masculine => 1/2
  | .emphatic,       .feminine  => 1/2
  | .confirmSeeking, .masculine => 1/2
  | .confirmSeeking, .feminine  => 1/2

-- ============================================================================
-- §3. Composed field — indirect indexicality
-- ============================================================================

/-- The composed (indirect) form → gender association.
    This IS @cite{ochs-1992}'s central theoretical claim: linguistic
    forms index gender only indirectly, mediated through stances.

    composedAssoc(sfp, g) = Σ_s formStance(sfp, s) × stanceGender(s, g) -/
def composedAssoc (sfp : SFP) (g : GenderPole) : ℚ :=
  composeIndex formStanceAssoc stanceGenderAssoc Stance.all sfp g

-- ============================================================================
-- §4. Mediation theorems
-- ============================================================================

/-- *ze* indirectly indexes masculinity more than femininity.
    The asymmetry is mediated through coarse intensity (3/4 masc). -/
theorem ze_indexes_masculine :
    composedAssoc .ze .masculine > composedAssoc .ze .feminine := by native_decide

/-- *wa* indirectly indexes femininity more than masculinity.
    The asymmetry is mediated through delicate intensity (3/4 fem). -/
theorem wa_indexes_feminine :
    composedAssoc .wa .feminine > composedAssoc .wa .masculine := by native_decide

/-- *zo* patterns like *ze* (both index coarse intensity). -/
theorem zo_indexes_masculine :
    composedAssoc .zo .masculine > composedAssoc .zo .feminine := by native_decide

-- ============================================================================
-- §5. Non-exclusivity theorems
-- ============================================================================

/-- **Universal non-exclusivity**: every SFP has positive association
    with both gender poles. This is @cite{ochs-1992}'s property 1:
    "few features of language directly and exclusively index gender."

    The proof follows from the fact that every stance has positive
    association with both genders (the 1/4 floor in `stanceGenderAssoc`),
    and every SFP indexes at least one stance. -/
theorem all_nonexclusive :
    ∀ sfp : SFP, ∀ g : GenderPole, composedAssoc sfp g > 0 := by
  intro sfp g; cases sfp <;> cases g <;> native_decide

-- ============================================================================
-- §6. Gender-neutral stances
-- ============================================================================

/-- *yo* (emphatic) is gender-neutral: equal association with both poles. -/
theorem yo_gender_neutral :
    composedAssoc .yo .masculine = composedAssoc .yo .feminine := by native_decide

/-- *ne* (confirmation-seeking) is gender-neutral. -/
theorem ne_gender_neutral :
    composedAssoc .ne .masculine = composedAssoc .ne .feminine := by native_decide

-- ============================================================================
-- §7. Symmetry — coarse/delicate intensity as mirror images
-- ============================================================================

/-- **Symmetry**: *ze* and *wa* are mirror images on the gender axis.
    *ze*'s masculine association equals *wa*'s feminine association (3/4),
    and vice versa (1/4). This symmetry arises from the mirror structure
    of `stanceGenderAssoc` on the coarse/delicate intensity poles. -/
theorem ze_wa_symmetry :
    composedAssoc .ze .masculine = composedAssoc .wa .feminine ∧
    composedAssoc .ze .feminine  = composedAssoc .wa .masculine := by
  constructor <;> native_decide

/-- *zo* inherits *ze*'s symmetry with *wa*. -/
theorem zo_wa_symmetry :
    composedAssoc .zo .masculine = composedAssoc .wa .feminine ∧
    composedAssoc .zo .feminine  = composedAssoc .wa .masculine := by
  constructor <;> native_decide

-- ============================================================================
-- §8. Factorization — the mediation thesis made explicit
-- ============================================================================

/-- The composed form–gender association factors through the stance
    domain. This makes the mediation thesis computationally explicit:
    the value for (*ze*, masculine) is determined entirely by the
    sum-product through all four stances. -/
theorem mediation_ze_masc :
    composedAssoc .ze .masculine =
      formStanceAssoc .ze .coarse         * stanceGenderAssoc .coarse         .masculine
    + formStanceAssoc .ze .delicate       * stanceGenderAssoc .delicate       .masculine
    + formStanceAssoc .ze .emphatic       * stanceGenderAssoc .emphatic       .masculine
    + formStanceAssoc .ze .confirmSeeking * stanceGenderAssoc .confirmSeeking .masculine := by
  native_decide

-- ============================================================================
-- §9. Rankings — ordinal structure
-- ============================================================================

/-- Ranking of SFPs by masculine association strength:
    ze = zo (3/4) > yo = ne (1/2) > wa (1/4). -/
theorem masculine_ranking :
    composedAssoc .ze .masculine = composedAssoc .zo .masculine ∧
    composedAssoc .ze .masculine > composedAssoc .yo .masculine ∧
    composedAssoc .yo .masculine = composedAssoc .ne .masculine ∧
    composedAssoc .yo .masculine > composedAssoc .wa .masculine := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Ranking of SFPs by feminine association strength:
    wa (3/4) > yo = ne (1/2) > ze = zo (1/4).
    This is the exact mirror of the masculine ranking. -/
theorem feminine_ranking :
    composedAssoc .wa .feminine > composedAssoc .yo .feminine ∧
    composedAssoc .yo .feminine = composedAssoc .ne .feminine ∧
    composedAssoc .yo .feminine > composedAssoc .ze .feminine ∧
    composedAssoc .ze .feminine = composedAssoc .zo .feminine := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- §10. Bridge to IndexicalField framework
-- ============================================================================

/-- The form–stance relation as an `IndexicalField` at second indexical
    order: SFPs are consciously manipulable markers
    (@cite{silverstein-2003}). -/
def formStanceField : IndexicalField SFP Stance where
  association := formStanceAssoc
  order := .second

/-- The composed relation as an `IndexicalField`. -/
def composedField : IndexicalField SFP GenderPole where
  association := composedAssoc
  order := .second

/-- The composed field indexes *ze* toward masculinity. -/
theorem composedField_ze_indexes_masc :
    composedField.indexes .ze .masculine := by
  simp only [IndexicalField.indexes, composedField]
  native_decide

/-- The composed field indexes *wa* toward femininity. -/
theorem composedField_wa_indexes_fem :
    composedField.indexes .wa .feminine := by
  simp only [IndexicalField.indexes, composedField]
  native_decide

/-- *ze* and *wa* contrast on the masculine trait: their composed
    associations differ. -/
theorem ze_wa_contrast_masculine :
    composedField.contrasts .ze .wa .masculine := by
  simp only [IndexicalField.contrasts, composedField]
  native_decide

end Ochs1992
