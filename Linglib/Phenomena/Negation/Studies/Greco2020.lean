import Linglib.Theories.Syntax.Minimalism.Core.Phase
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic
import Linglib.Phenomena.Negation.Studies.Rett2026
import Linglib.Phenomena.Negation.Typology

/-!
# Phase-Based Analysis of Surprise Negation
@cite{greco-2020} @cite{chomsky-2001}

Greco, M. (2020). On the syntax of surprise negation sentences: A case
study on expletive negation. *NLLT* 38(3), 775–825.

## Overview

Surprise negation (Sneg) arises when a negative morpheme merges in the
CP layer rather than in the standard TP-internal NegP position. Greco's
analysis rests on four factors:

1. A negative morpheme α exists in the language
2. α is a **syntactic head** (X°), not a phrase (XP)
3. α merges in the **CP phase** after vP-phase exhaustion (Transfer)
4. TP is **focused** (moves to Spec-FocP)

The head requirement (2) explains why Italian (*non*, X°) has Sneg but
Spanish (*no*, XP) does not: only heads can merge directly into the
functional spine without projecting their own phrase. The phase-based
account (3) explains why Sneg negation is non-truth-conditional: by the
time the neg head merges, the vP complement has been transferred to LF,
so the negation cannot scope into the propositional content.

## Connections

- `Phenomena.Negation.ExpletiveNegation.ENType` — high vs low EN
- `Phenomena.Negation.Typology.NegationProfile.negIsHead` — head status
- `Minimalism.fValue` — f-value classification (Extended Projection)
- `Minimalism.isPhaseHead` — phase head identification
-/

namespace Phenomena.Negation.Studies.Greco2020

open Minimalism (Cat fValue isPhaseHead)
open Phenomena.Negation.ExpletiveNegation (ENType ENDatum)
open Phenomena.Negation.Typology (NegationProfile italian spanish french)

-- ════════════════════════════════════════════════════
-- § 1. Neg merge position relative to the clause spine
-- ════════════════════════════════════════════════════

/-- Where a negation head is merged in the extended projection.
    Standard NegP is in the inflectional domain (F2, between v and C).
    In surprise negation, *non* merges in the CP layer (F3+, between
    Fin and Foc). -/
inductive NegMergePosition where
  | tp   -- Standard NegP: inflectional domain (F2)
  | cp   -- CP-area: left periphery (F3+, @cite{greco-2020} §4)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. F-value classification — derive TP vs CP from Extended Projection
-- ════════════════════════════════════════════════════

/-- A category is in the CP area iff its f-value is at or above Fin (F3).
    @cite{rizzi-1997}: Fin is the boundary between the inflectional domain and
    the left periphery. -/
def isCPArea (c : Cat) : Bool := fValue c ≥ fValue .Fin

/-- Standard NegP (F2) is in TP, not CP. -/
theorem neg_in_tp : isCPArea .Neg = false := by decide

/-- Foc (F4) is in the CP area. -/
theorem foc_in_cp : isCPArea .Foc = true := by decide

/-- Force (F6) is in the CP area. -/
theorem force_in_cp : isCPArea .Force = true := by decide

/-- Fin (F3) is the boundary (inclusive — it's the lowest CP head). -/
theorem fin_is_cp_boundary : isCPArea .Fin = true := by decide

-- ════════════════════════════════════════════════════
-- § 3. Phase-based scope restriction (@cite{greco-2020}, §4.3)
-- ════════════════════════════════════════════════════

/-- Whether a Neg head at this merge position can scope into the vP domain.
    Under weak PIC: vP complement is accessible until the
    NEXT phase head (C) is merged. Standard NegP (F2) is merged before C,
    so vP is still accessible. CP-area Neg is merged during/after C-phase
    assembly, when vP complement has been transferred. -/
def NegMergePosition.scopesIntoVP : NegMergePosition → Bool
  | .tp => true    -- Merged before C, vP still accessible
  | .cp => false   -- Merged with/after C, vP transferred

/-- CP-area negation is non-truth-conditional (= high EN).
    TP-area negation is truth-conditional (standard or low EN). -/
def NegMergePosition.toENEffect : NegMergePosition → ENType
  | .tp => .low   -- Can scope → truth-conditional
  | .cp => .high  -- Cannot scope → non-truth-conditional (Greco's high EN)

/-- TP-area negation scopes into vP. -/
theorem tp_neg_scopes : NegMergePosition.tp.scopesIntoVP = true := rfl

/-- CP-area negation does NOT scope into vP. -/
theorem cp_neg_no_scope : NegMergePosition.cp.scopesIntoVP = false := rfl

/-- CP-area negation maps to high EN. -/
theorem cp_is_high_en : NegMergePosition.cp.toENEffect = .high := rfl

/-- TP-area negation maps to low EN. -/
theorem tp_is_low_en : NegMergePosition.tp.toENEffect = .low := rfl

-- ════════════════════════════════════════════════════
-- § 4. Greco's four factors for surprise negation
-- ════════════════════════════════════════════════════

/-- @cite{greco-2020}: four necessary conditions for surprise negation.
    (i) a negative morpheme α, (ii) α is a syntactic head (X°),
    (iii) α merges in the CP-phase after vP-phase exhaustion,
    (iv) TP is focused (moves to Spec-FocP). -/
structure SnegConditions where
  hasNegMorpheme : Bool
  negIsHead : Bool
  mergePosition : NegMergePosition
  tpIsFocused : Bool
  deriving DecidableEq, BEq, Repr

/-- A set of conditions yields surprise negation iff all four
    are satisfied. -/
def SnegConditions.yieldsSnegs (c : SnegConditions) : Bool :=
  c.hasNegMorpheme && c.negIsHead &&
  c.mergePosition == .cp && c.tpIsFocused

/-- Italian satisfies all four Sneg conditions. -/
def italianSnegConditions : SnegConditions :=
  { hasNegMorpheme := true
  , negIsHead := true      -- non is X° (clitic)
  , mergePosition := .cp
  , tpIsFocused := true }

theorem italian_yields_snegs :
    italianSnegConditions.yieldsSnegs = true := by native_decide

/-- Spanish fails condition (ii): *no* is XP, not X°. -/
def spanishSnegConditions : SnegConditions :=
  { hasNegMorpheme := true
  , negIsHead := false     -- no is XP (can be focused/coordinated)
  , mergePosition := .cp
  , tpIsFocused := true }

theorem spanish_no_snegs :
    spanishSnegConditions.yieldsSnegs = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Cross-linguistic predictions — connect to NegationProfile
-- ════════════════════════════════════════════════════

/-- Sneg attestation datum: links a language's negation profile to
    whether surprise negation is attested. -/
structure SnegAttestation where
  language : String
  attested : Bool
  negIsHead : Option Bool
  deriving DecidableEq, BEq, Repr

def italianSnegs : SnegAttestation :=
  { language := "Italian", attested := true, negIsHead := italian.negIsHead }

def spanishSnegs : SnegAttestation :=
  { language := "Spanish", attested := false, negIsHead := spanish.negIsHead }

def brazilianPortugueseSnegs : SnegAttestation :=
  { language := "Brazilian Portuguese", attested := true
  , negIsHead := some true }

def allSnegAttestations : List SnegAttestation :=
  [italianSnegs, spanishSnegs, brazilianPortugueseSnegs]

/-- Greco's prediction: Snegs are attested only when negIsHead = true. -/
theorem sneg_requires_head :
    allSnegAttestations.all (λ s =>
      if s.attested then s.negIsHead == some true else true) = true := by native_decide

/-- Converse: head-status neg predicts Sneg availability (in our sample). -/
theorem head_predicts_snegs :
    allSnegAttestations.all (λ s =>
      if s.negIsHead == some false then !s.attested else true) = true := by native_decide

/-- The Italian Sneg attestation derives its head status from the
    NegationProfile, not by stipulation. -/
theorem italian_snegs_from_profile :
    italianSnegs.negIsHead = italian.negIsHead := rfl

/-- The Spanish Sneg attestation derives its head status from the
    NegationProfile. -/
theorem spanish_snegs_from_profile :
    spanishSnegs.negIsHead = spanish.negIsHead := rfl

-- ════════════════════════════════════════════════════
-- § 6. Phase theory connection
-- ════════════════════════════════════════════════════

/-- The f-value boundary: anything at F3+ (CP area) is above the
    inflectional domain where standard NegP resides. -/
theorem cp_area_above_neg : fValue .Fin > fValue .Neg := by decide

/-- NegP and T share the same f-value (both F2, inflectional domain). -/
theorem neg_t_same_fvalue : fValue .Neg = fValue .T := by decide

/-- The merge position determines scope: TP-area neg is truth-conditional,
    CP-area neg is non-truth-conditional. This is consistent: CP-area
    maps to high EN, TP-area maps to low EN. -/
theorem scope_determines_entype (pos : NegMergePosition) :
    (pos.scopesIntoVP = true) ↔ (pos.toENEffect = .low) := by
  cases pos <;> simp [NegMergePosition.scopesIntoVP, NegMergePosition.toENEffect]

end Phenomena.Negation.Studies.Greco2020
