import Linglib.Core.InformationStructure

/-!
# Arnold, Wasow, Losongco & Ginstrom (2000) @cite{arnold-wasow-losongco-ginstrom-2000}

Heaviness vs. Newness: The Effects of Structural Complexity and
Discourse Status on Constituent Ordering. *Language* 76(1):28–55.

Two corpus studies (Switchboard) disentangle two confounded predictors of
English constituent ordering:

1. **Heaviness** — structural complexity, measured by word count
2. **Newness** — discourse status: given (mentioned in prior discourse)
   vs. new (not previously mentioned)

These factors are naturally confounded: new referents require more descriptive
material, so they tend to be heavier. Arnold et al. use logistic regression
to show that in the **dative alternation**, both weight and newness independently
predict construction choice; in **NP shift** (particle placement), only weight
is significant.

## Constructions

- **Double Object (DO)**: V Recipient Theme — "give Mary the book"
- **Prepositional Dative (PD)**: V Theme to-Recipient — "give the book to Mary"
- **Shifted**: V Particle NP — "pick up the heavy box"
- **Unshifted**: V NP Particle — "pick the box up"

The "heavy/new last" principle: speakers place heavier and newer constituents
in later position. DO puts the theme last; PD puts the recipient last. Shift
puts the NP after the particle (later). In all cases, the later position is
the one that attracts heavy and/or new material.

## Data

- Study 1: Dative alternation, N = 637 (Switchboard corpus)
- Study 2: NP shift in particle constructions, N = 307 (Switchboard corpus)
- Mean NP lengths from Table 1 of the paper
- All length values × 100; proportions × 1000 (permille)

## Bridges

- `Core.InformationStructure.DiscourseStatus`: Arnold et al.'s given/new
  distinction maps to `.given` and `.new`. Their classification is coarser
  than Kratzer & Selkirk (2020): it conflates K&S's unmarked "new" with
  [FoC]-marked "focused" into a single "new" category.
- `DependencyLength.lean`: the "heavy last" effect is DLM's short-before-long
  (Behaghel's Gesetz der wachsenden Glieder)
- `Phenomena.ArgumentStructure.DativeAlternation`: records both frames as
  grammatical — the precondition for this ordering study
-/

namespace Phenomena.WordOrder.Studies.ArnoldEtAl2000

open Core.InformationStructure

-- ============================================================================
-- §1: Study 1 — Dative Alternation (Switchboard)
-- ============================================================================

def dative_nDO : Nat := 323
def dative_nPD : Nat := 314
def dative_n   : Nat := 637

theorem dative_total : dative_nDO + dative_nPD = dative_n := by native_decide

/-- Neither frame exceeds 51% — the alternation is a genuine choice,
    not a strong default with rare exceptions. -/
theorem dative_genuine_alternation :
    dative_nDO * 1000 / dative_n ≤ 510 ∧
    dative_nPD * 1000 / dative_n ≤ 510 := by native_decide

-- Table 1: Mean NP length by construction and position

/-- Mean NP length (× 100) in first vs. second postverbal position. -/
structure PositionLengths where
  label : String
  first100 : Nat   -- mean word count of first postverbal NP × 100
  second100 : Nat  -- mean word count of second postverbal NP × 100
  deriving Repr, DecidableEq, BEq

/-- Table 1, row 1: DO (V Recipient Theme).
    First NP = recipient (1.60 words), second NP = theme (2.99 words). -/
def doLengths : PositionLengths :=
  { label := "DO: V Rec Theme", first100 := 160, second100 := 299 }

/-- Table 1, row 2: PD (V Theme to-Recipient).
    First NP = theme (1.85 words), second NP = recipient (2.55 words). -/
def pdLengths : PositionLengths :=
  { label := "PD: V Theme to-Rec", first100 := 185, second100 := 255 }

/-- **Heavy Last**: in both frames, the second NP is heavier than the first.
    Consistent with Behaghel's Gesetz der wachsenden Glieder and DLM's
    short-before-long prediction (cf. `DependencyLength.lean`). -/
theorem heavy_last :
    doLengths.second100 > doLengths.first100 ∧
    pdLengths.second100 > pdLengths.first100 :=
  ⟨by native_decide, by native_decide⟩

/-- The weight gap is larger in DO (Δ = 1.39) than PD (Δ = 0.70):
    speakers prefer DO especially when the theme is much heavier. -/
theorem do_stronger_weight_asymmetry :
    doLengths.second100 - doLengths.first100 >
    pdLengths.second100 - pdLengths.first100 := by native_decide

-- ============================================================================
-- §2: Study 2 — NP Shift in Particle Constructions (Switchboard)
-- ============================================================================

def shift_nShifted   : Nat := 88
def shift_nUnshifted : Nat := 219
def shift_n          : Nat := 307

theorem shift_total : shift_nShifted + shift_nUnshifted = shift_n := by native_decide

/-- Mean NP length (× 100) by shift status. -/
def shifted_length100   : Nat := 505  -- 5.05 words
def unshifted_length100 : Nat := 159  -- 1.59 words

/-- Shifted NPs are > 3× longer than unshifted NPs on average. -/
theorem shifted_much_heavier :
    shifted_length100 > 3 * unshifted_length100 := by native_decide

/-- Shift rate (× 1000) by NP length in words. Shows the gradient
    relationship between constituent weight and shift probability.
    Values approximate from Arnold et al. (2000) results; 4 = "4+ words." -/
def shiftRate1w : Nat :=  41  -- 1-word NPs: ~4.1% shifted
def shiftRate2w : Nat := 178  -- 2-word NPs: ~17.8% shifted
def shiftRate3w : Nat := 429  -- 3-word NPs: ~42.9% shifted
def shiftRate4w : Nat := 714  -- 4+-word NPs: ~71.4% shifted

/-- Shift rate increases monotonically with NP length. -/
theorem shift_rate_monotone :
    shiftRate1w < shiftRate2w ∧
    shiftRate2w < shiftRate3w ∧
    shiftRate3w < shiftRate4w :=
  ⟨by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §3: Core Finding — Factor Independence
-- ============================================================================

/-- Logistic regression results: which factors significantly predict ordering.
    Based on Arnold et al. (2000) §3–4. -/
structure FactorResult where
  label : String
  /-- Structural weight (word count) is a significant predictor -/
  weightSig : Bool
  /-- Discourse newness (given vs. new) is a significant predictor -/
  newnessSig : Bool
  deriving Repr, DecidableEq, BEq

def dativeResult : FactorResult :=
  { label := "Dative Alternation", weightSig := true, newnessSig := true }

def shiftResult : FactorResult :=
  { label := "NP Shift (particles)", weightSig := true, newnessSig := false }

/-- Dative: both weight and newness independently predict ordering. -/
theorem dative_both_factors :
    dativeResult.weightSig ∧ dativeResult.newnessSig := ⟨rfl, rfl⟩

/-- NP Shift: only weight predicts ordering; newness does not. -/
theorem shift_weight_only :
    shiftResult.weightSig ∧ !shiftResult.newnessSig := ⟨rfl, rfl⟩

/-- The constructions weight factors differently: newness matters for
    datives but not for NP shift. This is the paper's central finding. -/
theorem constructions_differ :
    dativeResult.newnessSig ≠ shiftResult.newnessSig := by decide

-- ============================================================================
-- §4: Bridge — Arnold et al.'s "given/new" ↔ DiscourseStatus
-- ============================================================================

/-- Arnold et al.'s "given" (mentioned in prior 10 clauses) maps to
    `DiscourseStatus.given` ([G]-marked in K&S 2020). -/
def arnoldGiven : DiscourseStatus := .given

/-- Arnold et al.'s "new" (not previously mentioned) maps to
    `DiscourseStatus.new` (unmarked default in K&S 2020).
    Note: Arnold et al.'s "new" is broader than K&S's `.new` — it includes
    material that K&S would mark as `.focused` ([FoC]-marked, contrasted). -/
def arnoldNew : DiscourseStatus := .new

/-- The two-way classification aligns with the K&S three-way partition:
    Arnold's "given" = K&S given, Arnold's "new" ⊇ K&S new. -/
theorem given_aligns : arnoldGiven = DiscourseStatus.given := rfl
theorem new_aligns   : arnoldNew   = DiscourseStatus.new   := rfl

end Phenomena.WordOrder.Studies.ArnoldEtAl2000
