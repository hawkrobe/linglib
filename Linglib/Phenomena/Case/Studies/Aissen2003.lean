import Linglib.Core.Prominence
import Linglib.Theories.Phonology.OT.Core
import Linglib.Phenomena.Case.Typology

/-!
# Aissen (2003): Differential Object Marking @cite{aissen-2003}

Differential Object Marking: Iconicity vs. Economy.
Natural Language & Linguistic Theory 21(3): 435–483.

Formalizes the core OT analysis: Harmonic Alignment of prominence scales
with the relational scale (Subj > Obj) derives two constraint families:

- **Iconicity** (*Ø/X): penalizes zero-marked objects at prominence level X.
  Fixed ranking: *Ø most prominent >> ... >> *Ø least prominent.
- **Economy** (*!/X): penalizes marked objects at prominence level X.
  Fixed ranking: *!/least prominent >> ... >> *!/most prominent.

Rankings are fixed within each family but free between families. The factorial
typology over all consistent interleavings predicts exactly the attested DOM
patterns.

## Key Results

| Scale Size | Consistent Rankings | Language Types | Impossible Patterns |
|------------|-------------------|---------------|-------------------|
| 2 elements | 6 | 3 | Mark low without high |
| 3 elements | 20 | 4 | Any non-monotone pattern |

For the 3-element animacy scale {Hu > An > In}, 4 of 8 logically possible
patterns are generated — exactly the monotone ones (Table 17, p. 476).

## Connection to Existing Infrastructure

The predicted DOM profiles are matched against the `DOMProfile` language data
in `Phenomena.Case.Typology`, verifying that every attested pattern corresponds
to a possible OT grammar.

## References

- Aissen, J. (2003). Differential Object Marking: Iconicity vs. Economy.
  NLLT 21(3): 435–483.
-/

namespace Phenomena.Case.Studies.Aissen2003

open Core.Prominence
open Theories.Phonology.OT
open Phenomena.Case.Typology

-- ============================================================================
-- § 1: Interleavings
-- ============================================================================

/-- All interleavings of two lists, preserving internal order of each.

    Given two constraint families with fixed internal rankings, this generates
    all total orders consistent with both (Aissen 2003, §3). The number of
    interleavings of lists of lengths m and n is C(m+n, m). -/
def interleavings {α : Type} : List α → List α → List (List α)
  | [], ys => [ys]
  | xs, [] => [xs]
  | x :: xs, y :: ys =>
    (interleavings xs (y :: ys)).map (x :: ·) ++
    (interleavings (x :: xs) ys).map (y :: ·)

-- ============================================================================
-- § 2: Two-Element Scale (Table 14, p. 473)
-- ============================================================================

/-- DOM candidate for a 2-element prominence scale {High > Low}.
    `true` = overtly case-marked; `false` = zero-marked. -/
structure Scale2Cand where
  high : Bool
  low : Bool
  deriving DecidableEq, BEq, Repr

def scale2Cands : List Scale2Cand :=
  [⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩]

theorem scale2_nonempty : scale2Cands ≠ [] := by decide

/-- *Ø/High: penalize unmarked High objects (Aissen 2003, §3). -/
def starZeroHigh : NamedConstraint Scale2Cand :=
  { name := "*Ø/High", family := .markedness,
    eval := λ c => if c.high then 0 else 1 }

/-- *Ø/Low: penalize unmarked Low objects. -/
def starZeroLow : NamedConstraint Scale2Cand :=
  { name := "*Ø/Low", family := .markedness,
    eval := λ c => if c.low then 0 else 1 }

/-- *!/Low: penalize marked Low objects (economy). -/
def starBangLow : NamedConstraint Scale2Cand :=
  { name := "*!/Low", family := .faithfulness,
    eval := λ c => if c.low then 1 else 0 }

/-- *!/High: penalize marked High objects (economy). -/
def starBangHigh : NamedConstraint Scale2Cand :=
  { name := "*!/High", family := .faithfulness,
    eval := λ c => if c.high then 1 else 0 }

/-- Iconicity family (fixed: *Ø/High >> *Ø/Low). -/
def iconicity2 : List (NamedConstraint Scale2Cand) := [starZeroHigh, starZeroLow]

/-- Economy family (fixed: *!/Low >> *!/High). -/
def economy2 : List (NamedConstraint Scale2Cand) := [starBangLow, starBangHigh]

/-- All consistent rankings: interleavings of the two families. -/
def rankings2 : List (List (NamedConstraint Scale2Cand)) :=
  interleavings iconicity2 economy2

/-- There are exactly 6 consistent rankings (C(4,2) = 6). -/
theorem rankings2_count : rankings2.length = 6 := by native_decide

/-- Compute optima for each consistent ranking. -/
def optima2 : List (List Scale2Cand) :=
  rankings2.map λ ranking =>
    (buildTableau scale2Cands ranking scale2_nonempty).optimal

/-- Distinct language types. -/
def types2 : List (List Scale2Cand) := optima2.eraseDups

/-- The 2-element scale yields exactly 3 language types, not 4
    (Table 14, p. 473). -/
theorem two_element_three_types : types2.length = 3 := by native_decide

/-- The impossible pattern — mark Low without High — is never optimal. -/
theorem no_low_without_high :
    optima2.all (λ opts =>
      opts.all (λ c => !(c.low && !c.high))) = true := by native_decide

-- ============================================================================
-- § 3: Three-Element Animacy Scale (Table 17, p. 476)
-- ============================================================================

/-- DOM candidate for the 3-element animacy scale {Hu > An > In}.
    `true` = overtly case-marked; `false` = zero-marked. -/
structure AnimCand where
  hu : Bool
  an : Bool
  inan : Bool
  deriving DecidableEq, BEq, Repr

def animCands : List AnimCand :=
  [⟨true, true, true⟩, ⟨true, true, false⟩,
   ⟨true, false, true⟩, ⟨true, false, false⟩,
   ⟨false, true, true⟩, ⟨false, true, false⟩,
   ⟨false, false, true⟩, ⟨false, false, false⟩]

theorem anim_nonempty : animCands ≠ [] := by decide

/-- Iconicity: *Ø/Hu >> *Ø/An >> *Ø/In. -/
def starZeroHu : NamedConstraint AnimCand :=
  { name := "*Ø/Hu", family := .markedness,
    eval := λ c => if c.hu then 0 else 1 }

def starZeroAn : NamedConstraint AnimCand :=
  { name := "*Ø/An", family := .markedness,
    eval := λ c => if c.an then 0 else 1 }

def starZeroIn : NamedConstraint AnimCand :=
  { name := "*Ø/In", family := .markedness,
    eval := λ c => if c.inan then 0 else 1 }

/-- Economy: *!/In >> *!/An >> *!/Hu. -/
def starBangIn : NamedConstraint AnimCand :=
  { name := "*!/In", family := .faithfulness,
    eval := λ c => if c.inan then 1 else 0 }

def starBangAn : NamedConstraint AnimCand :=
  { name := "*!/An", family := .faithfulness,
    eval := λ c => if c.an then 1 else 0 }

def starBangHu : NamedConstraint AnimCand :=
  { name := "*!/Hu", family := .faithfulness,
    eval := λ c => if c.hu then 1 else 0 }

/-- Iconicity family (fixed: *Ø/Hu >> *Ø/An >> *Ø/In). -/
def animIconicity : List (NamedConstraint AnimCand) :=
  [starZeroHu, starZeroAn, starZeroIn]

/-- Economy family (fixed: *!/In >> *!/An >> *!/Hu). -/
def animEconomy : List (NamedConstraint AnimCand) :=
  [starBangIn, starBangAn, starBangHu]

/-- All consistent rankings for the 3-element scale. -/
def animRankings : List (List (NamedConstraint AnimCand)) :=
  interleavings animIconicity animEconomy

/-- There are exactly 20 consistent rankings (C(6,3) = 20). -/
theorem anim_rankings_count : animRankings.length = 20 := by native_decide

/-- Compute optima for each consistent ranking. -/
def animOptima : List (List AnimCand) :=
  animRankings.map λ ranking =>
    (buildTableau animCands ranking anim_nonempty).optimal

/-- Distinct language types. -/
def animTypes : List (List AnimCand) := animOptima.eraseDups

/-- The 3-element animacy scale yields exactly 4 language types, not 8
    (Table 17, p. 476). -/
theorem animacy_four_types : animTypes.length = 4 := by native_decide

/-- Every generated type is monotone: if An is marked then Hu is too;
    if In is marked then An is too (Aissen's central prediction). -/
theorem animacy_all_monotone :
    animOptima.all (λ opts =>
      opts.all (λ c =>
        (if c.an then c.hu else true) &&
        (if c.inan then c.an else true))) = true := by native_decide

-- ============================================================================
-- § 4: Type Identification
-- ============================================================================

/-- Type 1: mark all (Hu + An + In). Extreme iconicity. -/
theorem anim_type_all :
    animTypes.any (λ opts =>
      opts.any (λ c => c.hu && c.an && c.inan)) = true := by native_decide

/-- Type 2: mark Hu + An only. Russian pattern (animate accusative). -/
theorem anim_type_hu_an :
    animTypes.any (λ opts =>
      opts.any (λ c => c.hu && c.an && !c.inan)) = true := by native_decide

/-- Type 3: mark Hu only. Spanish pattern (personal `a`). -/
theorem anim_type_hu_only :
    animTypes.any (λ opts =>
      opts.any (λ c => c.hu && !c.an && !c.inan)) = true := by native_decide

/-- Type 4: mark none. No DOM (economy dominates). -/
theorem anim_type_none :
    animTypes.any (λ opts =>
      opts.any (λ c => !c.hu && !c.an && !c.inan)) = true := by native_decide

-- ============================================================================
-- § 5: Impossible Patterns
-- ============================================================================

/-- Mark In without An: never generated. -/
theorem no_in_without_an :
    animOptima.all (λ opts =>
      opts.all (λ c => !(c.inan && !c.an))) = true := by native_decide

/-- Mark An without Hu: never generated. -/
theorem no_an_without_hu :
    animOptima.all (λ opts =>
      opts.all (λ c => !(c.an && !c.hu))) = true := by native_decide

/-- Mark In without Hu: never generated. -/
theorem no_in_without_hu :
    animOptima.all (λ opts =>
      opts.all (λ c => !(c.inan && !c.hu))) = true := by native_decide

/-- Mark In only (without An or Hu): never generated. -/
theorem no_in_only :
    animOptima.all (λ opts =>
      opts.all (λ c => !(c.inan && !c.an && !c.hu))) = true := by native_decide

-- ============================================================================
-- § 6: Bridge to DOMProfiles
-- ============================================================================

/-- Convert an AnimCand to a one-dimensional animacy DOMProfile. -/
def animCandToDOM (c : AnimCand) : DOMProfile :=
  DOMProfile.mk' "OT-predicted" λ a _ =>
    match a with
    | .human => c.hu
    | .animate => c.an
    | .inanimate => c.inan

/-- Every OT-generated animacy type produces a monotone DOMProfile. -/
theorem ot_types_are_monotone_dom :
    animOptima.all (λ opts =>
      opts.all (λ c => (animCandToDOM c).isMonotone)) = true := by native_decide

/-- Spanish DOM (human only) matches OT Type 3 (Hu only). -/
theorem spanish_matches_type3 :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        spanishDOM.marks a d == (animCandToDOM ⟨true, false, false⟩).marks a d)) = true := by
  native_decide

/-- Russian DOM (animate+) matches OT Type 2 (Hu + An). -/
theorem russian_matches_type2 :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        russianDOM.marks a d == (animCandToDOM ⟨true, true, false⟩).marks a d)) = true := by
  native_decide

/-- No-DOM profile matches OT Type 4 (none marked). -/
theorem nodom_matches_type4 :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        noDOMProfile.marks a d == (animCandToDOM ⟨false, false, false⟩).marks a d)) = true := by
  native_decide

-- ============================================================================
-- § 7: Definiteness Scale (2-Element: Pro > D)
-- ============================================================================

/-! The 2-element definiteness scale {Pro > D} from §4 of the paper,
    where "D" covers definite NPs (including proper names). This gives
    the same 3-type factorial typology as any 2-element scale. -/

/-- Convert a Scale2Cand to a definiteness-based DOMProfile.
    High = personalPronoun, Low = properName + definite (i.e., ≥ definite). -/
def defCandToDOM (c : Scale2Cand) : DOMProfile :=
  DOMProfile.mk' "OT-predicted" λ _ d =>
    if d.rank ≥ DefinitenessLevel.personalPronoun.rank then c.high
    else if d.rank ≥ DefinitenessLevel.definite.rank then c.low
    else false

/-- Catalan DOM (pronouns only) matches 2-element Type 2 (High only). -/
theorem catalan_matches_high_only :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        catalanDOM.marks a d == (defCandToDOM ⟨true, false⟩).marks a d)) = true := by
  native_decide

/-- Turkish DOM (definite+) matches 2-element Type 1 (both marked). -/
theorem turkish_matches_both :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        turkishDOM.marks a d == (defCandToDOM ⟨true, true⟩).marks a d)) = true := by
  native_decide

/-- Hebrew DOM (definite+) also matches 2-element Type 1. -/
theorem hebrew_matches_both :
    AnimacyLevel.all.all (λ a =>
      DefinitenessLevel.all.all (λ d =>
        hebrewDOM.marks a d == (defCandToDOM ⟨true, true⟩).marks a d)) = true := by
  native_decide

-- ============================================================================
-- § 8: Counting Argument (§4.1, p. 473)
-- ============================================================================

/-- Of 8 logically possible 3-element patterns, OT generates exactly 4. -/
theorem animacy_excludes_half : animCands.length = 8 ∧ animTypes.length = 4 := by
  constructor <;> native_decide

/-- Of 4 logically possible 2-element patterns, OT generates exactly 3. -/
theorem two_element_excludes_one : scale2Cands.length = 4 ∧ types2.length = 3 := by
  constructor <;> native_decide

/-- The number of consistent rankings grows as C(2n, n).
    For n=2: C(4,2) = 6. For n=3: C(6,3) = 20. -/
theorem ranking_counts :
    rankings2.length = 6 ∧ animRankings.length = 20 := by
  constructor <;> native_decide

end Phenomena.Case.Studies.Aissen2003
