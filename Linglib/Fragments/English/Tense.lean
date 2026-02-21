import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Theories.Semantics.Tense.ParticipantPerspective
import Linglib.Theories.Semantics.Tense.Kratzer

/-!
# English Tense Fragment (Cumming 2026 + Lakoff 1970)

Paradigm entries for English tense forms from Cumming (2026), Tables 20 and 22.
Each entry specifies evidential perspective (EP) and utterance perspective (UP)
constraints via `EPCondition` and `UPCondition` enums.

## Cumming Entries

| Form              | EP constraint | UP constraint | Nonfuture? |
|-------------------|---------------|---------------|------------|
| simple past       | T ≤ A         | T < S         | yes        |
| present prog      | T ≤ A         | T = S         | yes        |
| future (will)     | (none)        | S < T         | no         |
| will have V-ed    | A < T         | S < T         | no         |
| will now be V-ing | A < T         | T = S         | no         |
| will (bare)       | (none)        | S < T         | no         |

## Lakoff Perspective Entries (§4)

`TensePerspectiveEntry` extends `TAMEEntry` with the morphological form
type (synthetic vs periphrastic) and grammatical tense, connecting Cumming's
evidential constraints to Lakoff's false-tense diagnostic.

## References

- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175. Tables 20, 22.
- Lakoff, R. (1970). Tense and its relation to participants. *Language* 46(4).
-/

namespace Fragments.English.Tense

open Semantics.Tense.Evidential

-- ════════════════════════════════════════════════════
-- § 1. Table 20: Simple Past, Present Progressive, Future
-- ════════════════════════════════════════════════════

/-- English simple past: T ≤ A (downstream), T < S (past). -/
def simplePast : TAMEEntry where
  label := "simple past"
  ep := .downstream
  up := .past

/-- English present progressive: T ≤ A (downstream), T = S (present). -/
def presentProg : TAMEEntry where
  label := "present progressive"
  ep := .downstream
  up := .present

/-- English future (will): no EP constraint, S < T (future). -/
def future : TAMEEntry where
  label := "future (will)"
  ep := .unconstrained
  up := .future

-- ════════════════════════════════════════════════════
-- § 2. Table 22: Will-Forms
-- ════════════════════════════════════════════════════

/-- English "will have V-ed": A < T (prospective), S < T (future). -/
def willHave : TAMEEntry where
  label := "will have V-ed"
  ep := .prospective
  up := .future

/-- English "will now be V-ing": A < T (prospective), T = S (present). -/
def willNow : TAMEEntry where
  label := "will now be V-ing"
  ep := .prospective
  up := .present

/-- English bare "will": no EP constraint, S < T (future). -/
def willBare : TAMEEntry where
  label := "will (bare)"
  ep := .unconstrained
  up := .future

-- ════════════════════════════════════════════════════
-- § 3. Collection
-- ════════════════════════════════════════════════════

/-- All English tense paradigm entries. -/
def allEntries : List TAMEEntry :=
  [simplePast, presentProg, future, willHave, willNow, willBare]

/-- English nonfuture entries. -/
def nonfutureEntries : List TAMEEntry :=
  allEntries.filter (·.isNonfuture)

-- ════════════════════════════════════════════════════
-- § 4. Tense Perspective Entries (Lakoff 1970)
-- ════════════════════════════════════════════════════

open Semantics.Tense
open Semantics.Tense.ParticipantPerspective
open Core.Morphology.Tense

/-- A tense paradigm entry enriched with Lakoff's perspective dimensions:
    grammatical tense and morphological form type (synthetic vs periphrastic).

    `allowsFalseTense` is derived: only synthetic forms permit false tense. -/
structure TensePerspectiveEntry extends TAMEEntry where
  /-- The grammatical tense this form realizes -/
  gramTense : GramTense
  /-- Synthetic (inflectional) or periphrastic (auxiliary-based) -/
  formType : TenseFormType

/-- Does this form allow false-tense interpretations?
    Derived from `formType`: only synthetic forms can. -/
def TensePerspectiveEntry.allowsFalseTense (e : TensePerspectiveEntry) : Bool :=
  e.formType == .synthetic

/-- English simple past with perspective: synthetic, allows false past. -/
def simplePastPerspective : TensePerspectiveEntry where
  label := "simple past"
  ep := .downstream
  up := .past
  gramTense := .past
  formType := .synthetic

/-- English simple present with perspective: synthetic, allows false uses. -/
def simplePresentPerspective : TensePerspectiveEntry where
  label := "simple present"
  ep := .downstream
  up := .present
  gramTense := .present
  formType := .synthetic

/-- English periphrastic past "used to V": cannot express false past. -/
def usedTo : TensePerspectiveEntry where
  label := "used to"
  ep := .downstream
  up := .past
  gramTense := .past
  formType := .periphrastic

/-- English periphrastic future "going to V": cannot express false future. -/
def goingTo : TensePerspectiveEntry where
  label := "going to"
  ep := .unconstrained
  up := .future
  gramTense := .future
  formType := .periphrastic

-- ════════════════════════════════════════════════════
-- § 5. Perspective Entry Verification
-- ════════════════════════════════════════════════════

/-- Synthetic entries allow false tense. -/
theorem simplePast_allows_false : simplePastPerspective.allowsFalseTense = true := rfl
theorem simplePresent_allows_false : simplePresentPerspective.allowsFalseTense = true := rfl

/-- Periphrastic entries block false tense. -/
theorem usedTo_blocks_false : usedTo.allowsFalseTense = false := rfl
theorem goingTo_blocks_false : goingTo.allowsFalseTense = false := rfl

-- ════════════════════════════════════════════════════
-- § 6. Kratzer Decomposition (Kratzer 1998)
-- ════════════════════════════════════════════════════

open Semantics.Tense.Kratzer
open Core.Tense

/-- English simple past: Kratzer decomposition.
    Surface "V-ed" = PRESENT tense + PERFECT aspect.
    The tense head is present (indexical), so the form can be
    used deictically ("out of the blue"). -/
def kratzerSimplePast : KratzerDecomposition where
  language := "English"
  surfaceForm := "V-ed"
  tensePronoun := kratzerEnglishPast
  hasPerfect := true

/-- English present perfect: no decomposition mismatch.
    Surface "have V-ed" = PRESENT tense + PERFECT aspect.
    Identical underlying structure to simple past — the difference
    is that the present perfect is morphologically transparent. -/
def kratzerPresentPerfect : KratzerDecomposition where
  language := "English"
  surfaceForm := "have V-ed"
  tensePronoun := kratzerEnglishPast
  hasPerfect := true

/-- English simple past can be deictic (from decomposition). -/
theorem kratzerSimplePast_deictic :
    kratzerSimplePast.canBeDeictic = true := rfl

/-- The underlying tense head is PRESENT, not PAST.
    Pastness comes from the PERF aspect head, not the tense. -/
theorem kratzerSimplePast_underlyingPresent :
    kratzerSimplePast.tensePronoun.constraint = GramTense.present := rfl

/-- Simple past and present perfect share the same underlying decomposition:
    both are PRESENT + PERFECT. The difference is that simple past fuses
    the two morphemes while present perfect makes the PERF transparent
    via auxiliary "have". -/
theorem simplePast_presentPerfect_same_decomposition :
    kratzerSimplePast.tensePronoun = kratzerPresentPerfect.tensePronoun ∧
    kratzerSimplePast.hasPerfect = kratzerPresentPerfect.hasPerfect :=
  ⟨rfl, rfl⟩

/-- The Lakoff `gramTense = .past` records the surface morphology;
    the Kratzer `constraint = .present` records the underlying tense head.
    These are DIFFERENT for English simple past — that's Kratzer's point. -/
theorem lakoff_kratzer_diverge :
    simplePastPerspective.gramTense = GramTense.past ∧
    kratzerSimplePast.tensePronoun.constraint = GramTense.present := ⟨rfl, rfl⟩

end Fragments.English.Tense
