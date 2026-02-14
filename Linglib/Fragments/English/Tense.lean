import Linglib.Theories.TruthConditional.Sentence.Tense.Evidential

/-!
# English Tense Fragment (Cumming 2026)

Paradigm entries for English tense forms from Cumming (2026), Tables 20 and 22.
Each entry specifies evidential perspective (EP) and utterance perspective (UP)
constraints via `EPCondition` and `UPCondition` enums.

## Entries

| Form              | EP constraint | UP constraint | Nonfuture? |
|-------------------|---------------|---------------|------------|
| simple past       | T ≤ A         | T < S         | yes        |
| present prog      | T ≤ A         | T = S         | yes        |
| future (will)     | (none)        | S < T         | no         |
| will have V-ed    | A < T         | S < T         | no         |
| will now be V-ing | A < T         | T = S         | no         |
| will (bare)       | (none)        | S < T         | no         |

## References

- Cumming, S. (2026). Tense and evidence. *L&P* 49:153–175. Tables 20, 22.
-/

namespace Fragments.English.Tense

open TruthConditional.Sentence.Tense.Evidential

-- ════════════════════════════════════════════════════
-- § 1. Table 20: Simple Past, Present Progressive, Future
-- ════════════════════════════════════════════════════

/-- English simple past: T ≤ A (downstream), T < S (past). -/
def simplePast : TenseEvidentialParadigm where
  label := "simple past"
  ep := .downstream
  up := .past

/-- English present progressive: T ≤ A (downstream), T = S (present). -/
def presentProg : TenseEvidentialParadigm where
  label := "present progressive"
  ep := .downstream
  up := .present

/-- English future (will): no EP constraint, S < T (future). -/
def future : TenseEvidentialParadigm where
  label := "future (will)"
  ep := .unconstrained
  up := .future

-- ════════════════════════════════════════════════════
-- § 2. Table 22: Will-Forms
-- ════════════════════════════════════════════════════

/-- English "will have V-ed": A < T (prospective), S < T (future). -/
def willHave : TenseEvidentialParadigm where
  label := "will have V-ed"
  ep := .prospective
  up := .future

/-- English "will now be V-ing": A < T (prospective), T = S (present). -/
def willNow : TenseEvidentialParadigm where
  label := "will now be V-ing"
  ep := .prospective
  up := .present

/-- English bare "will": no EP constraint, S < T (future). -/
def willBare : TenseEvidentialParadigm where
  label := "will (bare)"
  ep := .unconstrained
  up := .future

-- ════════════════════════════════════════════════════
-- § 3. Collection
-- ════════════════════════════════════════════════════

/-- All English tense paradigm entries. -/
def allEntries : List TenseEvidentialParadigm :=
  [simplePast, presentProg, future, willHave, willNow, willBare]

/-- English nonfuture entries. -/
def nonfutureEntries : List TenseEvidentialParadigm :=
  allEntries.filter (·.isNonfuture)

end Fragments.English.Tense
