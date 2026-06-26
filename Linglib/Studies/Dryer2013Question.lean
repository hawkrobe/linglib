import Linglib.Syntax.Question
import Linglib.Fragments.English.Questions
import Linglib.Fragments.HindiUrdu.Questions
import Linglib.Fragments.Japanese.Questions
import Linglib.Fragments.Italian.Questions
import Linglib.Fragments.Singlish.Questions
import Linglib.Fragments.Mandarin.Questions

/-!
# Dryer (2013): WALS chapters on question formation (92A, 93A, 116A)
[dryer-2013-wals] [wals-2013]

WALS chapters by Matthew S. Dryer covering question typology:

- Ch 92A: Position of Polar Question Particles
- Ch 93A: Position of Interrogative Phrases in Content Questions
- Ch 116A: Polar Questions

This study file holds **cross-linguistic generalisations** that consume the
Fragment-side `def question : QuestionProfile` data with non-trivial
semantic content. Per-language Fragment-vs-WALS data-equality theorems are
**deliberately absent** — verifying that
`X.Questions.question.field` equals `Data.WALS.lookup "iso"`
is "encoding conclusions as definitions": the typed Fragment value already
encodes the WALS coding at definition site, and the substrate's
distribution theorems already capture the corpus-level claims.

WALS aggregate sample-size theorems live in `Linglib/Typology/Question.lean`.
-/

set_option autoImplicit false

namespace Dryer2013Question

open Syntax.Question

-- ============================================================================
-- §1. The Fragment sample
-- ============================================================================

/-- The 6-language sample drawn from per-language Fragment Question files.
    Italian + Singlish are partial (not in all WALS chapters). -/
def allQuestionProfiles : List QuestionProfile :=
  [ English.Questions.question
  , HindiUrdu.Questions.question
  , Japanese.Questions.question
  , Italian.Questions.question
  , Singlish.Questions.question
  , Mandarin.Questions.question ]

-- ============================================================================
-- §2. Sample-level summaries
-- ============================================================================

/-- Sample size including the contact-variety Singlish entry. -/
theorem sample_size : allQuestionProfiles.length = 6 := by native_decide

/-- Sample distribution: wh-in-situ is the most common wh-strategy in this
    6-language sample (Hindi, Japanese, Mandarin) — three of six. -/
theorem in_situ_count :
    (allQuestionProfiles.filter
      (λ p => p.whMovement == some .inSitu)).length = 3 := by
  native_decide

/-- Sample distribution: particle-based polar strategy dominates this sample
    (Hindi, Japanese, Singlish, Mandarin) — four of six. -/
theorem particle_polar_count :
    (allQuestionProfiles.filter
      (λ p => p.polarStrategy == some .particle)).length = 4 := by
  native_decide

end Dryer2013Question
