import Linglib.Core.InformationStructure
import Linglib.Theories.Semantics.Questions.Hamblin
import Linglib.Fragments.Turkish.QuestionParticles
import Linglib.Phenomena.Questions.PolarAnswers

/-!
# Turk, Hirsch & İnce (2026) — Category Match Bridge

Connects the empirical judgments in `PolarAnswers.lean` (modal answers
are infelicitous to Turkish polar questions) to the formal explanation:
Fox & Katzir (2011) category match over UPOS tags.

## The Problem

Turkish *mI* heads PolP and bears focus (Σ_F). Under Rooth-style
type-theoretic alternative computation, any operator of the same
semantic type counts as an alternative — including deontic modals.
This yields {p, ¬p, □p}, wrongly predicting □p is a felicitous answer.

## The Fix

Category match restricts alternatives to items sharing *mI*'s UPOS tag
`PART`. Polarity operators (Σ, NEG) are `PART`; "must" is `AUX`.
Category match yields {p, ¬p} — the correct polar question.

## Scenario

Four worlds: Ali sleeps/doesn't × deontic must/free.

## References

- Turk, E., Hirsch, A. & İnce, A. (2026). Constraining Alternatives
  in Turkish Polar Questions.
- Fox, D. & Katzir, R. (2011). On the characterization of alternatives.
- Rooth, M. (1992). A Theory of Focus Interpretation. NLS 1: 75-116.
- Kratzer, A. & Selkirk, E. (2020). Deconstructing Information Structure.
-/

namespace Phenomena.Questions.Studies.TurkHirschInce2026Bridge

open Core.InformationStructure
open Semantics.Questions.Hamblin

-- ═══════════════════════════════════════════════════════════════════════
-- §1  World Type and Propositions
-- ═══════════════════════════════════════════════════════════════════════

/-- Four worlds crossing Ali-sleeps with deontic-must. -/
inductive PolarWorld where
  | sleeps_must   -- Ali sleeps, must is in force
  | sleeps_free   -- Ali sleeps, no deontic necessity
  | nosleep_must  -- Ali doesn't sleep, must is in force
  | nosleep_free  -- Ali doesn't sleep, no deontic necessity
  deriving DecidableEq, BEq, Repr

open PolarWorld

def allWorlds : List PolarWorld :=
  [sleeps_must, sleeps_free, nosleep_must, nosleep_free]

/-- p = "Ali sleeps": true when Ali sleeps regardless of modality. -/
def p : PolarWorld → Bool
  | sleeps_must  => true
  | sleeps_free  => true
  | nosleep_must => false
  | nosleep_free => false

/-- ¬p = "Ali doesn't sleep". -/
def notP : PolarWorld → Bool
  | sleeps_must  => false
  | sleeps_free  => false
  | nosleep_must => true
  | nosleep_free => true

/-- □p = "Ali must sleep" (deontic necessity). -/
def mustP : PolarWorld → Bool
  | sleeps_must  => true
  | sleeps_free  => false
  | nosleep_must => true
  | nosleep_free => false

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Operators as CatItems (UPOS-tagged)
-- ═══════════════════════════════════════════════════════════════════════

/-- The lexicon of propositional operators at type ⟨⟨s,t⟩,t⟩.
    Polarity heads (Σ, NEG) are tagged `PART`; the deontic modal is `AUX`.
    This UPOS distinction is what category match exploits. -/
def opLexicon : List (CatItem (PolarWorld → Bool)) :=
  [⟨.PART, p⟩, ⟨.PART, notP⟩, ⟨.AUX, mustP⟩]

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Alternative Sets
-- ═══════════════════════════════════════════════════════════════════════

/-- Type-theoretic alternatives (Rooth D_τ): all operators regardless
    of UPOS → {p, ¬p, □p}. Over-generates. -/
def typeTheoAlternatives : List (PolarWorld → Bool) :=
  typeTheoAlts opLexicon

/-- Category-match alternatives (Fox & Katzir 2011): only `PART`-tagged
    operators → {p, ¬p}. Correct. -/
def catMatchAlternatives : List (PolarWorld → Bool) :=
  categoryMatchAlts .PART opLexicon

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Hamblin Questions
-- ═══════════════════════════════════════════════════════════════════════

/-- Type-theoretic question: {p, ¬p, □p} — over-generated. -/
def typeTheoQ : QuestionDen PolarWorld :=
  fromAlternatives typeTheoAlternatives allWorlds

/-- Category-match question: {p, ¬p} — correct. -/
def catMatchQ : QuestionDen PolarWorld :=
  fromAlternatives catMatchAlternatives allWorlds

/-- The expected polar question: {p, ¬p}. -/
def polarQ : QuestionDen PolarWorld :=
  polar p allWorlds

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Core Theorems
-- ═══════════════════════════════════════════════════════════════════════

/-- Category-matched question = standard polar question.
    Fox & Katzir's category match yields the correct {p, ¬p} partition. -/
theorem catMatch_eq_polar :
    (catMatchQ mustP = polarQ mustP) ∧
    (catMatchQ p = polarQ p) ∧
    (catMatchQ notP = polarQ notP) := by native_decide

/-- Type-theoretic question ≠ polar question.
    The D_τ computation admits □p as an answer, which the polar
    question rejects. -/
theorem typeTheo_ne_polar :
    typeTheoQ mustP ≠ polarQ mustP := by native_decide

/-- The spurious prediction: □p is an answer to the type-theoretic question.
    Under Rooth-style D_τ, "Ali must sleep" is predicted to be a felicitous
    answer to "Does Ali sleep?" — which is empirically wrong. -/
theorem typeTheo_admits_modal :
    isAnswer typeTheoQ mustP = true := by native_decide

/-- The correct prediction: □p is NOT an answer to the polar question.
    "Ali must sleep" is not a felicitous answer to a yes/no question
    about whether Ali sleeps. -/
theorem polar_rejects_modal :
    isAnswer polarQ mustP = false := by native_decide

/-- Category match fixes the over-generation: □p is NOT an answer
    to the category-matched question. -/
theorem catMatch_rejects_modal :
    isAnswer catMatchQ mustP = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Bridge: Data ↔ Theory
-- ═══════════════════════════════════════════════════════════════════════

/-! Connect the empirical judgments from `PolarAnswers.lean` to the
    formal model. The data says modal answers are infelicitous;
    the theory (category match) explains why: □p is excluded from
    the Hamblin alternative set. -/

open Phenomena.Questions.PolarAnswers

/-- The empirical datum: modal answer is infelicitous. -/
theorem data_modal_infelicitous :
    turkishPolar_must.felicitous = false := rfl

/-- The theory predicts it: □p is not an answer under category match. -/
theorem theory_modal_excluded :
    isAnswer catMatchQ mustP = false := by native_decide

/-- The theory would wrongly predict felicity without category match. -/
theorem theory_overgen_without_catmatch :
    isAnswer typeTheoQ mustP = true := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §7  Bridge: K&S 2020 AltMeaning
-- ═══════════════════════════════════════════════════════════════════════

/-! The connection to Kratzer & Selkirk (2020) is via the A-value of
    a [FoC]-marked expression. In Rooth/K&S's framework, the A-value
    of a [FoC]-marked constituent is the set of alternatives of the
    same semantic type — i.e., exactly the type-theoretic D_τ computation.

    Turk et al.'s contribution is showing that this over-generates for
    Turkish polar questions, and that category match (Fox & Katzir 2011)
    is the correct constraint on alternative computation. -/

/-- Applying [FoC] with type-theoretic A-value yields the over-generating set. -/
def applyFoC_typeTheo : AltMeaning (PolarWorld → Bool) :=
  { oValue := p, aValue := typeTheoAlternatives }

/-- The type-theoretic A-value produces the wrong question denotation. -/
theorem applyFoC_is_typeTheo :
    fromAlternatives applyFoC_typeTheo.aValue allWorlds mustP = true := by
  native_decide

/-- Restricting the A-value by category match corrects the prediction. -/
def applyFoC_catMatch : AltMeaning (PolarWorld → Bool) :=
  { oValue := p, aValue := catMatchAlternatives }

/-- The category-matched A-value produces the correct question denotation. -/
theorem categoryMatch_fixes_applyFoC :
    fromAlternatives applyFoC_catMatch.aValue allWorlds mustP = false := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Turkish Fragment Connection
-- ═══════════════════════════════════════════════════════════════════════

open Fragments.Turkish.QuestionParticles

/-- The Turkish mI particle's UPOS tag matches the category used in
    the category-match computation. -/
theorem mi_category_matches :
    mi.cat = UD.UPOS.PART := rfl

end Phenomena.Questions.Studies.TurkHirschInce2026Bridge
