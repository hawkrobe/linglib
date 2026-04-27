import Linglib.Features.InformationStructure
import Linglib.Core.IntensionalLogic.Premise
import Linglib.Core.Lexical.UD
import Linglib.Theories.Semantics.Alternatives.AltMeaning
import Linglib.Theories.Semantics.Polarity.Operator
import Linglib.Theories.Semantics.Focus.Interpretation
import Linglib.Fragments.Turkish.QuestionParticles
import Linglib.Phenomena.Questions.PolarAnswers
import Mathlib.Data.Set.Basic

/-!
# Türk & Hirsch (2026) — Category Match constrains polar question alternatives
@cite{turk-hirsch-2026} @cite{atlamaz-2023} @cite{fox-katzir-2011} @cite{rooth-1992}

Connects the empirical judgments in `PolarAnswers.lean` (modal answers
are infelicitous to Turkish polar questions) to the formal explanation
@cite{turk-hirsch-2026} propose: @cite{fox-katzir-2011} category match
over UPOS tags applied to the focus alternatives evoked by the polarity
head Σ_F that hosts Turkish *mI*.

## The puzzle

Following @cite{atlamaz-2023}'s bidimensional analysis, Turkish *mI* heads
PolP and bears focus (Σ_F). Under @cite{rooth-1992}-style type-theoretic
alternative computation, any operator of the same semantic type counts as
an alternative — including deontic modals. This yields {p, ¬p, □p}, wrongly
predicting □p is a felicitous answer.

## The fix

Category match restricts alternatives to items sharing *mI*'s UPOS tag
`PART`. Polarity operators (Σ = `id`, NEG = `pnot`) are `PART`; "must"
is `AUX`. Category match yields {p, ¬p} — the correct polar question.

## Scenario

Four worlds: Ali sleeps/doesn't × deontic must/free.
-/

namespace Phenomena.Focus.Studies.TurkHirsch2026

open Features.InformationStructure
open Semantics.Alternatives
open Semantics.FocusInterpretation (PropFocusValue)

-- ═══════════════════════════════════════════════════════════════════════
-- §1  World type and propositions
-- ═══════════════════════════════════════════════════════════════════════

/-- Four worlds crossing Ali-sleeps with deontic-must. -/
inductive PolarWorld where
  | sleeps_must   -- Ali sleeps, must is in force
  | sleeps_free   -- Ali sleeps, no deontic necessity
  | nosleep_must  -- Ali doesn't sleep, must is in force
  | nosleep_free  -- Ali doesn't sleep, no deontic necessity
  deriving DecidableEq, Repr

open PolarWorld

def allWorlds : List PolarWorld :=
  [sleeps_must, sleeps_free, nosleep_must, nosleep_free]

/-- p = "Ali sleeps": holds at the worlds where Ali sleeps. -/
def p : Set PolarWorld := {sleeps_must, sleeps_free}

/-- ¬p = "Ali doesn't sleep". Set complement of `p`. -/
def notP : Set PolarWorld := pᶜ

/-! Deontic must, grounded in @cite{kratzer-1977}'s premise-set semantics.

    The deontic source maps each world to the propositions encoding the
    deontic obligations in force at that world. In the *_must worlds the
    obligation "Ali sleeps" is in force; in the *_free worlds nothing is.
    `mustP` is then the Bool reflection of `mustInView deonticBase pProp` —
    no longer a stipulated 4-row table. -/

/-- Prop view of `p` for use with the polymorphic Kratzer machinery
    (which lives at type `Index → Prop`). Just set membership. -/
def pProp : PolarWorld → Prop := fun w => w ∈ p

/-- The deontic premise set: in must-worlds the obligation `pProp` is
    in force; in free-worlds the premise set is empty. -/
def deonticBase : PolarWorld → List (PolarWorld → Prop)
  | sleeps_must  => [pProp]
  | nosleep_must => [pProp]
  | sleeps_free  => []
  | nosleep_free => []

/-- Kratzer-grounded deontic must: `□p` as @cite{kratzer-1977} Def 5
    (`mustInView`) over the deontic premise set. -/
def mustGrounded (w : PolarWorld) : Prop :=
  Core.IntensionalLogic.Premise.mustInView deonticBase pProp w

/-- □p = "Ali must sleep" (deontic necessity). The Set reflection of
    `mustGrounded`; equivalence proved by `mustP_iff_mustGrounded`. -/
def mustP : Set PolarWorld := {sleeps_must, nosleep_must}

/-- The stipulated table matches the Kratzer-grounded derivation. The
    over-generation argument below is therefore about a genuine modal
    proposition, not a hand-tuned function. -/
theorem mustP_iff_mustGrounded (w : PolarWorld) :
    w ∈ mustP ↔ mustGrounded w := by
  unfold mustGrounded Core.IntensionalLogic.Premise.mustInView
         Core.IntensionalLogic.Premise.followsFrom
         Core.IntensionalLogic.Premise.propIntersection
         Core.IntensionalLogic.Premise.propExtension
  cases w
  · -- sleeps_must: deonticBase = [pProp], obligation entails p
    simp [mustP, deonticBase, pProp, p]
  · -- sleeps_free: deonticBase = [], requires p at every world — fails at nosleep_must
    refine iff_of_false (by simp [mustP]) ?_
    intro h
    have hmem : nosleep_must ∈ ({a | ∀ p ∈ deonticBase sleeps_free, p a} : Set _) := by
      simp [deonticBase]
    have := h hmem
    simp [pProp, p] at this
  · -- nosleep_must: deonticBase = [pProp], obligation entails p
    simp [mustP, deonticBase, pProp, p]
  · -- nosleep_free: deonticBase = [], same shape as sleeps_free
    refine iff_of_false (by simp [mustP]) ?_
    intro h
    have hmem : nosleep_must ∈ ({a | ∀ p ∈ deonticBase nosleep_free, p a} : Set _) := by
      simp [deonticBase]
    have := h hmem
    simp [pProp, p] at this

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Operators as UPOS-tagged items
-- ═══════════════════════════════════════════════════════════════════════

/-- A denotation tagged with its UD UPOS category. Study-internal
    utility used to model @cite{turk-hirsch-2026}'s claim that *mI*'s
    PART tag licenses only PART-tagged alternatives. -/
structure TaggedDen (α : Type) where
  cat : UD.UPOS
  den : α
  deriving Repr

/-- The lexicon of propositional operators at type ⟨⟨s,t⟩,t⟩.
    Polarity heads (Σ, NEG) are tagged `PART`; the deontic modal is `AUX`.
    This UPOS distinction is what category match exploits. -/
def opLexicon : List (TaggedDen (Set PolarWorld)) :=
  [⟨.PART, p⟩, ⟨.PART, notP⟩, ⟨.AUX, mustP⟩]

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Alternative sets
-- ═══════════════════════════════════════════════════════════════════════

/-- Type-theoretic alternatives (@cite{rooth-1985} D_τ): all operators
    regardless of UPOS → {p, ¬p, □p}. Over-generates. -/
def typeTheoAlternatives : List (Set PolarWorld) :=
  opLexicon.map (·.den)

/-- Category-match alternatives: only `PART`-tagged
    operators → {p, ¬p}. Correct. -/
def catMatchAlternatives : List (Set PolarWorld) :=
  (opLexicon.filter (·.cat == .PART)).map (·.den)

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Hamblin questions
-- ═══════════════════════════════════════════════════════════════════════

/-- Type-theoretic question: {p, ¬p, □p} — over-generated. -/
def typeTheoQ : PropFocusValue PolarWorld :=
  { q | q ∈ typeTheoAlternatives }

/-- Category-match question: {p, ¬p} — correct. -/
def catMatchQ : PropFocusValue PolarWorld :=
  { q | q ∈ catMatchAlternatives }

/-- The expected polar question: {p, ¬p}. -/
def polarQ : PropFocusValue PolarWorld := {p, notP}

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Core theorems
-- ═══════════════════════════════════════════════════════════════════════

/-- Category-matched question = standard polar question.
    @cite{fox-katzir-2011}'s category match yields the correct {p, ¬p} partition.
    `catMatchAlternatives` filters opLexicon to `[p, notP]`, and the
    resulting set-of-alternatives equals the polar `{p, notP}` literal. -/
theorem catMatch_eq_polar : catMatchQ = polarQ := by
  ext q
  simp [catMatchQ, polarQ, catMatchAlternatives, opLexicon]

/-- The spurious prediction: □p is an answer to the type-theoretic question.
    Under @cite{rooth-1992}-style D_τ, "Ali must sleep" is predicted to be a
    felicitous answer to "Does Ali sleep?" — which is empirically wrong. -/
theorem typeTheo_admits_modal : mustP ∈ typeTheoQ := by
  simp [typeTheoQ, typeTheoAlternatives, opLexicon]

/-- The correct prediction: □p is NOT an answer to the polar question.
    "Ali must sleep" is not a felicitous answer to a yes/no question
    about whether Ali sleeps. -/
theorem polar_rejects_modal : mustP ∉ polarQ := by
  intro h
  rcases h with h | h
  · -- mustP = p contradiction (different singletons membership)
    have : sleeps_free ∈ mustP := by
      rw [h]; simp [p]
    simp [mustP] at this
  · -- mustP = notP contradiction
    have : sleeps_must ∈ mustP := by simp [mustP]
    rw [h] at this
    simp [notP, p] at this

/-- Category match fixes the over-generation: □p is NOT an answer
    to the category-matched question. -/
theorem catMatch_rejects_modal : mustP ∉ catMatchQ := by
  rw [catMatch_eq_polar]
  exact polar_rejects_modal

/-- Type-theoretic question ≠ polar question. The D_τ computation
    admits □p, which the polar question rejects. -/
theorem typeTheo_ne_polar : typeTheoQ ≠ polarQ := by
  intro h
  exact polar_rejects_modal (h ▸ typeTheo_admits_modal)

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Bridge: data ↔ theory
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
theorem theory_modal_excluded : mustP ∉ catMatchQ :=
  catMatch_rejects_modal

/-- The theory would wrongly predict felicity without category match. -/
theorem theory_overgen_without_catmatch : mustP ∈ typeTheoQ :=
  typeTheo_admits_modal

-- ═══════════════════════════════════════════════════════════════════════
-- §7  Bridge: A-value computation
-- ═══════════════════════════════════════════════════════════════════════

/-! Following @cite{rooth-1992}, the A-value of a [FoC]-marked
    constituent is the set of alternatives of the same semantic type — i.e.,
    exactly the type-theoretic D_τ computation.

    @cite{turk-hirsch-2026}'s contribution is showing that this over-generates
    for Turkish polar questions, and that category match (@cite{fox-katzir-2011})
    is the correct constraint on alternative computation when the focus host
    is Σ_F. -/

/-- Applying [FoC] with type-theoretic A-value yields the over-generating set. -/
def applyFoC_typeTheo : AltMeaning (Set PolarWorld) :=
  { oValue := p, aValue := typeTheoAlternatives }

/-- The type-theoretic A-value produces the wrong question denotation. -/
theorem applyFoC_is_typeTheo : mustP ∈ ({q | q ∈ applyFoC_typeTheo.aValue} : Set _) := by
  simp [applyFoC_typeTheo, typeTheoAlternatives, opLexicon]

/-- Restricting the A-value by category match corrects the prediction. -/
def applyFoC_catMatch : AltMeaning (Set PolarWorld) :=
  { oValue := p, aValue := catMatchAlternatives }

/-- The category-matched A-value produces the correct question denotation. -/
theorem categoryMatch_fixes_applyFoC :
    mustP ∉ ({q | q ∈ applyFoC_catMatch.aValue} : Set _) := by
  simp only [applyFoC_catMatch, Set.mem_setOf_eq]
  show mustP ∉ catMatchAlternatives
  -- catMatchAlternatives = [p, notP]; mustP is neither.
  have hcm : catMatchAlternatives = [p, notP] := by
    simp [catMatchAlternatives, opLexicon]
  rw [hcm]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h)
  · -- mustP = p contradiction
    have : sleeps_free ∈ mustP := h ▸ (by simp [p])
    simp [mustP] at this
  · -- mustP = notP contradiction
    have : sleeps_must ∈ mustP := by simp [mustP]
    rw [h] at this
    simp [notP, p] at this

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Turkish fragment connection
-- ═══════════════════════════════════════════════════════════════════════

/-! The fragment exposes only theory-neutral lexical primitives. Here we
    add the theory-specific tagging that @cite{turk-hirsch-2026}'s analysis
    requires: a UPOS label (for @cite{fox-katzir-2011} category match) and
    a `Head` label (for @cite{laka-1990}-style PolP). These commitments
    live in the study file, not the fragment, so the fragment stays
    reusable across syntactic theories. -/

open Fragments.Turkish.QuestionParticles
open Semantics.Polarity

/-- Polarity-head labels assumed by this study (Laka-style ΣP/NEGP).
    Lean reserves `Σ` for sigma types, so the affirmative head's
    Lean-side identifier is `affirm` (the linguistic name "Σ" is
    preserved in docstrings). -/
inductive Head where
  /-- Affirmative polarity head (Laka's Σ). -/
  | affirm
  /-- Negation polarity head. -/
  | neg
  deriving DecidableEq, Repr

/-- The bare semantic operator each head spells out. -/
def Head.toOp : Head → ((PolarWorld → Prop) → (PolarWorld → Prop))
  | .affirm => Semantics.Polarity.affirm _
  | .neg    => Semantics.Polarity.neg _

/-- This study's commitments about Turkish *mI*. -/
structure MiAnalysis where
  /-- Which polarity head *mI* spells out (Σ in @cite{atlamaz-2023}). -/
  head : Head
  /-- UPOS tag used by @cite{fox-katzir-2011} category match. -/
  upos : UD.UPOS

/-- The @cite{turk-hirsch-2026} / @cite{atlamaz-2023} analysis: *mI* is Σ
    and tagged `PART`. -/
def miAnalysis : MiAnalysis :=
  { head := Head.affirm, upos := UD.UPOS.PART }

/-- *mI*'s lexical denotation matches the operator its analyzed head
    spells out — a definitional consistency check between the fragment
    entry and the head analysis adopted here. -/
theorem mi_denotation_matches_head :
    (mi.denotation : (PolarWorld → Prop) → (PolarWorld → Prop)) =
      miAnalysis.head.toOp := rfl

/-- The UPOS tag this study assigns to *mI* matches the category used in
    the alternative-restriction computation. -/
theorem mi_category_matches :
    miAnalysis.upos = UD.UPOS.PART := rfl

end Phenomena.Focus.Studies.TurkHirsch2026
