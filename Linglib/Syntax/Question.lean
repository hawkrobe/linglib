import Linglib.Data.WALS.Features.F92A
import Linglib.Data.WALS.Features.F93A
import Linglib.Data.WALS.Features.F116A

/-!
# Question typology — substrate
[wals-2013] [pesetsky-1987] [huang-1982]
[sato-ngui-2017] [chan-shen-2026]

Per-language question-typology substrate for Fragment import. Mirrors the
`Linglib/Typology/{Domain}.lean` pattern (Possession, Case, Phonology,
WordOrder).

## Substrate enums

- `WhMovementStrategy` (WALS Ch 93A)
- `WhInterpMechanism` ([pesetsky-1987], [huang-1982],
  [sato-ngui-2017])
- `QParticlePosition` (WALS Ch 92A)
- `PolarQuestionStrategy` (WALS Ch 116A)
- `QuestionProfile`: bundle struct over Chs 92A/93A/116A
- `MWFParameter`: multiple-wh-fronting parameter ([rudin-1988],
  with [citko-gracanin-yuksek-2025]'s tri-valued refinement
  splitting non-MWF into vP-only vs both-edges asterisk languages)
- `PhaseEdge`: which phase edge an asterisk lands on
- `EdgeAsterisk`/`MWFViolation`/`EllipsisRepairsMWF`: Prop predicates
  derived from `MWFParameter`

## Theory-laden caveats

- **`WhInterpMechanism` is NOT theory-neutral.** The four mechanisms
  (`overtMovement`, `covertMovement`, `partialMovement`,
  `unselectiveBinding`) commit to a movement-vs-binding split that is
  contested. Cable 2010's Q-particle Agree analysis, Reinhart's choice
  functions, and Beck 2006's intervention-based account each derive the
  same surface position via different mechanisms. The `partialMovement`
  case is specifically Sato &amp; Ngui 2017's Singlish analysis.

- **The cartographic clause-typing locus is contested.** Rizzi 1997 places
  it at `Force⁰[+Q]`; Holmberg 2016 places it at `Pol⁰`; Dayal 2025 places
  it at `C` with PerspP-shift. `QuestionProfile` is silent on this — see
  `Studies/Dayal2025.lean`,
  `Studies/Holmberg2016.lean`, and
  `Syntax/Minimalist/Questions.lean` for competing analyses.

## WALS aggregates

WALS chapter aggregate distributions (`ch92Total`, `ch93Total`, etc.)
live in this file at the substrate layer per the project's "WALS goes to
`Linglib/Typology/`" rule. Cross-linguistic theorems consuming Fragment
per-language data live in
`Studies/Dryer2013Question.lean`.
-/

set_option autoImplicit false

namespace Syntax.Question

private abbrev ch92  := Data.WALS.F92A.allData
private abbrev ch93  := Data.WALS.F93A.allData
private abbrev ch116 := Data.WALS.F116A.allData

/-- WALS Ch 93A: position of interrogative phrases (wh-words). -/
inductive WhMovementStrategy where
  /-- Wh-phrase obligatorily fronted (overt wh-movement). -/
  | initial
  /-- Wh-phrase stays in situ. -/
  | inSitu
  /-- Both strategies available. -/
  | mixed
  deriving DecidableEq, Repr

/-- How a wh-phrase is interpreted at the syntax-semantics interface.
    Distinct from `WhMovementStrategy` (surface position): the same surface
    position (in-situ) can arise from different mechanisms (covert movement
    vs unselective binding), with different empirical consequences for
    island sensitivity and modifier licensing.

    [pesetsky-1987] [sato-ngui-2017] [chan-shen-2026] -/
inductive WhInterpMechanism where
  /-- Successive cyclic overt movement to matrix Spec-CP. -/
  | overtMovement
  /-- Single LF movement to Spec-CP ([huang-1982]; Mandarin *daodi*). -/
  | covertMovement
  /-- Two-step: overt to intermediate Spec-CP, *then* covert to matrix
      Spec-CP. This is Singlish partial wh-movement
      ([sato-ngui-2017]). Distinct from `.covertMovement` because
      the overt-then-covert derivation has both a Spell-Out landing site
      and a separate covert step that crosses islands at LF. -/
  | partialMovement
  /-- Q operator in C binds variable in situ; no movement (overt or
      covert). Island-insensitive. -/
  | unselectiveBinding
  deriving DecidableEq, Repr

/-- Does this mechanism involve the wh-phrase reaching matrix Spec-CP
    (overtly or covertly, in one step or two)? -/
def WhInterpMechanism.ReachesSpecCP : WhInterpMechanism → Prop
  | .overtMovement      => True
  | .covertMovement     => True
  | .partialMovement    => True
  | .unselectiveBinding => False

instance (m : WhInterpMechanism) : Decidable m.ReachesSpecCP := by
  cases m <;> unfold WhInterpMechanism.ReachesSpecCP <;> infer_instance

/-- Is this mechanism sensitive to syntactic islands? Partial movement
    *is* island-sensitive at its covert step ([sato-ngui-2017]: ex 15). -/
def WhInterpMechanism.IslandSensitive : WhInterpMechanism → Prop
  | .overtMovement      => True
  | .covertMovement     => True
  | .partialMovement    => True
  | .unselectiveBinding => False

instance (m : WhInterpMechanism) : Decidable m.IslandSensitive := by
  cases m <;> unfold WhInterpMechanism.IslandSensitive <;> infer_instance

/-- Does this mechanism involve a covert movement step? Distinguishes
    overt-only from covert/partial. Used by analyses that care about
    LF-only operations (e.g., island sensitivity diagnostics). -/
def WhInterpMechanism.HasCovertStep : WhInterpMechanism → Prop
  | .overtMovement      => False
  | .covertMovement     => True
  | .partialMovement    => True
  | .unselectiveBinding => False

instance (m : WhInterpMechanism) : Decidable m.HasCovertStep := by
  cases m <;> unfold WhInterpMechanism.HasCovertStep <;> infer_instance

/-- For all current mechanisms, `ReachesSpecCP` and `IslandSensitive`
    coincide. This is a contingent fact about the current taxonomy, not
    a necessary truth: a future mechanism (e.g., long-distance Agree) could
    be island-sensitive without reaching Spec-CP, or reach Spec-CP without
    island sensitivity. The predicates are kept separate for this reason. -/
theorem reachesSpecCP_iff_islandSensitive (m : WhInterpMechanism) :
    m.ReachesSpecCP ↔ m.IslandSensitive := by
  cases m <;> exact Iff.rfl

/-- WALS Ch 92A: position of polar question particles. -/
inductive QParticlePosition where
  /-- Particle precedes the clause. -/
  | initial
  /-- Particle follows the clause. -/
  | final
  /-- Particle in second (Wackernagel) position. -/
  | secondPosition
  /-- Other position. -/
  | otherPosition
  /-- In either of two positions. -/
  | eitherOfTwo
  /-- No question particle in the language. -/
  | noParticle
  deriving DecidableEq, Repr

/-- WALS Ch 116A: how polar questions are formed. -/
inductive PolarQuestionStrategy where
  /-- Dedicated question particle. -/
  | particle
  /-- Interrogative verb morphology. -/
  | verbMorphology
  /-- Mixture of particle and verb morphology. -/
  | particleOrMorphology
  /-- Interrogative word order (e.g., subject-aux inversion). -/
  | wordOrder
  /-- Absence of declarative morphemes. -/
  | absenceOfDeclarative
  /-- Interrogative intonation only. -/
  | intonationOnly
  /-- No interrogative-declarative distinction. -/
  | noDistinction
  deriving DecidableEq, Repr

/-- A language's question-formation profile across [wals-2013]
    Chs 92A, 93A, 116A. Each field is `Option` since WALS samples vary
    by chapter. -/
structure QuestionProfile where
  /-- Language name. -/
  language : String
  /-- WALS language code. -/
  walsCode : String
  /-- Ch 92A: position of polar question particles. -/
  qParticlePos : Option QParticlePosition := none
  /-- Ch 93A: wh-phrase position in content questions. -/
  whMovement : Option WhMovementStrategy := none
  /-- Ch 116A: strategy for forming polar questions. -/
  polarStrategy : Option PolarQuestionStrategy := none
  deriving Repr, DecidableEq

-- ============================================================================
-- §2. WALS converters (Ch 92A, 93A, 116A)
-- ============================================================================

/-- WALS Ch 92A → `QParticlePosition`. -/
def fromWALS92A : Data.WALS.F92A.PositionOfPolarQuestionParticles →
    QParticlePosition
  | .initial                => .initial
  | .final                  => .final
  | .secondPosition         => .secondPosition
  | .otherPosition          => .otherPosition
  | .inEitherOfTwoPositions => .eitherOfTwo
  | .noQuestionParticle     => .noParticle

/-- WALS Ch 93A → `WhMovementStrategy`. -/
def fromWALS93A :
    Data.WALS.F93A.PositionOfInterrogativePhrasesInContentQuestions →
    WhMovementStrategy
  | .initialInterrogativePhrase    => .initial
  | .notInitialInterrogativePhrase => .inSitu
  | .mixed                         => .mixed

/-- WALS Ch 116A → `PolarQuestionStrategy`. -/
def fromWALS116A : Data.WALS.F116A.PolarQuestionType →
    PolarQuestionStrategy
  | .questionParticle                      => .particle
  | .interrogativeVerbMorphology           => .verbMorphology
  | .mixtureOfPreviousTwoTypes             => .particleOrMorphology
  | .interrogativeWordOrder                => .wordOrder
  | .absenceOfDeclarativeMorphemes         => .absenceOfDeclarative
  | .interrogativeIntonationOnly           => .intonationOnly
  | .noInterrogativeDeclarativeDistinction => .noDistinction

-- ============================================================================
-- §3. Multiple Wh-Fronting parameter ([rudin-1988], refined by
--      [citko-gracanin-yuksek-2025] p. 19)
-- ============================================================================

/-- The MWF parameter as in [rudin-1988] + [citko-gracanin-yuksek-2025].

    The textbook contrast ([rudin-1988]) is binary — MWF (Bulgarian,
    Romanian) vs non-MWF (English, German, Greek). C&G-Y refine the
    non-MWF case by where the PF asterisk for multiple wh-specifiers
    lands: vP-only (sluicing repairs by deleting vP) vs both vP and CP
    (sluicing leaves the CP-edge asterisk unrepaired). The tripartition
    lets the multiple-sluicing asymmetry be **derived** from the
    parameter rather than stipulated as an independent flag. -/
inductive MWFParameter where
  /-- Multiple wh-fronting language (Bulgarian, Romanian). No PF asterisk
      at any edge. -/
  | fronts
  /-- Non-MWF with vP-only asterisk (German, Greek;
      [citko-gracanin-yuksek-2025] "English variety B"). Sluicing
      (deleting the vP edge) repairs. -/
  | nonFrontsVPOnly
  /-- Non-MWF with asterisks at *both* vP and CP edges
      ([citko-gracanin-yuksek-2025] "English variety A"). Sluicing
      cannot repair — the CP-edge asterisk survives ellipsis. -/
  | nonFrontsBothEdges
  deriving DecidableEq, Repr

/-- Which phase edge is being checked for an MWF asterisk. -/
inductive PhaseEdge where
  | vP
  | CP
  deriving DecidableEq, Repr

namespace MWFParameter

/-- The language allows multiple wh-fronting in matrix questions. -/
def AllowsMWF : MWFParameter → Prop
  | .fronts => True
  | .nonFrontsVPOnly | .nonFrontsBothEdges => False

instance (p : MWFParameter) : Decidable (AllowsMWF p) := by
  cases p <;> unfold AllowsMWF <;> infer_instance

/-- The given phase edge incurs a PF asterisk under `n > 1`
    wh-specifiers. Generalizes the per-edge `vPEdgeAsterisk` /
    `cPEdgeAsterisk` distinction earlier revisions of this code carried
    as separate definitions. -/
def EdgeAsterisk : MWFParameter → PhaseEdge → Nat → Prop
  | .fronts,             _,    _ => False
  | .nonFrontsVPOnly,    .vP,  n => n > 1
  | .nonFrontsVPOnly,    .CP,  _ => False
  | .nonFrontsBothEdges, _,    n => n > 1

instance (p : MWFParameter) (e : PhaseEdge) (n : Nat) :
    Decidable (EdgeAsterisk p e n) := by
  cases p <;> cases e <;> unfold EdgeAsterisk <;> infer_instance

end MWFParameter

/-- A multiple-wh-fronting violation: *some* phase edge incurs an
    asterisk for `n` wh-specifiers. -/
def MWFViolation (p : MWFParameter) (n : Nat) : Prop :=
  p.EdgeAsterisk .vP n ∨ p.EdgeAsterisk .CP n

instance (p : MWFParameter) (n : Nat) : Decidable (MWFViolation p n) := by
  unfold MWFViolation; infer_instance

/-- Ellipsis of the vP edge repairs an MWF violation iff doing so
    eliminates every asterisk — i.e., there is no surviving CP-edge
    asterisk. In `nonFrontsVPOnly` languages, deleting the vP edge
    removes the only asterisk; in `nonFrontsBothEdges`, the CP-edge
    asterisk survives. -/
def EllipsisRepairsMWF (p : MWFParameter) (n : Nat) (vpEdgeDeleted : Bool) : Prop :=
  ¬ MWFViolation p n ∨ (vpEdgeDeleted = true ∧ ¬ p.EdgeAsterisk .CP n)

instance (p : MWFParameter) (n : Nat) (vpDel : Bool) :
    Decidable (EllipsisRepairsMWF p n vpDel) := by
  unfold EllipsisRepairsMWF; infer_instance

/-- Single wh-specifier never triggers an MWF violation. -/
theorem single_wh_no_violation (p : MWFParameter) :
    ¬ MWFViolation p 1 := by
  cases p <;> decide

/-- Zero wh-specifiers never trigger an MWF violation. -/
theorem zero_wh_no_violation (p : MWFParameter) :
    ¬ MWFViolation p 0 := by
  cases p <;> decide

/-- MWF languages never have violations. -/
theorem mwf_language_no_violation (p : MWFParameter)
    (h : p.AllowsMWF) (n : Nat) : ¬ MWFViolation p n := by
  cases p <;> simp_all [MWFParameter.AllowsMWF, MWFViolation,
    MWFParameter.EdgeAsterisk]

end Syntax.Question

