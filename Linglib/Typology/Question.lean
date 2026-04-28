/-!
# Question typology — wh-movement and interpretation mechanism enums
@cite{wals-2013} @cite{pesetsky-1987} @cite{huang-1982}
@cite{sato-ngui-2017} @cite{chan-shen-2026}

Type-level enums for wh-movement strategies and the syntax-semantics
mechanisms that derive them, extracted from
`Phenomena/Questions/Typology.lean` so that Fragments can import them
without violating the Fragments → Phenomena dependency rule.
-/

set_option autoImplicit false

namespace Typology.Question

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

    @cite{pesetsky-1987} @cite{sato-ngui-2017} @cite{chan-shen-2026} -/
inductive WhInterpMechanism where
  /-- Successive cyclic overt movement to matrix Spec-CP. -/
  | overtMovement
  /-- Single LF movement to Spec-CP (@cite{huang-1982}; Mandarin *daodi*). -/
  | covertMovement
  /-- Two-step: overt to intermediate Spec-CP, *then* covert to matrix
      Spec-CP. This is Singlish partial wh-movement
      (@cite{sato-ngui-2017}). Distinct from `.covertMovement` because
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
    *is* island-sensitive at its covert step (@cite{sato-ngui-2017}: ex 15). -/
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

/-- A language's question-formation profile across @cite{wals-2013}
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

end Typology.Question
