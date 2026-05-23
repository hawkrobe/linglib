import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

/-!
# Person Features as Presuppositions
@cite{schlenker-2003}

@cite{schlenker-2003}'s MELP (Monstrous Egli Language with Presuppositions)
treats person features as presuppositions on the context:

- `+author*(x)`: x is the agent of the utterance context c*
- `+author(x, cᵢ)`: x is the agent of context cᵢ (at tower depth i)

Logophoric pronouns are then derived as `+author(x, cᵢ) ∧ −author*(x)`:
the referent is the agent of an embedded context but NOT the actual speaker.

## Key Definitions

- `PersonFeature`: a presuppositional constraint parameterized by tower depth
- `authorAt`: +author(x, d) — x is the agent at depth d
- `authorStar`: +author*(x) = authorAt .origin
- `isLogophoric`: +author(x, cᵢ) ∧ −author*(x)

## Key Results

- `authorStar_root`: in a root tower, +author* checks against the origin agent
- `authorLocal_shifted`: under attitude shift, +author(local) picks out the holder
- `logophoric_refers_to_holder`: logophoric pronouns refer to the attitude holder
  when the holder differs from the speaker
- `speaker_not_logophoric`: the actual speaker never satisfies the logophoric
  condition
-/

namespace Semantics.Reference.PersonFeatures

open Core.Context

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

-- ════════════════════════════════════════════════════════════════
-- § Person Features
-- ════════════════════════════════════════════════════════════════

/-- A person feature: a presuppositional constraint on which entity can
    serve as the referent of a pronoun, parameterized by which context
    layer the feature refers to.

    In @cite{schlenker-2003}'s MELP, person features are presuppositions
    of the form "+F(x, c)" where F is a feature (author, hearer),
    x is the entity, and c is a context variable bound by an attitude
    operator. -/
structure PersonFeature (W E P T : Type*) where
  /-- Which tower depth the feature refers to -/
  depth : DepthSpec
  /-- The constraint: does entity x satisfy the feature relative to context c? -/
  check : E → KContext W E P T → Bool

/-- Evaluate a person feature against a tower: resolve the depth to a
    concrete context layer and check the constraint. -/
def PersonFeature.eval (f : PersonFeature W E P T)
    (x : E) (t : ContextTower (KContext W E P T)) : Bool :=
  f.check x (t.contextAt (f.depth.resolve t.depth))

-- ════════════════════════════════════════════════════════════════
-- § Standard Features
-- ════════════════════════════════════════════════════════════════

/-- +author(x, d): x is the agent of the context at depth d.

    @cite{schlenker-2003}: "+author(x, cᵢ)" presupposes that x is the
    agent (speaker) of context cᵢ. In the tower framework, cᵢ is
    resolved by `contextAt (d.resolve depth)`. -/
def authorAt [BEq E] (d : DepthSpec) : PersonFeature W E P T :=
  { depth := d, check := fun x c => x == c.agent }

/-- +author*(x) = +author(x, c*): x is the agent of the utterance
    context. The star notation indicates the utterance context (origin).

    Using "I" presupposes that the referent is the actual speaker. -/
def authorStar [BEq E] : PersonFeature W E P T := authorAt .origin

/-- +hearer(x, d): x is the addressee of the context at depth d.

    Using "you" presupposes that the referent is the addressee. -/
def hearerAt [BEq E] (d : DepthSpec) : PersonFeature W E P T :=
  { depth := d, check := fun x c => x == c.addressee }

/-- +hearer*(x) = +hearer(x, c*): x is the addressee of the utterance
    context. -/
def hearerStar [BEq E] : PersonFeature W E P T := hearerAt .origin

-- ════════════════════════════════════════════════════════════════
-- § Logophoric Pronouns
-- ════════════════════════════════════════════════════════════════

/-- Logophoric pronoun condition: +author(x, cᵢ) ∧ −author*(x).

    @cite{schlenker-2003} §6: logophoric pronouns in languages like Ewe are
    licensed in embedded clauses where x is the agent of the embedding
    context (attitude holder) but NOT the agent of the utterance context
    (actual speaker).

    This formalizes the key insight: logophoric pronouns are derived from
    the interaction of two person features — one referring to an embedded
    context variable, one to the utterance context. -/
def isLogophoric [BEq E] (x : E) (t : ContextTower (KContext W E P T))
    (embeddedDepth : DepthSpec) : Bool :=
  (authorAt embeddedDepth).eval x t &&
  !(authorStar (W := W) (P := P) (T := T)).eval x t

-- ════════════════════════════════════════════════════════════════
-- § Properties
-- ════════════════════════════════════════════════════════════════

/-- In a root tower, +author* checks against the origin agent. -/
@[simp] theorem authorStar_root [BEq E] (x : E) (c : KContext W E P T) :
    (authorStar (W := W) (P := P) (T := T)).eval x
      (ContextTower.root c) = (x == c.agent) := rfl

/-- Under an attitude shift, +author(x, local) is satisfied when x is the
    attitude holder. -/
theorem authorLocal_shifted [BEq E] [LawfulBEq E]
    (holder : E) (w' : W)
    (t : ContextTower (KContext W E P T)) :
    (authorAt (W := W) (P := P) (T := T) .local).eval holder
      (t.push (attitudeShift holder w')) = true := by
  simp only [authorAt, PersonFeature.eval, DepthSpec.local_resolve,
    ContextTower.contextAt_depth, ContextTower.push_innermost,
    attitudeShift, beq_self_eq_true]

/-- A logophoric pronoun refers to the attitude holder when the holder
    differs from the speaker.

    Given: the speaker is the origin agent, and the holder ≠ speaker.
    Then under attitude shift, the holder satisfies +author(local) (they
    are the agent of the shifted context) and fails +author* (they are
    not the actual speaker). -/
theorem logophoric_refers_to_holder [BEq E] [LawfulBEq E]
    (holder : E) (w' : W)
    (t : ContextTower (KContext W E P T))
    (hDiff : (holder == t.origin.agent) = false) :
    isLogophoric holder (t.push (attitudeShift holder w')) .local = true := by
  unfold isLogophoric
  rw [authorLocal_shifted]
  simp only [Bool.true_and, authorStar, authorAt, PersonFeature.eval,
    DepthSpec.origin_resolve, ContextTower.contextAt_zero,
    ContextTower.push_origin, hDiff, Bool.not_false]

/-- The actual speaker never satisfies the logophoric condition: +author*
    is always true for the origin agent, so −author* blocks logophoricity.

    This is why logophoric pronouns are restricted to embedded contexts —
    the actual speaker cannot be logophoric in their own utterance. -/
theorem speaker_not_logophoric [BEq E] [LawfulBEq E]
    (t : ContextTower (KContext W E P T)) (d : DepthSpec) :
    isLogophoric t.origin.agent t d = false := by
  simp only [isLogophoric, authorStar, authorAt, PersonFeature.eval,
    DepthSpec.origin_resolve, ContextTower.contextAt_zero,
    beq_self_eq_true, Bool.not_true, Bool.and_false]

end Semantics.Reference.PersonFeatures
