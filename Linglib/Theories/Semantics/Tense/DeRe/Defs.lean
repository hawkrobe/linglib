import Linglib.Theories.Semantics.Tense.Basic

/-!
# Temporal De Re — substrate
@cite{abusch-1997}

The `TemporalDeRe` structure: the *output* of res-movement (a
back-shifted frame with a constraint tag), as a substrate primitive.
The actual LF rewrite mechanism + time-concept (acquaintance relation)
machinery is not formalized; only the output-level structure is.

@cite{abusch-1997}'s paper-anchored derivation theorems live in
`Phenomena/TenseAspect/Studies/Abusch1997.lean`. The substrate file
also has `upperLimitConstraint` in `Theories/Semantics/Tense/Basic.lean`
(value-level reduction; modal-layer formulation deferred per
@cite{klecha-2016} `WorldHistory` discipline).
-/

namespace Semantics.Tense.DeRe

open Core.Time.Tense
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § Temporal De Re structure
-- ════════════════════════════════════════════════════════════════

/-- @cite{abusch-1997}'s temporal de re: a tense variable can take
    wide scope over an attitude operator by occupying the res position.

    The res has three components:
    - `referent`: the time denoted (resolved in the matrix context)
    - `evalTime`: the evaluation time in the embedded context
    - `constraint`: the presupposed temporal relation

    This parallels individual de re: "John believes the president is
    wise" where "the president" is evaluated in the actual world, not
    in John's belief worlds. Similarly, temporal de re evaluates tense
    in the matrix temporal context.

    Note: this structure captures the *output* of res-movement (a
    back-shifted frame with a constraint tag), not the LF mechanism.
    Abusch's actual de re involves an LF rewrite that abstracts a tense
    variable above the attitude operator and reintroduces it via a
    time-concept (acquaintance relation). Formalizing res-movement as
    an LF rewrite is deferred. -/
structure TemporalDeRe (Time : Type*) where
  /-- The time referred to (resolved in matrix context) -/
  referent : Time
  /-- The evaluation time (shifted by attitude) -/
  evalTime : Time
  /-- The temporal constraint (past/present/future) -/
  constraint : GramTense

/-- A temporal de re is felicitous when the constraint is satisfied
    in the matrix context (referent checked against matrix eval time). -/
def TemporalDeRe.isFelicitous {Time : Type*} [LinearOrder Time]
    (dr : TemporalDeRe Time) : Prop :=
  dr.constraint.constrains dr.referent dr.evalTime


end Semantics.Tense.DeRe
