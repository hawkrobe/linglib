import Linglib.Phenomena.Modality.Studies.Yalcin2007

/-!
# @cite{mandelkern-2019}: Wittgenstein Sentences and Distributivity Failure

@cite{mandelkern-2019}

Mandelkern (2019) "Bounded Modality" (*Philosophical Review* 128(1):1-61)
sharpens Yalcin's (2007) program in two ways:

1. **Terminology**: Mandelkern coined the term *Wittgenstein sentences* for
   the symmetric form `◇¬p ∧ p` ("It might not be raining and it is
   raining"). Yalcin's original term was "epistemic contradiction" and
   focused on the `p ∧ ◇¬p` ordering. Mandelkern argues both orderings are
   equally infelicitous and have the same source — a claim contested by
   dynamic-semantic accounts (Veltman 1996; Groenendijk-Stokhof-Veltman 1996)
   that make the two inequivalent. See also @cite{holliday-mandelkern-2024}
   p. 4 for discussion.

2. **Distributivity-failure argument**: Mandelkern argues that classical
   distributivity of conjunction over disjunction *fails* for sentences
   mixing modal and non-modal content. The canonical example: a sentence
   schema of the form `(p ∨ ¬p) ∧ (◇p ∧ ◇¬p)` is felicitous (the LHS is a
   tautology, the RHS is "full uncertainty"), but its classical-distributive
   re-expression `(p ∧ ◇p ∧ ◇¬p) ∨ (¬p ∧ ◇p ∧ ◇¬p)` is infelicitous
   (each disjunct is a Wittgenstein sentence). HM 2024 (10a-b) restate the
   example with a winner-of-race scenario.

This file records the Mandelkern-attributed empirical observation — the
distributivity-failure intuition. Holliday-Mandelkern 2024 then provide a
formal semantic account (the orthologic) that derives this failure from
non-distributivity of the underlying ortholattice.
-/

namespace Phenomena.Modality.Studies.Mandelkern2019

open Phenomena.Modality.Studies.Yalcin2007 (SentenceType)

/-- Distributivity-failure intuition: a felicitous sentence becomes
    infelicitous when classically distributed. The natural-language LHS and
    RHS are recorded as `String` for documentation; cross-theory
    verification requires a formula-tree representation that's currently
    unavailable (deferred substrate work). -/
structure DistribIntuition where
  /-- The original (felicitous) sentence. -/
  lhs : String
  /-- The classically-equivalent re-expression (infelicitous). -/
  rhs : String
  /-- Whether the LHS is felicitous as asserted. -/
  lhsFelicitous : Bool
  /-- Whether the RHS is felicitous as asserted. -/
  rhsFelicitous : Bool
  deriving Repr

/-- The Mandelkern (2019) distributivity-failure example, in the form
    @cite{holliday-mandelkern-2024} (10a-b) restate it: a sentence about
    Sue being the winner that is felicitous as a "might/might-not + tautology"
    but not under classical distribution.

    LHS: "Sue might be the winner and she might not be, and either she is
    the winner or she isn't" — felicitous (the conjunction is consistent;
    the second conjunct is a tautology).

    RHS: distributing the second conjunct yields a disjunction of two
    Wittgenstein sentences — infelicitous. -/
def distribFailure : DistribIntuition :=
  { lhs := "Sue might be the winner and she might not be, and either she is the winner or she isn't"
  , rhs := "Sue might not be the winner and she is the winner, or else Sue might be the winner and she isn't the winner"
  , lhsFelicitous := true
  , rhsFelicitous := false }

end Phenomena.Modality.Studies.Mandelkern2019
