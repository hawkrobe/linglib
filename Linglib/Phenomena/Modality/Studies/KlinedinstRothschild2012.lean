/-!
# @cite{klinedinst-rothschild-2012}: Disjunctive Syllogism Failure for Epistemic Modals

@cite{klinedinst-rothschild-2012}

Klinedinst & Rothschild (2012) "Connectives without truth tables"
(*Natural Language Semantics* 20(2):137-175) argue that the standard
truth-table account of conjunction and disjunction fails for sentences with
epistemic modals — citing among other things the failure of *disjunctive
syllogism*.

The canonical example: from "Either the dog is inside or it must be
outside" together with "It's not the case that the dog must be outside,"
classical logic concludes "The dog is inside." But for epistemic
disjunction this conclusion is intuitively *not* warranted — the first
premise was epistemically tautological (it carries no information), and so
the second premise can be true without the dog actually being inside.

Holliday & Mandelkern (2024) §2.3 take the example up directly, noting
that K&R cite Yalcin (2007) for the underlying observation. The orthologic
account in HM 2024 then derives the failure of disjunctive syllogism from
the non-Boolean structure of the regular-set ortholattice (formalized in
`Studies/HollidayMandelkern2024.lean::disjSyllogism_fails`).

## What's encoded

The natural-language judgment that the inference is *invalid* — i.e., the
conclusion does not follow from the premises despite the classical pattern
suggesting otherwise. Cross-theory verification (against HM's orthologic,
Veltman's update semantics, etc.) requires a formula-tree representation
that's currently unavailable (deferred substrate work).
-/

namespace Phenomena.Modality.Studies.KlinedinstRothschild2012

/-- Disjunctive syllogism failure intuition: from `p ∨ q` and `¬q`,
    classical logic concludes `p`. For epistemic-modal `q`, this inference
    is intuitively invalid. The natural-language premises and conclusion
    are recorded as `String` for documentation; cross-theory verification
    requires a formula-tree representation that's currently unavailable. -/
structure DisjSyllIntuition where
  /-- The first premise (the disjunction). -/
  premise1 : String
  /-- The second premise (the negated disjunct). -/
  premise2 : String
  /-- The classical conclusion. -/
  conclusion : String
  /-- Whether the inference is intuitively valid. -/
  valid : Bool
  deriving Repr

/-- Klinedinst & Rothschild's canonical disjunctive-syllogism-failure
    example: "Either the dog is inside or it must be outside; it's not the
    case that the dog must be outside; therefore the dog is inside" is
    intuitively invalid for epistemic modals.

    K&R credit Yalcin (2007); the example reappears in
    @cite{holliday-mandelkern-2024} §2.3 as a centerpiece of the case for
    a non-classical logic. -/
def disjSyllFailure : DisjSyllIntuition :=
  { premise1 := "Either the dog is inside or it must be outside"
  , premise2 := "It's not the case that the dog must be outside"
  , conclusion := "The dog is inside"
  , valid := false }

end Phenomena.Modality.Studies.KlinedinstRothschild2012
