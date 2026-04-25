import Linglib.Theories.Discourse.Centering.Basic
import Linglib.Theories.Semantics.Dynamic.Boxes.Syntax

/-!
# Centering ↔ DRT Bridge
@cite{grosz-joshi-weinstein-1995} @cite{kamp-reyle-1993} @cite{bittner-2014}

A bridge between Centering Theory's notion of *realization* and the
Discourse Representation Theory notion of *occurrence in a DRS*.

Centering is normally presented with a list-of-realizations utterance
representation. But the "realizes" relation is, in @cite{grosz-joshi-weinstein-1995}
§3, deliberately abstracted from the underlying semantic theory:
the paper allows any semantic representation that supplies a realizes
relation. DRT's `DRSExpr` is one natural choice — its drefs are exactly
the discourse entities that an utterance contributes — and using a DRS
as the current-utterance representation lets Centering compute Cb
directly off the dynamic semantic structure rather than off a separate
list.

This module provides the `Realizes DRSExpr Nat` instance: a DRS realizes
a dref iff that dref *occurs* anywhere in the DRS (free or bound).
With this instance, `cb prev cur` from `Theories/Discourse/Centering/Basic.lean`
applies directly to a `(Utterance Nat R, DRSExpr)` pair, no glue code.

This bridge is for Cb computation. DRT abstracts away from surface
pronominal form, so a `Pronominalizes` instance is not provided here —
Rule 1 is not directly applicable to DRSs without an additional layer
that records which drefs are realized pronominally.
-/

set_option autoImplicit false

namespace Interfaces.SemanticsDiscourse.CenteringDRT

open Discourse.Centering
open Semantics.Dynamic.Core.DRSExpr (DRSExpr occurs)

/-- A DRS realizes a dref `e` iff `e` occurs anywhere in the DRS.
    This includes both freshly introduced drefs (in any `.box`) and
    drefs referred to in atomic conditions (anaphoric uses). -/
instance : Realizes DRSExpr Nat where
  decide := fun K e => occurs e K

/-- A `.box` realizes each of its newly introduced drefs. -/
theorem box_realizes_new_dref (drefs : List Nat) (conds : List DRSExpr)
    (e : Nat) (h : e ∈ drefs) :
    realizes (DRSExpr.box drefs conds) e := by
  unfold realizes
  show occurs e (DRSExpr.box drefs conds) = true
  unfold occurs
  exact Bool.or_eq_true_iff.mpr (Or.inl (List.contains_iff_mem.mpr h))

end Interfaces.SemanticsDiscourse.CenteringDRT
