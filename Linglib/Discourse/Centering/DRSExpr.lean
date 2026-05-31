import Linglib.Discourse.Centering.Basic
import Linglib.Semantics.Dynamic.Boxes.Syntax

/-!
# Centering ↔ DRT Bridge
@cite{grosz-joshi-weinstein-1995} @cite{kamp-reyle-1993}

A bridge between Centering Theory's notion of *realization* and the
Discourse Representation Theory notion of *occurrence in a DRS*.

Centering is normally presented with a list-of-realizations utterance
representation. But the "realizes" relation is, in @cite{grosz-joshi-weinstein-1995},
deliberately abstracted from the underlying semantic theory:
the paper allows any semantic representation that supplies a realizes
relation. DRT's `DRS` is one natural choice — its drefs are exactly
the discourse entities that an utterance contributes — and using a DRS
as the current-utterance representation lets Centering compute Cb
directly off the dynamic semantic structure rather than off a separate
list.

This module provides the `Realizes DRS Nat` instance: a DRS realizes
a dref iff that dref *occurs* anywhere in the DRS (free or bound).
With this instance, `cb prev cur` from `Discourse/Centering/Basic.lean`
applies directly to a `(Utterance Nat R, DRS)` pair, no glue code.

This bridge is for Cb computation. DRT abstracts away from surface
pronominal form, so a `Pronominalizes` instance is not provided here —
Rule 1 is not directly applicable to DRSs without an additional layer
that records which drefs are realized pronominally.
-/

namespace Discourse.Centering.DRS

open Discourse.Centering
open _root_.DRS

/-- A DRS realizes a dref `e` iff `e` occurs anywhere in the DRS.
    This includes both freshly introduced drefs (in any `.box`) and
    drefs referred to in atomic conditions (anaphoric uses). The
    underlying `occurs` predicate is `Bool`-valued; the instance lifts
    it to `Prop` via `= true`. -/
instance : Realizes DRS Nat where
  Rel K e := occurs e K = true
  decRel _ _ := inferInstance

/-- A `.box` realizes each of its newly introduced drefs. -/
theorem box_realizes_new_dref (drefs : List Nat) (conds : List DRS)
    (e : Nat) (h : e ∈ drefs) :
    realizes (DRS.box drefs conds) e := by
  show occurs e (DRS.box drefs conds) = true
  unfold occurs
  exact Bool.or_eq_true_iff.mpr (Or.inl (List.contains_iff_mem.mpr h))

end Discourse.Centering.DRS
