import Linglib.Discourse.Centering.Basic
import Linglib.Semantics.Dynamic.DRS.Basic

/-!
# Centering ↔ DRT Bridge
@cite{grosz-joshi-weinstein-1995} @cite{kamp-reyle-1993}

A bridge between Centering Theory's notion of *realization* and the
Discourse Representation Theory notion of *occurrence in a DRS*.

Centering is normally presented with a list-of-realizations utterance
representation. But the "realizes" relation is, in @cite{grosz-joshi-weinstein-1995},
deliberately abstracted from the underlying semantic theory: the paper allows any
semantic representation that supplies a realizes relation. DRT's `DRS` is one
natural choice — its discourse referents are exactly the discourse entities an
utterance contributes — and using a DRS as the current-utterance representation
lets Centering compute Cb directly off the dynamic semantic structure rather than
off a separate list.

This module provides the `Realizes (DRS L V) V` instance: a DRS realizes a
referent `e` iff `e` *occurs* in the DRS (free or bound), i.e. `e ∈ DRS.occ K`.
`DRS.occ` is `Finset`-valued (the `Term.varFinset` analogue), so membership is
decidable and `Realizes.decRel` is `inferInstance`. With this instance,
`cb prev cur` from `Discourse/Centering/Basic.lean` applies directly to a
`(Utterance V R, DRS L V)` pair, no glue code.

This bridge is for Cb computation. DRT abstracts away from surface pronominal
form, so a `Pronominalizes` instance is not provided here — Rule 1 is not directly
applicable to DRSs without an additional layer recording which referents are
realized pronominally.
-/

open FirstOrder

namespace Discourse.Centering.DRT

open _root_.DRT

universe u v w
variable {L : Language.{u, v}} {V : Type w} [DecidableEq V]

/-- A DRS realizes a referent `e` iff `e` occurs anywhere in it (free or bound):
`e ∈ DRS.occ K`, a decidable `Finset` membership. -/
instance : Realizes (DRS L V) V where
  Rel K e := e ∈ DRS.occ K
  decRel _ _ := inferInstance

/-- A DRS realizes each referent in its universe. -/
theorem mk_realizes_referent (U : Finset V) (conds : List (Condition L V))
    (e : V) (h : e ∈ U) : realizes (DRS.mk U conds) e := by
  show e ∈ DRS.occ (DRS.mk U conds)
  exact Finset.mem_union_left _ h

end Discourse.Centering.DRT
