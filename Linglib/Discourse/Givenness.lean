/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Givenness

The cognitive statuses of discourse referents. A givenness status is one of the six tiers of
the Givenness Hierarchy of [gundel-hedberg-zacharski-1993], from *in focus* down to *type
identifiable*, ordered so that each status entails every lower one (`GivennessStatus`); the
binary givenness of information structure ([krifka-2008]) is the coarsening of the hierarchy at
the identifiability boundary ([lambrecht-1994]), *given* against *new* (`BinaryGivenness`,
`GivennessStatus.toBinary`).

## Main definitions

* `Discourse.GivennessStatus`: the six-tier hierarchy, as a linear order.
* `Discourse.BinaryGivenness`: given or new, as a two-element bounded linear order.
* `Discourse.GivennessStatus.toBinary`: the identifiability coarsening, monotone.

## Implementation notes

`BinaryGivenness` is identifiability. It is not [prince-1992]'s hearer-old against hearer-new,
which cross-cuts identifiability, nor alternatives-based givenness ([schwarzschild-1999]); a
consumer meaning another axis should say so. The finer scales over referring forms are
`Discourse.AccessibilityLevel` ([ariel-2001]) and Centering's information-status tiers
([strube-hahn-1999]).

## References

* [gundel-hedberg-zacharski-1993]
* [krifka-2008]
* [lambrecht-1994]
* [prince-1981]
* [chafe-1976]
-/

@[expose] public section

namespace Discourse

/-- A givenness status is a tier of the Givenness Hierarchy of [gundel-hedberg-zacharski-1993],
the cognitive status of a referent for the hearer. -/
inductive GivennessStatus where
  /-- In focus: the referent is currently in attention (an unstressed pronoun). -/
  | inFocus
  /-- Activated: the referent is in working memory (*that*, *this*, *this N*). -/
  | activated
  /-- Familiar: the referent is in long-term memory (*that N*). -/
  | familiar
  /-- Uniquely identifiable: the hearer can construct the referent from the description alone
  (*the N*). -/
  | uniquelyIdentifiable
  /-- Referential: the speaker has a particular referent in mind (indefinite *this N*). -/
  | referential
  /-- Type identifiable: the hearer can construct a representation of the type described
  (*a N*). -/
  | typeIdentifiable
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace GivennessStatus

/-- The rank of a status, higher for the more accessible. -/
def rank : GivennessStatus → ℕ
  | .inFocus              => 5
  | .activated            => 4
  | .familiar             => 3
  | .uniquelyIdentifiable => 2
  | .referential          => 1
  | .typeIdentifiable     => 0

/-- `typeIdentifiable < ⋯ < inFocus`: each status entails every lower one. -/
instance : LinearOrder GivennessStatus := LinearOrder.lift' rank (by decide)

end GivennessStatus

/-- Binary givenness is the given–new distinction of information structure, identifiability
of the referent by the hearer ([lambrecht-1994]). -/
inductive BinaryGivenness where
  /-- Given: the hearer can identify the referent. -/
  | given
  /-- New: the referent is not yet identifiable. -/
  | new
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace BinaryGivenness

/-- The rank of a binary status, higher for given. -/
def rank : BinaryGivenness → ℕ
  | .given => 1
  | .new   => 0

/-- `new < given`. -/
instance : LinearOrder BinaryGivenness := LinearOrder.lift' rank (by decide)

/-- `⊥ = new`, `⊤ = given`. -/
instance : BoundedOrder BinaryGivenness where
  top := .given
  le_top := by decide
  bot := .new
  bot_le := by decide

instance : IsSimpleOrder BinaryGivenness where
  exists_pair_ne := ⟨.new, .given, by decide⟩
  eq_bot_or_eq_top := by decide

end BinaryGivenness

/-- The identifiability coarsening: the identifiable tiers are given, the indefinite tiers
new. -/
def GivennessStatus.toBinary : GivennessStatus → BinaryGivenness
  | .inFocus | .activated | .familiar | .uniquelyIdentifiable => .given
  | .referential | .typeIdentifiable                          => .new

theorem GivennessStatus.toBinary_monotone : Monotone GivennessStatus.toBinary := by decide

end Discourse
