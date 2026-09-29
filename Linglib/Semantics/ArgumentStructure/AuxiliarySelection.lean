/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Perfect-auxiliary selection (be/have)

Many Romance and Germanic languages form the perfect with either *be* or *have*, and the choice
tracks split intransitivity. The binary account, [burzio-1986]'s for Italian, has unaccusatives
and reflexives take *be* (Italian *è arrivato*, French *est arrivé*) and unergatives and
transitives *have* (Italian *ha mangiato*); German and Dutch reflexives take *have*
([sorace-2000], §1). [sorace-2000] refines the intransitives into the Auxiliary Selection
Hierarchy, a chain of seven aspectual and thematic verb types along which the preference for
*be* falls: the verbs at the two ends choose their auxiliary categorically and in every language,
the verbs between them vary, and each language draws its cutoff between *be* and *have* at its
own point. The inflectional typology of auxiliary verb constructions lives in
`Syntax/Category/Auxiliary/Constructions.lean`.

## Main definitions

* `PerfectAux`: *be* or *have*.
* `TransitivityClass` and its `selection`, `canonicalSelection` and `SelectsBe`: the binary
  account.
* `AuxiliarySelectionHierarchy`: the verb types of the Auxiliary Selection Hierarchy, a bounded
  linear order with the type most consistent in taking *be* at the bottom.

## References

* [burzio-1986]
* [sorace-2000]
-/

@[expose] public section

namespace ArgumentStructure

/-- Perfect auxiliary choice. -/
inductive PerfectAux where
  /-- Italian *essere*, French *être*, German *sein*. -/
  | be
  /-- Italian *avere*, French *avoir*, German *haben*. -/
  | have
  deriving DecidableEq, Repr

/-- Transitivity class relevant to auxiliary selection. -/
inductive TransitivityClass where
  /-- Subject is the theme: *arrive*, *fall*, *die*. -/
  | unaccusative
  /-- Subject is an agent and there is no object: *run*, *laugh*. -/
  | unergative
  /-- Subject is an agent and the object a theme: *eat*, *build*. -/
  | transitive
  /-- A reflexive clitic, which selects *be* in Romance and *have* in
      German. -/
  | reflexive
  deriving DecidableEq, Repr, Fintype

namespace TransitivityClass

/-- The binary account of auxiliary selection, given the auxiliary of reflexives: unaccusatives
select *be*, unergatives and transitives *have*, and reflexives are the locus of variation, *be*
in Romance and *have* in German ([burzio-1986] for the Italian generalization). -/
def selection (refl : PerfectAux) : TransitivityClass → PerfectAux
  | unaccusative => .be
  | reflexive    => refl
  | unergative   => .have
  | transitive   => .have

/-- Canonical (Romance) auxiliary selection: reflexives → *be*. -/
def canonicalSelection : TransitivityClass → PerfectAux := selection .be

/-- Does this transitivity class canonically select *be*? -/
def SelectsBe (c : TransitivityClass) : Prop :=
  c.canonicalSelection = .be

instance : DecidablePred SelectsBe := fun c =>
  inferInstanceAs (Decidable (c.canonicalSelection = .be))

end TransitivityClass

/-- The Auxiliary Selection Hierarchy ([sorace-2000], Table 1): the aspectual and thematic types
of monadic intransitive verbs, ordered from the type most consistent in taking *be* to the type
most consistent in taking *have*. The transitions and states come first, by decreasing telicity,
then the processes, by increasing control. The two ends are the core types, whose verbs choose
their auxiliary categorically. -/
inductive AuxiliarySelectionHierarchy where
  /-- A telic change of location: *arrive*, *come*, *fall*. -/
  | changeOfLocation
  /-- A change of state, mostly without a specified endpoint: *rise*, *rot*, *become*, *die*. -/
  | changeOfState
  /-- The continuation of a pre-existing state: *stay*, *remain*, *last*, *survive*. -/
  | continuationOfState
  /-- The existence of a state: *be*, *exist*, *belong*, *seem*. -/
  | existenceOfState
  /-- A process without volition: *tremble*, *cough*, verbs of emission and weather verbs. -/
  | uncontrolledProcess
  /-- A controlled process of motion, whose agent undergoes an undirected displacement: *run*,
      *swim*, *walk*. -/
  | motionalProcess
  /-- A controlled process without motion, which leaves its agent unaffected: *work*, *play*,
      *talk*. -/
  | nonmotionalProcess
  deriving DecidableEq, Repr, Fintype

namespace AuxiliarySelectionHierarchy

/-- The types are ordered as they are listed. -/
instance : LinearOrder AuxiliarySelectionHierarchy :=
  LinearOrder.lift' AuxiliarySelectionHierarchy.ctorIdx (by decide)

instance : BoundedOrder AuxiliarySelectionHierarchy where
  bot := changeOfLocation
  bot_le := by decide
  top := nonmotionalProcess
  le_top := by decide

end AuxiliarySelectionHierarchy

end ArgumentStructure
