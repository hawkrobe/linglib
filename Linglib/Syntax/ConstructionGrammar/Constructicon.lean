/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.ConstructionGrammar.Basic
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Logic.Nonmonotonic.Inheritance

/-!
# The constructicon

A constructicon is a network of constructions ([goldberg-1995] §3.3; [diessel-2023]). Each node of
a `Constructicon ι Sem` carries a construction. Its inheritance links run up from a construction
to the constructions it inherits from, its mothers, and its horizontal links relate it to
constructions at its own level of abstraction, which motivate it without passing information
down: the links between syntactic alternates of [ten-wolde-2023], the motivation links of
[goldberg-shirtz-2025].

Inheritance is in the normal mode of [goldberg-1995] §3.3.1: "information is inherited from
dominant nodes transitively as long as that information does not conflict with information
specified by nodes lower in the inheritance hierarchy" (p. 73). That is default inheritance over
the order the inheritance links generate (`DefaultInheritance.inherited`): a construction takes
each property from the most specific constructions above it that specify one. A construction
whose mothers conflict on a property inherits both values unless it specifies its own, which is
why normal mode, unlike complete mode, admits several mothers. A study puts the order on its node
type with `Constructicon.partialOrder`, from a rank that every inheritance link decreases, so the
network is the directed acyclic graph the book requires (p. 73).

The relation an inheritance link records constrains the forms it joins (§3.3.2): "the syntactic
specifications of the central sense are inherited by the extensions" of a polysemy link (p. 75),
a subpart is "a proper subpart of another construction" (p. 78), and an instance link exists
"iff one construction is a more fully specified version of the other" (p. 79).
`Constructicon.WellTyped` checks every inheritance link against its relation.

## Main definitions

* `LinkType`, `LinkType.Admits`: the relations an inheritance link records, and what each
  requires of the forms it joins
* `Constructicon`: constructions at nodes, with inheritance and horizontal links
* `Constructicon.IsMother`, `Constructicon.partialOrder`, `Constructicon.decidableLE`: the
  inheritance order
* `Constructicon.WellTyped`: every inheritance link respects its relation

## Implementation notes

A slot of an instance refines the corresponding slot of the construction it instantiates when the
two are equal or the latter is open; the categories of fixed lexemes are not checked. A
metaphorical extension may change its form, so the relation places no constraint on forms.

## References

* [goldberg-1995]
* [diessel-2023]
* [goldberg-shirtz-2025]
* [ten-wolde-2023]
-/

@[expose] public section

namespace ConstructionGrammar

/-! ### Link types -/

/-- The semantic relation an inheritance link records: [goldberg-1995]'s four major link types
(§3.3.2, p. 75). -/
inductive LinkType where
  /-- I_P: from a central sense to an extension, which inherits the syntax but differs in meaning
  (the senses of the ditransitive, pp. 75–77). -/
  | polysemy
  /-- I_M: source and target related by a systematic metaphor (caused motion to the resultative,
  change of state as change of location, p. 81). -/
  | metaphorical
  /-- I_S: the linked construction is a proper subpart of the other (intransitive motion inside
  caused motion, p. 78). -/
  | subpart
  /-- I_I: the linked construction is a more fully specified version of the other (*drive*-crazy
  as an instance of the resultative, p. 79). -/
  | instance
  deriving DecidableEq, Repr

variable {Lex : Type*}

/-- A slot refines another when the two are equal or the other is open: the lexically filled
slots of an instance fill open slots of the construction it instantiates. -/
def Slot.Refines (s t : Slot Lex) : Prop := s = t ∨ t.filler.isOpen = true

instance [DecidableEq Lex] (s t : Slot Lex) : Decidable (s.Refines t) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- What a link type requires of the form `c` of the linked construction, given the form `m` of
the construction it inherits from. -/
def LinkType.Admits : LinkType → TypedForm Lex → TypedForm Lex → Prop
  | .polysemy, c, m => c = m
  | .metaphorical, _, _ => True
  | .subpart, c, m => c.Sublist m ∧ c ≠ m
  | .instance, c, m => List.Forall₂ Slot.Refines c m ∧ c ≠ m

instance [DecidableEq Lex] : ∀ (t : LinkType) (c m : TypedForm Lex), Decidable (t.Admits c m)
  | .polysemy, c, m => inferInstanceAs (Decidable (c = m))
  | .metaphorical, _, _ => .isTrue trivial
  | .subpart, c, m => inferInstanceAs (Decidable (c.Sublist m ∧ c ≠ m))
  | .instance, c, m => inferInstanceAs (Decidable (List.Forall₂ Slot.Refines c m ∧ c ≠ m))

/-! ### The network -/

/-- A constructicon over the nodes `ι`: the construction at each node, the inheritance links from
a node up to its mothers, and the horizontal links from a node to constructions at its level,
each with the relation it records if any. -/
structure Constructicon (ι Sem : Type*) where
  /-- The construction at each node. -/
  cxn : ι → Construction Sem
  /-- The mothers of each node, the constructions it inherits from. -/
  mothers : ι → List (ι × Option LinkType)
  /-- The constructions each node is related to at its own level, without inheritance. -/
  related : ι → List (ι × Option LinkType) := fun _ ↦ []

namespace Constructicon

variable {ι Sem : Type*} (N : Constructicon ι Sem)

/-- `m` is a mother of `c`: `c` inherits from `m` by an inheritance link. -/
def IsMother (c m : ι) : Prop := m ∈ (N.mothers c).map Prod.fst

instance [DecidableEq ι] : DecidableRel N.IsMother :=
  fun c m ↦ inferInstanceAs (Decidable (m ∈ (N.mothers c).map Prod.fst))

/-- The inheritance order: `c ≤ m` when `c` inherits from `m` through a chain of links. A rank
that every link decreases makes it antisymmetric. -/
abbrev partialOrder (rank : ι → ℕ) (h : ∀ c m, N.IsMother c m → rank m < rank c) :
    PartialOrder ι :=
  partialOrderOfCovers N.IsMother rank h

/-- The inheritance order is decidable given a list of every mother. -/
abbrev decidableLE [DecidableEq ι] (nodes : List ι) (h : ∀ c m, N.IsMother c m → m ∈ nodes)
    (c m : ι) : Decidable (Relation.ReflTransGen N.IsMother c m) :=
  decidableLEOfCovers nodes h c m

/-- Every inheritance link respects the relation it records. -/
def WellTyped : Prop :=
  ∀ c, ∀ e ∈ N.mothers c, ∀ t ∈ e.2, t.Admits (N.cxn c).form (N.cxn e.1).form

instance [Fintype ι] : Decidable N.WellTyped :=
  inferInstanceAs <| Decidable <|
    ∀ c, ∀ e ∈ N.mothers c, ∀ t ∈ e.2, t.Admits (N.cxn c).form (N.cxn e.1).form

end Constructicon

end ConstructionGrammar
