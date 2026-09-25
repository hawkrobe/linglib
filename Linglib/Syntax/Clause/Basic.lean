module

public import Linglib.Syntax.Case.Basic
public import Mathlib.Basic.Rel
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Clause axes

This file defines the axes of a clause by which the lexicon and the studies index their facts.
A sentence type is the grammatical kind of a clause: Sadock and Zwicky's declarative,
interrogative, imperative and exclamative, with the interrogative subtyped as polar,
alternative or constituent, and the promissive that Korean grammaticalizes beside the
imperative. A sentence type is a form; the speech act it conventionally performs is its force,
`Mood.Illocutionary`, read off by `Clause.SentenceType.force`. An embedding context is where a
clause token occurs, Bhatt and Dayal's four cells. A cell is a sentence type in an embedding
context, and a distribution records for each cell whether some element or process is
obligatory, optional or excluded there, or nothing where the source is silent; the cells where
it is possible and where it is required are the two relations a distribution determines. A
particle's licensing and a language's verb-second grammar are distributions. The subject
requirement and the semantic size of a complement clause are the remaining axes.

## Main definitions

* `Clause.SentenceType`, `Clause.SentenceType.IsInterrogative`: the sentence types.
* `Clause.EmbeddingContext`, `Clause.root`, `Clause.embedded`: the embedding contexts and the
  cells of root and subordinated clauses.
* `Clause.Occurrence`, `Clause.Distribution`: the value of a cell and a table of cells.
* `Clause.Distribution.recorded`, `possible`, `required`: the relations a distribution
  determines.
* `Clause.EmbeddedSubject`, `Clause.Size`: the subject requirement and the size of a
  complement clause.

## References

* [sadock-zwicky-1985]
* [zanuttini-pak-portner-2012]
* [bhatt-dayal-2020]
* [dayal-2025]
* [noonan-2007]
* [bondarenko-2022]
* [wurmbrand-lohninger-2023]
* [wurmbrand-2024]
-/

@[expose] public section

namespace Clause

/-! ### Sentence types -/

/-- The sentence types, the grammatical kinds of clause a language distinguishes. -/
inductive SentenceType where
  | declarative
  /-- The polar, or yes/no, interrogative. -/
  | polar
  /-- The alternative interrogative, *p or q?*. -/
  | alternative
  /-- The constituent, or wh, interrogative. -/
  | constituent
  | imperative
  | exclamative
  /-- The promissive, which Korean grammaticalizes beside the imperative. -/
  | promissive
  deriving DecidableEq, Repr, Fintype

/-- A sentence type is interrogative when it is polar, alternative or constituent. -/
def SentenceType.IsInterrogative (t : SentenceType) : Prop :=
  t = .polar ∨ t = .alternative ∨ t = .constituent

instance : DecidablePred SentenceType.IsInterrogative :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-! ### Embedding contexts and cells -/

/-- Where a clause token occurs, the interrogative-embedding contexts of Bhatt and Dayal and of
Dayal: a property of the token, not of the clause. -/
inductive EmbeddingContext where
  | matrix
  | subordinated
  /-- Embedded root-like clauses, as Hindi-Urdu *kya:* and Belfast English embedded inversion
  have them. -/
  | quasiSubordinated
  | quotation
  deriving DecidableEq, Repr, Fintype

/-- The cell of a root clause of sentence type `t`. -/
abbrev root (t : SentenceType) : SentenceType × EmbeddingContext := (t, .matrix)

/-- The cell of a subordinated clause of sentence type `t`. -/
abbrev embedded (t : SentenceType) : SentenceType × EmbeddingContext := (t, .subordinated)

/-! ### Distributions -/

/-- An occurrence says whether an element or process is obligatory, optional or excluded in a
cell. -/
inductive Occurrence where
  | obligatory
  | optional
  | excluded
  deriving DecidableEq, Repr, Fintype

/-- A distribution records the occurrence of an element or process in each cell; `none` means
that the source records nothing for the cell, not that it is excluded. -/
abbrev Distribution := SentenceType → EmbeddingContext → Option Occurrence

namespace Distribution

variable (d : Distribution)

/-- The cells the source records. -/
def recorded : SetRel SentenceType EmbeddingContext := {c | (d c.1 c.2).isSome = true}

/-- The cells where the element or process is possible, recorded as obligatory or optional. -/
def possible : SetRel SentenceType EmbeddingContext :=
  {c | d c.1 c.2 = some .obligatory ∨ d c.1 c.2 = some .optional}

/-- The cells where the element or process is required. -/
def required : SetRel SentenceType EmbeddingContext := {c | d c.1 c.2 = some .obligatory}

variable {d}

instance (c : SentenceType × EmbeddingContext) : Decidable (c ∈ d.recorded) :=
  inferInstanceAs (Decidable ((d c.1 c.2).isSome = true))

instance (c : SentenceType × EmbeddingContext) : Decidable (c ∈ d.possible) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (c : SentenceType × EmbeddingContext) : Decidable (c ∈ d.required) :=
  inferInstanceAs (Decidable (_ = _))

instance (t : SentenceType) : Decidable (t ∈ d.possible.dom) :=
  inferInstanceAs (Decidable (∃ e, (t, e) ∈ d.possible))

instance (e : EmbeddingContext) : Decidable (e ∈ d.possible.cod) :=
  inferInstanceAs (Decidable (∃ t, (t, e) ∈ d.possible))

instance : Decidable d.recorded.Nonempty :=
  inferInstanceAs (Decidable (∃ c, c ∈ d.recorded))

theorem required_subset_possible : d.required ⊆ d.possible := fun _ h ↦ Or.inl h

theorem possible_subset_recorded : d.possible ⊆ d.recorded := by
  rintro c (h | h) <;> simp [recorded, h]

end Distribution

/-! ### Complement clauses -/

/-- The subject of an embedded clause is obligatorily null, as in control complements, or
overt, optionally with a fixed case. Genitive marking on the subject is Noonan's criterion for
the nominalization coding; Bondarenko's Buryat genitive subjects of nominalized clauses are the
modern instance. -/
inductive EmbeddedSubject where
  | obligatorilyNull
  | overt (subjCase : Option Case)
  deriving DecidableEq, Repr

/-- The semantic sort of a complement clause, which fixes the minimal structure it needs, the
implicational complementation hierarchy of Wurmbrand and Lohninger: an event needs only the
thematic domain, a situation adds the tense–mood–aspect domain, a proposition adds the
operator domain. Ordered by containment. -/
inductive Size where
  | event
  | situation
  | proposition
  deriving DecidableEq, Repr, Fintype

/-- Position on the containment order. -/
def Size.rank : Size → Nat
  | .event => 0
  | .situation => 1
  | .proposition => 2

instance : LinearOrder Size :=
  .lift' Size.rank fun a b ↦ by cases a <;> cases b <;> simp [Size.rank]

end Clause
