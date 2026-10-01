module

public import Linglib.Semantics.Reference.Kind
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Quantification.NP
public import Linglib.Data.Examples.LeBruynDeSwart2022

/-!
# Le Bruyn and de Swart (2022): Exceptional Wide Scope of Bare Nominals

This file formalizes the scope argument of [le-bruyn-de-swart-2022]. Bare plurals take
narrow scope across languages, which the kinds approach of [chierchia-1998] derives from a
default kind shift followed by derived kind predication, an existential introduced locally
where the kind meets the predicate. Dutch scrambled bare plurals are the counterexample: a
bare plural scrambled over negation takes unambiguous wide scope while keeping its kind
reading, and under the surface-oriented composition of scrambling the kind shift still
delivers narrow scope, whereas the flexible type shifting of [krifka-2003], which lets the
bare plural shift directly to an existential by a local type repair, delivers the wide scope
reading at the scrambled position.

On the kinds approach the bare plural denotes its kind, and derived kind predication introduces
the existential over the kind's instances where the kind meets the verb, below negation, (38);
scrambling the kind over negation changes nothing, a kind being scopeless as a name is
(`chierchiaScrambled_iff`). Krifka's existential shift makes the bare plural a quantifier, which
takes scope: narrow in place, (40), wide when scrambled, (41). On a two-book model of the
attested example (35), one book finished and one not, the scrambled existential is true and both
narrow readings false (`books_example`).

## Implementation notes

* Individuals are Link's nonempty sets of atoms, `Plurality.Algebra.Individual`, so no empty
  plurality satisfies a distributive predicate vacuously. Both derivations quantify over all
  pluralities of books, the instances of the kind; the plural noun's own extension, without the
  atoms, would change no truth value on the model.
* The attested examples are rows of `Data/Examples/LeBruynDeSwart2022.json`.

## References

* [le-bruyn-de-swart-2022]
* [chierchia-1998]
* [krifka-2003]
-/

@[expose] public section

namespace LeBruynDeSwart2022

open Reference Plurality.Algebra Quantifier

/-- The books of the attested example (35). -/
inductive Book
  | finished
  | unfinished
  deriving DecidableEq, Nonempty

/-- *books*: every plurality of books, singular or plural. -/
def books : Unit → Set (Individual Book) := fun _ ↦ Set.univ

/-- Read to the end, distributively: every book of the plurality was finished. -/
def read (x : Individual Book) : Prop := x.1 ⊆ {Book.finished}

/-- Krifka's existential shift in place, as in (40): no book was read. -/
def krifkaUnscrambled : Prop := ¬ GQ.some (books ()) read

/-- Krifka's existential shift scrambled over negation, (41): some book was not read. -/
def krifkaScrambled : Prop := GQ.some (books ()) readᶜ

/-- The kinds approach, (38): the bare plural shifts to its kind, and derived kind predication
introduces the existential over its instances where the kind meets the verb, below negation. -/
def chierchiaUnscrambled : Prop := ¬ GQ.some ((Kind.down books).up ()) read

/-- The kinds approach with the kind scrambled over negation, abstracting over a kind-level
trace. -/
def chierchiaScrambled : Prop :=
  NP.individual (Kind.down books) (fun k : Kind Unit (Individual Book) ↦ GQ.some (k.up ()) read)ᶜ

/-- Scrambling a kind over negation changes nothing: a kind takes no scope, as a name takes none
([chierchia-1998] §4.2), so the kinds approach gives narrow scope at either position. -/
theorem chierchiaScrambled_iff : chierchiaScrambled ↔ chierchiaUnscrambled :=
  NP.individual_compl _ _

theorem not_read_unfinished : ¬ read (Individual.atom .unfinished) := fun h ↦
  Book.noConfusion (Set.mem_singleton_iff.1 (h (Set.mem_singleton _)))

theorem read_finished : read (Individual.atom .finished) := subset_rfl

/-- (35) on the two-book model, one book finished and one not: Krifka's scrambled existential
gives the attested reading, and the narrow readings, his in place and the kinds approach's at
either position, are false. -/
theorem books_example : krifkaScrambled ∧ ¬ krifkaUnscrambled ∧ ¬ chierchiaScrambled := by
  refine ⟨⟨Individual.atom .unfinished, trivial, not_read_unfinished⟩,
    not_not.2 ⟨Individual.atom .finished, trivial, read_finished⟩, ?_⟩
  rw [chierchiaScrambled_iff, chierchiaUnscrambled, not_not]
  have hd : (⟨Set.univ, Set.univ_nonempty⟩ : Individual Book) ∈ Kind.down books () :=
    Kind.mem_down.2 ⟨trivial, fun x _ ↦ (Set.subset_univ x.1 : x ≤ _)⟩
  exact ⟨Individual.atom .finished,
    ⟨_, hd, (Set.subset_univ _ : Individual.atom Book.finished ≤ _)⟩, read_finished⟩

end LeBruynDeSwart2022
