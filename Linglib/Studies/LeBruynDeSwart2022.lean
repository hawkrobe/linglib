import Linglib.Semantics.Genericity.NominalMappingParameter
import Linglib.Data.Examples.LeBruynDeSwart2022

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

The two derivations coincide below negation (`krifkaUnscrambled`) and part company above it:
Chierchia's is position-invariant (`Semantics.Kinds.NMP.chierchia_position_invariant`),
while Krifka's scrambled reading is wide and its narrow reading false exactly when some book
was finished and some was not (`krifkaScrambled_and_not_unscrambled_iff`), the situation
the paper's attested example describes. On that two-book model the kind shift cannot deliver
the attested reading (`chierchia_not_wide`).

## Implementation notes

Existential closure is the substrate's `Semantics.Kinds.NMP.existsClose` over a finite
domain, shared by both derivations so that they differ only in where negation sits; the
compositional detail of the paper's derivations (38) and (41) is not represented. The
attested examples are rows of `Data/Examples/LeBruynDeSwart2022.json`.

## References

* [le-bruyn-de-swart-2022]
* [chierchia-1998]
* [krifka-2003]
-/

namespace LeBruynDeSwart2022

open Semantics.Kinds.NMP

variable {Entity : Type*} (dom : List Entity) (P Q : Entity → Prop)

/-- Krifka's existential shift at the unscrambled position, below negation (the derivation
of the paper's (40)): `¬ ∃ x ∈ dom, P x ∧ Q x`. -/
def krifkaUnscrambled : Prop := ¬ existsClose dom P Q

/-- Krifka's existential shift at the scrambled position, above negation (the derivation of
the paper's (41)): `∃ x ∈ dom, P x ∧ ¬ Q x`. -/
def krifkaScrambled : Prop := existsClose dom P λ x => ¬ Q x

/-- Below negation the kind shift and the existential shift agree. -/
theorem chierchiaDerivUnscrambled_eq :
    chierchiaDerivUnscrambled dom P Q = krifkaUnscrambled dom P Q := rfl

/-- The scrambled bare plural takes wide scope while its narrow reading fails exactly when
the domain holds both a `P` that is `Q` and one that is not. -/
theorem krifkaScrambled_and_not_unscrambled_iff :
    krifkaScrambled dom P Q ∧ ¬ krifkaUnscrambled dom P Q ↔
      (∃ x ∈ dom, P x ∧ ¬ Q x) ∧ ∃ x ∈ dom, P x ∧ Q x := by
  simp [krifkaScrambled, krifkaUnscrambled, existsClose]

/-- Whenever some `P` is `Q`, the kind shift's scrambled reading is false: derived kind
predication keeps the existential below negation at either position. -/
theorem chierchia_not_wide (h : ∃ x ∈ dom, P x ∧ Q x) : ¬ chierchiaDerivScrambled dom P Q :=
  not_not.mpr h

/-! ### The attested example

*Het klopt dat ik boeken niet heb uitgelezen* (`Examples.boeken_niet_uitgelezen`): with two
books, one finished and one not, the scrambled bare plural is true on the wide scope reading
and false on the narrow one. -/

/-- The books of the attested example. -/
inductive Book
  | finished
  | unfinished
  deriving DecidableEq, Repr

/-- Both books were read. -/
def read : Book → Prop := (· = .finished)

/-- Krifka's shift at the scrambled position gives the attested wide scope reading, and the
narrow reading, on which no book was finished, is false; the kind shift gives only the
latter. -/
theorem books :
    krifkaScrambled [Book.finished, .unfinished] (λ _ => True) read ∧
      ¬ krifkaUnscrambled [Book.finished, .unfinished] (λ _ => True) read ∧
      ¬ chierchiaDerivScrambled [Book.finished, .unfinished] (λ _ => True) read := by
  unfold krifkaScrambled krifkaUnscrambled chierchiaDerivScrambled read; decide

end LeBruynDeSwart2022
