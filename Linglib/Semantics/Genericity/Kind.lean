import Mathlib.Data.Set.Basic
import Mathlib.Order.UpperLower.Basic
import Linglib.Semantics.Mereology

/-!
# Kinds

This file defines the kind ontology of [chierchia-1998] over [link-1983]'s semilattice. An
individual is a non-empty set of atoms, so `⊆` and `∪` are Link's part-of and join from
mathlib's `Set` instances; a property is a function from worlds to sets of individuals; and a
kind is an individual concept, a function from worlds to individuals, the totality of the
kind's instances at each world. The operator ∩ takes a property to the kind of its instances and
∪ takes a kind back to the property of its parts, inverse to each other on mass properties and
on kinds. Derived Kind Predication applies an object-level predicate to a kind by existential
closure over its instances, locally, so a bare plural has no scope.

## Main definitions

* `Individual`, `Property`, `Kind` — the ontology
* `Property.down`, `Kind.up` — ∩ and ∪
* `Property.IsMass`, `Property.pluralClosure` — the mass condition and Link's plural closure
* `DKP`, `DPP`, `existsClose` — Derived Kind and Property Predication and existential closure

## Main results

* `Kind.up_down`, `Kind.down_up` — ∪ and ∩ are inverse on mass properties and on kinds
* `Property.pluralClosure_of_isMass` — plural closure fixes a mass property
* `chierchia_position_invariant` — Derived Kind Predication is position-invariant

## References

* [chierchia-1998]
* [link-1983]
* [krifka-2003]
* [moroney-2021]
* [guerrini-2026]
-/

namespace Genericity

variable {World Atom : Type*}

/-- An individual: a non-empty set of atoms, an atom being a singleton and a plurality a larger
set, so that `⊆` and `∪` are Link's part-of and join. -/
abbrev Individual (Atom : Type*) := Set Atom

/-- The singular individual of an atom. -/
def Individual.atom (a : Atom) : Individual Atom := {a}

/-- A property: a function from worlds to sets of individuals. -/
abbrev Property (World Atom : Type*) := World → Set (Individual Atom)

/-- A kind: an individual concept, the totality of the kind's instances at each world. -/
structure Kind (World Atom : Type*) where
  /-- The instances of the kind at each world. -/
  concept : World → Individual Atom

namespace Property

/-- ∩: the kind of a property, at each world the totality of its atomic instances. Defined
semantically for mass and plural properties only (`DownDefined`). -/
def down (P : Property World Atom) : Kind World Atom :=
  ⟨λ w => { a | Individual.atom a ∈ P w }⟩

/-- A property is mass when its extension at each world is determined by its atomic content
([chierchia-1998]), whence its cumulative and divisive reference. -/
def IsMass (P : Property World Atom) : Prop :=
  ∀ w (x : Individual Atom), x ∈ P w ↔ ∀ a ∈ x, Individual.atom a ∈ P w

/-- A mass property has divisive reference. -/
theorem IsMass.div {P : Property World Atom} (h : P.IsMass) (w : World) :
    Mereology.DIV (P w) :=
  λ x y hyx hx => (h w y).mpr λ a ha => (h w x).mp hx a (hyx ha)

/-- A mass property has cumulative reference. -/
theorem IsMass.cum {P : Property World Atom} (h : P.IsMass) (w : World) :
    Mereology.CUM (P w) :=
  λ x hx y hy => (h w (x ⊔ y)).mpr λ a ha =>
    ha.elim (λ h' => (h w x).mp hx a h') (λ h' => (h w y).mp hy a h')

/-- Link's plural closure: the extension at each world closed under join, the denotation of the
bare plural of a count property. -/
def pluralClosure (P : Property World Atom) : Property World Atom :=
  λ w => Mereology.AlgClosure (P w)

/-- Plural closure fixes a mass property, which is already cumulative ([krifka-2026]'s
absorption). -/
theorem pluralClosure_of_isMass {P : Property World Atom} (h : P.IsMass) :
    P.pluralClosure = P := by
  funext w; ext x
  exact Mereology.algClosure_of_cum (h.cum w)

theorem subset_pluralClosure (P : Property World Atom) (w : World) :
    P w ⊆ P.pluralClosure w :=
  λ _ h => Mereology.AlgClosure.base h

theorem pluralClosure_cum (P : Property World Atom) (w : World) :
    Mereology.CUM (P.pluralClosure w) :=
  Mereology.algClosure_cum

end Property

namespace Kind

/-- ∪: the property of a kind, at each world the individuals that are part of the totality of
its instances; a mass denotation, atoms and pluralities alike. -/
def up (k : Kind World Atom) : Property World Atom := λ w => { x | x ⊆ k.concept w }

/-- ∪ inverts ∩ on mass properties. -/
theorem up_down {P : Property World Atom} (h : P.IsMass) : P.down.up = P := by
  funext w; ext x
  simp only [up, Property.down, Set.mem_ofPred_eq]
  constructor
  · intro h'; exact (h w x).mpr λ a ha => h' ha
  · intro h' a ha; exact (h w x).mp h' a ha

/-- ∩ inverts ∪ on kinds. -/
theorem down_up (k : Kind World Atom) : k.up.down = k := by
  simp only [Property.down, up, Set.mem_ofPred_eq, Individual.atom, Set.singleton_subset_iff,
    Set.ofPred_mem_eq]

end Kind

/-! ### Derived predication -/

/-- Derived Kind Predication: an object-level predicate applied to a kind holds when some
instance of the kind satisfies it, a coercion triggered by the sort mismatch. -/
def DKP (P : Individual Atom → Prop) (k : Kind World Atom) (w : World) : Prop :=
  ∃ x ∈ k.up w, P x

/-- Derived Property Predication: a property composed with a predicate holds when some
individual satisfies both, the low-scope existential of a property-denoting bare noun
([moroney-2021], [guerrini-2026]). -/
def DPP (P Q : Individual Atom → Prop) : Prop := ∃ x, P x ∧ Q x

/-! ### Scopelessness

Bare plurals are scopeless because Derived Kind Predication introduces its existential locally,
where the kind meets the predicate, so negation always scopes outside it whether or not the bare
plural has moved: `chierchia_position_invariant`. The position-sensitive shift that
`Studies/LeBruynDeSwart2022.lean` reads into [krifka-2003] reuses the same `existsClose`, so
the two accounts share one closure and differ only in where negation sits. `existsClose` is
Partee's existential closure in plain extensional form; `Quantification.A` is the same operator
in the deep embedding. -/

section DKPDerivation

variable {Entity : Type*}

/-- Existential closure of a property `P` against a predicate `Q` over a finite domain;
`reducible` so that concrete instances are decidable. -/
@[reducible] def existsClose (dom : List Entity) (P Q : Entity → Prop) : Prop :=
  ∃ x ∈ dom, P x ∧ Q x

/-- Chierchia's derivation of an unmoved bare plural under negation, `[niet [BP V]]`: the
existential is introduced locally, so negation scopes over it. -/
def chierchiaDerivUnscrambled (kind : List Entity) (P Q : Entity → Prop) : Prop :=
  ¬ existsClose kind P Q

/-- Chierchia's derivation of a scrambled bare plural, `[BP [niet V]]`: the same, since locality
keeps surface position from moving the existential. -/
def chierchiaDerivScrambled (kind : List Entity) (P Q : Entity → Prop) : Prop :=
  ¬ existsClose kind P Q

/-- Derived Kind Predication is local: the scrambled and unscrambled derivations coincide, so
Chierchia predicts obligatory narrow scope whatever the surface position. -/
theorem chierchia_position_invariant (kind : List Entity) (P Q : Entity → Prop) :
    chierchiaDerivScrambled kind P Q = chierchiaDerivUnscrambled kind P Q :=
  rfl

end DKPDerivation

end Genericity
