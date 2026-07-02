import Linglib.Semantics.Possessive.GQ

/-!
# Barker 1995: *Possessive Descriptions*

Paper-anchored consumer of the possessive substrate for [barker-1995]. Two of
the dissertation's signature claims, tested against concrete models:

* **Narrowing** ([barker-1995] p. 139): a quantificational possessor restricts
  quantification to those possessors that stand in the possession relation to
  some possessee. *Most planets' rings are made of ice* is evaluated only over
  planets that have rings. The substrate operator
  `Possessive.Poss` builds this in via the domain
  restriction `dom A R`; here we exhibit a model where narrowing flips the truth
  value (demonstrated with `every`, since the `dom` restriction is independent of
  the choice of possessor quantifier; `most` is noncomputable cardinality).

* **Definiteness and uniqueness**: a definite possessive denotes a unique
  possessee. The `HasIotaWitness` capability of `Possessive.Definite` yields this
  via `existsUnique_possessee` with no bespoke proof — the payoff of the
  composable-mixin design.

## Main statements

* `narrowed_holds` / `unnarrowed_fails` / `narrowing_flips_truth_value`: the
  narrowing contrast on the planets/rings model.
* `theBoysCat_unique`: a definite possessive inherits `∃!`-reference from its
  capability instance.
* `johnsSisters_possesseeSet`: a relational possessive's `possesseeSet` is its
  lexical relation applied to the possessor.

## References

* [barker-1995]: Possessive Descriptions. CSLI Publications.
-/

namespace Barker1995

open Quantification
open Possessive
open ArgumentStructure.Relational

/-! ### Narrowing

Model over `Fin 5`: `0, 1, 2` are planets, `3, 4` are rings. Planet `0` has
ring `3`, planet `1` has ring `4`, and planet `2` has no ring. Both rings are
icy. *Most/every planet's rings are made of ice* should be evaluated only over
the ring-having planets `0, 1` — planet `2` is narrowed away. -/

/-- The planets `{0, 1, 2}`. -/
def isPlanet : Fin 5 → Prop := fun x => x.val < 3

/-- The rings `{3, 4}`. -/
def isRing : Fin 5 → Prop := fun x => 3 ≤ x.val

/-- Both rings are icy. -/
def isIcy : Fin 5 → Prop := isRing

/-- Planet `0` has ring `3`; planet `1` has ring `4`; planet `2` has no ring. -/
def hasRing : Fin 5 → Fin 5 → Prop := fun x y => (x = 0 ∧ y = 3) ∨ (x = 1 ∧ y = 4)

/-- With narrowing, *every planet's rings are made of ice* is **true**: the
ring-less planet `2` is excluded by the `dom isRing hasRing` restriction. -/
theorem narrowed_holds :
    Poss every_sem isPlanet some_sem hasRing isRing isIcy := by
  simp only [Poss, dom, every_sem, some_sem, isPlanet, isIcy, isRing, hasRing]
  decide

/-- Without narrowing, the naive reading *for every planet, it has an icy ring*
is **false**: the ring-less planet `2` falsifies it. -/
theorem unnarrowed_fails :
    ¬ every_sem isPlanet (fun x => some_sem (fun y => isRing y ∧ hasRing x y) isIcy) := by
  simp only [every_sem, some_sem, isPlanet, isIcy, isRing, hasRing]
  decide

/-- Narrowing is truth-conditionally active in this model: the narrowed reading
is true exactly where the un-narrowed reading is false. This is Barker's
narrowing — quantification ranges only over possessors with a possessee. -/
theorem narrowing_flips_truth_value :
    Poss every_sem isPlanet some_sem hasRing isRing isIcy ∧
      ¬ every_sem isPlanet (fun x => some_sem (fun y => isRing y ∧ hasRing x y) isIcy) :=
  ⟨narrowed_holds, unnarrowed_fails⟩

/-! ### Definiteness and the capability mixins

A definite possessive ("the boy's cat") and a relational possessive ("John's
sisters"), exercising the possessive-carrier capability mixins
(`HasIotaWitness`, `HasPossessor`, `HasPossessionRelation`). -/

/-- "the boy's cat": possessor `0` (the boy), with a uniquely-identified cat
`1`. Entities are `Fin 3` (boy, cat, dog); one situation. -/
def theBoysCat : Possessive.Definite (Fin 3) Unit where
  possessor := 0
  predicate := fun y _ => y = 1
  presupposition := fun _ => ⟨1, rfl, fun _ hy => hy⟩

/-- The definite possessive denotes a unique possessee, inherited from its
`HasIotaWitness` instance via `existsUnique_possessee` — no bespoke proof. -/
theorem theBoysCat_unique (s : Unit) :
    ∃! y : Fin 3, HasPossesseePredicate.possesseePredicate theBoysCat y s :=
  existsUnique_possessee theBoysCat s

/-- The sibling relation: `0`'s siblings are `1` and `2`. -/
def sibling : Fin 3 → Fin 3 → Prop := fun x y => x = 0 ∧ (y = 1 ∨ y = 2)

/-- "John's sisters": possessor `0` (John), with the sibling relation as the
possession relation (a relational noun, so the restrictor is trivial). -/
def johnsSisters : Possessive.Carrier (Fin 3) Unit where
  possessor := 0
  relation := fun x y _ => sibling x y
  restrictor := fun _ _ => True

/-- The relational possessive's `possesseeSet` is its lexical possession
relation applied to the possessor — derived through the `HasPossessor` and
`HasPossessionRelation` instances. -/
theorem johnsSisters_possesseeSet (y : Fin 3) (s : Unit) :
    possesseeSet johnsSisters y s ↔ sibling 0 y :=
  Iff.rfl

/-! ### Narrowing through a carrier

The same narrowing, now for a type ⟨1⟩ possessor ("planet 2's rings"). A carrier
bundles a single possessor, so narrowing surfaces as existential import: routed
through the unified `carrierGQ` denotation, *planet 2's rings are icy* is false
because planet 2 has no ring. Reuses the planets/rings model above. -/

/-- "planet 2's rings": possessor `2`, with `hasRing` as the possession
relation. -/
def planet2sRings : Possessive.Carrier (Fin 5) Unit where
  possessor := 2
  relation := fun x y _ => hasRing x y
  restrictor := fun y _ => isRing y

/-- *Planet 2's rings are icy* is false: via the unified carrier denotation,
existential import (`carrierGQ_existential_import`) requires planet 2 to possess
a ring, but it has none — narrowing at the individual level. -/
theorem planet2sRings_no_icy_rings :
    ¬ carrierGQ planet2sRings some_sem () isRing isIcy := by
  intro h
  obtain ⟨b, _, hr⟩ := carrierGQ_existential_import planet2sRings some_sem () h
  have hb : hasRing 2 b := hr
  simp only [hasRing] at hb
  rcases hb with ⟨h2, _⟩ | ⟨h2, _⟩ <;> exact absurd h2 (by decide)

end Barker1995
