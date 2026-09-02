import Linglib.Semantics.Possessive.Basic

/-!
# Partee & Borschev 2001: Some puzzles of predicate possessives

Do predicate possessives (*that team is John's*) refute the uniform analysis of the genitive
([jensen-vikner-1994]), on which every genitive is the argument of a relational noun, a plain noun
being coerced to a relation first? A bare *John's* in predicate position is one of two things.
Either it is an elliptical NP with an understood relational noun — *that teacher is John's* is
*John's teacher* (17c), so the earlier verdict that predicate possessives take only a free
relation ([stockwell-schachter-partee-1973]; the (c) examples of [partee-1997], repeated as
(1)–(3)) is withdrawn, the oddness of *that father is John's* being charged to the demonstrative
subject (17a). Or it is a genuine ⟨e,t⟩ predicate `λx[R_POSS(John)(x)]` (31), whose relation of
possession or control comes from the possessive form and not from any noun; inside an NP such a
possessive is an intersective modifier, the modifier genitive (6) being the noun conjoined with
it (`Possessive.viaModifier_eq_inf`). German non-agreeing *mein* and Russian and Polish nominative
predicate pronouns are bare predicates with the possession reading only; the agreeing and
instrumental forms are elliptical NPs and admit the noun's relation as well ((28)–(30),
(32)–(35)). Russian marks the split in form — postnominal genitive an argument, prenominal
possessive a modifier — and on a relational noun the two constructions come apart (25).

## Main statements

* `elliptical_iff_bare` — predicated of a `P`, the elliptical NP *[John's P]* on its possession
  reading and the bare predicate possessive agree: the reading the two forms share.
* `ubijcaPeti_ne_petinUbijca` — *ubijca Peti* 'murderer of Petja' (the noun's own relation
  applied to Petja) and *Petin ubijca* (the modifier over the relatum-closed noun) are distinct
  predicates; the latter holds exactly of a murderer Petja controls (`petinUbijca_iff`).

## References

* [partee-borschev-2001]
* [jensen-vikner-1994]
* [partee-1997]
* [stockwell-schachter-partee-1973]
-/

namespace ParteeBorschev2001

open ArgumentStructure.Relational Possessive

variable {E S : Type*}

/-! ### Elliptical NPs and bare predicates (§2.3–2.4) -/

/-- Predicated of something that is a `P`, the elliptical NP *[John's P]* on its possession
reading — `P` coerced by `R`, then taken as the genitive's argument — and the bare predicate
possessive `λx[R(John)(x)]` (31) agree. -/
theorem elliptical_iff_bare {P : E → S → Prop} {x : E} {s : S} (possessor : E)
    (R : E → E → S → Prop) (hP : P x s) :
    viaArgument possessor (π P R) x s ↔ viaArgument possessor R x s := by
  simp [viaArgument, π, hP]

/-! ### Russian genitive vs prenominal possessive (§2.2)

*stul Peti* and *Petin stul* (23)–(24) describe the same range of cases: with a plain noun the
argument genitive over the coerced noun and the modifier possessive coincide
(`Possessive.viaArgument_pi`). On a relational noun they part: *ubijca Peti* is 'murderer of
Petja', while *Petin ubijca* is only 'a murderer Petja has hired' (25). Model: Petja `0`, the
killer `1` who murdered Petja, a hireling `2` who murdered the killer and whom Petja controls. -/

/-- Entities: Petja, the killer, the hireling. -/
abbrev Ent := Fin 3
/-- Petja. -/
abbrev petja : Ent := 0
/-- The one who murdered Petja. -/
abbrev killer : Ent := 1
/-- The murderer in Petja's employ. -/
abbrev hireling : Ent := 2

/-- *ubijca*: `murderer v y` iff `y` murdered `v`. -/
def murderer : Ent → Ent → Unit → Prop := fun v y _ =>
  v = petja ∧ y = killer ∨ v = killer ∧ y = hireling

/-- `R_POSS`: Petja controls the hireling. -/
def rPoss : Ent → Ent → Unit → Prop := fun p y _ => p = petja ∧ y = hireling

/-- *ubijca Peti* (25a): the relational noun's own relation applied to Petja — the killer. -/
theorem ubijcaPeti_iff (y : Ent) : viaArgument petja murderer y () ↔ y = killer := by
  unfold viaArgument murderer; decide +revert

/-- *Petin ubijca* (25b): the modifier possessive over the noun with its relatum slot closed —
a murderer Petja controls, the hireling, never Petja's own murderer. -/
theorem petinUbijca_iff (y : Ent) :
    viaModifier petja (ExPossessor murderer) rPoss y () ↔ y = hireling := by
  unfold viaModifier π ExPossessor murderer rPoss; decide +revert

/-- The genitive and the prenominal possessive are distinct predicates on a relational noun. -/
theorem ubijcaPeti_ne_petinUbijca :
    viaArgument petja murderer ≠ viaModifier petja (ExPossessor murderer) rPoss := fun h =>
  absurd ((ubijcaPeti_iff killer).2 rfl) (by rw [h, petinUbijca_iff]; decide)

end ParteeBorschev2001
