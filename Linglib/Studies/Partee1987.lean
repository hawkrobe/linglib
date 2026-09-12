import Linglib.Semantics.Composition.TypeShifting

/-!
# Partee (1987): Noun Phrase Interpretation and Type-shifting Principles

This file formalizes the type-shifting principles of [partee-1987]. A noun phrase may denote
an entity, a predicate, or a generalized quantifier as its environment demands, and the
mappings between the three types come in inverse pairs, the paper's Figure 1: `lift`, the
substrate's `Quantification.individual`, and `lower`, the total injection of an entity into
its principal ultrafilter and its partial inverse; `ident` and `iota`, the singleton property
of an entity and the unique member of a property; and `nom` and `pred`, the correlates of
properties and entities after [chierchia-1984] (`lower_lift`, `iota_ident`, `nom_pred`). The
definite article has a partial entity meaning, `iota`, and a total quantifier meaning, `THE`,
related by `THE(king') = lift(iota(king'))` whenever the latter is defined, and the
predicative reading of *the king* is `BE(THE(king'))`, so that the three readings of Figure 2
cohere, `BE(THE(king')) = ident(iota(king'))`, and coincide with the common noun when there
is exactly one king, which is why the article can be dropped in *John is (the) president*
(`THE_eq_lift_iota`, `lower_THE`, `BE_THE`, `BE_THE_eq_of_unique`). The functor `BE`,
Montague's translation of *be* reconceived as a type shifter, is a homomorphism of the
Boolean structures, Fact 1 of §3.3, the substrate's `Quantification.BE_hom`, and the unique
homomorphism making Figure 3 commute, `BE(lift(j)) = ident(j)`, Fact 2 (`BE_lift`,
`BE_natural`); the indefinite article `A` is natural as its inverse, `BE(A(P)) = P`, so *be a
man* comes out as *man* (`BE_A`). English *be* itself is then predicate application, the
predicative reading having moved into the noun phrase.

## Implementation notes

The setting is extensional over a listed domain, so `pred` is `ident` and `nom` is `iota`,
and `THE` is the partial composite `lift ∘ iota` the paper offers as the alternative to its
total, presuppositionless quantifier meaning. The mappings to and from kinds of §3.4 onward
and the analysis of the Williams counterexample are not formalized.

## References

* [partee-1987]
* [chierchia-1984]
* [keenan-faltz-1985]
-/

namespace Partee1987

open Quantification Semantics.Composition.TypeShifting

variable {E : Type} (domain : List E) (j : E) (P : E → Prop)

/-! ### Figure 1: three inverse pairs -/

/-- `lower(lift(j)) = j`: `lower` inverts the total injection `lift`. -/
theorem lower_lift [DecidableEq E] (hmem : j ∈ domain) (hnd : domain.Nodup) :
    lower domain (individual j) = some j :=
  lower_individual domain j hmem hnd

/-- `iota(ident(j)) = j`: `iota` inverts the singleton map `ident`. -/
theorem iota_ident [DecidableEq E] (hmem : j ∈ domain) (hnd : domain.Nodup) :
    iota domain (ident j) = some j :=
  Semantics.Composition.TypeShifting.iota_ident domain j hmem hnd

/-- `nom(pred(j)) = j`: the extensional correlates of [chierchia-1984] are inverses. -/
theorem nom_pred [DecidableEq E] (hmem : j ∈ domain) (hnd : domain.Nodup) :
    NOM domain (pred j) = some j :=
  NOM_pred domain j hmem hnd

/-! ### Figure 2: *the king* in three types (§3.2) -/

/-- Whenever `iota` is defined, `THE(king') = lift(iota(king'))`. -/
theorem THE_eq_lift_iota (h : iota domain P = some j) : THE domain P = some (individual j) := by
  simp [THE, h]

/-- Whenever `iota` is defined, `lower(THE(king')) = iota(king')`. -/
theorem lower_THE [DecidableEq E] (hmem : j ∈ domain) (hnd : domain.Nodup)
    (h : iota domain P = some j) :
    (THE domain P).bind (lower domain) = some j := by
  simp [THE_eq_lift_iota domain j P h, lower_lift domain j hmem hnd]

/-- The predicative reading `BE(THE(king'))` is `ident(iota(king'))`: the diagram commutes. -/
theorem BE_THE (h : iota domain P = some j) : ∃ Q ∈ THE domain P, BE Q = ident j :=
  ⟨individual j, by simp [THE, h], BE_individual_eq_ident j⟩

/-- With exactly one king the predicative *the king* is the common noun *king*, the
equivalence that lets the article drop in *John is (the) president* (12). -/
theorem BE_THE_eq_of_unique (h : iota domain P = some j) (hP : ∀ x, P x ↔ x = j) :
    ∃ Q ∈ THE domain P, BE Q = P := by
  refine ⟨individual j, by simp [THE, h], ?_⟩
  rw [BE_individual_eq_ident]
  funext x
  exact propext (eq_comm.trans (hP x).symm)

/-! ### `A` and `BE` as natural functors (§3.3) -/

/-- Figure 3 commutes: `BE(lift(j)) = ident(j)`. -/
theorem BE_lift : BE (individual j) = ident j :=
  BE_individual_eq_ident j

/-- Fact 2: `BE` is the unique Boolean homomorphism making Figure 3 commute; Fact 1, that it
is one, is `Quantification.BE_hom`. -/
theorem BE_natural [Fintype E] [DecidableEq E] (f : BoundedLatticeHom (Quantifier E) (E → Prop))
    (hcomm : ∀ j : E, f (individual j) = ident j) (Q : Quantifier E) : f Q = BE Q :=
  BE_unique f hcomm Q

/-- `A` is an inverse of `BE`: `BE(A(man')) = man'`, so *be a man* is *man*. -/
theorem BE_A (hcomplete : ∀ x : E, x ∈ domain) : BE (A domain P) = P :=
  BE_A_id domain P hcomplete

end Partee1987
