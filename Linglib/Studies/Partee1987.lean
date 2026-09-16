import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Definiteness.Maximality
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Partee (1987): Noun Phrase Interpretation and Type-shifting Principles

This file formalizes the type-shifting principles of [partee-1987]. A noun phrase may denote
an entity, a predicate, or a generalized quantifier as its environment demands, and the
mappings between the three types come in inverse pairs, the paper's Figure 1: `lift`, the
substrate's `Quantification.individual`, and `lower`, the total injection of an entity into
its principal ultrafilter and its partial inverse; `ident` and `iota`, the singleton property
of an entity and the unique member of a property; and `nom` and `pred`, the correlates of
properties and entities after [chierchia-1984] (`lower_lift`, `iota_ident`). The definite
article has a partial entity meaning, `iota`, and a total quantifier meaning, `THE`, related
by `THE(king') = lift(iota(king'))` whenever the latter is defined, and the predicative reading
of *the king* is `BE(THE(king'))`, so that the three readings of Figure 2 cohere,
`BE(THE(king')) = ident(iota(king'))`, and coincide with the common noun when there is exactly
one king, which is why the article can be dropped in *John is (the) president*
(`THE_eq_lift_iota`, `lower_THE`, `BE_THE`, `BE_THE_eq_of_unique`). The functor `BE`,
Montague's translation of *be* reconceived as a type shifter, is a homomorphism of the Boolean
structures, Fact 1 of §3.3, the substrate's `Quantification.BE_hom`, and the unique
homomorphism making Figure 3 commute, `BE(lift(j)) = ident(j)`, Fact 2 (`BE_lift`,
`BE_natural`); the indefinite article `A` is natural as its inverse, `BE(A(P)) = P`, so *be a
man* comes out as *man* (`BE_A`). English *be* itself is then predicate application, the
predicative reading having moved into the noun phrase.

## Implementation notes

The setting is extensional, so `pred` is `ident`, `nom` and `iota` are both the Russellian
`Definiteness.russellIota`, and `THE` is the partial composite `lift ∘ iota` the paper offers
as the alternative to its total, presuppositionless quantifier meaning. Fact 2 is proved after
[keenan-faltz-1985]: the homomorphism is pinned on the atom at each singleton property, a meet
of the lifts and their complements, and monotonicity decides it everywhere else. The mappings
to and from kinds of §3.4 onward and the analysis of the Williams counterexample are not
formalized.

## References

* [partee-1987]
* [chierchia-1984]
* [keenan-faltz-1985]
-/

namespace Partee1987

open Quantification Definiteness

variable {E : Type*} (j : E) (P : E → Prop)

/-! ### Figure 1: three inverse pairs -/

/-- `lower(lift(j)) = j`: `lower` inverts the total injection `lift`. -/
theorem lower_lift : lower (individual j) = some j :=
  lower_individual j

/-- `iota(ident(j)) = j`: `iota` inverts the singleton map `ident`, and extensionally this is
`nom(pred(j)) = j` as well. -/
theorem iota_ident : russellIota (ident j) = some j :=
  russellIota_ident j

/-- (48): lowering a lifted entity through `BE` and `iota` returns it. -/
theorem iota_BE_lift : russellIota (BE (individual j)) = some j := by
  rw [BE_individual_eq_ident]; exact russellIota_ident j

/-! ### Figure 2: *the king* in three types (§3.2) -/

/-- Whenever `iota` is defined, `THE(king') = lift(iota(king'))`. -/
theorem THE_eq_lift_iota (h : russellIota P = some j) : THE P = some (individual j) := by
  simp [THE, h]

/-- Whenever `iota` is defined, `lower(THE(king')) = iota(king')`. -/
theorem lower_THE (h : russellIota P = some j) : (THE P).bind lower = some j := by
  simp [THE_eq_lift_iota j P h, lower_individual]

/-- The predicative reading `BE(THE(king'))` is `ident(iota(king'))`: the diagram commutes. -/
theorem BE_THE (h : russellIota P = some j) : ∃ Q ∈ THE P, BE Q = ident j :=
  ⟨individual j, by simp [THE, h], BE_individual_eq_ident j⟩

/-- With exactly one king the predicative *the king* is the common noun *king*, the
equivalence that lets the article drop in *John is (the) president* (12). -/
theorem BE_THE_eq_of_unique (h : russellIota P = some j) (hP : ∀ x, P x ↔ x = j) :
    ∃ Q ∈ THE P, BE Q = P :=
  ⟨individual j, by simp [THE, h],
    by rw [BE_individual_eq_ident]; exact funext λ x => propext (hP x).symm⟩

/-! ### `A` and `BE` as natural functors (§3.3) -/

/-- Figure 3 commutes: `BE(lift(j)) = ident(j)`. -/
theorem BE_lift : BE (individual j) = ident j :=
  BE_individual_eq_ident j

/-- Fact 2: `BE` is the unique Boolean homomorphism making Figure 3 commute; Fact 1, that it
is one, is `Quantification.BE_hom`. -/
theorem BE_natural [Fintype E] [DecidableEq E] (f : BoundedLatticeHom (Quantifier E) (E → Prop))
    (hcomm : ∀ j : E, f (individual j) = ident j) (Q : Quantifier E) : f Q = BE Q := by
  funext x
  show f Q x = Q (ident x)
  -- the atom of the quantifier algebra at `{x}`, as a meet of literals
  let lit : E → Quantifier E := λ j => if j = x then individual j else (individual j)ᶜ
  let atom : Quantifier E := Finset.univ.inf lit
  have hf_lit : ∀ j, f (lit j) = if j = x then ident j else (ident j)ᶜ := λ j => by
    simp only [lit]; split
    · exact hcomm j
    · rw [map_compl' f, hcomm j]
  have hf_atom : f atom x := by
    show f (Finset.univ.inf lit) x
    rw [map_finset_inf, Finset.inf_apply]
    refine Finset.le_inf (λ j _ => show ⊤ ≤ f (lit j) x from λ _ => ?_) trivial
    rw [hf_lit]; split
    · exact ‹j = x›.symm
    · exact λ e : x = j => ‹¬ j = x› e.symm
  have hatom_point : ∀ R, atom R → R = ident x := λ R hR => by
    funext j
    have hj : lit j R := (Finset.inf_le (Finset.mem_univ j) : atom ≤ lit j) R hR
    simp only [lit] at hj; split at hj
    · exact propext ⟨λ _ => ‹j = x›, λ _ => hj⟩
    · exact propext ⟨λ hr => absurd hr hj, λ e => absurd e ‹¬ j = x›⟩
  have hatom_le : ∀ S : Quantifier E, S (ident x) → atom ≤ S :=
    λ S hS R hR => hatom_point R hR ▸ hS
  by_cases hQ : Q (ident x)
  · exact propext ⟨λ _ => hQ, λ _ => OrderHomClass.mono f (hatom_le Q hQ) x hf_atom⟩
  · have hfQc : f Qᶜ x := OrderHomClass.mono f (hatom_le Qᶜ hQ) x hf_atom
    rw [map_compl' f] at hfQc
    exact propext ⟨λ h => absurd h hfQc, λ h => absurd h hQ⟩

/-- `A` is an inverse of `BE`: `BE(A(man')) = man'`, so *be a man* is *man*. -/
theorem BE_A (domain : List E) (hcomplete : ∀ x : E, x ∈ domain) : BE (A domain P) = P :=
  BE_A_id domain P hcomplete

end Partee1987
