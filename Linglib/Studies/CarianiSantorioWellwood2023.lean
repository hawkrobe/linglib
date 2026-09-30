module

public import Linglib.Semantics.Degree.Background
public import Linglib.Semantics.Degree.Hom
public import Linglib.Fragments.English.Adjectives

/-!
# Cariani, Santorio and Wellwood 2023: positive gradable adjectives without positive morphemes

[cariani-santorio-wellwood-2023] give a gradable adjective two components (4), (17): a
background ordering of states, the states of having some heat for *hot*, and a
context-dependent threshold property, true of the states that count as hot. The positive form
says that the subject holds a state with the threshold property (20). The comparative bypasses
the threshold (22): some state of the subject's measures, under an admissible measure, above the
greatest degree of the standard's (23), the comparative of [wellwood-2015]. The positive form
therefore needs no covert *pos*, and neither form entails the other. Scale-mates such as *warm*
and *hot* share their background and differ in threshold (24), so their comparatives are one
comparison (25) while the higher threshold's positive form entails the lower's (26).

The framework is `Semantics/Degree/Background.lean`, and its relations to [klein-1980]'s
delineations and to degree thresholds are in `Semantics/Degree/Hom.lean`; this file checks the
paper's claims against it. The inference (19), from *Barcelona is hot* and *Miami is hotter than
Barcelona* to *Miami is hot*, which the paper grounds in its monotonicity postulate (18), holds
for an admissible measure on a total background (`Degree.mem_image_of_maxComparative`) and fails
on any non-total one (`Degree.not_mem_image_Ici_of_not_le`). The paper argues from two cities of
equal temperature that the background is not linear (§4). Its premises, distinct holders and
equal measure, make the two states distinct and tied whenever the measure reflects the ordering,
as (15b)'s *as much heat as* requires, and then make the background total
(`ne_and_antisymmRel_and_total`): the argument refutes antisymmetry, not comparability, and the
two states share one degree, the class of fn. 10. Read as the text words it, with the two
states unordered, the background would refute (19) and let a threshold count one city hot and
the other not at the same temperature.

The monotonicity postulate parallels Klein's Consistency Postulate (fn. 11): the thresholds of a
background form a consistent delineation exactly when the background is total
(`Degree.isMonotoneDelineation_upperSets_iff`). The injection of §6 into a degree semantics with
a lexical threshold degree (28)–(32) is exact when the measure reflects the background: a
threshold above a contrast state is then the degree threshold at its degree
(`Degree.Comparison.ge_over_eq_Ici`), and every threshold is a pulled-back degree threshold
(`Degree.forall_isUpperSet_exists_preimage_iff`). On a non-total background some threshold is no
degree threshold (`Degree.exists_isUpperSet_forall_ne_preimage`), the difference the paper's
Coda credits to states.

## Main results

* `ne_and_antisymmRel_and_total`: the equal-temperature cities of §4 hold distinct, tied states
  of a total background.
* The examples check (19) on a three-state model, the split verdict of the literal reading of
  §4, (24) against the English fragment, and the failure of the converse of (26).

## Implementation notes

The states of all holders form a type `S` with the background preorder, and `holder : S → X` is
a function, each state having one holder (fn. 9), but not injective, since the than-clause
maximum ranges over a holder's several states. The presupposition that a state lies in the
domain of the background is membership in `S`. The comparative's standard degree `d_b` is the
greatest element of `Degree.thanDegrees`. In (31) the comparative binds `g` but writes
`background(f)`.

## TODO

* The crispness contrast (8) and *for*-phrases (33), (34), for which the paper gives no semantics.

## References

* [cariani-santorio-wellwood-2023]
* [wellwood-2015]
* [klein-1980]
* [cresswell-1976]
-/

@[expose] public section

namespace CarianiSantorioWellwood2023

open Set Degree

variable {S X : Type*} [Preorder S] {holder : S → X}

/-! ### The inference (19) -/

/-- (19) on three heat states `0 < 1 < 2`, Barcelona holding `0` and `1` and Miami `2`, with *hot*
the states from `1` up and the identity as measure: *Barcelona is hot* and *Miami is hotter than
Barcelona*, and so, by upward monotonicity, *Miami is hot*. -/
example :
    let holder : Fin 3 → Bool := fun s ↦ decide (s = 2)
    false ∈ holder '' Ici 1 ∧ maxComparative (holder · = true) (holder · = false) id ∧
      true ∈ holder '' Ici 1 := by
  intro holder
  have hb : false ∈ holder '' Ici 1 := ⟨1, mem_Ici.2 le_rfl, by decide⟩
  have hc : maxComparative (holder · = true) (holder · = false) id := by
    refine ⟨1, ⟨⟨1, by decide, le_rfl⟩, ?_⟩, 2, by decide, by decide⟩
    rintro d ⟨s, hs, hds⟩
    exact hds.trans ((by decide : ∀ s : Fin 3, decide (s = 2) = false → s ≤ 1) s hs)
  exact ⟨hb, hc, mem_image_of_maxComparative (isUpperSet_Ici 1) strictMono_id hb hc⟩

/-! ### The equal-temperature cities (§4, fn. 10) -/

/-- The cities of §4: states of distinct holders at equal measure are distinct and, when the
measure reflects the background into a linear scale, tied, and the background is total. -/
theorem ne_and_antisymmRel_and_total {D : Type*} [LinearOrder D] {μ : S → D}
    (hμ : ∀ a b, μ a ≤ μ b → a ≤ b) {s t : S} (hne : holder s ≠ holder t) (heq : μ s = μ t) :
    s ≠ t ∧ AntisymmRel (· ≤ ·) s t ∧ ∀ u v : S, u ≤ v ∨ v ≤ u :=
  ⟨ne_of_apply_ne holder hne, ⟨hμ s t heq.le, hμ t s heq.ge⟩, total_of_reflect_le hμ⟩

/-- On the literal reading of §4 the two cities' states are unordered. Then a threshold can hold
of one and not of the other at the same temperature: on the componentwise order of `ℕ × ℕ` with
the sum as measure, `(1, 0)` and `(0, 1)` measure alike, and the states from `(1, 0)` up include
the one and not the other. -/
example :
    (1, 0).1 + (1, 0).2 = (0, 1).1 + (0, 1).2 ∧ ((1, 0) : ℕ × ℕ) ∈ Ici (1, 0) ∧
      ((0, 1) : ℕ × ℕ) ∉ Ici (1, 0) := by
  refine ⟨rfl, mem_Ici.2 le_rfl, ?_⟩
  simp [Prod.mk_le_mk]

/-! ### Scale-mates (24)–(26) -/

/-- (24) in the English fragment: *hot* and *warm* measure one dimension. -/
example : English.Adjectives.hot.dimension = English.Adjectives.warm.dimension := rfl

/-- The converse of (26) fails: with *warm* the states from `1` up and *hot* the states from `2`
up on `Fin 3`, a city holding only the state `1` is warm and not hot. -/
example :
    let holder : Fin 3 → Bool := fun s ↦ decide (s = 1)
    true ∈ holder '' Ici 1 ∧ true ∉ holder '' Ici 2 := by
  intro holder
  refine ⟨⟨1, mem_Ici.2 le_rfl, by decide⟩, ?_⟩
  rintro ⟨s, hs, hs1⟩
  revert s
  decide

end CarianiSantorioWellwood2023
