import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Semantics.Homogeneity.Plural
import Linglib.Semantics.Polarity.Sentence
import Linglib.Data.Examples.TieuKrizChemla2019

/-!
# Tieu, Križ and Chemla (2019): Children's Acquisition of Homogeneity in Plural Definite Descriptions

This file formalizes the readings of the plural definite that [tieu-kriz-chemla-2019] tests
on four- and five-year-old French-speaking children, and the prediction of the implicature
account of homogeneity, [magri-2014], that the study falsifies. *The trucks are blue* and
*The trucks are not blue*, (1)–(2), are neither true nor false when some but not all of the
trucks are blue, a GAP context, whereas the universal (3)–(4) has a complementary negation.
A child might read the definite homogeneously, existentially as (6), or universally as (7),
and the three readings predict distinct pairs of responses to the positive and the negative
sentence in a GAP context, Figure 2, `Reading.value` and `value_of_isGap`. On the
implicature account, (10)–(11), the definite has the existential meaning and reaches the
universal one by exhaustifying twice, the outer exhaustification negating the *not all*
implicature of *some*, so that implicature is a sub-computation of homogeneity: a child who
accepts *some* where all objects have the property should accept the positive definite in a
GAP context, and one who rejects the first should reject the second,
`implicature_gap_iff_si`. Experiment 2's ternary judgments separate the homogeneous reading,
undefined in a GAP context, from a universal reading outscoping negation, false there,
which the binary judgments of Experiment 1 conflate, `gapPattern_injective` and
`binary_collapse`.

## Implementation notes

A world is the set of objects with the property and the definite's plurality a finite set
of atoms, so the homogeneous reading is the substrate's `Homogeneity.barePlural`, the
universal readings `Homogeneity.allPlural` at either scope relative to negation, and the
scope-ambiguous universal of Experiment 2 supervaluates over the two scopes with the
`Trivalent.dist` that supervaluates the bare plural over its atoms. A ternary reward is the
trivalent value itself, Table 8's coding, and a binary judgment accepts exactly the true
sentences. The implicature account is computed with the substrate's innocent exclusion on
these worlds, and a participant computes the implicature exactly when *all* is among their
alternatives to *some*, the paper's assumption that the same alternatives drive both
inferences. Partial-truth responding, Table 8's PT column, is a response strategy rather than
a reading, and the paper finds no evidence for it. The experiments are reported in prose. In
Experiment 1, a binary truth-value judgment task, sixteen of 24 children showed the
homogeneous pattern and eight the existential one, no child the universal one; six of the
homogeneous children, and five of 22 adults, accepted *some* where all objects had the
property, the HOM/−SI group the account excludes, and the group survives a Bayesian group
assignment and leave-one-out cross-validation. Experiment 2, a ternary reward task after
[katsos-bishop-2011], replicated the group with five of 22 children and two of 25 adults.
Since nearly all children with the implicature read the definite homogeneously while the
converse fails, the paper concludes that homogeneity is acquired before, and independently
of, the scalar implicature, resolving the conflict between the non-maximal interpretations
of [karmiloff-smith-1979] and [caponigro-etal-2012] and the maximal ones of earlier
act-out tasks: young children's definite is existential and scopes under negation. The
examples are the rows of `Data.Examples.TieuKrizChemla2019`.

## TODO

The printed Table 8 assigns the scope-ambiguous and wide-scope universal groups GAP
responses that contradict the definitions beside it, which are followed here.

## References

* [tieu-kriz-chemla-2019]
* [magri-2014]
* [kriz-2015]
* [kriz-chemla-2015]
* [spector-2013]
* [fox-2007]
* [katsos-bishop-2011]
* [karmiloff-smith-1979]
* [caponigro-etal-2012]
-/

namespace TieuKrizChemla2019

open Exhaustification Homogeneity

variable {Atom : Type*} (x : Finset Atom)

/-- A GAP context: some but not all objects of the plurality have the property, Figure 1. -/
def IsGap (w : Finset Atom) : Prop := (∃ a ∈ x, a ∈ w) ∧ ∃ a ∈ x, a ∉ w

/-! ### Readings of the plural definite (section 1) -/

section Readings

variable [DecidableEq Atom]

/-- The scope of a universal reading of the definite relative to negation. -/
inductive Scope where
  | low
  | wide
  deriving DecidableEq, Fintype

/-- The negated sentence under a universal reading of the definite at a scope: *not all* or
*none*. -/
def universalNeg : Scope → Trivalent.Prop3 (Finset Atom)
  | .low => λ w => (allPlural (λ a w => a ∈ w) x w).neg
  | .wide => allPlural (λ a w => a ∉ w) x

/-- The readings a participant may assign to the plural definite: the three of Figure 2 and
the two further universal readings of Experiment 2, Table 8. -/
inductive Reading where
  /-- THE as SOME, (6), scoping under negation. -/
  | existential
  /-- THE with a truth-value gap, (1)–(2). -/
  | homogeneous
  /-- THE as ALL, (7), scoping under negation. -/
  | universal
  /-- THE as ALL, scoping over negation. -/
  | wideScopeUniversal
  /-- THE as ALL, ambiguous in scope relative to negation. -/
  | scopeAmbiguous
  deriving Repr, DecidableEq, Fintype

/-- The value of the definite sentence at a polarity under a reading. Negation is Kleene
negation except where the universal outscopes it; the scope-ambiguous reading supervaluates
over the two scopes. -/
def Reading.value : Reading → SentencePolarity → Trivalent.Prop3 (Finset Atom)
  | .existential, .positive => λ w => .ofProp (∃ a ∈ x, a ∈ w)
  | .existential, .negative => λ w => (Trivalent.ofProp (∃ a ∈ x, a ∈ w)).neg
  | .homogeneous, .positive => barePlural (λ a w => a ∈ w) x
  | .homogeneous, .negative => λ w => (barePlural (λ a w => a ∈ w) x w).neg
  | .universal, .positive | .wideScopeUniversal, .positive | .scopeAmbiguous, .positive =>
      allPlural (λ a w => a ∈ w) x
  | .universal, .negative => universalNeg x .low
  | .wideScopeUniversal, .negative => universalNeg x .wide
  | .scopeAmbiguous, .negative => λ w => Trivalent.dist Finset.univ (universalNeg x · w = .true)

/-- The values of the positive and the negative sentence in a GAP context under each reading,
Figure 2 and Table 8. -/
def Reading.gapPattern : Reading → Trivalent × Trivalent
  | .existential => (.true, .false)
  | .homogeneous => (.indet, .indet)
  | .universal => (.false, .true)
  | .wideScopeUniversal => (.false, .false)
  | .scopeAmbiguous => (.false, .indet)

/-- The binary judgments of a reading's GAP pattern: each sentence is accepted iff true. -/
def Reading.binaryPattern (r : Reading) : Bool × Bool :=
  (r.gapPattern.1 = .true, r.gapPattern.2 = .true)

variable {x}

/-- In a GAP context every reading takes the values of Figure 2 and Table 8. -/
theorem value_of_isGap {w : Finset Atom} (hw : IsGap x w) (r : Reading) :
    (r.value x .positive w, r.value x .negative w) = r.gapPattern := by
  have hall : allPlural (λ a w => a ∈ w) x w = .false :=
    (allPlural_eq_false_iff _ _ _).2 λ h => hw.2.elim λ a ha => ha.2 (h a ha.1)
  have hnone : allPlural (λ a w => a ∉ w) x w = .false :=
    (allPlural_eq_false_iff _ _ _).2 λ h => hw.1.elim λ a ha => h a ha.1 ha.2
  have hbare : barePlural (λ a w => a ∈ w) x w = .indet :=
    (Trivalent.dist_eq_indet_iff _ _).2 ⟨hw.1, hw.2⟩
  have hamb : Trivalent.dist Finset.univ (universalNeg x · w = .true) = .indet :=
    (Trivalent.dist_eq_indet_iff _ _).2
      ⟨⟨.low, Finset.mem_univ _, by simp [universalNeg, hall]⟩,
        ⟨.wide, Finset.mem_univ _, by simp [universalNeg, hnone]⟩⟩
  cases r
  · simp [Reading.value, Reading.gapPattern, hw.1]
  · simp [Reading.value, Reading.gapPattern, hbare]
  · simp [Reading.value, Reading.gapPattern, universalNeg, hall]
  · simp [Reading.value, Reading.gapPattern, universalNeg, hall, hnone]
  · simp only [Reading.value, Reading.gapPattern, hall, hamb]

/-- Ternary judgments separate all five readings in a GAP context, Experiment 2's design. -/
theorem gapPattern_injective : Function.Injective Reading.gapPattern := by decide

/-- The three readings of Figure 2 predict pairwise distinct binary responses in a GAP
context, so Experiment 1 identifies them. -/
theorem binaryPattern_figure2 :
    ∀ r ∈ [Reading.existential, .homogeneous, .universal],
      ∀ r' ∈ [Reading.existential, .homogeneous, .universal],
        r.binaryPattern = r'.binaryPattern → r = r' := by decide

/-- Binary judgments conflate the homogeneous reading with the universal readings that
outscope negation, all three rejecting both sentences in a GAP context: Experiment 1 cannot
tell a truly homogeneous child from a wide-scope universal one. -/
theorem binary_collapse :
    Reading.homogeneous.binaryPattern = Reading.wideScopeUniversal.binaryPattern ∧
      Reading.homogeneous.binaryPattern = Reading.scopeAmbiguous.binaryPattern := by decide

end Readings

/-! ### The implicature account (section 2) -/

section Implicature

/-- The literal existential meaning of the definite and of *some*: some object of the
plurality has the property. -/
def someMeaning : Set (Finset Atom) := {w | ∃ a ∈ x, a ∈ w}

/-- *All*: every object of the plurality has the property. -/
def allMeaning : Set (Finset Atom) := {w | x ⊆ w}

/-- A participant's alternatives to *some*: *all* is among them exactly when the participant
computes the *not all* implicature. -/
def alts : Bool → Set (Set (Finset Atom))
  | true => {someMeaning x, allMeaning x}
  | false => {someMeaning x}

/-- (11): the strengthened definite of the implicature account, [magri-2014]'s double
exhaustification. The definite's only Horn-mate is the equivalent *some*, so the inner
exhaustification leaves its existential meaning; the outer exhaustifies that against the
exhaustified *some*, (10). -/
def strengthened (si : Bool) : Set (Finset Atom) :=
  exhIE {someMeaning x, exhIE (alts x si) (someMeaning x)} (someMeaning x)

variable {x}

private theorem allMeaning_subset_someMeaning (hx : x.Nonempty) :
    allMeaning x ⊆ someMeaning x :=
  λ _ hw => hx.elim λ a ha => ⟨a, ha, hw ha⟩

/-- (10): with *all* among its alternatives, *some* is exhaustified to *some but not all*. -/
theorem exhIE_someMeaning {w : Finset Atom} (hw : IsGap x w) :
    exhIE {someMeaning x, allMeaning x} (someMeaning x) = someMeaning x \ allMeaning x :=
  exhIE_pair_sdiff (φ := someMeaning x) (d := allMeaning x)
    ⟨w, hw.1, λ h => hw.2.elim λ _ ha => ha.2 (h ha.1)⟩

/-- (11): with the implicature, the strengthened definite is universal. -/
theorem strengthened_true (hx : x.Nonempty) {w : Finset Atom} (hw : IsGap x w) :
    strengthened x true = allMeaning x := by
  rw [strengthened, alts, exhIE_someMeaning hw,
    exhIE_pair_sdiff (φ := someMeaning x) (d := someMeaning x \ allMeaning x)
      ⟨x, hx.elim λ a ha => ⟨a, ha, ha⟩,
        λ h => h.2 (show x ⊆ x from Finset.Subset.refl x)⟩,
    Set.sdiff_sdiff_right_self]
  exact Set.inter_eq_right.2 (allMeaning_subset_someMeaning hx)

/-- Without the implicature both exhaustifications are vacuous and the definite keeps its
existential meaning. -/
theorem strengthened_false : strengthened x false = someMeaning x := by
  rw [strengthened, alts, exhIE_singleton_self, Set.pair_eq_singleton, exhIE_singleton_self]

/-- The *not all* implicature is a sub-computation of the homogeneity implicature: a
participant accepts the positive definite in a GAP context `w` exactly when they accept
*some* in a context `w'` where every object has the property. The HOM/−SI participants of
both experiments, who reject the first and accept the second, contradict the account. -/
theorem implicature_gap_iff_si (hx : x.Nonempty) {w w' : Finset Atom} (hw : IsGap x w)
    (hw' : x ⊆ w') (si : Bool) :
    w ∈ strengthened x si ↔ w' ∈ exhIE (alts x si) (someMeaning x) := by
  cases si
  · rw [strengthened_false, alts, exhIE_singleton_self]
    exact iff_of_true hw.1 (hx.elim λ a ha => ⟨a, ha, hw' ha⟩)
  · rw [strengthened_true hx hw, alts, exhIE_someMeaning hw]
    exact iff_of_false (λ h => hw.2.elim λ _ ha => ha.2 (h ha.1)) λ h => h.2 hw'

/-- Negation is downward-entailing, so the account leaves the negated definite its
existential meaning, false in a GAP context whatever the participant's implicatures: the
universal pattern of Figure 2 is never predicted, and the account's two profiles are the
existential pattern without the implicature and the homogeneous pattern with it. -/
theorem implicature_binaryPattern (hx : x.Nonempty) {w : Finset Atom} (hw : IsGap x w) :
    (w ∈ strengthened x false ↔ Reading.existential.binaryPattern.1 = true) ∧
      (w ∈ (someMeaning x)ᶜ ↔ Reading.existential.binaryPattern.2 = true) ∧
      (w ∈ strengthened x true ↔ Reading.homogeneous.binaryPattern.1 = true) ∧
      (w ∈ (someMeaning x)ᶜ ↔ Reading.homogeneous.binaryPattern.2 = true) := by
  rw [strengthened_false, strengthened_true hx hw]
  exact ⟨iff_of_true hw.1 rfl, iff_of_false (λ h => h hw.1) (by decide),
    iff_of_false (λ h => hw.2.elim λ _ ha => ha.2 (h ha.1)) (by decide),
    iff_of_false (λ h => h hw.1) (by decide)⟩

end Implicature

end TieuKrizChemla2019
