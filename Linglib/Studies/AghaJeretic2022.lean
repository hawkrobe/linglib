import Linglib.Logic.Duality
import Linglib.Semantics.Homogeneity.Usable
import Linglib.Semantics.Quantification.Witness
import Linglib.Data.Generalizations.HomogeneityGap
import Linglib.Data.Examples.AghaJeretic2022

/-!
# Weak necessity modals as homogeneous pluralities of worlds

Weak necessity modals take obligatory apparent wide scope over negation, whether the negation is
clausemate or in a higher clause: *you shouldn't go* cannot be continued by *but you are allowed
to go*, where *you don't have to go* can. The pattern is that of plural definites, and Agha and
Jeretič propose that *should* is to *must* what *the* is to *all*: strong necessity quantifies
universally over the best worlds while weak necessity predicates the prejacent of their
plurality. This file instantiates Križ's plural predication with worlds as the atoms: `should D p`
is `Trivalent.dist` over the best worlds `D w` and `must D p` the universal quantifier, so the
gap arises exactly in mixed domains (`should_eq_indet_iff`), negation is symmetric and hence
scopeless (`should_not`), a true negated *should* contradicts the existential continuation where
a negated *must* does not (`not_exists_of_should_not`, `must_false_of_indet`), and *necessarily*
is the same gap remover as *all*, `Prop3.metaAssert`, which turns *should* into *must*
(`must_eq_metaAssert_should`, `necessarily_removes_gap`). Križ's sufficient truth and
addressing give the exception tolerance of the perfect-grade scenario under one question but
not the other, and the unusability of *have to* under either (`exception_tolerance`), and the
two-doors scenario where *should* is indeterminate and *must* false (`two_doors`).

Weak necessity is derived from strong necessity by an operator picking the unique minimal
witness set of the quantifier: for *must* this is the domain itself, so the result is the
plurality *should* denotes (`x_must`), while possibility has one minimal witness per best world,
so the operator is undefined on it — Javanese NE attaches to necessity only — whereas a
counterfactual marker needing only some witness applies to both, as French *devrais* and
*pourrais* show (`possibility_witnesses`). Domain restriction, on which *should* quantifies over
a proper subset of the worlds *allowed* ranges over, cannot make the negated modal contradict
the existential continuation (`domainRestriction_no_contradiction`); run over the pooled
polarity-by-scenario rows it matches the classical cells and fails exactly the gap cells
(`domainRestriction_fails_exactly_gap`), which the plural semantics reproduces
(`should_matches_grid`). The continuation, remover, and derivation patterns of the paper's
examples are stated over its rows (`weak_negated_contradicts`, `strong_extraclausal_compatible`,
`necessarily_licenses_continuation`, `ne_only_necessity`). The proportional and degree-based
rivals, and the conditionals, generics, and habituals of the closing section, are discussed
without a formal counterpart here.

## References

* [agha-jeretic-2022]
* [kriz-2016]
* [kratzer-1981]
* [von-fintel-iatridou-2008]
* [vander-klok-hohaus-2020]
* [barwise-cooper-1981]
* [schlenker-2004]
-/

namespace AghaJeretic2022

open Trivalent (Prop3 dist dist_eq_true_iff dist_eq_false_iff dist_eq_indet_iff
  dist_not_of_nonempty)
open Semantics.Homogeneity Quantification Data.Examples
open Generalizations.HomogeneityGap (GapDatum GapScenario fromExample)
open Features (Polarity)

variable {W : Type*} (D : W → Finset W) (p : W → Prop) [DecidablePred p]

/-! ### Weak necessity as plural predication over worlds -/

/-- `should D p`: the prejacent predicated of the plurality of best worlds `D w`. -/
def should : Prop3 W := fun w => dist (D w) p

/-- `must D p`: the prejacent holds in every best world. -/
def must : Prop3 W := fun w => Trivalent.ofBool (decide (∀ w' ∈ D w, p w'))

theorem should_eq_true_iff (w : W) : should D p w = .true ↔ ∀ w' ∈ D w, p w' :=
  dist_eq_true_iff _ _

theorem should_eq_false_iff (w : W) :
    should D p w = .false ↔ (D w).Nonempty ∧ ∀ w' ∈ D w, ¬ p w' :=
  dist_eq_false_iff _ _

/-- The gap: some best worlds satisfy the prejacent and some do not. -/
theorem should_eq_indet_iff (w : W) :
    should D p w = .indet ↔ (∃ w' ∈ D w, p w') ∧ ∃ w' ∈ D w, ¬ p w' :=
  dist_eq_indet_iff _ _

/-- Homogeneity: over a nonempty domain, negating the prejacent negates the modal sentence, so
the gap is symmetric and negation is scopeless. -/
theorem should_not (w : W) (hne : (D w).Nonempty) :
    should D (fun w' => ¬ p w') w = (should D p w).neg :=
  dist_not_of_nonempty _ _ hne

/-- A true negated weak necessity leaves no best world for the existential continuation. -/
theorem not_exists_of_should_not (w : W) (h : should D (fun w' => ¬ p w') w = .true) :
    ¬ ∃ w' ∈ D w, p w' :=
  fun ⟨w', hw', hp⟩ => (should_eq_true_iff D _ w).1 h w' hw' hp

/-- In a mixed domain a negated strong necessity is true and the existential continuation
holds with it. -/
theorem must_false_of_indet (w : W) (h : should D p w = .indet) :
    must D p w = .false ∧ ∃ w' ∈ D w, p w' := by
  obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (should_eq_indet_iff D p w).1 h
  have : ¬ ∀ w' ∈ D w, p w' := fun hall => hn (hall b hb)
  exact ⟨by simp [must, this, Trivalent.ofBool], a, ha, hp⟩

/-! ### Homogeneity removal -/

/-- *Must* is *should* with its gap removed: the universal quantifier is the meta-assertion of
the plural predication, as *all* is of *the*. -/
theorem must_eq_metaAssert_should : must D p = (should D p).metaAssert := by
  funext w
  simp only [must, should, Prop3.metaAssert]
  by_cases h : ∀ w' ∈ D w, p w'
  · rw [decide_eq_true h, (dist_eq_true_iff _ _).2 h]; rfl
  · rw [decide_eq_false h]
    rcases hd : dist (D w) p with _ | _ | _
    · exact absurd ((dist_eq_true_iff _ _).1 hd) h
    all_goals rfl

theorem isBivalent_must : (must D p).isBivalent :=
  must_eq_metaAssert_should D p ▸ Prop3.isBivalent_metaAssert _

/-- In a mixed domain the negated bare *should* is not true, while the negated *necessarily
should* is true and compatible with the existential continuation. -/
theorem necessarily_removes_gap (w : W) (h : should D p w = .indet) :
    should D (fun w' => ¬ p w') w ≠ .true ∧ ((should D p).metaAssert w).neg = .true ∧
      ∃ w' ∈ D w, p w' := by
  obtain ⟨⟨a, ha, hp⟩, -⟩ := (should_eq_indet_iff D p w).1 h
  refine ⟨fun h' => not_exists_of_should_not D p w h' ⟨a, ha, hp⟩, ?_, a, ha, hp⟩
  simp only [Prop3.metaAssert]
  rw [h]; rfl

/-! ### Borderline cases and exception tolerance -/

/-- The two doors to the living room. -/
inductive Door
  | left
  | right
  deriving DecidableEq, Fintype

/-- Both doors are equally good, so both worlds are best. -/
def doors : Door → Finset Door := fun _ => {.left, .right}

/-- The issue that separates every world from every other. -/
def strict : QUD Door :=
  ⟨⟨(· = ·), ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩, fun a b => inferInstanceAs (Decidable (a = b))⟩

/-- Taking the right door *should* be taken is neither true nor false — neither assertible nor
deniable — while that it *must* be taken is false. -/
theorem two_doors : ∀ w, should doors (· = .right) w = .indet ∧
    ¬ usable strict (should doors (· = .right)) w ∧ must doors (· = .right) w = .false := by
  decide

/-- Worlds of the perfect-grade scenario: the rules require every exercise or only most, and
the addressee does every exercise or only most. -/
inductive Grade
  | strictAll
  | strictMost
  | lenientAll
  | lenientMost
  deriving DecidableEq, Fintype

/-- The perfect-grade worlds under a world's rules. -/
def grade : Grade → Finset Grade
  | .strictAll | .strictMost => {.strictAll}
  | .lenientAll | .lenientMost => {.lenientAll, .lenientMost}

/-- Doing every exercise. -/
def everyExercise (w : Grade) : Prop := w = .strictAll ∨ w = .lenientAll

instance : DecidablePred everyExercise := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- *What is a way to get a perfect grade?* — every world answers alike. -/
def wayQUD : QUD Grade :=
  ⟨⟨fun _ _ => True, ⟨fun _ => trivial, id, fun _ _ => trivial⟩⟩,
    fun _ _ => inferInstanceAs (Decidable True)⟩

/-- *What are the minimal requirements?* — worlds are grouped by their rules. -/
def minimalQUD : QUD Grade :=
  ⟨⟨fun a b => grade a = grade b, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩,
    fun a b => inferInstanceAs (Decidable (grade a = grade b))⟩

/-- Where most exercises suffice, *you should do every exercise* is usable under the first
question but not the second, and *you have to do every exercise* under neither. -/
theorem exception_tolerance :
    usable wayQUD (should grade everyExercise) .lenientAll ∧
      ¬ usable minimalQUD (should grade everyExercise) .lenientAll ∧
      ¬ usable wayQUD (must grade everyExercise) .lenientAll ∧
      ¬ usable minimalQUD (must grade everyExercise) .lenientAll := by
  decide

/-! ### Domain restriction -/

/-- If weak necessity quantifies over a proper subset of the domain of *allowed*, the negated
modal and the existential continuation are jointly satisfiable. -/
theorem domainRestriction_no_contradiction {D' D : Finset W} (h : D' ⊂ D) :
    ∃ q : W → Prop, (∀ w ∈ D', ¬ q w) ∧ ∃ w ∈ D, q w :=
  let ⟨w, hw, hw'⟩ := Finset.exists_of_ssubset h
  ⟨(· ∉ D'), fun _ hw h' => h' hw, w, hw, hw'⟩

/-! ### Deriving weak from strong necessity -/

variable [DecidableEq W] (w : W)

/-- Strong necessity, as a quantifier over sets of worlds, has the domain as its unique minimal
witness set, so picking that set out yields the plurality weak necessity denotes. -/
theorem x_must :
    (∃! X, IsMinimalWitness (D w ⊆ ·) X) ∧ ∀ X, IsMinimalWitness (D w ⊆ ·) X ↔ X = D w :=
  ⟨existsUnique_isMinimalWitness_subset _, fun _ => isMinimalWitness_subset_iff _ _⟩

/-- Possibility over two or more best worlds has minimal witness sets but no unique one: a
marker that needs only some witness applies to it, one that needs the unique witness does
not. -/
theorem possibility_witnesses (h : 1 < (D w).card) :
    (∃ X, IsMinimalWitness (fun X => (D w ∩ X).Nonempty) X) ∧
      ¬ ∃! X, IsMinimalWitness (fun X => (D w ∩ X).Nonempty) X :=
  ⟨exists_isMinimalWitness_inter_nonempty (Finset.card_pos.1 (by omega)),
    not_existsUnique_isMinimalWitness_inter_nonempty h⟩

/-! ### The data -/

/-- The paper's rows in the cross-paper homogeneity pool. -/
def gapData : List GapDatum := Examples.all.filterMap fromExample

/-- The polarity-by-scenario grid for *should*. -/
def shouldGrid : List GapDatum :=
  (Examples.all.filter (·.feature? "modal" == some "should")).filterMap fromExample

/-- A representative domain for each scenario; a world is the prejacent's truth value at it. -/
def scenarioDomain : GapScenario → Finset Bool
  | .all => {true}
  | .none => {false}
  | .gap => {true, false}

/-- The plural semantics' value at a cell: negative polarity predicates the negated prejacent. -/
def shouldPredict (pol : Polarity) (s : GapScenario) : Trivalent :=
  match pol with
  | .positive => should (fun _ => scenarioDomain s) (· = true) true
  | .negative => should (fun _ => scenarioDomain s) (· = false) true

/-- Domain restriction's value at a cell: universal quantification, negated by Strong Kleene
negation. -/
def domainRestrictionPredict (pol : Polarity) (s : GapScenario) : Trivalent :=
  match pol with
  | .positive => must (fun _ => scenarioDomain s) (· = true) true
  | .negative => (must (fun _ => scenarioDomain s) (· = true) true).neg

theorem gapData_subset_allData : ∀ d ∈ gapData, d ∈ Generalizations.HomogeneityGap.allData := by
  decide

/-- The plural semantics reproduces every cell of the *should* grid. -/
theorem should_matches_grid :
    ∀ d ∈ shouldGrid, shouldPredict d.polarity d.scenario = d.observed := by
  decide

/-- Domain restriction matches the classical cells and fails exactly the gap cells. -/
theorem domainRestriction_fails_exactly_gap :
    ∀ d ∈ shouldGrid,
      (domainRestrictionPredict d.polarity d.scenario = d.observed ↔ d.scenario ≠ .gap) := by
  decide

/-- A negated weak necessity modal, however the negation is placed, rejects the existential
continuation. -/
theorem weak_negated_contradicts :
    ∀ e ∈ Examples.all, e.feature? "force" = some "weak" → (e.feature? "negation").isSome →
      e.feature? "remover" = none → e.feature? "continuation_felicity" = some "infelicitous" := by
  decide

/-- A strong necessity modal under extra-clausal negation accepts it. -/
theorem strong_extraclausal_compatible :
    ∀ e ∈ Examples.all, e.feature? "force" = some "strong" →
      e.feature? "negation" = some "extra-clausal" →
        e.feature? "continuation_felicity" = some "felicitous" := by
  decide

/-- *Necessarily* licenses the continuation wherever it is inserted. -/
theorem necessarily_licenses_continuation :
    ∀ e ∈ Examples.all, e.feature? "remover" = some "necessarily" →
      e.feature? "continuation_felicity" = some "felicitous" := by
  decide

/-- NE on a possibility base is ungrammatical; counterfactual marking is grammatical on either
base. -/
theorem ne_only_necessity :
    ∀ e ∈ Examples.all,
      (e.feature? "derivation" = some "NE" → e.feature? "base" = some "possibility" →
        e.judgment = .ungrammatical) ∧
      (e.feature? "derivation" = some "CF" → e.judgment = .acceptable) := by
  decide

end AghaJeretic2022
