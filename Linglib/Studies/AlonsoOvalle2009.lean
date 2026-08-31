import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Conditionals.Counterfactual.Alternatives
import Linglib.Studies.McKayVanInwagen1977
import Linglib.Data.Examples.AlonsoOvalle2009

/-!
# Alonso-Ovalle (2009): counterfactuals, correlatives, and disjunction

A *would*-counterfactual with a disjunctive antecedent is read as checking the consequent in
the closest worlds of each disjunct, which a minimal-change semantics with Boolean *or*
cannot do: on the bumper-crop scenario (1) it hands the modal the union and predicts the
counterfactual true (`bumperCrop_boolean`). The paper keeps minimal change and instead lets
*or* introduce its disjuncts as Hamblin alternatives (10) and treats conditionals as
correlatives: the *if*-clause universally quantifies over the alternatives (25) and the
consequent, abstracted over the propositional anaphor *then*, supplies the modal (24). The
composition is `Distributive` for *would* and `DistributiveMight` for *might*; it validates
Simplification (27), makes (1) false (`bumperCrop_alternatives`), and leaves the negated (29)
true when one simplification holds, where a sum with the homogeneity presupposition (33)
gives a gap (`hitler_negation`, `homogeneity_ne_false`).

Rival derivations fail. A strict conditional makes Simplification a monotonicity inference
(`strict_simplification`) but not for the dual *might* (`strictMight_not_simplifying`), and
Stalnaker's ◇(*would*) recovers it (`stalnaker_might_simplification`) only for epistemic
modals. On von Fintel's modal horizon (44)–(45), Simplification is Strawson-valid like
Strengthening the Antecedent (`horizonWould_anti`) but not dynamically valid
(`horizon_sunCold_undefined`). The manner implicature (75)–(76) does not deliver both
simplifications (`manner_insufficient`). Nute's (80) is a contradiction unless a disjunct is
impossible (`distributive_pair_disjoint_iff`) and needs Existential Closure (82) (`budget`).
The paper's verdicts are checked in `rows_agree`.

## References

* [alonso-ovalle-2009]
* [lewis-1973]
* [mckay-vaninwagen-1977]
* [nute-1975]
* [hamblin-1973b]
* [dayal-1996]
* [von-fintel-2000]
* [von-fintel-1999]
* [stalnaker-1984]
* [bennett-2003]
* [lewis-1977]
-/

namespace AlonsoOvalle2009

open Conditionals Conditionals.Counterfactual McKayVanInwagen1977
  Data.Examples

variable {W : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W)
  (S : List (Finset W)) (C : W → Prop) [DecidablePred C] (w : W)

/-! ### Conditionals as correlatives (§2) -/

/-- *Might* in the consequent (70)–(71) under the universal *if*-clause (25): the closest
worlds of every alternative are compatible with the consequent. -/
def DistributiveMight : Prop := ∀ A ∈ S, lewisMight sim (· ∈ A) C w

instance : Decidable (DistributiveMight sim S C w) :=
  inferInstanceAs (Decidable (∀ A ∈ S, lewisMight sim (· ∈ A) C w))

/-- Simplification (27): the disjunctive counterfactual entails each disjunct's. -/
theorem simplification {A B : Finset W} (h : Distributive sim [A, B] C w) :
    universalCounterfactual sim (· ∈ A) C w ∧ universalCounterfactual sim (· ∈ B) C w :=
  ⟨h A (by simp), h B (by simp)⟩

/-- Simplification for *might* (54), the extension of §3.3. -/
theorem simplification_might {A B : Finset W} (h : DistributiveMight sim [A, B] C w) :
    lewisMight sim (· ∈ A) C w ∧ lewisMight sim (· ∈ B) C w :=
  ⟨h A (by simp), h B (by simp)⟩

/-- The good-weather and cold-sun worlds of the bumper-crop model. -/
abbrev goodWeatherW : Finset CropWorld := Finset.univ.filter goodWeather
abbrev sunColdW : Finset CropWorld := Finset.univ.filter sunCold

/-- Boolean *or* (6) hands the modal the union, and (1) comes out true (Fig. 1). -/
theorem bumperCrop_boolean : would cropSim [goodWeatherW, sunColdW] bumperCrop .actual := by
  decide

/-- With the disjuncts as alternatives (13) under universal force (26), (1) is false: the
closest cold-sun worlds have no crop. -/
theorem bumperCrop_alternatives :
    ¬ Distributive cropSim [goodWeatherW, sunColdW] bumperCrop .actual := by decide

/-! ### Universal quantifier or sum (§2.2.3) -/

/-- A sum analysis falsifies a disjunctive counterfactual only when every disjunct's
counterfactual fails. -/
theorem homogeneity_ne_false {A : Finset W} (hA : A ∈ S)
    (h : universalCounterfactual sim (· ∈ A) C w) : homogeneity sim S C w ≠ .false :=
  fun hf => ((homogeneity_eq_false_iff sim S C w).1 hf).2 A hA h

/-- (29)–(31): Spain joining Germany is closer than Spain joining the U.S., and Hitler is
pleased only in the former. -/
inductive HitlerWorld | actual | germany | us
  deriving DecidableEq, Fintype

def HitlerWorld.rank : HitlerWorld → ℕ
  | .actual => 0 | .germany => 1 | .us => 2

def hitlerSim : SimilarityOrdering HitlerWorld := .ofRank fun _ => HitlerWorld.rank

abbrev joinedGermany : Finset HitlerWorld := {.germany}
abbrev joinedUS : Finset HitlerWorld := {.us}

def pleased (w : HitlerWorld) : Prop := w = .germany

instance : DecidablePred pleased := fun w => inferInstanceAs (Decidable (w = .germany))

/-- Under the universal quantifier (29) is true, with (30a) true and (30b) false as (31)
continues; under a sum with homogeneity (33) it is a gap. -/
theorem hitler_negation :
    ¬ Distributive hitlerSim [joinedGermany, joinedUS] pleased .actual ∧
      universalCounterfactual hitlerSim (· ∈ joinedGermany) pleased .actual ∧
      ¬ universalCounterfactual hitlerSim (· ∈ joinedUS) pleased .actual ∧
      homogeneity hitlerSim [joinedGermany, joinedUS] pleased .actual = .indet := by decide

/-! ### Downward entailingness (§3) -/

section Strict

variable {I : Type*} (access : I → Set W) (φ ψ χ : Set W)

omit [DecidableEq W] [Fintype W] in
/-- (37)–(38): a strict conditional is antitone in its antecedent, so Simplification is a
monotonicity inference. -/
theorem strict_simplification {i : I} (h : i ∈ strictImp access (φ ∪ ψ) χ) :
    i ∈ strictImp access φ χ ∧ i ∈ strictImp access ψ χ :=
  ⟨strictImp_anti_left Set.subset_union_left h, strictImp_anti_left Set.subset_union_right h⟩

omit [DecidableEq W] [Fintype W] in
/-- (60)–(64): Stalnaker's *might* counterfactual, epistemic possibility over `E` of the
strict *would*, inherits Simplification. -/
theorem stalnaker_might_simplification (E : I → Set I) {i : I}
    (h : ∃ i' ∈ E i, i' ∈ strictImp access (φ ∪ ψ) χ) :
    (∃ i' ∈ E i, i' ∈ strictImp access φ χ) ∧ ∃ i' ∈ E i, i' ∈ strictImp access ψ χ :=
  let ⟨i', hi, hs⟩ := h
  ⟨⟨i', hi, (strict_simplification access φ ψ χ hs).1⟩,
    ⟨i', hi, (strict_simplification access φ ψ χ hs).2⟩⟩

end Strict

/-- Accommodation (44): the modal horizon `f` grows by every world at least as close as the
closest antecedent worlds. -/
def expand (f : W → Finset W) (φ : Finset W) (w : W) : Finset W :=
  f w ∪ Finset.univ.filter fun w' => ∀ w'' ∈ φ, sim.closer w w' w''

/-- The counterfactual on a horizon (45): every antecedent world in the horizon is a
consequent world. -/
def horizonWould (f : W → Finset W) (φ ψ : Finset W) (w : W) : Prop :=
  ∀ w' ∈ f w ∩ φ, w' ∈ ψ

/-- The presupposition of (45): the horizon reaches the antecedent. -/
def HorizonReaches (f : W → Finset W) (φ : Finset W) (w : W) : Prop := (f w ∩ φ).Nonempty

instance (f : W → Finset W) (φ : Finset W) : Decidable (HorizonReaches f φ w) :=
  inferInstanceAs (Decidable (f w ∩ φ).Nonempty)

omit [Fintype W] in
/-- Strawson validity (50) of Strengthening the Antecedent and of Simplification alike: on a
horizon that already reaches the stronger antecedent, (45) is antitone in it. -/
theorem horizonWould_anti {f : W → Finset W} {φ φ' ψ : Finset W} (h : φ' ⊆ φ)
    (hw : horizonWould f φ ψ w) : horizonWould f φ' ψ w :=
  fun w' hw' =>
    hw w' (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hw').1, h (Finset.mem_inter.1 hw').2⟩)

/-- Dynamic invalidity (47): accommodating (48)'s antecedent from the initial horizon reaches
the good-weather world only, so (49b) is undefined. -/
theorem horizon_sunCold_undefined :
    ¬ HorizonReaches (expand cropSim (fun w => {w}) (goodWeatherW ∪ sunColdW)) sunColdW
      .actual := by decide

/-! ### Might counterfactuals (§3.2) -/

/-- (51): having a magic book is closer than being a newborn baby; the fork is bent in one
of the closest magic-book worlds and in no newborn world (Fig. 2). -/
inductive ForkWorld | actual | book | bookBent | baby
  deriving DecidableEq, Fintype

def ForkWorld.rank : ForkWorld → ℕ
  | .actual => 0 | .book | .bookBent => 1 | .baby => 2

def forkSim : SimilarityOrdering ForkWorld := .ofRank fun _ => ForkWorld.rank

abbrev hasBook : Finset ForkWorld := {.book, .bookBent}
abbrev newborn : Finset ForkWorld := {.baby}

def bent (w : ForkWorld) : Prop := w = .bookBent

instance : DecidablePred bent := fun w => inferInstanceAs (Decidable (w = .bookBent))

/-- Under (52)–(53) the closest worlds of the union are magic-book worlds, one of which bends
the fork, so (51) is true; under the correlative analysis it is false, since (58a) is true
but (58b) is not. -/
theorem fork :
    lewisMight forkSim (· ∈ disjunctiveClosure [hasBook, newborn]) bent .actual ∧
      ¬ DistributiveMight forkSim [hasBook, newborn] bent .actual ∧
      lewisMight forkSim (· ∈ hasBook) bent .actual ∧
      ¬ lewisMight forkSim (· ∈ newborn) bent .actual := by decide

/-- (57)–(58): the strict dual *might*, with every world accessible, is true of the
disjunction but not of the newborn disjunct. -/
theorem strictMight_not_simplifying :
    (∃ w, w ∈ hasBook ∪ newborn ∧ bent w) ∧ ¬ ∃ w, w ∈ newborn ∧ bent w := by decide

/-! ### An implicature? (§4) -/

/-- Figs. 3–4: two worlds compatible with the speaker's beliefs; magic-book and newborn
worlds are equally close to each, and the fork is bent in a closest magic-book world of the
first and in a closest newborn world of the second. -/
inductive BeliefWorld | w₃ | book₃ | baby₃ | w₄ | book₄ | baby₄
  deriving DecidableEq, Fintype

def BeliefWorld.rank : BeliefWorld → BeliefWorld → ℕ
  | .w₃, .w₃ | .w₄, .w₄ => 0
  | .w₃, .book₃ | .w₃, .baby₃ | .w₄, .book₄ | .w₄, .baby₄ => 1
  | _, _ => 2

def beliefSim : SimilarityOrdering BeliefWorld := .ofRank BeliefWorld.rank

abbrev belief : Finset BeliefWorld := {.w₃, .w₄}
abbrev bookB : Finset BeliefWorld := {.book₃, .book₄}
abbrev babyB : Finset BeliefWorld := {.baby₃, .baby₄}

def bentB (w : BeliefWorld) : Prop := w = .book₃ ∨ w = .baby₄

instance : DecidablePred bentB := fun w => inferInstanceAs (Decidable (w = .book₃ ∨ w = .baby₄))

/-- Manner (75)–(76) is satisfied — (73) holds throughout the belief state and neither (74a)
nor (74b) does — yet the two simplifications hold together nowhere in it, so (77) is not
predicted deviant. -/
theorem manner_insufficient :
    (∀ w ∈ belief, lewisMight beliefSim (· ∈ disjunctiveClosure [bookB, babyB]) bentB w) ∧
      (∃ w ∈ belief, ¬ lewisMight beliefSim (· ∈ bookB) bentB w) ∧
      (∃ w ∈ belief, ¬ lewisMight beliefSim (· ∈ babyB) bentB w) ∧
      ∀ w ∈ belief, ¬ DistributiveMight beliefSim [bookB, babyB] bentB w := by decide

/-! ### The visibility of the disjuncts (§5.2) -/

/-- Nute's recipe (80): when the consequent is one of two incompatible disjuncts, the
analysis makes the counterfactual true only if the other disjunct is impossible. -/
theorem distributive_pair_disjoint_iff {A B : Finset W} (h : Disjoint A B) :
    Distributive sim [A, B] (· ∈ A) w ↔ B = ∅ := by
  refine ⟨fun hd => ?_, fun hB => ?_⟩
  · by_contra hne
    obtain ⟨b, hb⟩ := sim.closestWorlds_nonempty w (Finset.nonempty_iff_ne_empty.2 hne)
    have hbA : b ∈ A := hd B (by simp) b (by simpa [universalCounterfactual] using hb)
    exact Finset.disjoint_left.1 h hbA (sim.closestWorlds_subset w B hb)
  · subst hB
    intro X hX w' hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · simpa using sim.closestWorlds_subset w _ hw'
    · simp at hw'

/-- (80): more defense spending is closer than more education spending. -/
inductive BudgetWorld | actual | defense | education
  deriving DecidableEq, Fintype

def BudgetWorld.rank : BudgetWorld → ℕ
  | .actual => 0 | .defense => 1 | .education => 2

def budgetSim : SimilarityOrdering BudgetWorld := .ofRank fun _ => BudgetWorld.rank

abbrev defense : Finset BudgetWorld := {.defense}
abbrev education : Finset BudgetWorld := {.education}

/-- (80) is a contradiction under the analysis and true once Existential Closure (82)
returns the Boolean antecedent. -/
theorem budget :
    (∀ w, ¬ Distributive budgetSim [defense, education] (· ∈ defense) w) ∧
      would budgetSim [defense, education] (· ∈ defense) .actual :=
  ⟨fun w h => by simpa using (distributive_pair_disjoint_iff budgetSim w (by decide)).1 h,
    by decide⟩

/-! ### The paper's verdicts -/

/-- The alternatives a row's `antecedent` feature names in each model. -/
def cropAlts : String → Option (List (Finset CropWorld))
  | "good weather" => some [goodWeatherW]
  | "sun cold" => some [sunColdW]
  | "good weather or sun cold" => some [goodWeatherW, sunColdW]
  | _ => none

def hitlerAlts : String → Option (List (Finset HitlerWorld))
  | "joined Germany" => some [joinedGermany]
  | "joined the U.S." => some [joinedUS]
  | "joined Germany or the U.S." => some [joinedGermany, joinedUS]
  | _ => none

def forkAlts : String → Option (List (Finset ForkWorld))
  | "magic book" => some [hasBook]
  | "newborn baby" => some [newborn]
  | "magic book or newborn baby" => some [hasBook, newborn]
  | _ => none

/-- The verdict of the analysis for a *would* or *might* consequent, possibly negated. -/
def verdict : String → Bool → Option Bool
  | "would", neg => some (decide (Distributive sim S C w) != neg)
  | "might", neg => some (decide (DistributiveMight sim S C w) != neg)
  | _, _ => none

/-- A row's predicted verdict from its `scenario`, `antecedent`, `modal`, and `polarity`
features; (80) takes the Existential Closure reading (82). -/
def predicted (row : LinguisticExample) : Option Bool :=
  let neg := decide (row.feature? "polarity" = some "negated")
  match row.feature? "scenario", row.feature? "antecedent", row.feature? "modal" with
  | some "bumperCrop", some a, some m =>
    cropAlts a >>= fun S => verdict cropSim S bumperCrop .actual m neg
  | some "hitler", some a, some m =>
    hitlerAlts a >>= fun S => verdict hitlerSim S pleased .actual m neg
  | some "fork", some a, some m => forkAlts a >>= fun S => verdict forkSim S bent .actual m neg
  | some "budget", some "defense or education", some "would" =>
    some (decide (would budgetSim [defense, education] (· ∈ defense) .actual))
  | _, _, _ => none

/-- Every row with a stated verdict that the models cover carries the predicted one. -/
theorem rows_agree :
    ∀ row ∈ Examples.all, ∀ v, row.feature? "verdict" = some v →
      ∀ b, predicted row = some b → v = if b then "true" else "false" := by
  decide +kernel

example :
    (Examples.all.filter fun row =>
      (row.feature? "verdict").isSome ∧ (predicted row).isSome).length = 10 := by
  decide +kernel

end AlonsoOvalle2009
