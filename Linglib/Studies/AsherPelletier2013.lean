import Linglib.Studies.Cohen1999
import Linglib.Data.Examples.AsherPelletier2013
import Mathlib.Probability.ConditionalProbability

/-!
# Asher & Pelletier 2013: generics as modal quantifiers

A characterizing generic *φs ψ* is ∀x(φ(x) > ψ(x)), with > the weak conditional of commonsense
entailment: for each individual, ψ holds throughout the worlds where that individual is a
normal φ. Normality is selected per restrictor, so *Birds fly* and *Penguins don't fly* hold
together — the normal Opus-penguin worlds are not normal Opus-bird worlds — and it has give:
the teleological and the statistical construal disagree on whether turtles live to be a
hundred. Against the probabilistic rival, on which a generic is true when the scope is more
likely than not given the restrictor, the paper objects that a margin just over half verifies
generics that are not true, and that embedded generics trivialize the account: under
conditionalization the probability of the conditional collapses to that of the scope. Logical
forms are then built by putting the focused material in the nuclear scope and its
alternatives in the restrictor, which weakens the restrictor where needed (ducks lay eggs),
lets a tautologous restrictor deliver an existential (firemen are available), and, with a
further generic over circumstances, gives mosquitoes their disposition to carry the virus.

Item numbers follow the 2012 preprint.

## Main definitions

* `NormalWorlds`, `NormalWorlds.cond`, `NormalWorlds.generic`: the selection of normal worlds,
  the weak conditional, and the generic quantifier.
* `generic_disjoint`, `generic_inter`, `not_cond_union`: contrary generics select disjoint
  worlds; the scope weakens; the restrictor does not strengthen.
* `existentialReading`, `NormalWorlds.cond_univ`, `doubleGeneric`: the alternatives-based, the
  tautologous, and the circumstantial restrictor.
* `Conditionalizes`, `cond_eq_of_conditionalizes`: the trivialization of probabilistic
  generics.

## References

* [asher-pelletier-2013]
* [asher-morreau-1991], [asher-morreau-1995], [pelletier-asher-1997] — the modal account
* [cohen-1999a] — the probabilistic rival
* [leslie-2008] — the counterexamples
* [lewis-1976], [milne-2003] — the triviality argument
-/

namespace AsherPelletier2013

open Data.Examples MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {W E : Type*}

/-! ### The modal quantifier -/

/-- The normal worlds for a proposition, always among the worlds where it holds. -/
structure NormalWorlds (W : Type*) where
  star : W → Set W → Set W
  star_subset : ∀ w p, star w p ⊆ p

namespace NormalWorlds

variable (n : NormalWorlds W)

/-- `p > q`: `q` holds throughout the normal `p`-worlds. -/
def cond (p q : Set W) (w : W) : Prop := n.star w p ⊆ q

/-- ∀x(φ(x) > ψ(x)): for each individual, ψ throughout the worlds where it is a normal φ. -/
def generic (φ ψ : E → Set W) (w : W) : Prop := ∀ a, n.cond (φ a) (ψ a) w

/-- Contrary generics select disjoint normal worlds for each individual: if birds fly and
    penguins don't, the normal Opus-penguin worlds are not normal Opus-bird worlds. -/
theorem generic_disjoint {φ φ' ψ : E → Set W} {w : W} (h : n.generic φ ψ w)
    (h' : n.generic φ' (λ a => (ψ a)ᶜ) w) (a : E) :
    Disjoint (n.star w (φ a)) (n.star w (φ' a)) :=
  Set.disjoint_left.2 λ _ hv hv' => h' a hv' (h a hv)

/-- A generic with a conjoined scope entails the generic with either conjunct. -/
theorem generic_inter {φ ψ χ : E → Set W} {w : W} (h : n.generic φ (λ a => ψ a ∩ χ a) w) :
    n.generic φ ψ w :=
  λ a _ hv => (h a hv).1

/-- With logical truths selecting the world of evaluation itself, a tautologous restrictor
    makes the conditional its consequent at that world. -/
theorem cond_univ {w : W} (h : n.star w Set.univ = {w}) (q : Set W) :
    n.cond Set.univ q w ↔ w ∈ q := by
  simp [cond, h]

end NormalWorlds

/-- Strengthening the restrictor is not valid: the normal worlds of a weaker restrictor may
    all lie in the scope while those of a stronger one do not. -/
theorem not_cond_union :
    ∃ (n : NormalWorlds Bool) (p d q : Set Bool) (w : Bool), n.cond p q w ∧ ¬ n.cond (p ∪ d) q w :=
  ⟨⟨λ _ p => p, λ _ _ => subset_rfl⟩, {true}, {false}, {true}, true, subset_rfl,
    λ h => by simpa using h (Set.mem_union_right _ rfl)⟩

/-- The teleological construal of a turtle's normality: the worlds where it reaches a hundred. -/
def teleological : NormalWorlds Bool := ⟨λ _ p => p ∩ {true}, λ _ _ => Set.inter_subset_left⟩

/-- The statistical construal: the worlds where it dies young. -/
def statistical : NormalWorlds Bool := ⟨λ _ p => p ∩ {false}, λ _ _ => Set.inter_subset_left⟩

/-- *Turtles live to be 100* is true under the teleological construal and false under the
    statistical one. -/
theorem turtles (w : Bool) :
    teleological.cond Set.univ {true} w ∧ ¬ statistical.cond Set.univ {true} w :=
  ⟨Set.inter_subset_right, λ h => by simpa using h ⟨Set.mem_univ _, rfl⟩⟩

/-! ### Restrictors -/

/-- The existential reading of *Typhoons arise in this part of the Pacific*: for every
    alternative property `P` of the place, normally `P` is the property that typhoons arise
    there. -/
def existentialReading (n : NormalWorlds W) (Alt : Set (E → Set W)) (T : E → Set W) (c : E)
    (w : W) : Prop :=
  ∀ P ∈ Alt, n.cond (P c) {_v | P = T} w

/-- An alternative that applies makes the reading defeasibly entail that typhoons arise
    there: throughout that alternative's normal worlds. -/
theorem existentialReading.star_subset {n : NormalWorlds W} {Alt : Set (E → Set W)}
    {T : E → Set W} {c : E} {w : W} (h : existentialReading n Alt T c w) {P : E → Set W}
    (hP : P ∈ Alt) : n.star w (P c) ⊆ T c := by
  intro v hv
  have hPT : P = T := h P hP hv
  subst hPT
  exact n.star_subset w (P c) hv

/-- Double genericity: for each individual, in its normal worlds every appropriate
    circumstance normally has it carry the virus — a disposition rather than a frequency. -/
def doubleGeneric {Ev : Type*} (n : NormalWorlds W) (φ : E → Set W) (C : Ev → Set W)
    (ψ : E → Ev → Set W) (w : W) : Prop :=
  n.generic φ (λ a => {v | ∀ e, n.cond (C e) (ψ a e) v}) w

/-- Without a circumstance restriction, and with logical truths selecting the world of
    evaluation, double genericity is ordinary genericity over every circumstance. -/
theorem doubleGeneric_univ {Ev : Type*} {n : NormalWorlds W} (h : ∀ v, n.star v Set.univ = {v})
    (φ : E → Set W) (ψ : E → Ev → Set W) (w : W) :
    doubleGeneric n φ (λ _ => Set.univ) ψ w ↔ n.generic φ (λ a => {v | ∀ e, v ∈ ψ a e}) w := by
  simp [doubleGeneric, NormalWorlds.generic, NormalWorlds.cond, h]

/-! ### Against the probabilistic account -/

/-- Tails in 11 of 20 equally normal cat cases: just over half. -/
def tailed : Fin 20 → Prop := λ w => w.val < 11

instance : DecidablePred tailed := λ w => Nat.decLt w.val 11

/-- Every case equally normal: the normal `p`-worlds are the `p`-worlds. -/
def flat (W : Type*) : NormalWorlds W := ⟨λ _ p => p, λ _ _ => subset_rfl⟩

/-- The majority account verifies *Cats have tails* on a margin just over half; the modal
    account does not, since a normal case lacks a tail. -/
theorem cohen_too_weak :
    Cohen1999.gen (Finset.univ : Finset (Fin 20)) (λ _ => True) (λ _ => True) tailed ∧
      ¬ (flat (Fin 20)).cond Set.univ {w | tailed w} 0 := by
  refine ⟨(Cohen1999.gen_iff_thresholdGt _ _ _ _ (by decide)).mpr (by decide), λ h => ?_⟩
  exact absurd (h (Set.mem_univ (11 : Fin 20))) (by decide)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A proposition `c` for the conditional `a > b` conditionalizes when its probability given
    any `d` is that of `b` given `a` and `d`. -/
def Conditionalizes (a b c : Set Ω) : Prop := ∀ d, MeasurableSet d → μ[c | d] = μ[b | a ∩ d]

/-- Under conditionalization the probability of the scope given the restrictor is the
    probability of the scope, whenever the restrictor is compatible with the scope. -/
theorem cond_eq_of_conditionalizes {a b c : Set Ω} (ha : MeasurableSet a)
    (hb : MeasurableSet b) (h : Conditionalizes μ a b c) (h₁ : μ (a ∩ b) ≠ 0) :
    μ[b | a] = μ b := by
  have hc : μ c = μ[b | a] := by simpa using h Set.univ MeasurableSet.univ
  have hb1 : μ[c | b] = 1 := by
    rw [h b hb, cond_apply (ha.inter hb), Set.inter_assoc, Set.inter_self]
    exact ENNReal.inv_mul_cancel h₁ (measure_ne_top μ _)
  have hb0 : μ[c | bᶜ] = 0 := by
    rw [h bᶜ hb.compl, cond_apply (ha.inter hb.compl), Set.inter_assoc, Set.compl_inter_self,
      Set.inter_empty, measure_empty, mul_zero]
  have htot := cond_add_cond_compl_eq hb μ (t := c)
  rw [hb1, hb0, one_mul, zero_mul, add_zero] at htot
  rw [← hc]
  exact htot.symm

/-- The probabilistic generic, under conditionalization, says only that the scope is more
    likely than not. -/
theorem cohen_iff_scope {a b c : Set Ω} (ha : MeasurableSet a) (hb : MeasurableSet b)
    (h : Conditionalizes μ a b c) (h₁ : μ (a ∩ b) ≠ 0) :
    1 / 2 < μ[b | a] ↔ 1 / 2 < μ b := by
  rw [cond_eq_of_conditionalizes μ ha hb h h₁]

end AsherPelletier2013
