import Linglib.Semantics.Attitudes.Desire.QuestionBased
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Cariani 2013: ought and resolution semantics

This file formalizes the account of *ought* in [cariani-2013]. Reading *ought* as universal
quantification over the best worlds validates INHERITANCE — if `p` entails `q` then *ought p*
entails *ought q* — and [cariani-2013] argues that this is wrong. *Joan ought to attend her
classes* does not commit one to *Joan ought to either attend her classes or burn down the
philosophy department* ([ross-1941]), and *Procrastinate ought to accept and write the review*
does not commit one to *Procrastinate ought to accept* ([jackson-pargetter-1986]). Both are cases
of coarseness: an ought-sentence can be true although some way of making its prejacent true is
impermissible, and it is false as soon as a relevant option compatible with the prejacent is
impermissible.

Resolution semantics replaces the modal base and ordering source ([kratzer-1981]) with three
parameters — a set of mutually exclusive options, an ordering on them, and a benchmark. *Ought p*
holds when the options settle `p`, when every best option is a way of `p`, and when every option
that is a way of `p` meets the benchmark. The third clause is what fails in both puzzles, and
what makes the account anti-inheritance by construction rather than by stipulation.

## Main definitions

* `ResolutionContext`, `ofRanking` — the three parameters, and the context of a ranked space
* `isWayOf`, `isVisible`, `isBest`, `isOptimal`, `isStronglyPermissible` — the clauses
* `ought`, `permitted` — the two deontic operators
* `Inheritance` — closure of *ought* under entailment of the prejacent

## Main results

* `not_ought_of_impermissible_way` — one impermissible way of `p` falsifies *ought p*
* `permitted_of_ought` — *ought* entails *permitted* wherever some option is best
* `ought_iff_of_all_meetBenchmark` — with every option at the benchmark only the boxing clauses
  do any work
* `not_inheritance_ross`, `not_inheritance_proc` — either puzzle refutes INHERITANCE

## References

* [cariani-2013]
* [ross-1941]
* [jackson-pargetter-1986]
* [kratzer-1981]
-/

namespace Cariani2013

open Desire.QuestionBased (IsConsidered)

variable {W : Type*}

/-! ### The three contextual parameters -/

/-- The parameters of a resolution context: mutually exclusive options, an ordering on them, and
a benchmark. The benchmark is a cutoff in the ordering's range rather than a number, since
[cariani-2013] is non-committal between ranking and quantitative scales. -/
structure ResolutionContext (W : Type*) where
  /-- The options: mutually exclusive courses of action, a partition of the action space. -/
  options : List (Finset W)
  /-- `betterThan o o'`: `o` is at least as good as `o'`. -/
  betterThan : Finset W → Finset W → Prop
  /-- Decidability of the ordering. -/
  betterThanDec : ∀ a b, Decidable (betterThan a b)
  /-- Whether an option is at or above the benchmark. -/
  meetsBenchmark : Finset W → Prop
  /-- Decidability of the benchmark. -/
  meetsBenchmarkDec : ∀ o, Decidable (meetsBenchmark o)

instance (rc : ResolutionContext W) (a b : Finset W) :
    Decidable (rc.betterThan a b) := rc.betterThanDec a b

instance (rc : ResolutionContext W) (o : Finset W) :
    Decidable (rc.meetsBenchmark o) := rc.meetsBenchmarkDec o

/-- The context of a ranked action space: an option is as good as another when its best world
ranks at least as high, and it meets the benchmark when that rank reaches `b`. -/
def ofRanking (options : List (Finset W)) (rank : W → ℕ) (b : ℕ) : ResolutionContext W where
  options := options
  betterThan o o' := o'.sup rank ≤ o.sup rank
  betterThanDec _ _ := inferInstanceAs (Decidable (_ ≤ _))
  meetsBenchmark o := b ≤ o.sup rank
  meetsBenchmarkDec _ := inferInstanceAs (Decidable (_ ≤ _))

/-! ### The clauses -/

/-- Cariani's propositions carry function-form decidability; the question-based substrate reads
membership. -/
instance {p : Set W} [DecidablePred p] : DecidablePred (· ∈ p) :=
  fun w => inferInstanceAs (Decidable (p w))

instance [DecidableEq W] (a : W) : DecidablePred ({a} : Set W) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance [DecidableEq W] (a b : W) : DecidablePred ({a, b} : Set W) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

variable (rc : ResolutionContext W)

/-- An option is a *way of* `p` when it entails `p`. -/
def isWayOf (o : Finset W) (p : Set W) : Prop := ∀ w ∈ o, p w

instance (o : Finset W) (p : Set W) [DecidablePred p] : Decidable (isWayOf o p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- `p` is *visible* when the options settle it: each is a way of `p` or a way of its
negation. -/
abbrev isVisible (p : Set W) : Prop := IsConsidered rc.options p

/-- An option is *best* when it is at least as good as every option. -/
def isBest (o : Finset W) : Prop := ∀ o' ∈ rc.options, rc.betterThan o o'

instance (o : Finset W) : Decidable (isBest rc o) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- `p` is *optimal* when every best option is a way of it. -/
def isOptimal (p : Set W) : Prop := ∀ o ∈ rc.options, isBest rc o → isWayOf o p

instance (p : Set W) [DecidablePred p] : Decidable (isOptimal rc p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- `p` is *strongly permissible* when every option that is a way of it meets the benchmark. -/
def isStronglyPermissible (p : Set W) : Prop :=
  ∀ o ∈ rc.options, isWayOf o p → rc.meetsBenchmark o

instance (p : Set W) [DecidablePred p] : Decidable (isStronglyPermissible rc p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### The two operators -/

/-- *Ought p*: the options settle `p`, every best option is a way of `p`, and every option that
is a way of `p` meets the benchmark. -/
def ought (p : Set W) : Prop :=
  isVisible rc p ∧ isOptimal rc p ∧ isStronglyPermissible rc p

instance (p : Set W) [DecidablePred p] : Decidable (ought rc p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- *Permitted p*: some option that is a way of `p` meets the benchmark. -/
def permitted (p : Set W) : Prop := ∃ o ∈ rc.options, isWayOf o p ∧ rc.meetsBenchmark o

instance (p : Set W) [DecidablePred p] : Decidable (permitted rc p) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Coarse falsemaking: a single option that is a way of `p` and falls below the benchmark makes
*ought p* false, however good the rest of the options are. -/
theorem not_ought_of_impermissible_way (p : Set W) (o : Finset W) (ho : o ∈ rc.options)
    (hway : isWayOf o p) (himp : ¬ rc.meetsBenchmark o) : ¬ ought rc p :=
  fun ⟨_, _, hsp⟩ => himp (hsp o ho hway)

/-- What one ought to do is permitted, as long as some option is best: that option is a way of
`p` by optimality, and meets the benchmark by strong permissibility. -/
theorem permitted_of_ought (p : Set W) (h : ∃ o ∈ rc.options, isBest rc o)
    (hought : ought rc p) : permitted rc p := by
  obtain ⟨o, ho, hbest⟩ := h
  obtain ⟨_, hopt, hsp⟩ := hought
  exact ⟨o, ho, hopt o ho hbest, hsp o ho (hopt o ho hbest)⟩

/-- When every option is at the benchmark the permissibility clause does no work and *ought* is
the boxing reading — quantification over the best options, restricted to visible prejacents. -/
theorem ought_iff_of_all_meetBenchmark (p : Set W)
    (h : ∀ o ∈ rc.options, rc.meetsBenchmark o) :
    ought rc p ↔ isVisible rc p ∧ isOptimal rc p :=
  ⟨fun ⟨hv, ho, _⟩ => ⟨hv, ho⟩, fun ⟨hv, ho⟩ => ⟨hv, ho, fun o hoo _ => h o hoo⟩⟩

/-- INHERITANCE: *ought* is closed under entailment of the prejacent. -/
def Inheritance : Prop := ∀ p q : Set W, (∀ w, p w → q w) → ought rc p → ought rc q

/-! ### Ross's paradox -/

/-- Joan's three courses of action. -/
inductive RossW | attend | stayHome | burn
  deriving DecidableEq, Fintype, Repr

/-- Attending is best, staying home is next, burning down the department is worst. -/
def rossRank : RossW → ℕ
  | .attend => 3
  | .stayHome => 2
  | .burn => 1

/-- Joan's context: the three actions as options, with the benchmark at staying home, so that
burning down the department is the one impermissible option. -/
def rossContext : ResolutionContext RossW :=
  ofRanking [{.attend}, {.stayHome}, {.burn}] rossRank 2

/-- *Joan ought to attend her classes* is true. -/
theorem ross_ought_attend : ought rossContext {RossW.attend} := by decide +kernel

/-- The disjunction is visible, so it is only the permissibility clause that rejects it: burning
down the department is a way of *attend or burn* below the benchmark. -/
theorem ross_disjunction_visible_not_permissible :
    isVisible rossContext {RossW.attend, .burn} ∧
      ¬ isStronglyPermissible rossContext {RossW.attend, .burn} := by decide +kernel

/-- *Joan ought to either attend her classes or burn down the philosophy department* is false. -/
theorem ross_not_ought_disjunction : ¬ ought rossContext {RossW.attend, .burn} := by
  decide +kernel

/-- *Joan ought to stay home* is false as well, on the optimality clause rather than the
permissibility one: staying home is at the benchmark but is not the best option. -/
theorem ross_not_ought_stayHome : ¬ ought rossContext {RossW.stayHome} := by decide +kernel

/-- Ross's paradox refutes INHERITANCE. -/
theorem not_inheritance_ross : ¬ Inheritance rossContext := fun h =>
  ross_not_ought_disjunction (h _ _ (fun _ hw => Or.inl hw) ross_ought_attend)

/-! ### Procrastinate -/

/-- Procrastinate's three courses of action ([jackson-pargetter-1986]): accepting the review and
writing it, declining it, and accepting without writing. -/
inductive ProcW | acceptWrite | doNotAccept | acceptNoWrite
  deriving DecidableEq, Fintype, Repr

/-- Accepting and writing is best; declining is better than accepting and not writing, which is
what Procrastinate would in fact do. -/
def procRank : ProcW → ℕ
  | .acceptWrite => 3
  | .doNotAccept => 2
  | .acceptNoWrite => 1

/-- Procrastinate's context, with the benchmark at declining. -/
def procContext : ResolutionContext ProcW :=
  ofRanking [{.acceptWrite}, {.doNotAccept}, {.acceptNoWrite}] procRank 2

/-- *Procrastinate ought to accept and write the review* is true. -/
theorem proc_ought_acceptWrite : ought procContext {ProcW.acceptWrite} := by decide +kernel

/-- *Procrastinate ought to accept* is false: accepting without writing is a way of accepting,
and it is below the benchmark. -/
theorem proc_not_ought_accept :
    ¬ ought procContext {ProcW.acceptWrite, .acceptNoWrite} := by decide +kernel

/-- Procrastinate refutes INHERITANCE too, on a prejacent that is weaker by way of an
impermissible option rather than by a disjunct. -/
theorem not_inheritance_proc : ¬ Inheritance procContext := fun h =>
  proc_not_ought_accept (h _ _ (fun _ hw => Or.inl hw) proc_ought_acceptWrite)

end Cariani2013
