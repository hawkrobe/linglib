import Linglib.Semantics.Questions.Partition.SubjectMatter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod

/-!
# Cariani (2013): 'Ought' and resolution semantics

This file formalizes [cariani-2013]'s resolution semantics for *ought*. Reading *ought* as a
universal quantifier over the best worlds validates INHERITANCE, closure of *ought* under
entailment of the prejacent, and the paper takes the classical counterexamples at face value:
*Joan ought to attend her classes* does not entail *Joan ought to either attend her classes or
burn down the philosophy department* ([ross-1941]), and *Procrastinate ought to accept and write
the review* does not entail *Procrastinate ought to accept* ([jackson-pargetter-1986]). The
account keeps COARSENESS, on which an ought-sentence can be true although some way of making its
prejacent true is impermissible, by relativizing *ought* to a resolution: a partition of the
modal base into the agent's options (`Setoid W`), an ordering of the options, and a benchmark
below which an option is impermissible (`ResolutionContext`). *Ought p* holds when the
resolution settles `p`, every best option entails `p`, and every option entailing `p` meets the
benchmark (`Ought`), so that one impermissible option compatible with the prejacent falsifies
the sentence, the paper's COARSE FALSEMAKING (`not_ought_of_not_meetsBenchmark`), while
impermissible ways of `p` that no option distinguishes leave it true.

Both puzzles refute INHERITANCE (`not_inheritance_ross`, `not_inheritance_proc`). Permission has
two candidate entries, some option at the benchmark entails `p` or some best option does
(`Permitted₁`, `Permitted₂`); *ought* entails both, both are closed under entailment, and since
that closure together with the duality of *ought* and permission would restore INHERITANCE
(`inheritance_of_dual`), *ought* is the dual of neither. A boxing semantics is the special case
of the finest resolution with a benchmark every option meets (`ought_bot_iff`).

## Implementation notes

* The ordering on options is a valuation of worlds in a preordered scale that the resolution
  settles, so that it ranks options, with the benchmark a threshold of the scale; this is
  neutral between the ranking and quantitative scales the paper allows, and the best options
  are the `MaximalFor` elements of the valuation. The paper's examples value an option at the
  rank of its best world (`ofRanking`).
* The resolution partitions the modal base itself, so the modal base is not a separate
  parameter and the ordering does not vary with it. The paper's third puzzle, conditional
  *oughts* under the restrictor analysis of conditionals, needs the modal base and is not
  formalized.
* Visibility is `Setoid.Settles`, the resolution settling the prejacent.

## References

* [cariani-2013]
* [ross-1941]
* [jackson-pargetter-1986]
* [kratzer-1981]
-/

namespace Cariani2013

variable {W V : Type*}

/-- A resolution context: the resolution, a partition of the modal base into the agent's
options; the ordering, a valuation of worlds that the resolution settles, so that it ranks
options; and the benchmark, the threshold of the scale below which an option is
impermissible. -/
structure ResolutionContext (W V : Type*) where
  /-- The resolution: worlds in one cell realize the same option. -/
  resolution : Setoid W
  /-- The ordering: the value of a world's option in the scale. -/
  value : W → V
  /-- The valuation is constant on options. -/
  value_settled : resolution ≤ Setoid.ker value
  /-- The benchmark: the least permissible value. -/
  benchmark : V

namespace ResolutionContext

/-- The context of a ranked action space: an option is valued at the rank of its best world. -/
def ofRanking [Fintype W] [SemilatticeSup V] [OrderBot V] (s : Setoid W) [DecidableRel s]
    (rank : W → V) (benchmark : V) : ResolutionContext W V where
  resolution := s
  value w := (Finset.univ.filter (s · w)).sup rank
  value_settled _ _ h := congrArg (Finset.sup · rank) <| Finset.filter_congr λ _ _ =>
    ⟨λ h' => s.trans' h' h, λ h' => s.trans' h' (s.symm' h)⟩
  benchmark := benchmark

variable [Preorder V] (rc : ResolutionContext W V) (p : Set W)

/-! ### The clauses -/

/-- `p` is *visible* when the resolution settles it: each option entails `p` or its negation. -/
abbrev IsVisible : Prop := rc.resolution.Settles p

/-- An option *meets the benchmark* when its value is at least the benchmark. -/
def MeetsBenchmark (w : W) : Prop := rc.benchmark ≤ rc.value w

/-- An option is *best* when no option is strictly better. -/
def IsBest (w : W) : Prop := MaximalFor (λ _ => True) rc.value w

/-- `p` is *optimal* when every best option entails it. -/
def IsOptimal : Prop := ∀ w, rc.IsBest w → rc.resolution.cell w ⊆ p

/-- `p` is *strongly permissible* when every option that entails it meets the benchmark. -/
def IsStronglyPermissible : Prop := ∀ w, rc.resolution.cell w ⊆ p → rc.MeetsBenchmark w

/-! ### The operators -/

/-- *Ought p*: `p` is visible, optimal, and strongly permissible. -/
def Ought : Prop := rc.IsVisible p ∧ rc.IsOptimal p ∧ rc.IsStronglyPermissible p

/-- *Permitted p*, first entry: some option that entails `p` meets the benchmark. -/
def Permitted₁ : Prop := ∃ w, rc.resolution.cell w ⊆ p ∧ rc.MeetsBenchmark w

/-- *Permitted p*, second entry: some best option entails `p`. -/
def Permitted₂ : Prop := ∃ w, rc.IsBest w ∧ rc.resolution.cell w ⊆ p

/-- INHERITANCE: *ought* is closed under entailment of the prejacent. -/
def Inheritance : Prop := ∀ p q : Set W, p ⊆ q → rc.Ought p → rc.Ought q

section Decidable

variable [Fintype W] [DecidableRel rc.resolution] [DecidableRel (α := V) (· ≤ ·)]
  [DecidablePred (· ∈ p)]

instance (w : W) : Decidable (rc.MeetsBenchmark w) := inferInstanceAs (Decidable (_ ≤ _))

instance (w : W) : Decidable (rc.IsBest w) :=
  inferInstanceAs (Decidable (True ∧ ∀ _, True → _ → _))

instance : Decidable (rc.IsOptimal p) := inferInstanceAs (Decidable (∀ _, _ → _))

instance : Decidable (rc.IsStronglyPermissible p) := inferInstanceAs (Decidable (∀ _, _ → _))

instance : Decidable (rc.Ought p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : Decidable (rc.Permitted₁ p) := inferInstanceAs (Decidable (∃ _, _ ∧ _))

instance : Decidable (rc.Permitted₂ p) := inferInstanceAs (Decidable (∃ _, _ ∧ _))

end Decidable

variable {rc p} {q : Set W} {w : W}

/-! ### Coarse falsemaking and permission -/

/-- COARSE FALSEMAKING: one option below the benchmark that entails `p` falsifies *ought p*,
however good the other options are. -/
theorem not_ought_of_not_meetsBenchmark (hp : rc.resolution.cell w ⊆ p)
    (h : ¬ rc.MeetsBenchmark w) : ¬ rc.Ought p :=
  λ ⟨_, _, hsp⟩ => h (hsp w hp)

/-- Some option is best as soon as there are options. -/
theorem exists_isBest [Finite W] [Nonempty W] : ∃ w, rc.IsBest w :=
  Set.Finite.exists_maximalFor rc.value Set.univ Set.finite_univ Set.univ_nonempty

/-- What one ought to do some best option does. -/
theorem Ought.permitted₂ [Finite W] [Nonempty W] (ho : rc.Ought p) : rc.Permitted₂ p :=
  let ⟨w, hbest⟩ := exists_isBest (rc := rc)
  ⟨w, hbest, ho.2.1 w hbest⟩

/-- What one ought to do is permitted: a best option does it by optimality and meets the
benchmark by strong permissibility. -/
theorem Ought.permitted₁ [Finite W] [Nonempty W] (ho : rc.Ought p) : rc.Permitted₁ p :=
  let ⟨w, hbest⟩ := exists_isBest (rc := rc)
  ⟨w, ho.2.1 w hbest, ho.2.2 w (ho.2.1 w hbest)⟩

/-- PI: permission is closed under entailment of the prejacent, on either entry. -/
theorem Permitted₁.mono (hpq : p ⊆ q) : rc.Permitted₁ p → rc.Permitted₁ q :=
  λ ⟨w, hp, hb⟩ => ⟨w, hp.trans hpq, hb⟩

theorem Permitted₂.mono (hpq : p ⊆ q) : rc.Permitted₂ p → rc.Permitted₂ q :=
  λ ⟨w, hb, hp⟩ => ⟨w, hb, hp.trans hpq⟩

/-! ### The boxing special case -/

/-- On the finest resolution with every option at the benchmark, *ought p* is quantification
over the best worlds: the boxing semantics is a resolution semantics. -/
theorem ought_bot_iff (h : rc.resolution = ⊥) (hb : ∀ w, rc.MeetsBenchmark w) :
    rc.Ought p ↔ ∀ w, rc.IsBest w → w ∈ p := by
  simp only [Ought, IsVisible, IsOptimal, IsStronglyPermissible, h, Setoid.bot_settles,
    Setoid.cell_bot, Set.singleton_subset_iff, true_and]
  exact ⟨λ h => h.1, λ h => ⟨h, λ w _ => hb w⟩⟩

end ResolutionContext

/-! ### Duality -/

/-- DUALITY of an operator with a permission closed under entailment yields INHERITANCE. -/
theorem inheritance_of_dual {O P : Set W → Prop} (hd : ∀ p, O p ↔ ¬ P pᶜ)
    (hP : ∀ p q : Set W, p ⊆ q → P p → P q) {p q : Set W} (hpq : p ⊆ q) (hp : O p) : O q :=
  (hd q).2 λ hq => (hd p).1 hp (hP _ _ (Set.compl_subset_compl.2 hpq) hq)

variable [Preorder V] {rc : ResolutionContext W V}

/-- Where INHERITANCE fails, *ought* is not the dual of benchmark permission. -/
theorem ResolutionContext.not_dual₁ (h : ¬ rc.Inheritance) :
    ¬ ∀ p, rc.Ought p ↔ ¬ rc.Permitted₁ pᶜ :=
  λ hd => h λ _ _ hpq => inheritance_of_dual hd (λ _ _ => Permitted₁.mono) hpq

/-- Where INHERITANCE fails, *ought* is not the dual of best-option permission. -/
theorem ResolutionContext.not_dual₂ (h : ¬ rc.Inheritance) :
    ¬ ∀ p, rc.Ought p ↔ ¬ rc.Permitted₂ pᶜ :=
  λ hd => h λ _ _ hpq => inheritance_of_dual hd (λ _ _ => Permitted₂.mono) hpq

/-! ### Ross's paradox -/

/-- Joan's three courses of action. -/
inductive RossW | attend | stayHome | burn
  deriving DecidableEq, Fintype

/-- Attending is best, staying home next, burning down the department worst. -/
def rossRank : RossW → ℕ
  | .attend => 3
  | .stayHome => 2
  | .burn => 1

/-- Joan's context: each action its own option, the benchmark at staying home, so that burning
down the department is the one impermissible option. -/
def rossContext : ResolutionContext RossW ℕ := .ofRanking ⊥ rossRank 2

instance : DecidableRel rossContext.resolution := inferInstanceAs (DecidableRel (⊥ : Setoid RossW))

/-- *Joan ought to attend her classes* is true. -/
theorem ross_ought_attend : rossContext.Ought {RossW.attend} := by decide +kernel

/-- The disjunction is visible, so only the permissibility clause rejects it: burning down the
department entails *attend or burn* and is below the benchmark. -/
theorem ross_disjunction_visible_not_permissible :
    rossContext.IsVisible {RossW.attend, .burn} ∧
      ¬ rossContext.IsStronglyPermissible {RossW.attend, .burn} := by decide +kernel

/-- *Joan ought to either attend her classes or burn down the philosophy department* is false. -/
theorem ross_not_ought_disjunction : ¬ rossContext.Ought {RossW.attend, .burn} := by
  decide +kernel

/-- Staying home is permitted but not obligatory: it is at the benchmark and not best. -/
theorem ross_stayHome_permitted_not_ought :
    rossContext.Permitted₁ {RossW.stayHome} ∧ ¬ rossContext.Ought {RossW.stayHome} := by
  decide +kernel

/-- Ross's paradox refutes INHERITANCE. -/
theorem not_inheritance_ross : ¬ rossContext.Inheritance := λ h =>
  ross_not_ought_disjunction
    (h _ _ (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) ross_ought_attend)

/-- And so *ought* is the dual of neither permission. -/
theorem not_dual_ross :
    (¬ ∀ p, rossContext.Ought p ↔ ¬ rossContext.Permitted₁ pᶜ) ∧
      ¬ ∀ p, rossContext.Ought p ↔ ¬ rossContext.Permitted₂ pᶜ :=
  ⟨ResolutionContext.not_dual₁ not_inheritance_ross,
    ResolutionContext.not_dual₂ not_inheritance_ross⟩

/-! ### Procrastinate -/

/-- Procrastinate's three courses of action ([jackson-pargetter-1986]): accepting the review and
writing it, declining it, and accepting without writing. -/
inductive ProcW | acceptWrite | decline | acceptNoWrite
  deriving DecidableEq, Fintype

/-- Accepting and writing is best; declining is better than accepting and not writing, which is
what Procrastinate would in fact do. -/
def procRank : ProcW → ℕ
  | .acceptWrite => 3
  | .decline => 2
  | .acceptNoWrite => 1

/-- Procrastinate's context, with the benchmark at declining. -/
def procContext : ResolutionContext ProcW ℕ := .ofRanking ⊥ procRank 2

instance : DecidableRel procContext.resolution := inferInstanceAs (DecidableRel (⊥ : Setoid ProcW))

/-- *Procrastinate ought to accept and write the review* is true. -/
theorem proc_ought_acceptWrite : procContext.Ought {ProcW.acceptWrite} := by decide +kernel

/-- *Procrastinate ought to accept* is false: accepting without writing is a way of accepting
and is below the benchmark. -/
theorem proc_not_ought_accept : ¬ procContext.Ought {ProcW.acceptWrite, .acceptNoWrite} := by
  decide +kernel

/-- Procrastinate refutes INHERITANCE too, on a prejacent weakened by an impermissible option
rather than by a disjunct. -/
theorem not_inheritance_proc : ¬ procContext.Inheritance := λ h =>
  proc_not_ought_accept
    (h _ _ (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) proc_ought_acceptWrite)

/-! ### Jenny's ways to school -/

/-- Jenny's ways to school. -/
inductive Mode | running | walking | swimming | driving
  deriving DecidableEq, Fintype

/-- Running is best, walking and swimming tie, driving is worst. -/
def jennyRank : Mode → ℕ
  | .running => 3
  | .walking => 2
  | .swimming => 2
  | .driving => 1

/-- The proposition that Jenny goes to school by `m`; a world also records whether she has a cup
of coffee, which the resolution ignores. -/
abbrev mode (m : Mode) : Set (Mode × Bool) := {w | w.1 = m}

/-- Jenny's context: the ways to school as options, coffee below the resolution, and the
benchmark between walking and driving, so that driving is the one impermissible option. -/
def jennyContext : ResolutionContext (Mode × Bool) ℕ :=
  .ofRanking (Setoid.ker Prod.fst) (jennyRank ·.1) 2

instance : DecidableRel jennyContext.resolution :=
  inferInstanceAs (DecidableRel (Setoid.ker (Prod.fst : Mode × Bool → Mode)))

/-- Running is permissible, optimal, and strongly permissible, so Jenny ought to run. -/
theorem jenny_ought_running : jennyContext.Ought (mode .running) := by decide +kernel

/-- Running or driving is permissible and optimal but not strongly permissible. -/
theorem jenny_running_or_driving :
    jennyContext.Permitted₁ (mode .running ∪ mode .driving) ∧
      jennyContext.IsOptimal (mode .running ∪ mode .driving) ∧
        ¬ jennyContext.IsStronglyPermissible (mode .running ∪ mode .driving) := by
  decide +kernel

/-- Swimming or driving is permissible but neither strongly permissible nor optimal. -/
theorem jenny_swimming_or_driving :
    jennyContext.Permitted₁ (mode .swimming ∪ mode .driving) ∧
      ¬ jennyContext.IsOptimal (mode .swimming ∪ mode .driving) ∧
        ¬ jennyContext.IsStronglyPermissible (mode .swimming ∪ mode .driving) := by
  decide +kernel

/-- Running or walking is visible in Jenny's resolution; having a cup of coffee is not. -/
theorem jenny_visible :
    jennyContext.IsVisible (mode .running ∪ mode .walking) ∧
      ¬ jennyContext.IsVisible {w | w.2 = true} := by decide +kernel

end Cariani2013
