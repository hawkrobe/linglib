import Linglib.Semantics.Attitudes.Desire.QuestionBased
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Preorder.Finite

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
modal base into the agent's options, an ordering of the options, and a benchmark below which an
option is impermissible (`ResolutionContext`). *Ought p* holds when the options settle `p`,
every best option entails `p`, and every option entailing `p` meets the benchmark (`Ought`), so
that one impermissible option compatible with the prejacent falsifies the sentence, the paper's
COARSE FALSEMAKING (`not_ought_of_not_meetsBenchmark`), while impermissible ways of `p` that no
option distinguishes leave it true.

Both puzzles refute INHERITANCE (`not_inheritance_ross`, `not_inheritance_proc`). Permission has
two candidate entries, some option at the benchmark entails `p` or some best option does
(`Permitted₁`, `Permitted₂`); *ought* entails both, both are closed under entailment, and since
that closure together with the duality of *ought* and permission would restore INHERITANCE
(`inheritance_of_dual`), *ought* is the dual of neither. A boxing semantics is the special case
of a resolution whose cells are singletons and whose benchmark every option meets
(`ought_finest_iff`).

## Implementation notes

* The ordering on options is a valuation into a preordered scale with the benchmark a threshold
  of the scale, neutral between the ranking and quantitative scales the paper allows; the best
  options are the `MaximalFor` elements of the valuation. The paper's examples value an option
  at the rank of its best world (`ofRanking`).
* `options` is the partition of the modal base itself, so the modal base is not a separate
  parameter and the ordering does not vary with it. The paper's third puzzle, conditional
  *oughts* under the restrictor analysis of conditionals, needs the modal base and is not
  formalized.
* Visibility is `Desire.QuestionBased.IsConsidered`, every cell settling the prejacent.

## References

* [cariani-2013]
* [ross-1941]
* [jackson-pargetter-1986]
* [kratzer-1981]
-/

namespace Cariani2013

open Desire.QuestionBased

variable {W V : Type*}

/-- A resolution context: the agent's options, the cells of a partition of the modal base; the
ordering, a valuation of options in a preordered scale; and the benchmark, the threshold of the
scale below which an option is impermissible. -/
structure ResolutionContext (W V : Type*) where
  /-- The options, mutually exclusive courses of action. -/
  options : List (Finset W)
  /-- The ordering: the value of an option in the scale. -/
  value : Finset W → V
  /-- The benchmark: the least permissible value. -/
  benchmark : V

namespace ResolutionContext

/-- The context of a ranked action space: an option is valued at the rank of its best world. -/
def ofRanking [SemilatticeSup V] [OrderBot V] (options : List (Finset W)) (rank : W → V)
    (benchmark : V) : ResolutionContext W V :=
  ⟨options, (·.sup rank), benchmark⟩

variable [Preorder V] (rc : ResolutionContext W V) (p : Set W)

/-! ### The clauses -/

/-- `p` is *visible* when the options settle it: each entails `p` or entails its negation. -/
abbrev IsVisible : Prop := IsConsidered rc.options p

/-- An option *meets the benchmark* when its value is at least the benchmark. -/
def MeetsBenchmark (o : Finset W) : Prop := rc.benchmark ≤ rc.value o

/-- An option is *best* when no option is strictly better. -/
def IsBest (o : Finset W) : Prop := MaximalFor (· ∈ rc.options) rc.value o

/-- `p` is *optimal* when every best option entails it. -/
def IsOptimal : Prop := ∀ o ∈ rc.options, rc.IsBest o → ∀ w ∈ o, w ∈ p

/-- `p` is *strongly permissible* when every option that entails it meets the benchmark. -/
def IsStronglyPermissible : Prop := ∀ o ∈ rc.options, (∀ w ∈ o, w ∈ p) → rc.MeetsBenchmark o

/-! ### The operators -/

/-- *Ought p*: `p` is visible, optimal, and strongly permissible. -/
def Ought : Prop := rc.IsVisible p ∧ rc.IsOptimal p ∧ rc.IsStronglyPermissible p

/-- *Permitted p*, first entry: some option that entails `p` meets the benchmark. -/
def Permitted₁ : Prop := ∃ o ∈ rc.options, (∀ w ∈ o, w ∈ p) ∧ rc.MeetsBenchmark o

/-- *Permitted p*, second entry: some best option entails `p`. -/
def Permitted₂ : Prop := ∃ o ∈ rc.options, rc.IsBest o ∧ ∀ w ∈ o, w ∈ p

/-- INHERITANCE: *ought* is closed under entailment of the prejacent. -/
def Inheritance : Prop := ∀ p q : Set W, p ⊆ q → rc.Ought p → rc.Ought q

section Decidable

variable [DecidableRel (α := V) (· ≤ ·)]

instance (o : Finset W) : Decidable (rc.MeetsBenchmark o) := inferInstanceAs (Decidable (_ ≤ _))

instance [DecidableEq W] (o : Finset W) : Decidable (rc.IsBest o) :=
  inferInstanceAs (Decidable (o ∈ rc.options ∧ ∀ o' ∈ rc.options, _ → _))

instance [DecidableEq W] [DecidablePred (· ∈ p)] : Decidable (rc.IsOptimal p) :=
  inferInstanceAs (Decidable (∀ o ∈ rc.options, _ → _))

instance [DecidablePred (· ∈ p)] : Decidable (rc.IsStronglyPermissible p) :=
  inferInstanceAs (Decidable (∀ o ∈ rc.options, _ → _))

instance [DecidableEq W] [DecidablePred (· ∈ p)] : Decidable (rc.Ought p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidablePred (· ∈ p)] : Decidable (rc.Permitted₁ p) :=
  inferInstanceAs (Decidable (∃ o ∈ rc.options, _))

instance [DecidableEq W] [DecidablePred (· ∈ p)] : Decidable (rc.Permitted₂ p) :=
  inferInstanceAs (Decidable (∃ o ∈ rc.options, _))

end Decidable

variable {rc p} {q : Set W}

/-! ### Coarse falsemaking and permission -/

/-- COARSE FALSEMAKING: one option below the benchmark that entails `p` falsifies *ought p*,
however good the other options are. -/
theorem not_ought_of_not_meetsBenchmark {o : Finset W} (ho : o ∈ rc.options)
    (hp : ∀ w ∈ o, w ∈ p) (h : ¬ rc.MeetsBenchmark o) : ¬ rc.Ought p :=
  λ ⟨_, _, hsp⟩ => h (hsp o ho hp)

/-- Some option is best as soon as there are options. -/
theorem exists_isBest (h : rc.options ≠ []) : ∃ o ∈ rc.options, rc.IsBest o :=
  let ⟨o, ho⟩ := Set.Finite.exists_maximalFor rc.value _ (List.finite_toSet rc.options)
    (List.exists_mem_of_ne_nil rc.options h)
  ⟨o, ho.1, ho⟩

/-- What one ought to do some best option does. -/
theorem Ought.permitted₂ (h : rc.options ≠ []) (ho : rc.Ought p) : rc.Permitted₂ p :=
  let ⟨o, hmem, hbest⟩ := exists_isBest h
  ⟨o, hmem, hbest, ho.2.1 o hmem hbest⟩

/-- What one ought to do is permitted: a best option does it by optimality and meets the
benchmark by strong permissibility. -/
theorem Ought.permitted₁ (h : rc.options ≠ []) (ho : rc.Ought p) : rc.Permitted₁ p :=
  let ⟨o, hmem, hbest⟩ := exists_isBest h
  ⟨o, hmem, ho.2.1 o hmem hbest, ho.2.2 o hmem (ho.2.1 o hmem hbest)⟩

/-- PI: permission is closed under entailment of the prejacent, on either entry. -/
theorem Permitted₁.mono (hpq : p ⊆ q) : rc.Permitted₁ p → rc.Permitted₁ q :=
  λ ⟨o, ho, hp, hb⟩ => ⟨o, ho, λ w hw => hpq (hp w hw), hb⟩

theorem Permitted₂.mono (hpq : p ⊆ q) : rc.Permitted₂ p → rc.Permitted₂ q :=
  λ ⟨o, ho, hb, hp⟩ => ⟨o, ho, hb, λ w hw => hpq (hp w hw)⟩

/-! ### The boxing special case -/

/-- With singleton cells and every option at the benchmark, *ought p* is quantification over the
best worlds: the boxing semantics is a resolution semantics at the finest resolution. -/
theorem ought_finest_iff {worlds : List W} (hw : ∀ w, w ∈ worlds)
    (ho : rc.options = finest worlds) (hb : ∀ o ∈ rc.options, rc.MeetsBenchmark o) :
    rc.Ought p ↔ ∀ w, MaximalFor (λ _ => True) (λ w => rc.value {w}) w → w ∈ p := by
  have hv : IsConsidered (worlds.map ({·})) p := isConsidered_finest worlds
  simp only [Ought, IsVisible, IsOptimal, IsStronglyPermissible, IsBest, MaximalFor, ho, finest,
    List.mem_map, hw, true_and, true_implies, forall_exists_index, forall_apply_eq_imp_iff,
    Finset.mem_singleton, forall_eq, Finset.singleton_inj, exists_eq] at hb ⊢
  exact ⟨λ h w hm => h.2.1 w hm, λ h => ⟨hv, λ w hm => h w hm, λ w _ => hb w⟩⟩

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
  deriving DecidableEq

/-- Attending is best, staying home next, burning down the department worst. -/
def rossRank : RossW → ℕ
  | .attend => 3
  | .stayHome => 2
  | .burn => 1

/-- Joan's context: each action an option, the benchmark at staying home, so that burning down
the department is the one impermissible option. -/
def rossContext : ResolutionContext RossW ℕ :=
  .ofRanking [{.attend}, {.stayHome}, {.burn}] rossRank 2

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
  deriving DecidableEq

/-- Accepting and writing is best; declining is better than accepting and not writing, which is
what Procrastinate would in fact do. -/
def procRank : ProcW → ℕ
  | .acceptWrite => 3
  | .decline => 2
  | .acceptNoWrite => 1

/-- Procrastinate's context, with the benchmark at declining. -/
def procContext : ResolutionContext ProcW ℕ :=
  .ofRanking [{.acceptWrite}, {.decline}, {.acceptNoWrite}] procRank 2

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
  deriving DecidableEq

/-- Running is best, walking and swimming tie, driving is worst. -/
def jennyRank : Mode → ℕ
  | .running => 3
  | .walking => 2
  | .swimming => 2
  | .driving => 1

/-- The proposition that Jenny goes to school by `m`; a world also records whether she has a cup
of coffee, which no option settles. -/
abbrev mode (m : Mode) : Set (Mode × Bool) := {w | w.1 = m}

/-- Jenny's context: the four ways to school as options, coffee below the resolution, and the
benchmark between walking and driving, so that driving is the one impermissible option. -/
def jennyContext : ResolutionContext (Mode × Bool) ℕ :=
  .ofRanking ([.running, .walking, .swimming, .driving].map λ m => {(m, true), (m, false)})
    (jennyRank ·.1) 2

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

/-- Running or walking is visible in Jenny's options; having a cup of coffee is not. -/
theorem jenny_visible :
    jennyContext.IsVisible (mode .running ∪ mode .walking) ∧
      ¬ jennyContext.IsVisible {w | w.2 = true} := by decide +kernel

end Cariani2013
