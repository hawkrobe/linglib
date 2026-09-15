import Mathlib.Data.Set.Subsingleton
import Mathlib.Data.List.Basic

/-!
# Probes as interaction and satisfaction specifications

This file defines a probe over a goal type as two predicates on goals, following
[deal-2025a]'s interaction/satisfaction theory of Agree. A goal *interacts* with the probe
when it bears features the probe copies, and *satisfies* it when it bears features that halt
the search. A search over an ordered goal sequence stops at the first satisfying goal, and the
probe Agrees with that goal when it also interacts; a satisfying goal that does not interact
absorbs the probe, [deal-2024]'s satisfaction without interaction. The outcome of a search is
`valued` iff some goal satisfies the probe, and an unvalued outcome is failed Agree, tolerated
under [preminger-2014]'s obligatory-operations model. The full operation, which copies from
every interacting goal up to the satisfier, is `Probe.run` in `Probe/Run.lean`.

Probe *specifications*, such as relativized targets, horizon profiles and articulated probes,
denote a `Probe` by a `toProbe` map rather than re-implementing search.

## Main definitions

* `Minimalist.Probe`, `Minimalist.Probe.relativized`, `Minimalist.Probe.ofInt`,
  `Minimalist.Probe.insatiable`, `Minimalist.Probe.indiscriminate`
* `Minimalist.Probe.search`, `Minimalist.Probe.agree`, `Minimalist.Probe.outcome`
* `Minimalist.Probe.Licensed`, `Minimalist.Probe.AllLicensed`, `Minimalist.Probe.cascade`

## Main results

* `Minimalist.Probe.search_eq_some_iff_closest`: locality as list search.
* `Minimalist.Probe.not_rel_of_search_eq_some`: the found goal is minimal for any precedence
  the sequence respects.
* `Minimalist.Probe.allLicensed_iff`: one search licenses at most one goal.

## References

* [deal-2025a], [deal-2024]
* [bejar-rezac-2003], [preminger-2014]
* [chomsky-2000]
-/

namespace Minimalist

variable {α : Type*}

/-- A probe over goals of type `α` is an interaction predicate, the goals it copies from, and a
satisfaction predicate, the goals that halt its search ([deal-2025a]). -/
structure Probe (α : Type*) where
  /-- The goal bears features the probe copies. -/
  int : α → Bool
  /-- The goal bears features that halt the probe's search. -/
  sat : α → Bool

/-- The outcome of an obligatory probing operation, `valued` iff the search found a goal. An
`unvalued` outcome is failed Agree, tolerated under [preminger-2014]'s obligatory-operations
model and spelled out as the default exponent. -/
inductive Probe.Outcome where
  /-- The search found a goal. -/
  | valued
  /-- The search found no goal. -/
  | unvalued
  deriving DecidableEq, Repr

namespace Probe

/-- The probe relativized to `f`, which interacts with and is satisfied by the same goals, the
`[INT:F, SAT:F]` probe of [bejar-rezac-2003] and [preminger-2014]. -/
def relativized (f : α → Bool) : Probe α := ⟨f, f⟩

/-- The probe satisfied by every goal and interacting with those that pass `int`, which Agrees
with the closest goal iff that goal is active, the Active Goal Hypothesis of [chomsky-2000]. -/
def ofInt (int : α → Bool) : Probe α := ⟨int, fun _ => true⟩

/-- The insatiable probe interacting with `f`, which no goal halts, so that it copies from every
`f`-goal in its domain, Multiple Agree ([deal-2025a]). -/
def insatiable (f : α → Bool) : Probe α := ⟨f, fun _ => false⟩

/-- The indiscriminate probe, which every goal satisfies and interacts with, so that bare
minimality delivers the closest goal ([halpert-2012]'s L⁰). -/
def indiscriminate : Probe α := relativized fun _ => true

@[simp] theorem relativized_int (f : α → Bool) : (relativized f).int = f := rfl
@[simp] theorem relativized_sat (f : α → Bool) : (relativized f).sat = f := rfl
@[simp] theorem ofInt_int (f : α → Bool) : (ofInt f).int = f := rfl
@[simp] theorem ofInt_sat (f : α → Bool) (a : α) : (ofInt f).sat a = true := rfl
@[simp] theorem insatiable_int (f : α → Bool) : (insatiable f).int = f := rfl
@[simp] theorem insatiable_sat (f : α → Bool) (a : α) : (insatiable f).sat a = false := rfl

/-! ### Search -/

/-- The goal a probe finds in an ordered goal sequence, the first goal that satisfies it. -/
def search (p : Probe α) (goals : List α) : Option α :=
  goals.find? p.sat

/-- The found goal, if it interacts with the probe. A satisfying goal that does not interact
absorbs the probe. -/
def agree (p : Probe α) (goals : List α) : Option α :=
  (p.search goals).filter p.int

variable {p : Probe α} {goals : List α}

/-- A probe finds nothing iff no goal satisfies it. -/
@[simp]
theorem search_eq_none_iff : p.search goals = none ↔ ∀ a ∈ goals, ¬ p.sat a := by
  simp [search, List.find?_eq_none]

/-- The found goal is a member of the sequence. -/
theorem mem_of_search_eq_some {a : α} (h : p.search goals = some a) : a ∈ goals :=
  List.mem_of_find?_eq_some h

/-- The found goal satisfies the probe. -/
theorem sat_of_search_eq_some {a : α} (h : p.search goals = some a) : p.sat a :=
  List.find?_some h

/-- Over a two-goal sequence whose lower goal's satisfaction entails the higher's, the search
lands on the higher goal if anywhere, the kernel of gluttony only in inverse configurations
([coon-keine-2021]) and of highest-only licensing ([halpert-2012]). -/
theorem search_pair_of_imp {a b : α} (h : p.sat b → p.sat a) :
    p.search [a, b] = if p.sat a then some a else none := by
  simp only [search, List.find?_cons, List.find?_nil]
  revert h; cases p.sat a <;> cases p.sat b <;> simp

/-- The probe Agrees with `a` iff the search finds `a` and `a` interacts. -/
theorem agree_eq_some_iff {a : α} :
    p.agree goals = some a ↔ p.search goals = some a ∧ p.int a := by
  cases h : p.search goals with
  | none => simp [agree, h]
  | some b =>
    simp only [agree, h, Option.filter_some, Option.ite_none_right_eq_some, Option.some.injEq]
    constructor
    · rintro ⟨hb, rfl⟩
      exact ⟨rfl, hb⟩
    · rintro ⟨hb, ha⟩
      exact ⟨hb ▸ ha, hb.symm ▸ rfl⟩

/-- A probe satisfied by every goal finds the closest one. -/
@[simp] theorem ofInt_search (int : α → Bool) : (ofInt int).search goals = goals.head? := by
  cases goals <;> rfl

/-- A probe satisfied by every goal Agrees with the closest one iff it interacts. -/
theorem ofInt_agree_eq_some_iff {int : α → Bool} {a : α} :
    (ofInt int).agree goals = some a ↔ goals.head? = some a ∧ int a := by
  rw [agree_eq_some_iff, ofInt_search]; rfl

/-- A satisfying goal that does not interact absorbs the probe. -/
theorem agree_eq_none_of_not_int {a : α} (h : p.search goals = some a) (ha : p.int a = false) :
    p.agree goals = none := by
  simp [agree, h, Option.filter_some, ha]

@[simp] theorem search_nil : p.search [] = none := rfl

/-- What the probe Agrees with, it found. -/
theorem agree_le_search {a : α} (h : p.agree goals = some a) : p.search goals = some a :=
  (agree_eq_some_iff.mp h).1

/-- When every satisfying goal interacts, Agree coincides with search. -/
theorem agree_eq_search_of_int (h : ∀ a, p.sat a → p.int a) :
    p.agree goals = p.search goals := by
  rw [agree]
  cases hs : p.search goals with
  | none => rfl
  | some a => rw [Option.filter_some, if_pos (h a (sat_of_search_eq_some hs))]

/-- A relativized probe Agrees with the goal it finds. -/
theorem relativized_agree (f : α → Bool) :
    (relativized f).agree goals = (relativized f).search goals :=
  agree_eq_search_of_int fun _ h => h

theorem agree_eq_none_iff : p.agree goals = none ↔ ¬ ∃ a, p.search goals = some a ∧ p.int a := by
  simp only [← Option.not_isSome_iff_eq_none, Option.isSome_iff_exists, agree_eq_some_iff]

/-- Locality as list search. The probe finds `a` iff `a` satisfies it and every earlier goal
does not, so that nothing intervenes. -/
theorem search_eq_some_iff_closest {a : α} :
    p.search goals = some a ↔
      p.sat a ∧ ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ ∀ b ∈ l₁, !p.sat b :=
  List.find?_eq_some_iff_append

/-- Over a goal sequence in which no later goal precedes an earlier one, the found goal is
minimal among the satisfying goals. -/
theorem not_rel_of_search_eq_some {r : α → α → Prop} {a : α}
    (hord : goals.Pairwise λ x y => ¬ r y x) (h : p.search goals = some a) :
    ∀ b ∈ goals, p.sat b → b ≠ a → ¬ r b a := by
  obtain ⟨-, l₁, l₂, rfl, hl₁⟩ := search_eq_some_iff_closest.mp h
  intro b hb hvb hne hba
  rcases List.mem_append.mp hb with hb | hb
  · exact absurd hvb (by simpa using hl₁ b hb)
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact hne rfl
    · exact (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1 b hb hba

/-! ### Outcomes -/

/-- The outcome of an obligatory probing operation over a goal sequence, `valued` iff the search
finds a goal. -/
def outcome (p : Probe α) (goals : List α) : Probe.Outcome :=
  if (p.search goals).isSome then .valued else .unvalued

/-- The probe is valued iff the search finds a goal. -/
theorem outcome_eq_valued_iff_isSome : p.outcome goals = .valued ↔ (p.search goals).isSome := by
  rw [outcome]
  cases (p.search goals).isSome <;> decide

/-- The probe ends unvalued iff the search comes back empty. -/
theorem outcome_eq_unvalued_iff_eq_none : p.outcome goals = .unvalued ↔ p.search goals = none := by
  rw [outcome]
  cases p.search goals <;>
    simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      if_false, if_true, reduceCtorEq]

/-- The probe is valued iff some goal satisfies it. -/
@[simp]
theorem outcome_eq_valued_iff : p.outcome goals = .valued ↔ ∃ a ∈ goals, p.sat a :=
  outcome_eq_valued_iff_isSome.trans List.find?_isSome

/-- The probe ends unvalued iff no goal satisfies it. -/
@[simp]
theorem outcome_eq_unvalued_iff : p.outcome goals = .unvalued ↔ ∀ a ∈ goals, ¬ p.sat a := by
  rw [outcome_eq_unvalued_iff_eq_none]
  exact search_eq_none_iff

/-- Widening satisfaction can only keep a probe valued. If `p` is valued and `q` is satisfied by
everything that satisfies `p` among `goals`, so is `q`. -/
theorem outcome_valued_mono {q : Probe α} (h : ∀ a ∈ goals, p.sat a → q.sat a) :
    p.outcome goals = .valued → q.outcome goals = .valued := by
  simp only [outcome_eq_valued_iff]
  rintro ⟨a, ha, hva⟩
  exact ⟨a, ha, h a ha hva⟩

/-! ### Licensing -/

/-- A goal is licensed by a probe iff the probe's single search reaches it, since for
[bejar-rezac-2003] licensing is an Agree relation with the probe. -/
def Licensed (p : Probe α) (goals : List α) (a : α) : Prop :=
  p.search goals = some a

instance [DecidableEq α] (p : Probe α) (goals : List α) (a : α) :
    Decidable (p.Licensed goals a) :=
  inferInstanceAs (Decidable (p.search goals = some a))

/-- One search licenses at most one goal. -/
theorem Licensed.unique {a b : α} (ha : p.Licensed goals a) (hb : p.Licensed goals b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- Licensing is being the closest satisfying goal, with no satisfying goal intervening. -/
theorem licensed_iff_closest {a : α} :
    p.Licensed goals a ↔ p.sat a ∧ ∃ l₁ l₂, goals = l₁ ++ a :: l₂ ∧ ∀ b ∈ l₁, !p.sat b :=
  search_eq_some_iff_closest

/-- A licensed goal is a member of the sequence. -/
theorem Licensed.mem {a : α} (h : p.Licensed goals a) : a ∈ goals :=
  mem_of_search_eq_some h

/-- A licensed goal satisfies the probe. -/
theorem Licensed.sat {a : α} (h : p.Licensed goals a) : p.sat a :=
  sat_of_search_eq_some h

/-- Licensing by the indiscriminate probe is being the structurally closest goal, bare
minimality ([halpert-2012]'s L⁰). -/
theorem indiscriminate_licensed_iff {a : α} :
    (indiscriminate : Probe α).Licensed goals a ↔ goals.head? = some a := by
  unfold Licensed search indiscriminate relativized
  cases goals <;>
    simp only [List.find?_nil, List.find?_cons_of_pos, List.head?_nil, List.head?_cons]

/-- Every goal that needs licensing is licensed by the probe's search. Which goals need licensing
(`needs`) and which satisfy the probe come apart in general, since [halpert-2012]'s Zulu L⁰ is
satisfied by every goal while only augmentless nominals need it; feature-relativized probes are
the diagonal `p.AllLicensed p.sat`, where the probe is satisfied by exactly the needy
([bejar-rezac-2003]'s π as relativized by [preminger-2014]). -/
def AllLicensed (p : Probe α) (needs : α → Bool) (goals : List α) : Prop :=
  ∀ a ∈ goals, needs a = true → p.Licensed goals a

instance [DecidableEq α] (p : Probe α) (needs : α → Bool) (goals : List α) :
    Decidable (p.AllLicensed needs goals) :=
  inferInstanceAs (Decidable (∀ a ∈ goals, needs a = true → p.Licensed goals a))

/-- On the diagonal, where the probe is relativized to exactly the needy goals, all needy goals
are licensed iff the satisfying goals are subsingleton, one search licensing at most one goal,
the fact behind [preminger-2014]'s person restriction. -/
theorem allLicensed_iff {f : α → Bool} {goals : List α} :
    (relativized f).AllLicensed f goals ↔ ∀ a ∈ goals, ∀ b ∈ goals, f a → f b → a = b := by
  constructor
  · intro h a ha b hb hva hvb
    exact (h a ha hva).unique (h b hb hvb)
  · intro h a ha hva
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨a, ha, hva⟩)
    have hba := h b (mem_of_search_eq_some (p := relativized f) hb) a ha
      (sat_of_search_eq_some (p := relativized f) hb) hva
    exact hba ▸ hb

/-- `allLicensed_iff` in `Set.Subsingleton` form. -/
theorem allLicensed_iff_subsingleton {f : α → Bool} {goals : List α} :
    (relativized f).AllLicensed f goals ↔ {a | a ∈ goals ∧ f a}.Subsingleton := by
  rw [allLicensed_iff]
  exact ⟨fun h a ha b hb => h a ha.1 b hb.1 ha.2 hb.2,
         fun h a ha b hb hva hvb => h ⟨ha, hva⟩ ⟨hb, hvb⟩⟩

/-- Licensing by the indiscriminate probe pins every needy goal to the head of the sequence, the
highest-element condition of [halpert-2012]. -/
theorem indiscriminate_allLicensed_iff {needs : α → Bool} {goals : List α} :
    (indiscriminate : Probe α).AllLicensed needs goals ↔
      ∀ a ∈ goals, needs a = true → goals.head? = some a :=
  forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    indiscriminate_licensed_iff

/-! ### Cascades -/

/-- The goal an ordered sequence of probes delivers, the first probe's finding, else the next's,
and so on. This is `Probe.search` at the goal level composed with `List.findSome?` at the probe
level, and also the single-slot morphological competition in which the first probe with output
wins the slot, as in [preminger-2014] where π⁰'s clitic beats #⁰'s exponent beats nothing. -/
def cascade (ps : List (Probe α)) (goals : List α) : Option α :=
  ps.findSome? (·.search goals)

variable {ps : List (Probe α)}

/-- A cascade delivers nothing iff no goal satisfies any probe. -/
@[simp]
theorem cascade_eq_none_iff : cascade ps goals = none ↔ ∀ q ∈ ps, ∀ a ∈ goals, ¬ q.sat a := by
  simp [cascade, List.findSome?_eq_none_iff]

/-- Unfold one probe of the cascade. -/
theorem cascade_cons {q : Probe α} :
    cascade (q :: ps) goals = (q.search goals <|> cascade ps goals) := by
  rw [cascade, List.findSome?_cons]
  cases q.search goals <;> rfl

@[simp] theorem cascade_nil : cascade ([] : List (Probe α)) goals = none := rfl

@[simp] theorem cascade_singleton {q : Probe α} : cascade [q] goals = q.search goals := by
  rw [cascade_cons, cascade_nil]
  cases q.search goals <;> rfl

/-- `cascade` is a monoid map `(List (Probe α), ++) → (Option α, <|>)`, the single-slot
competition running the left probes and then the right. -/
theorem cascade_append {qs : List (Probe α)} :
    cascade (ps ++ qs) goals = (cascade ps goals <|> cascade qs goals) := by
  unfold cascade
  rw [List.findSome?_append]
  cases ps.findSome? (·.search goals) <;> rfl

/-- The cascade's goal is licensed by one of its probes. -/
theorem exists_licensed_of_cascade_eq_some {a : α} (h : cascade ps goals = some a) :
    ∃ q ∈ ps, q.Licensed goals a :=
  List.exists_of_findSome?_eq_some h

/-- The cascade's goal is a member of the sequence. -/
theorem mem_of_cascade_eq_some {a : α} (h : cascade ps goals = some a) : a ∈ goals :=
  let ⟨_, _, hq⟩ := exists_licensed_of_cascade_eq_some h
  mem_of_search_eq_some hq

end Probe

end Minimalist
