module

public import Linglib.Phonology.OptimalityTheory.Ranking
public import Linglib.Phonology.Constraints.Defs
public import Linglib.Phonology.Constraints.Profile
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.List.Permutation

/-!
# Tableaux

The OT evaluation vocabulary and machinery. A `Tableau` is the lexicographic
minimisation problem [prince-smolensky-1993] solves — a finite candidate set ranked by a
`ViolationProfile`-valued objective, whose winners are the candidates with a profile at most
every candidate's under mathlib's `Pi.Lex` order. On top of the vocabulary:
smart constructors, the structural optimality theorems, and factorial-typology
computation.

## Main definitions

* `Tableau C n` — a finite OT tableau over candidates `C` with `n` constraints.
* `Tableau.optimal` — the winner set; optimality is plain membership.
* `Ranking n` — a constraint ranking ([prince-2002]'s domination order).
* `Tableau.ofPerm` — a tableau from a fixed constraint set `CON C n` under a ranking
  `r : Ranking n` (priority position `p` reads constraint `r p`).
* `Tableau.ofRanking` — the list form: ranked constraint list, list order = priority
  (position `0` most dominant); `Tableau.ofPerm` under the identity ranking.
* `Tableau.ofFintype` — the same over every candidate of a finite type.
* `Tableau.ofOrder` — a tableau from a constraint *order* (labels, most dominant first)
  and the candidates' violation marks by label: the paper-tableau form.
* `factorialOptima` / `factorialTypologySize` — the distinct optimal sets predicted
  across all rankings, and their count.

## Main results

* `Tableau.mem_optimal_iff` / `Tableau.optimal_nonempty` / `Tableau.optimal_subset` —
  the winner characterization; winners exist.
* `Tableau.optimal_eq_singleton_iff` / `Tableau.optimal_eq_singleton_iff_pair` — sole
  winner ⟺ strict domination.
* `Tableau.ofPerm_profile_lt_iff` / `Tableau.ofPerm_profile_lt_iff_exists_dominates` — a
  candidate beats another under a ranking iff the most dominant constraint distinguishing
  them prefers it, iff some constraint preferring it dominates every constraint preferring
  the other.
* `Tableau.notMem_optimal_of_lt` / `Tableau.ofPerm_notMem_optimal_of_lt` — harmonic
  bounding: a candidate beaten pointwise never wins.
* `Tableau.ofPerm_zero_mem_optimal` / `Tableau.ofRanking_zero_mem_optimal` /
  `Tableau.ofRanking_zero_mem_optimal_allRankings` — a candidate with no violations
  wins under any (every) ranking.
* `Tableau.ofRanking_optimal_zero_first` — a satisfiable top constraint forces all
  winners to satisfy it.
-/

@[expose] public section

namespace OptimalityTheory

open Constraints

/-! ### The tableau vocabulary -/

/-- An OT tableau: a finite candidate set scored by a fixed-length violation profile, with a
witness that there is a candidate. -/
structure Tableau (C : Type*) [DecidableEq C] (n : Nat) where
  /-- The candidates. -/
  candidates : Finset C
  /-- Each candidate's violation profile. -/
  profile : C → ViolationProfile n
  /-- A tableau has a candidate. -/
  nonempty : candidates.Nonempty

namespace Tableau

variable {C : Type*} [DecidableEq C] {n : Nat} (t : Tableau C n) (c : C)

/-- The winning candidates, those whose profile is lexicographically at most every
candidate's; the comparison is decided by `Pi.Lex.decidableLE`. Optimality is plain membership
`c ∈ t.optimal`, unfolded by `mem_optimal_iff`; there is no separate winner predicate. -/
def optimal : Finset C :=
  t.candidates.filter fun c ↦ ∀ d ∈ t.candidates, t.profile c ≤ t.profile d

variable {t c}

/-- A winner is a candidate whose profile is lexicographically below that of every
candidate. -/
theorem mem_optimal_iff :
    c ∈ t.optimal ↔ c ∈ t.candidates ∧ ∀ d ∈ t.candidates, t.profile c ≤ t.profile d :=
  Finset.mem_filter

/-- Every tableau has a winner, since the linearly ordered image of a nonempty finset has a
minimum. -/
theorem optimal_nonempty : t.optimal.Nonempty :=
  let ⟨c, hc, hmin⟩ := Finset.exists_min_image t.candidates t.profile t.nonempty
  ⟨c, mem_optimal_iff.mpr ⟨hc, hmin⟩⟩

theorem optimal_subset : c ∈ t.optimal → c ∈ t.candidates := fun h ↦ (mem_optimal_iff.mp h).1

/-- A winner's profile bounds every candidate's. -/
theorem le_of_mem_optimal {d : C} (hc : c ∈ t.optimal) (hd : d ∈ t.candidates) :
    t.profile c ≤ t.profile d :=
  (mem_optimal_iff.mp hc).2 d hd

/-- Optimality factors through the profile, so it transports along profile equality:
scoring like a winner is winning. -/
theorem mem_optimal_of_profile_eq {d : C} (hd : d ∈ t.optimal) (hc : c ∈ t.candidates)
    (he : t.profile c = t.profile d) : c ∈ t.optimal :=
  mem_optimal_iff.mpr ⟨hc, fun _ he' ↦ he ▸ le_of_mem_optimal hd he'⟩

/-- A candidate whose profile vanishes wins, since `0` is the least profile. -/
theorem mem_optimal_of_profile_eq_zero (hc : c ∈ t.candidates) (h0 : t.profile c = 0) :
    c ∈ t.optimal :=
  mem_optimal_iff.mpr ⟨hc, fun _ _ ↦ h0 ▸ ViolationProfile.zero_le _⟩

/-- A tableau has sole winner `m` iff `m` strictly lex-dominates every other
candidate. -/
theorem optimal_eq_singleton_iff {m : C} (hm : m ∈ t.candidates) :
    t.optimal = {m} ↔ ∀ c ∈ t.candidates, c ≠ m → t.profile m < t.profile c := by
  constructor
  · intro h c hc hcm
    have hmo : m ∈ t.optimal := h ▸ Finset.mem_singleton_self m
    exact (le_of_mem_optimal hmo hc).lt_of_ne fun he ↦
      hcm <| Finset.mem_singleton.mp (h ▸ mem_optimal_of_profile_eq hmo hc he.symm)
  · intro h
    refine Finset.eq_singleton_iff_unique_mem.mpr
      ⟨mem_optimal_iff.mpr ⟨hm, fun d hd ↦ ?_⟩, fun c hc ↦ ?_⟩
    · rcases eq_or_ne d m with rfl | hdm
      · exact le_rfl
      · exact (h d hd hdm).le
    · by_contra hcm
      exact lt_irrefl (t.profile c) (lt_of_le_of_lt (le_of_mem_optimal hc hm)
        (h c (optimal_subset hc) hcm))

/-- A tableau with a single candidate has it as sole winner. -/
@[simp] theorem optimal_singleton (hc : t.candidates = {c}) : t.optimal = {c} := by
  ext x
  simp +contextual [mem_optimal_iff, hc]

/-- A two-candidate tableau has sole winner `c` iff `c` strictly lex-dominates `d`. -/
theorem optimal_eq_singleton_iff_pair {d : C} (hcand : t.candidates = {c, d}) (hne : c ≠ d) :
    t.optimal = {c} ↔ t.profile c < t.profile d := by
  rw [optimal_eq_singleton_iff (by rw [hcand]; exact Finset.mem_insert_self _ _), hcand]
  simp [hne.symm]

/-- A candidate strictly lex-dominated by a competitor is no winner. -/
theorem notMem_optimal_of_lt {d : C} (hc : c ∈ t.candidates) (h : t.profile c < t.profile d) :
    d ∉ t.optimal :=
  fun hd ↦ (le_of_mem_optimal hd hc).not_gt h

/-! ### Tableau constructors -/

variable (con : CON C n) (r : Ranking n) (candidates : List C)
  (ranking : List (Constraint C)) (h : candidates ≠ [])

/-- `ofPerm con r candidates` is the tableau of a fixed constraint set `con : CON C n` under a
ranking `r : Ranking n`. Priority position `p` reads constraint `r p`, so coordinate `0` of the
lexicographic profile is the most dominant constraint. Candidates are deduplicated via
`List.toFinset`. -/
def ofPerm (h : candidates ≠ [] := by first | decide | simp) : Tableau C n where
  candidates := candidates.toFinset
  profile c := buildViolationProfile (fun p => con (r p)) c
  nonempty := (candidates.exists_mem_of_ne_nil h).imp fun _ ha => List.mem_toFinset.mpr ha

/-- Build a `Tableau C ranking.length` from a candidate list and a ranked constraint
list, list order being priority (position `0` most dominant): `Tableau.ofPerm` under the
identity ranking. Study files use this as
`(Tableau.ofRanking candidates ranking h).optimal = {.winner}`. -/
def ofRanking (h : candidates ≠ [] := by first | decide | simp) : Tableau C ranking.length :=
  ofPerm ranking.get (Equiv.refl _) candidates h

/-- Build a `Tableau C ranking.length` whose candidates are every inhabitant of the finite
type `C` — the form for a candidate type that enumerates exactly the candidate set. -/
def ofFintype [Fintype C] [Nonempty C] : Tableau C ranking.length where
  candidates := Finset.univ
  profile c := buildViolationProfile ranking.get c
  nonempty := Finset.univ_nonempty

/-- Build a tableau from a constraint order — labels `L`, most dominant first — and each
candidate's violation marks by label, as a paper's tableau is printed: `order` is its column
order and `marks c l` the cell. Candidates are every inhabitant of `C`. -/
def ofOrder {L : Type*} (order : List L) (marks : C → L → ℕ) [Fintype C] [Nonempty C] :
    Tableau C order.length where
  candidates := Finset.univ
  profile c := buildViolationProfile (fun p _ => marks c (order.get p)) c
  nonempty := Finset.univ_nonempty

@[simp] theorem ofPerm_candidates :
    (ofPerm con r candidates h).candidates = candidates.toFinset := rfl

@[simp] theorem ofPerm_profile (c : C) :
    (ofPerm con r candidates h).profile c = buildViolationProfile (fun p => con (r p)) c := rfl

@[simp] theorem ofRanking_candidates :
    (ofRanking candidates ranking h).candidates = candidates.toFinset := rfl

@[simp] theorem ofRanking_profile (c : C) :
    (ofRanking candidates ranking h).profile c = buildViolationProfile ranking.get c := rfl

@[simp] theorem ofFintype_candidates [Fintype C] [Nonempty C] :
    (ofFintype ranking).candidates = (Finset.univ : Finset C) := rfl

@[simp] theorem ofFintype_profile [Fintype C] [Nonempty C] (c : C) :
    (ofFintype ranking).profile c = buildViolationProfile ranking.get c := rfl

@[simp] theorem ofOrder_candidates {L : Type*} (order : List L) (marks : C → L → ℕ)
    [Fintype C] [Nonempty C] : (ofOrder order marks).candidates = (Finset.univ : Finset C) := rfl

@[simp] theorem ofOrder_profile {L : Type*} (order : List L) (marks : C → L → ℕ)
    [Fintype C] [Nonempty C] (c : C) (p : Fin order.length) :
    (ofOrder order marks).profile c p = marks c (order.get p) := rfl

variable {con r candidates ranking h}

/-- Candidates in `(Tableau.ofRanking ...).optimal` belong to the original list. -/
theorem ofRanking_optimal_mem (hc : c ∈ (ofRanking candidates ranking h).optimal) :
    c ∈ candidates := List.mem_toFinset.mp (optimal_subset hc)

/-- Candidates in `(Tableau.ofPerm ...).optimal` belong to the original list. -/
theorem ofPerm_optimal_mem (hc : c ∈ (ofPerm con r candidates h).optimal) :
    c ∈ candidates := List.mem_toFinset.mp (optimal_subset hc)

/-- Under a ranking, one candidate beats another iff the most dominant constraint that
distinguishes them prefers it. -/
theorem ofPerm_profile_lt_iff {d : C} :
    (ofPerm con r candidates h).profile c < (ofPerm con r candidates h).profile d ↔
      ∃ i, (∀ j, r.Dominates j i → con j c = con j d) ∧ con i c < con i d :=
  ⟨fun ⟨p, hp, hlt⟩ ↦ ⟨r p, fun j hj ↦ by
      simpa using hp (r.symm j) (by simpa [Ranking.Dominates] using hj), hlt⟩,
    fun ⟨i, hi, hlt⟩ ↦ ⟨r.symm i, fun q hq ↦ hi (r q) (by simpa [Ranking.Dominates] using hq),
      by simpa using hlt⟩⟩

/-- One candidate beats another iff some constraint preferring it dominates every constraint
preferring the other, which is the elementary ranking condition. -/
theorem ofPerm_profile_lt_iff_exists_dominates {d : C} :
    (ofPerm con r candidates h).profile c < (ofPerm con r candidates h).profile d ↔
      ∃ i, con i c < con i d ∧ ∀ j, con j d < con j c → r.Dominates i j := by
  refine ⟨fun hlt ↦ ?_, fun ⟨i, hi, hd⟩ ↦ ?_⟩
  · obtain ⟨i, hi, hlt⟩ := ofPerm_profile_lt_iff.1 hlt
    refine ⟨i, hlt, fun j hj ↦ ?_⟩
    rcases lt_trichotomy (r.symm i) (r.symm j) with h | h | h
    · exact h
    · obtain rfl := r.symm.injective h
      exact absurd hj hlt.asymm
    · exact absurd (hi j h) hj.ne'
  · refine lt_of_le_of_ne (not_lt.1 fun hlt ↦ ?_) fun heq ↦ ?_
    · obtain ⟨j, hj, hlt⟩ := ofPerm_profile_lt_iff.1 hlt
      exact absurd (hj i (hd j hlt)) hi.ne'
    · exact hi.ne (by simpa using congrArg (· (r.symm i)) heq)

/-- A candidate is the sole winner under a ranking iff, against each competitor, some
constraint preferring it dominates every constraint preferring the competitor. -/
theorem ofPerm_optimal_eq_singleton_iff (hc : c ∈ candidates) :
    (ofPerm con r candidates h).optimal = {c} ↔
      ∀ d ∈ candidates, d ≠ c →
        ∃ i, con i c < con i d ∧ ∀ j, con j d < con j c → r.Dominates i j := by
  rw [optimal_eq_singleton_iff (List.mem_toFinset.2 hc)]
  simp only [ofPerm_candidates, List.mem_toFinset, ofPerm_profile_lt_iff_exists_dominates]

/-- A candidate that beats another pointwise on the constraint set beats it under every
ranking of the set. -/
theorem ofPerm_profile_lt_of_lt {d : C} (hlt : (con · c) < (con · d)) :
    (ofPerm con r candidates h).profile c < (ofPerm con r candidates h).profile d :=
  Pi.toLex_strictMono <| by
    obtain ⟨hle, i, hi⟩ := Pi.lt_def.1 hlt
    exact Pi.lt_def.2 ⟨fun p ↦ hle (r p), r.symm i, by simpa using hi⟩

/-- A candidate beaten pointwise on the constraint set by a competitor is harmonically bounded,
that is, optimal under no ranking of the set. -/
theorem ofPerm_notMem_optimal_of_lt {d : C} (hc : c ∈ candidates)
    (hlt : (con · c) < (con · d)) : d ∉ (ofPerm con r candidates h).optimal :=
  notMem_optimal_of_lt (List.mem_toFinset.2 hc) (ofPerm_profile_lt_of_lt hlt)

/-- A candidate that harmonically bounds every competitor is the sole winner under every
ranking of the constraint set. -/
theorem ofPerm_optimal_eq_singleton_of_forall_lt (hc : c ∈ candidates)
    (hlt : ∀ d ∈ candidates, d ≠ c → (con · c) < (con · d)) :
    (ofPerm con r candidates h).optimal = {c} :=
  (optimal_eq_singleton_iff (List.mem_toFinset.2 hc)).2 fun d hd hne ↦
    ofPerm_profile_lt_of_lt (hlt d (List.mem_toFinset.1 hd) hne)

/-- A candidate beats a competitor under a ranking that puts a constraint preferring it on
top. -/
theorem ofPerm_profile_lt_of_forall_dominates {d : C} {i : Fin n} (hi : con i c < con i d)
    (hr : ∀ j, j ≠ i → r.Dominates i j) :
    (ofPerm con r candidates h).profile c < (ofPerm con r candidates h).profile d :=
  ofPerm_profile_lt_iff_exists_dominates.2 ⟨i, hi, fun j hj ↦ hr j fun hji ↦ (hji ▸ hj).asymm hi⟩

/-- A candidate that some constraint prefers to a competitor beats it under some ranking, the
converse of harmonic bounding for a pair. -/
theorem exists_ofPerm_profile_lt {d : C} {i : Fin n} (hi : con i c < con i d) :
    ∃ r : Ranking n,
      (ofPerm con r candidates h).profile c < (ofPerm con r candidates h).profile d :=
  (Ranking.exists_forall_dominates i).imp fun _ hr ↦ ofPerm_profile_lt_of_forall_dominates hi hr

/-! ### Top-constraint optimality -/

/-- If any candidate has `0` violations on the top-ranked constraint, every optimal
candidate has `0` violations on it — constraint dominance: a satisfiable constraint
promoted to the top of the ranking forces all winners to satisfy it perfectly. -/
theorem ofRanking_optimal_zero_first (top : Constraint C) (rest : List (Constraint C))
    (hExists : ∃ c₀ ∈ candidates, top c₀ = 0)
    (hc : c ∈ (ofRanking candidates (top :: rest) h).optimal) : top c = 0 := by
  obtain ⟨c₀, hmem, h0⟩ := hExists
  simpa [h0] using
    ViolationProfile.le_apply_zero (le_of_mem_optimal hc (List.mem_toFinset.mpr hmem))

/-- A candidate with `0` violations on every constraint of `con` is optimal in
`Tableau.ofPerm con r` under every ranking `r`, since permuting the coordinates of the
all-zero profile leaves it zero. -/
theorem ofPerm_zero_mem_optimal (hc : c ∈ candidates) (hzero : ∀ i, con i c = 0) :
    c ∈ (ofPerm con r candidates h).optimal :=
  mem_optimal_of_profile_eq_zero (List.mem_toFinset.mpr hc) (funext fun p => hzero (r p))

/-- The list form of `ofPerm_zero_mem_optimal`. -/
theorem ofRanking_zero_mem_optimal (hc : c ∈ candidates) (hzero : ∀ con ∈ ranking, con c = 0) :
    c ∈ (ofRanking candidates ranking h).optimal :=
  ofPerm_zero_mem_optimal hc fun i => hzero _ (ranking.get_mem i)

/-- A candidate with `0` violations on every constraint is optimal under **every**
permutation of those constraints — the structural backbone of `adj_always_initial` in
[marco-rasin-2026]: the uniform-initial adjective paradigm has `[0, …, 0]` on all OP
constraints, so it wins regardless of ranking. -/
theorem ofRanking_zero_mem_optimal_allRankings {constraints : List (Constraint C)}
    (hc : c ∈ candidates) (hzero : ∀ con ∈ constraints, con c = 0)
    {rk : List (Constraint C)} (hrk : rk ∈ constraints.permutations') :
    c ∈ (ofRanking candidates rk h).optimal :=
  ofRanking_zero_mem_optimal hc fun con hcon =>
    hzero con ((List.mem_permutations'.mp hrk).subset hcon)

end Tableau

/-! ### Factorial typology -/

variable {C : Type*} [DecidableEq C]

/-- For each ranking of `constraints` — a permutation, via `List.permutations'`, which
unlike `List.permutations` reduces under `decide` — the set of optimal candidates;
deduplicated. The number of distinct sets is the number of language types the constraint
set predicts. -/
def factorialOptima (candidates : List C) (constraints : List (Constraint C))
    (h : candidates ≠ [] := by decide) : List (Finset C) :=
  (constraints.permutations'.map fun ranking =>
    (Tableau.ofRanking candidates ranking h).optimal).eraseDups

/-- The number of distinct language types predicted by the factorial typology. -/
def factorialTypologySize (candidates : List C) (constraints : List (Constraint C))
    (h : candidates ≠ [] := by decide) : ℕ :=
  (factorialOptima candidates constraints h).length

end OptimalityTheory
