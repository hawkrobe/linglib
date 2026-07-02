import Linglib.Core.Optimization.Evaluation
import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.Constraints.Profile
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.Permutation

/-!
# Tableaux

The OT evaluation vocabulary and machinery. A `Tableau` is the lexicographic
minimisation problem [prince-smolensky-1993] solves — a finite candidate set ranked by a
`ViolationProfile`-valued objective. These are OT-tradition names for the
`LexMinProblem` engine in `Core.Optimization.Evaluation`; downstream OT code uses
`Tableau`/`Tableau.optimal` rather than the generic spellings. On top of the vocabulary:
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
* `factorialOptima` / `factorialTypologySize` — the distinct optimal sets predicted
  across all rankings, and their count.

## Main results

* `Tableau.exists_optimal` / `Tableau.optimal_nonempty` / `mem_optimal_iff` /
  `optimal_subset` — winners exist; membership facts.
* `Tableau.optimal_eq_singleton_iff` — sole winner ⟺ strict domination.
* `ofPerm_zero_isOptimal` / `Tableau.ofRanking_zero_isOptimal` /
  `Tableau.ofRanking_zero_optimal_allRankings` — a candidate with no violations wins
  under any (every) ranking.
* `Tableau.ofRanking_isOptimal_zero_first` — a satisfiable top constraint forces all
  winners to satisfy it.
-/

namespace OptimalityTheory

open Core.Optimization.Evaluation LexMinProblem Constraints

/-! ### The tableau vocabulary -/

/-- A constraint ranking: a permutation of `Fin n` ([prince-2002]'s total domination
order `≫`). `r i` is the constraint at rank position `i` (position `0` is most
dominant); `r.symm k` is the rank position of `k`. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)

/-- OT-named alias for `LexMinProblem` — a finite candidate set ranked by a
fixed-length violation profile. -/
abbrev Tableau (C : Type*) [DecidableEq C] (n : Nat) := LexMinProblem C n

namespace Tableau

variable {C : Type*} [DecidableEq C] {n : Nat} (t : Tableau C n) (c : C)

/-- OT-named alias for `LexMinProblem.lexMins` — the winning candidates. Optimality is
plain membership `c ∈ t.optimal`, unfolded by `mem_optimal_iff`; there is no separate
winner predicate. -/
abbrev optimal : Finset C := lexMins t

/-- Membership in the winner set, unfolded: a winner is a candidate whose profile
lexicographically bounds the whole tableau. -/
theorem mem_optimal_iff :
    c ∈ t.optimal ↔ c ∈ t.candidates ∧ ∀ d ∈ t.candidates, t.profile c ≤ t.profile d :=
  mem_lexMins_iff t c

/-- OT-named alias for `LexMinProblem.lexMins_nonempty`. -/
theorem optimal_nonempty : t.optimal.Nonempty := lexMins_nonempty t

/-- OT-named alias for `LexMinProblem.lexMins_subset`. -/
theorem optimal_subset : c ∈ t.optimal → c ∈ t.candidates :=
  lexMins_subset t c

/-- A winner's profile bounds every candidate's. -/
theorem le_of_mem_optimal {d : C} (hc : c ∈ t.optimal) (hd : d ∈ t.candidates) :
    t.profile c ≤ t.profile d :=
  ((mem_optimal_iff t c).mp hc).2 d hd

/-- Optimality factors through the profile, so it transports along profile equality:
scoring like a winner is winning. -/
theorem mem_optimal_of_profile_eq {d : C} (hd : d ∈ t.optimal) (hc : c ∈ t.candidates)
    (he : t.profile c = t.profile d) : c ∈ t.optimal :=
  (mem_optimal_iff t c).mpr ⟨hc, fun e he' => he ▸ le_of_mem_optimal t d hd he'⟩

/-- A candidate whose profile vanishes wins: `0` is the global lex-minimum. -/
theorem mem_optimal_of_profile_eq_zero (hc : c ∈ t.candidates) (h0 : t.profile c = 0) :
    c ∈ t.optimal :=
  (mem_optimal_iff t c).mpr ⟨hc, fun d _ => h0 ▸ ViolationProfile.zero_le _⟩

/-- A tableau has sole winner `m` iff `m` strictly lex-dominates every other
candidate. -/
theorem optimal_eq_singleton_iff {m : C} (hm : m ∈ t.candidates) :
    t.optimal = {m} ↔ ∀ c ∈ t.candidates, c ≠ m → t.profile m < t.profile c := by
  constructor
  · intro h c hc hcm
    have hmo : m ∈ t.optimal := h ▸ Finset.mem_singleton_self m
    exact (le_of_mem_optimal t m hmo hc).lt_of_ne fun he => hcm <| Finset.mem_singleton.mp
      (h ▸ mem_optimal_of_profile_eq t c hmo hc he.symm)
  · intro h
    refine Finset.eq_singleton_iff_unique_mem.mpr
      ⟨(mem_optimal_iff t m).mpr ⟨hm, fun d hd => ?_⟩, fun c hc => ?_⟩
    · rcases eq_or_ne d m with rfl | hdm
      · exact le_rfl
      · exact (h d hd hdm).le
    · by_contra hcm
      exact absurd (le_of_mem_optimal t c hc hm)
        (not_le.mpr (h c (optimal_subset t c hc) hcm))

/-! ### Tableau constructors -/

variable (con : CON C n) (r : Ranking n) (candidates : List C)
  (ranking : List (Constraint C)) (h : candidates ≠ [])

/-- Build a `Tableau C n` from a fixed constraint set `con : CON C n` under a ranking
`r : Ranking n`: priority position `p` reads constraint `r p`, so coordinate `0` of the
lexicographic profile is the most dominant constraint. Candidates are deduplicated via
`List.toFinset`. -/
def ofPerm (h : candidates ≠ [] := by decide) : Tableau C n where
  candidates := candidates.toFinset
  profile c := buildViolationProfile (fun p => con (r p)) c
  nonempty := (candidates.exists_mem_of_ne_nil h).imp fun _ ha => List.mem_toFinset.mpr ha

/-- Build a `Tableau C ranking.length` from a candidate list and a ranked constraint
list, list order being priority (position `0` most dominant): `Tableau.ofPerm` under the
identity ranking. Study files use this as
`(Tableau.ofRanking candidates ranking h).optimal = {.winner}`. -/
def ofRanking (h : candidates ≠ [] := by decide) : Tableau C ranking.length :=
  ofPerm ranking.get (Equiv.refl _) candidates h

@[simp] theorem ofPerm_candidates :
    (Tableau.ofPerm con r candidates h).candidates = candidates.toFinset := rfl

@[simp] theorem ofPerm_profile (c : C) :
    (Tableau.ofPerm con r candidates h).profile c
      = buildViolationProfile (fun p => con (r p)) c := rfl

@[simp] theorem ofRanking_candidates :
    (Tableau.ofRanking candidates ranking h).candidates = candidates.toFinset := rfl

@[simp] theorem ofRanking_profile (c : C) :
    (Tableau.ofRanking candidates ranking h).profile c
      = buildViolationProfile ranking.get c := rfl

/-- Candidates in `(Tableau.ofRanking ...).optimal` belong to the original list. -/
theorem ofRanking_optimal_mem
    (hc : c ∈ (ofRanking candidates ranking h).optimal) : c ∈ candidates :=
  List.mem_toFinset.mp (optimal_subset _ c hc)

/-- Candidates in `(Tableau.ofPerm ...).optimal` belong to the original list. -/
theorem ofPerm_optimal_mem
    (hc : c ∈ (ofPerm con r candidates h).optimal) : c ∈ candidates :=
  List.mem_toFinset.mp (optimal_subset _ c hc)

/-! ### Top-constraint optimality -/

/-- If any candidate has `0` violations on the top-ranked constraint, every optimal
candidate has `0` violations on it — constraint dominance: a satisfiable constraint
promoted to the top of the ranking forces all winners to satisfy it perfectly. -/
theorem ofRanking_optimal_zero_first (con : Constraint C) (rest : List (Constraint C))
    (hExists : ∃ c₀ ∈ candidates, con c₀ = 0)
    (hc : c ∈ (ofRanking candidates (con :: rest) h).optimal) : con c = 0 := by
  obtain ⟨c₀, hmem, h0⟩ := hExists
  have hle := ViolationProfile.le_apply_zero
    (le_of_mem_optimal _ _ hc (List.mem_toFinset.mpr hmem))
  change con c ≤ con c₀ at hle
  omega

/-- A candidate with `0` violations on every constraint of `con` is optimal in
`Tableau.ofPerm con r` under **every** ranking `r`: permuting the coordinates of the
all-zero profile leaves it zero. -/
theorem ofPerm_zero_mem_optimal (hc : c ∈ candidates) (hzero : ∀ i, con i c = 0) :
    c ∈ (ofPerm con r candidates h).optimal :=
  mem_optimal_of_profile_eq_zero _ _ (List.mem_toFinset.mpr hc)
    (funext fun p => hzero (r p))

/-- The list form of `ofPerm_zero_mem_optimal`. -/
theorem ofRanking_zero_mem_optimal (hc : c ∈ candidates)
    (hzero : ∀ con ∈ ranking, con c = 0) :
    c ∈ (ofRanking candidates ranking h).optimal :=
  ofPerm_zero_mem_optimal _ _ _ _ h hc fun i => hzero _ (ranking.get_mem i)

/-- A candidate with `0` violations on every constraint is optimal under **every**
permutation of those constraints — the structural backbone of `adj_always_initial` in
[marco-rasin-2026]: the uniform-initial adjective paradigm has `[0, …, 0]` on all OP
constraints, so it wins regardless of ranking. -/
theorem ofRanking_zero_mem_optimal_allRankings (constraints : List (Constraint C))
    (hc : c ∈ candidates) (hzero : ∀ con ∈ constraints, con c = 0)
    {rk : List (Constraint C)} (hrk : rk ∈ constraints.permutations') :
    c ∈ (ofRanking candidates rk h).optimal :=
  ofRanking_zero_mem_optimal _ _ _ h hc fun con hcon =>
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
