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
* `Tableau.IsOptimal` / `Tableau.optimal` — the winner predicate and the winner set.
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

open Core.Optimization.Evaluation Constraints

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

/-- OT-named alias for `LexMinProblem.IsLexMin` — `c` is a lexicographic
winner of `t`. -/
abbrev IsOptimal : Prop := LexMinProblem.IsLexMin t c

/-- OT-named alias for `LexMinProblem.lexMins` — the winning candidates. -/
abbrev optimal : Finset C := LexMinProblem.lexMins t

/-- OT-named alias for `LexMinProblem.exists_lexMin`. -/
theorem exists_optimal : ∃ c, t.IsOptimal c := LexMinProblem.exists_lexMin t

/-- OT-named alias for `LexMinProblem.mem_lexMins_iff`. -/
theorem mem_optimal_iff : c ∈ t.optimal ↔ t.IsOptimal c :=
  LexMinProblem.mem_lexMins_iff t c

/-- OT-named alias for `LexMinProblem.lexMins_nonempty`. -/
theorem optimal_nonempty : t.optimal.Nonempty := LexMinProblem.lexMins_nonempty t

/-- OT-named alias for `LexMinProblem.lexMins_subset`. -/
theorem optimal_subset : c ∈ t.optimal → c ∈ t.candidates :=
  LexMinProblem.lexMins_subset t c

/-- A tableau has sole winner `m` iff `m` strictly lex-dominates every other
candidate. -/
theorem optimal_eq_singleton_iff {m : C} (hm : m ∈ t.candidates) :
    t.optimal = {m} ↔ ∀ c ∈ t.candidates, c ≠ m → t.profile m < t.profile c := by
  simp only [Finset.eq_singleton_iff_unique_mem, mem_optimal_iff]
  refine ⟨fun ⟨⟨_, hmin⟩, huniq⟩ c hc hcm => (hmin c hc).lt_of_ne fun he =>
      hcm (huniq c ⟨hc, fun d hd => he ▸ hmin d hd⟩),
    fun h => ⟨⟨hm, fun d hd => (eq_or_ne d m).elim (· ▸ le_rfl) fun hdm => (h d hd hdm).le⟩,
      fun c ⟨hc, hcmin⟩ => of_not_not fun hcm => not_le.mpr (h c hc hcm) (hcmin m hm)⟩⟩

/-! ### Tableau constructors -/

/-- Build a `Tableau C n` from a fixed constraint set `con : CON C n` under a ranking
`r : Ranking n`: priority position `p` reads constraint `r p`, so coordinate `0` of the
lexicographic profile is the most dominant constraint. Candidates are deduplicated via
`List.toFinset`. -/
def ofPerm (con : CON C n) (r : Ranking n) (candidates : List C)
    (h : candidates ≠ [] := by decide) : Tableau C n where
  candidates := candidates.toFinset
  profile c := buildViolationProfile (fun p => con (r p)) c
  nonempty := (candidates.exists_mem_of_ne_nil h).imp fun _ ha => List.mem_toFinset.mpr ha

/-- Build a `Tableau C ranking.length` from a candidate list and a ranked constraint
list, list order being priority (position `0` most dominant): `Tableau.ofPerm` under the
identity ranking. Study files use this as
`(Tableau.ofRanking candidates ranking h).optimal = {.winner}`. -/
def ofRanking (candidates : List C) (ranking : List (Constraint C))
    (h : candidates ≠ [] := by decide) : Tableau C ranking.length :=
  Tableau.ofPerm ranking.get (Equiv.refl _) candidates h

variable (con : CON C n) (r : Ranking n) (candidates : List C)
  (ranking constraints : List (Constraint C)) (h : candidates ≠ [])

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
theorem ofRanking_optimal_mem (c : C)
    (hc : c ∈ (Tableau.ofRanking candidates ranking h).optimal) : c ∈ candidates :=
  List.mem_toFinset.mp (optimal_subset _ c hc)

/-- Candidates in `(Tableau.ofPerm ...).optimal` belong to the original list. -/
theorem ofPerm_optimal_mem (c : C)
    (hc : c ∈ (ofPerm con r candidates h).optimal) : c ∈ candidates :=
  List.mem_toFinset.mp (optimal_subset _ c hc)

/-! ### Top-constraint optimality -/

/-- If any candidate has `0` violations on the top-ranked constraint, every optimal
candidate has `0` violations on it — constraint dominance: a satisfiable constraint
promoted to the top of the ranking forces all winners to satisfy it perfectly. -/
theorem ofRanking_isOptimal_zero_first (candidates : List C) (con : Constraint C)
    (rest : List (Constraint C)) (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con c₀ = 0) (c : C)
    (hc : (Tableau.ofRanking candidates (con :: rest) h).IsOptimal c) : con c = 0 := by
  obtain ⟨c₀, hc₀_mem, hc₀_zero⟩ := hExists
  have h0 := ViolationProfile.le_apply_zero (hc.2 c₀ (List.mem_toFinset.mpr hc₀_mem))
  change con c ≤ con c₀ at h0
  omega

/-- `∈ .optimal` version of `Tableau.ofRanking_isOptimal_zero_first`. -/
theorem ofRanking_optimal_zero_first (candidates : List C) (con : Constraint C)
    (rest : List (Constraint C)) (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con c₀ = 0) (c : C)
    (hc : c ∈ (Tableau.ofRanking candidates (con :: rest) h).optimal) : con c = 0 :=
  ofRanking_isOptimal_zero_first candidates con rest h hExists c
    ((mem_optimal_iff _ c).mp hc)

/-- A candidate with `0` violations on every constraint of `con` is optimal in
`Tableau.ofPerm con r` under **every** ranking `r`: permuting the coordinates of the
all-zero profile leaves it zero. -/
theorem ofPerm_zero_isOptimal (c : C) (hc : c ∈ candidates)
    (hzero : ∀ i, con i c = 0) :
    c ∈ (Tableau.ofPerm con r candidates h).optimal := by
  rw [mem_optimal_iff]
  refine ⟨List.mem_toFinset.mpr hc, fun c' _ => ?_⟩
  suffices hsuff : (Tableau.ofPerm con r candidates h).profile c = 0 by
    rw [hsuff]; exact ViolationProfile.zero_le _
  rw [ofPerm_profile]
  funext p
  exact hzero (r p)

/-- The list form of `ofPerm_zero_isOptimal`. -/
theorem ofRanking_zero_isOptimal (c : C) (hc : c ∈ candidates)
    (hzero : ∀ con ∈ ranking, con c = 0) :
    c ∈ (Tableau.ofRanking candidates ranking h).optimal :=
  ofPerm_zero_isOptimal _ _ candidates h c hc fun i => hzero _ (ranking.get_mem i)

/-- A candidate with `0` violations on every constraint is optimal under **every**
permutation of those constraints — the structural backbone of `adj_always_initial` in
[marco-rasin-2026]: the uniform-initial adjective paradigm has `[0, …, 0]` on all OP
constraints, so it wins regardless of ranking. -/
theorem ofRanking_zero_optimal_allRankings (c : C) (hc : c ∈ candidates)
    (hzero : ∀ con ∈ constraints, con c = 0) {rk : List (Constraint C)}
    (hrk : rk ∈ constraints.permutations') :
    c ∈ (Tableau.ofRanking candidates rk h).optimal :=
  ofRanking_zero_isOptimal candidates rk h c hc fun con hcon =>
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
