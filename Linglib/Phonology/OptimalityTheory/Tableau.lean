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

* `Tableau.exists_optimal` / `Tableau.optimal_nonempty` / `Tableau.mem_optimal_iff` /
  `Tableau.optimal_subset` — winners exist; membership facts.
* `Tableau.optimal_eq_singleton_iff` — sole winner ⟺ strict domination.
* `Tableau.ofPerm_zero_isOptimal` / `Tableau.ofRanking_zero_isOptimal` /
  `Tableau.ofRanking_zero_optimal_allRankings` — a candidate with no violations wins
  under any (every) ranking.
* `Tableau.ofRanking_isOptimal_zero_first` — a satisfiable top constraint forces all
  winners to satisfy it.
-/

namespace OptimalityTheory


open Core.Optimization.Evaluation
/-! ### The tableau vocabulary -/

/-- OT-named alias for `LexMinProblem` — a finite candidate set ranked by a
fixed-length violation profile. -/
abbrev Tableau (C : Type*) [DecidableEq C] (n : Nat) := LexMinProblem C n

variable {C : Type*} [DecidableEq C] {n : Nat}

/-- OT-named alias for `LexMinProblem.IsLexMin` — `c` is a lexicographic
winner of `t`. -/
abbrev Tableau.IsOptimal (t : Tableau C n) (c : C) : Prop :=
  LexMinProblem.IsLexMin t c

/-- OT-named alias for `LexMinProblem.lexMins` — the winning candidates. -/
abbrev Tableau.optimal (t : Tableau C n) : Finset C :=
  LexMinProblem.lexMins t

/-- OT-named alias for `LexMinProblem.exists_lexMin`. -/
theorem Tableau.exists_optimal (t : Tableau C n) : ∃ c, t.IsOptimal c :=
  LexMinProblem.exists_lexMin t

/-- OT-named alias for `LexMinProblem.mem_lexMins_iff`. -/
theorem Tableau.mem_optimal_iff (t : Tableau C n) (c : C) :
    c ∈ t.optimal ↔ t.IsOptimal c :=
  LexMinProblem.mem_lexMins_iff t c

/-- OT-named alias for `LexMinProblem.lexMins_nonempty`. -/
theorem Tableau.optimal_nonempty (t : Tableau C n) : t.optimal.Nonempty :=
  LexMinProblem.lexMins_nonempty t

/-- OT-named alias for `LexMinProblem.lexMins_subset`. -/
theorem Tableau.optimal_subset (t : Tableau C n) (c : C) :
    c ∈ t.optimal → c ∈ t.candidates :=
  LexMinProblem.lexMins_subset t c

/-- A tableau has sole winner `m` iff `m` strictly lex-dominates every other
candidate. -/
theorem Tableau.optimal_eq_singleton_iff (t : Tableau C n) {m : C}
    (hm : m ∈ t.candidates) :
    t.optimal = {m} ↔ ∀ c ∈ t.candidates, c ≠ m → t.profile m < t.profile c := by
  constructor
  · intro h c hc hcm
    have hmin : ∀ d ∈ t.candidates, t.profile m ≤ t.profile d :=
      ((t.mem_optimal_iff m).mp (h ▸ Finset.mem_singleton_self m)).2
    rcases lt_or_eq_of_le (hmin c hc) with hlt | heq
    · exact hlt
    · exact absurd (Finset.mem_singleton.mp (h ▸ (t.mem_optimal_iff c).mpr
        ⟨hc, fun d hd => heq ▸ hmin d hd⟩)) hcm
  · intro h
    refine Finset.eq_singleton_iff_unique_mem.mpr
      ⟨(t.mem_optimal_iff m).mpr ⟨hm, fun d hd => ?_⟩, fun c hc => ?_⟩
    · rcases eq_or_ne d m with rfl | hdm
      · exact le_refl _
      · exact (h d hd hdm).le
    · by_contra hcm
      exact absurd ((h c ((t.mem_optimal_iff c).mp hc).1 hcm).trans_le
        (((t.mem_optimal_iff c).mp hc).2 m hm)) (lt_irrefl _)

/-- A constraint ranking: a permutation of `Fin n` ([prince-2002]'s total
domination order `≫`). `r i` is the constraint at rank position `i` (position
`0` is most dominant); `r.symm k` is the rank position of `k`. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)


open Constraints

variable {C : Type*} [DecidableEq C] {n : ℕ}

/-! ### Tableau constructors -/

/-- Build a `Tableau C n` from a fixed constraint set `con : CON C n` under a ranking
`r : Ranking n`: priority position `p` reads constraint `r p`, so coordinate `0` of the
lexicographic profile is the most dominant constraint. Candidates are deduplicated via
`List.toFinset`. -/
def Tableau.ofPerm (con : CON C n) (r : Ranking n) (candidates : List C)
    (h : candidates ≠ [] := by decide) : Tableau C n where
  candidates := candidates.toFinset
  profile c := buildViolationProfile (fun p => con (r p)) c
  nonempty := (candidates.exists_mem_of_ne_nil h).imp fun _ ha => List.mem_toFinset.mpr ha

/-- Build a `Tableau C ranking.length` from a candidate list and a ranked constraint
list, list order being priority (position `0` most dominant): `Tableau.ofPerm` under the
identity ranking. Study files use this as
`(Tableau.ofRanking candidates ranking h).optimal = {.winner}`. -/
def Tableau.ofRanking (candidates : List C) (ranking : List (Constraint C))
    (h : candidates ≠ [] := by decide) : Tableau C ranking.length :=
  Tableau.ofPerm ranking.get (Equiv.refl _) candidates h

variable (con : CON C n) (r : Ranking n) (candidates : List C)
  (ranking constraints : List (Constraint C)) (h : candidates ≠ [])

@[simp] theorem Tableau.ofPerm_candidates :
    (Tableau.ofPerm con r candidates h).candidates = candidates.toFinset := rfl

@[simp] theorem Tableau.ofPerm_profile (c : C) :
    (Tableau.ofPerm con r candidates h).profile c
      = buildViolationProfile (fun p => con (r p)) c := rfl

@[simp] theorem Tableau.ofRanking_candidates :
    (Tableau.ofRanking candidates ranking h).candidates = candidates.toFinset := rfl

@[simp] theorem Tableau.ofRanking_profile (c : C) :
    (Tableau.ofRanking candidates ranking h).profile c
      = buildViolationProfile ranking.get c := rfl

/-- Candidates in `(Tableau.ofRanking ...).optimal` belong to the original list. -/
theorem Tableau.ofRanking_optimal_mem (c : C)
    (hc : c ∈ (Tableau.ofRanking candidates ranking h).optimal) : c ∈ candidates :=
  List.mem_toFinset.mp (Tableau.optimal_subset _ c hc)

/-! ### Top-constraint optimality -/

/-- If any candidate has `0` violations on the top-ranked constraint, every optimal
candidate has `0` violations on it — constraint dominance: a satisfiable constraint
promoted to the top of the ranking forces all winners to satisfy it perfectly. -/
theorem Tableau.ofRanking_isOptimal_zero_first (candidates : List C) (con : Constraint C)
    (rest : List (Constraint C)) (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con c₀ = 0) (c : C)
    (hc : (Tableau.ofRanking candidates (con :: rest) h).IsOptimal c) : con c = 0 := by
  obtain ⟨c₀, hc₀_mem, hc₀_zero⟩ := hExists
  have h0 := ViolationProfile.le_apply_zero (hc.2 c₀ (List.mem_toFinset.mpr hc₀_mem))
  change con c ≤ con c₀ at h0
  omega

/-- `∈ .optimal` version of `Tableau.ofRanking_isOptimal_zero_first`. -/
theorem Tableau.ofRanking_optimal_zero_first (candidates : List C) (con : Constraint C)
    (rest : List (Constraint C)) (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con c₀ = 0) (c : C)
    (hc : c ∈ (Tableau.ofRanking candidates (con :: rest) h).optimal) : con c = 0 :=
  Tableau.ofRanking_isOptimal_zero_first candidates con rest h hExists c
    ((Tableau.mem_optimal_iff _ c).mp hc)

/-- A candidate with `0` violations on every constraint of `con` is optimal in
`Tableau.ofPerm con r` under **every** ranking `r`: permuting the coordinates of the
all-zero profile leaves it zero. -/
theorem Tableau.ofPerm_zero_isOptimal (c : C) (hc : c ∈ candidates)
    (hzero : ∀ i, con i c = 0) :
    c ∈ (Tableau.ofPerm con r candidates h).optimal := by
  rw [Tableau.mem_optimal_iff]
  refine ⟨List.mem_toFinset.mpr hc, fun c' _ => ?_⟩
  suffices hsuff : (Tableau.ofPerm con r candidates h).profile c = 0 by
    rw [hsuff]; exact ViolationProfile.zero_le _
  rw [Tableau.ofPerm_profile]
  funext p
  exact hzero (r p)

/-- The list form of `Tableau.ofPerm_zero_isOptimal`. -/
theorem Tableau.ofRanking_zero_isOptimal (c : C) (hc : c ∈ candidates)
    (hzero : ∀ con ∈ ranking, con c = 0) :
    c ∈ (Tableau.ofRanking candidates ranking h).optimal :=
  Tableau.ofPerm_zero_isOptimal _ _ candidates h c hc fun i => hzero _ (ranking.get_mem i)

/-- A candidate with `0` violations on every constraint is optimal under **every**
permutation of those constraints — the structural backbone of `adj_always_initial` in
[marco-rasin-2026]: the uniform-initial adjective paradigm has `[0, …, 0]` on all OP
constraints, so it wins regardless of ranking. -/
theorem Tableau.ofRanking_zero_optimal_allRankings (c : C) (hc : c ∈ candidates)
    (hzero : ∀ con ∈ constraints, con c = 0) {rk : List (Constraint C)}
    (hrk : rk ∈ constraints.permutations') :
    c ∈ (Tableau.ofRanking candidates rk h).optimal :=
  Tableau.ofRanking_zero_isOptimal candidates rk h c hc fun con hcon =>
    hzero con ((List.mem_permutations'.mp hrk).subset hcon)

/-! ### Factorial typology -/

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
