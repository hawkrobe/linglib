import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.Constraints.Profile
import Linglib.Phonology.OptimalityTheory.Defs
import Mathlib.Data.List.Permutation

/-!
# Tableau Construction and Factorial Typology

The OT evaluation machinery built on the `Tableau` type (`OptimalityTheory.Defs`)
and the violation-profile vocabulary (`Constraints.Profile`): smart constructors
for tableaux, the structural optimality theorems, and factorial-typology
computation.

## Main definitions

* `Tableau.ofRanking` — build a `Tableau` from a candidate list and a ranked
  constraint list (list order = priority, position `0` most dominant).
* `Tableau.ofPerm` — build a `Tableau` from a fixed constraint set `CON C n` under
  a ranking `r : Ranking n` (priority position `p` reads constraint `r p`); the
  `Equiv.Perm`-indexed form, definitionally the identity case of `ofRanking`.
* `mkFactorialOptima` / `mkFactorialTypologySize` — the distinct optimal sets
  predicted across all rankings (`List.permutations'`), and their count.

## Main results

* `Tableau.ofRanking_zero_isOptimal` / `Tableau.ofPerm_zero_isOptimal` /
  `Tableau.ofRanking_zero_optimal_allRankings` — a candidate with no violations
  wins under any (every) ranking.
* `Tableau.ofRanking_isOptimal_zero_first` — a satisfiable top constraint forces
  all winners to satisfy it.
-/

namespace OptimalityTheory

open Constraints

-- ============================================================================
-- § 1: Permutations (for factorial typology)
-- ============================================================================

variable {α : Type*}

/-- A permutation of `l` — an element of mathlib's `List.permutations'` (the
    structurally-recursive insert-everywhere enumeration that, unlike
    `List.permutations`, reduces under `decide`) — has the same elements as `l`.
    The factorial-typology layer ranges over `List.permutations'`; this lemma
    feeds the all-rankings optimality result. -/
theorem permutations_subset {l l' : List α} (hp : l' ∈ l.permutations') :
    ∀ x ∈ l', x ∈ l :=
  fun _ hx => (List.mem_permutations'.mp hp).mem_iff.mp hx

-- ============================================================================
-- § 2: Tableau Constructors
-- ============================================================================

variable {C : Type*} [DecidableEq C] {n : Nat}

/-- Build a `Tableau C ranking.length` from a candidate list and a ranked
    constraint list: list order is priority (position `0` most dominant).

    Candidates are deduplicated via `List.toFinset`; profiles are fixed-length
    `ViolationProfile` built via `buildViolationProfile`. Study files use this as
    `(Tableau.ofRanking candidates ranking h).optimal = {.winner}`. -/
def Tableau.ofRanking (candidates : List C)
    (ranking : List (Constraint C))
    (h : candidates ≠ [] := by decide) : Tableau C ranking.length :=
  { candidates := candidates.toFinset
    profile := fun c => buildViolationProfile
      (fun i => ranking.get i) c
    nonempty := by
      cases candidates with
      | nil => contradiction
      | cons a _ => exact ⟨a, by simp⟩ }

/-- Build a `Tableau C n` from a fixed constraint set `con : CON C n` under a
    ranking `r : Ranking n`: priority position `p` reads constraint `r p`, so
    coordinate `0` of the lexicographic profile is the most dominant constraint.
    The `Equiv.Perm`-indexed evaluation that the `ElementaryRankingCondition`
    apparatus (`tableauERC`, `ERC.SatisfiedBy`) ranges over. -/
def Tableau.ofPerm (con : CON C n) (r : Ranking n)
    (candidates : List C)
    (h : candidates ≠ [] := by decide) : Tableau C n :=
  { candidates := candidates.toFinset
    profile := fun c => buildViolationProfile (fun p => con (r p)) c
    nonempty := by
      cases candidates with
      | nil => contradiction
      | cons a _ => exact ⟨a, by simp⟩ }

/-- A list ranking is its own `CON` (via `List.get`) under the identity
    permutation: the two constructors agree, definitionally. -/
theorem Tableau.ofRanking_eq_ofPerm (candidates : List C)
    (ranking : List (Constraint C)) (h : candidates ≠ []) :
    Tableau.ofRanking candidates ranking h =
      Tableau.ofPerm (fun j => ranking.get j) (Equiv.refl _) candidates h := rfl

/-- Candidates in `(Tableau.ofRanking ...).optimal` belong to the original list. -/
theorem Tableau.ofRanking_optimal_mem
    (candidates : List C) (ranking : List (Constraint C))
    (h : candidates ≠ []) (c : C) :
    c ∈ (Tableau.ofRanking candidates ranking h).optimal → c ∈ candidates :=
  fun hc => List.mem_toFinset.mp (Tableau.optimal_subset _ c hc)

-- ============================================================================
-- § 3: Top-Constraint Optimality
-- ============================================================================

/-- If any candidate has 0 violations on the top-ranked constraint,
    then **every** optimal candidate has 0 violations on it.

    This is the structural backbone of constraint dominance: once a
    faithfulness constraint (like MxBM-C) is promoted to the top of
    the ranking, it forces all winners to satisfy it perfectly. Uses
    `ViolationProfile.le_apply_zero` to extract the first component
    of the lexicographic comparison. -/
theorem Tableau.ofRanking_isOptimal_zero_first
    (candidates : List C) (con : Constraint C)
    (rest : List (Constraint C))
    (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con c₀ = 0)
    : ∀ c, (Tableau.ofRanking candidates (con :: rest) h).IsOptimal c →
        con c = 0 := by
  intro c ⟨_, hc_all⟩
  obtain ⟨c₀, hc₀_mem, hc₀_zero⟩ := hExists
  have hle := hc_all c₀ (List.mem_toFinset.mpr hc₀_mem)
  have h0 := ViolationProfile.le_apply_zero hle
  -- h0 is definitionally: con c ≤ con c₀
  change con c ≤ con c₀ at h0
  rw [hc₀_zero] at h0
  exact Nat.le_zero.mp h0

/-- `∈ .optimal` version of `Tableau.ofRanking_isOptimal_zero_first`. -/
theorem Tableau.ofRanking_optimal_zero_first
    (candidates : List C) (con : Constraint C)
    (rest : List (Constraint C))
    (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con c₀ = 0)
    : ∀ c ∈ (Tableau.ofRanking candidates (con :: rest) h).optimal,
        con c = 0 :=
  fun c hc => Tableau.ofRanking_isOptimal_zero_first candidates con rest h hExists c
    ((Tableau.mem_optimal_iff _ c).mp hc)

/-- If a candidate in `Tableau.ofRanking` has 0 violations on every constraint,
    it is optimal. -/
theorem Tableau.ofRanking_zero_isOptimal
    (candidates : List C) (ranking : List (Constraint C))
    (h : candidates ≠ []) (c : C) (hc : c ∈ candidates)
    (hzero : ∀ con ∈ ranking, con c = 0) :
    c ∈ (Tableau.ofRanking candidates ranking h).optimal := by
  rw [Tableau.mem_optimal_iff]
  refine ⟨List.mem_toFinset.mpr hc, fun c' _ => ?_⟩
  suffices hsuff : (Tableau.ofRanking candidates ranking h).profile c = 0 by
    rw [hsuff]; exact ViolationProfile.zero_le _
  show buildViolationProfile (fun i => ranking.get i) c = 0
  funext i
  exact hzero (ranking.get i) (List.get_mem ranking i)

/-- If a candidate has 0 violations on every constraint in a set, it is
    optimal under **every** permutation of those constraints.

    The structural backbone of `adj_always_initial` in [marco-rasin-2026]: the
    uniform-initial adjective paradigm has [0,…,0] on all OP constraints, so it
    wins regardless of ranking. Reduces to `Tableau.ofRanking_zero_isOptimal`
    after `permutations_subset`. -/
theorem Tableau.ofRanking_zero_optimal_allRankings
    (candidates : List C) (constraints : List (Constraint C))
    (h : candidates ≠ []) (c : C) (hc : c ∈ candidates)
    (hzero : ∀ con ∈ constraints, con c = 0) :
    ∀ ranking ∈ constraints.permutations',
      c ∈ (Tableau.ofRanking candidates ranking h).optimal :=
  fun ranking hp => Tableau.ofRanking_zero_isOptimal candidates ranking h c hc
    (fun con hcon => hzero con (permutations_subset hp con hcon))

/-- The `Equiv.Perm`-indexed analogue: a candidate with 0 violations on every
    constraint of `con` is optimal in `Tableau.ofPerm con r` under **every**
    ranking `r` — permuting the coordinates of the all-zero profile leaves it
    zero. n-agnostic and enumeration-free (no `decide`). -/
theorem Tableau.ofPerm_zero_isOptimal
    (con : CON C n) (candidates : List C)
    (h : candidates ≠ []) (c : C) (hc : c ∈ candidates)
    (hzero : ∀ i, con i c = 0) (r : Ranking n) :
    c ∈ (Tableau.ofPerm con r candidates h).optimal := by
  rw [Tableau.mem_optimal_iff]
  refine ⟨List.mem_toFinset.mpr hc, fun c' _ => ?_⟩
  suffices hsuff : (Tableau.ofPerm con r candidates h).profile c = 0 by
    rw [hsuff]; exact ViolationProfile.zero_le _
  show buildViolationProfile (fun p => con (r p)) c = 0
  funext p
  exact hzero (r p)

-- ============================================================================
-- § 4: Factorial Typology
-- ============================================================================

/-- For each ranking (permutation, via `List.permutations'`) of `constraints`,
    the set of optimal candidates as a `Finset`; the list of distinct optimal
    sets. The number of distinct sets is the number of language types the
    constraint set predicts. -/
def mkFactorialOptima
    (candidates : List C)
    (constraints : List (Constraint C))
    (h : candidates ≠ [] := by decide) : List (Finset C) :=
  let allRankings := constraints.permutations'
  let optima := allRankings.map fun ranking =>
    (Tableau.ofRanking candidates ranking h).optimal
  optima.eraseDups

/-- Number of distinct language types predicted by the factorial typology.
    Equals `|mkFactorialOptima|`. -/
def mkFactorialTypologySize
    (candidates : List C)
    (constraints : List (Constraint C))
    (h : candidates ≠ [] := by decide) : Nat :=
  (mkFactorialOptima candidates constraints h).length

end OptimalityTheory
