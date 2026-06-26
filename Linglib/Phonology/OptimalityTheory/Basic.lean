import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.Constraints.Profile
import Linglib.Phonology.OptimalityTheory.Defs

/-!
# Tableau Construction and Factorial Typology

The OT evaluation machinery built on the `Tableau` type (`OptimalityTheory.Defs`)
and the violation-profile vocabulary (`Constraints.Profile`): a smart constructor
for tableaux from ranked constraint lists, the structural optimality theorems,
and factorial-typology computation.

## Main definitions

* `mkTableau` — build a `Tableau` from a candidate list and a ranked constraint
  list.
* `permutations` — all rankings of a constraint list (factorial typology).
* `mkFactorialOptima` / `mkFactorialTypologySize` — the distinct optimal sets
  predicted across all rankings, and their count.

## Main results

* `mkTableau_zero_isOptimal` / `mkTableau_zero_optimal_allRankings` — a
  candidate with no violations wins under any (every) ranking.
* `mkTableau_isOptimal_zero_first` — a satisfiable top constraint forces all
  winners to satisfy it.
-/

namespace OptimalityTheory

open Constraints

-- ============================================================================
-- § 1: Permutations (for factorial typology)
-- ============================================================================

/-- Insert element `a` at every position in list `l`. -/
private def insertEverywhere {α : Type*} (a : α) : List α → List (List α)
  | [] => [[a]]
  | x :: xs =>
    (a :: x :: xs) :: (insertEverywhere a xs).map (x :: ·)

/-- All permutations of a list. -/
def permutations {α : Type*} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap (insertEverywhere x)

/-- Elements of `insertEverywhere a l` contain exactly `a` and the
    elements of `l`. -/
private theorem mem_of_mem_insertEverywhere {α : Type*} (a : α) :
    ∀ (l : List α) (l' : List α), l' ∈ insertEverywhere a l →
      ∀ x, x ∈ l' → x = a ∨ x ∈ l := by
  intro l
  induction l with
  | nil =>
    intro l' h x hx
    simp [insertEverywhere] at h
    subst h
    simp at hx
    exact Or.inl hx
  | cons y ys ih =>
    intro l' h x hx
    simp only [insertEverywhere, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨t, ht, rfl⟩
    · -- l' = a :: y :: ys
      simp [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (.head _)
      · exact Or.inr (.tail _ hx)
    · -- l' = y :: t, where t ∈ insertEverywhere a ys
      simp [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (.head _)
      · rcases ih t ht x hx with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr (.tail _ hm)

/-- Elements of any permutation of `l` are elements of `l`. -/
theorem mem_of_mem_permutations {α : Type*} {x : α} :
    ∀ {l l' : List α}, l' ∈ permutations l → x ∈ l' → x ∈ l := by
  intro l
  induction l with
  | nil =>
    intro l' hp hx
    simp [permutations] at hp
    subst hp; simp at hx
  | cons y ys ih =>
    intro l' hp hx
    simp only [permutations, List.mem_flatMap] at hp
    obtain ⟨p, hp_mem, hp_ins⟩ := hp
    rcases mem_of_mem_insertEverywhere y p l' hp_ins x hx with rfl | hm
    · exact .head _
    · exact .tail _ (ih hp_mem hm)

/-- A permutation of `constraints` has the same elements, so any
    `con ∈ ranking` for `ranking ∈ permutations constraints` satisfies
    `con ∈ constraints`. -/
theorem permutations_subset {α : Type*} {l l' : List α}
    (hp : l' ∈ permutations l) : ∀ x ∈ l', x ∈ l :=
  fun _ hx => mem_of_mem_permutations hp hx

-- ============================================================================
-- § 2: Tableau Construction
-- ============================================================================

/-- Build a `Tableau C ranking.length` from a candidate list and ranking.

    Candidates are deduplicated via `List.toFinset`; profiles are
    fixed-length `ViolationProfile n` built via `buildViolationProfile`.

    Study files use this as:
    ```
    (mkTableau candidates ranking h).optimal = {.winner}
    ```
    where `{.winner}` is a `Finset` literal. -/
def mkTableau {C : Type*} [DecidableEq C] (candidates : List C)
    (ranking : List (NamedConstraint C))
    (h : candidates ≠ [] := by decide) : Tableau C ranking.length :=
  { candidates := candidates.toFinset
    profile := fun c => buildViolationProfile
      (fun i c => (ranking.get i).eval c) c
    nonempty := by
      cases candidates with
      | nil => contradiction
      | cons a _ => exact ⟨a, by simp⟩ }

/-- Candidates in `mkTableau ... .optimal` belong to the original list. -/
theorem mkTableau_optimal_mem {C : Type*} [DecidableEq C]
    (candidates : List C) (ranking : List (NamedConstraint C))
    (h : candidates ≠ []) (c : C) :
    c ∈ (mkTableau candidates ranking h).optimal → c ∈ candidates :=
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
theorem mkTableau_isOptimal_zero_first {C : Type*} [DecidableEq C]
    (candidates : List C) (con : NamedConstraint C)
    (rest : List (NamedConstraint C))
    (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con.eval c₀ = 0)
    : ∀ c, (mkTableau candidates (con :: rest) h).IsOptimal c →
        con.eval c = 0 := by
  intro c ⟨_, hc_all⟩
  obtain ⟨c₀, hc₀_mem, hc₀_zero⟩ := hExists
  have hle := hc_all c₀ (List.mem_toFinset.mpr hc₀_mem)
  have h0 := ViolationProfile.le_apply_zero hle
  -- h0 is definitionally: con.eval c ≤ con.eval c₀
  change con.eval c ≤ con.eval c₀ at h0
  rw [hc₀_zero] at h0
  exact Nat.le_zero.mp h0

/-- `∈ .optimal` version of `mkTableau_isOptimal_zero_first`. -/
theorem mkTableau_optimal_zero_first {C : Type*} [DecidableEq C]
    (candidates : List C) (con : NamedConstraint C)
    (rest : List (NamedConstraint C))
    (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con.eval c₀ = 0)
    : ∀ c ∈ (mkTableau candidates (con :: rest) h).optimal,
        con.eval c = 0 :=
  fun c hc => mkTableau_isOptimal_zero_first candidates con rest h hExists c
    ((Tableau.mem_optimal_iff _ c).mp hc)

/-- If a candidate in `mkTableau` has 0 violations on every constraint,
    it is optimal. -/
theorem mkTableau_zero_isOptimal {C : Type*} [DecidableEq C]
    (candidates : List C) (ranking : List (NamedConstraint C))
    (h : candidates ≠ []) (c : C) (hc : c ∈ candidates)
    (hzero : ∀ con ∈ ranking, con.eval c = 0) :
    c ∈ (mkTableau candidates ranking h).optimal := by
  rw [Tableau.mem_optimal_iff]
  refine ⟨List.mem_toFinset.mpr hc, fun c' _ => ?_⟩
  suffices hsuff : (mkTableau candidates ranking h).profile c = 0 by
    rw [hsuff]; exact ViolationProfile.zero_le _
  show buildViolationProfile (fun i c => (ranking.get i).eval c) c = 0
  funext i
  exact hzero (ranking.get i) (List.get_mem ranking i)

/-- If a candidate has 0 violations on every constraint in a set, it is
    optimal under **every** permutation of those constraints.

    This is the structural backbone of `adj_always_initial` in Marco &
    Rasin (2026): the uniform-initial adjective paradigm has [0,0,0,0]
    on all four OP constraints, so it wins regardless of ranking. The
    proof reduces to `mkTableau_zero_isOptimal` after using
    `permutations_subset` to show that elements of a permutation are
    elements of the original list. -/
theorem mkTableau_zero_optimal_allRankings {C : Type*} [DecidableEq C]
    (candidates : List C) (constraints : List (NamedConstraint C))
    (h : candidates ≠ []) (c : C) (hc : c ∈ candidates)
    (hzero : ∀ con ∈ constraints, con.eval c = 0) :
    ∀ ranking ∈ permutations constraints,
      c ∈ (mkTableau candidates ranking h).optimal :=
  fun ranking hp => mkTableau_zero_isOptimal candidates ranking h c hc
    (fun con hcon => hzero con (permutations_subset hp con hcon))

-- ============================================================================
-- § 4: Factorial Typology
-- ============================================================================

/-- For each permutation of `constraints`, compute the set of optimal
    candidates as a `Finset`. Return the list of distinct optimal sets.

    This is the core of OT factorial typology: the number of distinct
    optimal sets equals the number of language types predicted by the
    constraint set. -/
def mkFactorialOptima {C : Type*} [DecidableEq C]
    (candidates : List C)
    (constraints : List (NamedConstraint C))
    (h : candidates ≠ [] := by decide) : List (Finset C) :=
  let allRankings := permutations constraints
  let optima := allRankings.map fun ranking =>
    (mkTableau candidates ranking h).optimal
  optima.eraseDups

/-- Number of distinct language types predicted by the factorial typology.
    Equals `|mkFactorialOptima|`. -/
def mkFactorialTypologySize {C : Type*} [DecidableEq C]
    (candidates : List C)
    (constraints : List (NamedConstraint C))
    (h : candidates ≠ [] := by decide) : Nat :=
  (mkFactorialOptima candidates constraints h).length

end OptimalityTheory
