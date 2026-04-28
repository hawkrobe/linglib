import Linglib.Core.Constraint.Evaluation

/-!
# Optimality Theory — Core Vocabulary

OT-specific vocabulary layered on `Core.Constraint.Evaluation`. Provides
named constraints with a faithfulness/markedness distinction, convenience
constructors for building tableaux from ranked constraint lists, and factorial
typology computation.

## Connection to Evaluation

`Core.Constraint.Evaluation` provides the generic engine (`LexLE`, `Tableau`,
`Tableau.optimal`). This module adds OT-specific structure: constraint
families, named constraints, `mkTableau` for building tableaux from ranked
constraint lists, and factorial typology computation.
-/

namespace Core.Constraint.OT

open Core.Constraint.Evaluation

-- ============================================================================
-- § 1: Named Constraints
-- ============================================================================

/-- Constraint families in OT. -/
inductive ConstraintFamily where
  /-- Faithfulness: penalizes deviation from the input. -/
  | faithfulness
  /-- Markedness: penalizes marked structures in the output. -/
  | markedness
  deriving DecidableEq, Repr

/-- A named OT constraint with family classification.
    `eval c` returns the number of violations candidate `c` incurs.

    The `name` field is purely documentary — no evaluation function reads it.
    It defaults to `""` so constraints can be defined without a name when
    the string label adds no information. -/
structure NamedConstraint (C : Type*) where
  name : String := ""
  family : ConstraintFamily
  eval : C → Nat

-- ============================================================================
-- § 1b: Constraint Constructors
-- ============================================================================

/-- Build a binary markedness constraint (violated → 1, otherwise 0).

    Takes a `Prop`-valued predicate with `[DecidablePred]` so that callers
    can use propositional equality (`=`) and other Prop predicates rather
    than `Bool`-valued operators (`==`). Decidability is required to evaluate
    the constraint on a candidate. -/
def mkMark {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] :
    NamedConstraint C :=
  { name, family := .markedness, eval := fun c => if P c then 1 else 0 }

/-- Build a binary faithfulness constraint (violated → 1, otherwise 0).

    Takes a `Prop`-valued predicate with `[DecidablePred]` so that callers
    can use propositional equality (`=`) and other Prop predicates rather
    than `Bool`-valued operators (`==`). -/
def mkFaith {C : Type*} (name : String) (P : C → Prop) [DecidablePred P] :
    NamedConstraint C :=
  { name, family := .faithfulness, eval := fun c => if P c then 1 else 0 }

/-- Build a gradient markedness constraint with a Nat-valued violation count. -/
def mkMarkGrad {C : Type*} (name : String) (violations : C → Nat) : NamedConstraint C :=
  { name, family := .markedness, eval := violations }

/-- Build a gradient faithfulness constraint with a Nat-valued violation count. -/
def mkFaithGrad {C : Type*} (name : String) (violations : C → Nat) : NamedConstraint C :=
  { name, family := .faithfulness, eval := violations }

/-- Pull a `NamedConstraint D` back along a candidate map `f : C → D`. The
    name and family are inherited; the new `eval` composes the original
    with the projection. Lets paper-specific carrier types reuse a
    constraint defined on a more general carrier. -/
def NamedConstraint.comap {C D : Type*} (f : C → D) (c : NamedConstraint D) :
    NamedConstraint C :=
  { name := c.name, family := c.family, eval := c.eval ∘ f }

@[simp] theorem NamedConstraint.comap_eval {C D : Type*} (f : C → D)
    (c : NamedConstraint D) (x : C) :
    (c.comap f).eval x = c.eval (f x) := rfl

@[simp] theorem NamedConstraint.comap_name {C D : Type*} (f : C → D)
    (c : NamedConstraint D) : (c.comap f).name = c.name := rfl

@[simp] theorem NamedConstraint.comap_family {C D : Type*} (f : C → D)
    (c : NamedConstraint D) : (c.comap f).family = c.family := rfl

-- ============================================================================
-- § 2: Tableau Construction
-- ============================================================================

/-- Build a `ViolationProfile ranking.length` from a ranked list of named
    constraints. This is the fixed-length analog of the profile computation
    inside `mkTableau` — use it to inspect or compare violation counts
    outside a tableau context. -/
def mkProfile {C : Type*} (ranking : List (NamedConstraint C)) (c : C)
    : ViolationProfile ranking.length :=
  buildViolationProfile (fun i c => (ranking.get i).eval c) c

/-- Create a `ViolationProfile n` from a `List Nat` literal.

    The length proof defaults to `by decide`, so study files can write
    readable profile comparisons without an explicit proof:
    ```
    theorem t24a_profile : mkProfile ranking c = vpOfList [2, 2, 0] := by native_decide
    ``` -/
def vpOfList {n : Nat} (vs : List Nat) (h : vs.length = n := by decide)
    : ViolationProfile n :=
  toLex fun (i : Fin n) => vs.get ⟨i.val, by omega⟩

-- ============================================================================
-- § 3: Permutations (for factorial typology)
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
-- § 4: Tableau Construction
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
-- § 5: Top-Constraint Optimality
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

-- ============================================================================
-- § 5b: Zero-Profile Optimality
-- ============================================================================

/-- The zero `ViolationProfile n` is the minimum: `0 ≤ p` for all `p`.
    This is the structural reason that a candidate with zero violations
    on every constraint wins under any ranking.

    Proof: `0 ≤ p` iff `¬(p < 0)`. Under `Pi.Lex`, `p < 0` requires
    `∃ i, p i < 0 i`, but `0 i = 0` and `Nat` has no negative values. -/
theorem ViolationProfile.zero_le {n : Nat} (p : ViolationProfile n) :
    (0 : ViolationProfile n) ≤ p := by
  rw [not_lt.symm]
  intro ⟨i, _, hi⟩
  exact absurd hi (Nat.not_lt_zero _)

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
-- § 6: Factorial Typology
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

end Core.Constraint.OT
