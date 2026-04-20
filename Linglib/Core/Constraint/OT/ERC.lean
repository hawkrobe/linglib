import Linglib.Core.Constraint.Evaluation
import Mathlib.GroupTheory.Perm.Basic

/-!
# OT — Elementary Ranking Conditions (Definitions + Operations)

Pure types and operations for OT's algebraic ranking-inference layer.
This module defines:

- `ERCVal` — the three-valued alphabet {W, L, e} for Elementary Ranking
  Conditions
- `ERC n` — an ERC over `n` constraints (a vector of `ERCVal`)
- `Ranking n` — a constraint ranking (a permutation of `Fin n`)
- `ercOfProfiles` — the bridge from violation profiles to ERCs
- `ERC.satisfiedBy`, `ERCSet.consistent`, `ERCSet.entails` — the
  satisfaction/consistency/entailment algebra
- `tableauERC` — build an ERC from a winner-loser pair in a tableau
- `simpleERC` — single-W/single-L ERCs corresponding to Hasse edges

These types connect the *evaluation* side of OT (`ViolationProfile`,
`Tableau`) to the *inference* side (ranking requirements, consistency,
typology). An ERC encodes the ranking requirements that make one
candidate beat another — the intermediate level between "a specific
ranking with specific evaluation functions" and "a violation profile
with no connection to which constraints matter."

## The ranking question

Given candidates α and β with violation profiles, the ERC [α ∼ β]
answers the **ranking question**: exactly which rankings select α over β?
A ranking satisfies [α ∼ β] iff at least one W-constraint (preferring
the winner α) is ranked above all L-constraints (preferring the loser β).

## References

@cite{prince-2002} — Entailed ranking arguments (original ERC formulation)
@cite{merchant-riggle-2016} — OT grammars, beyond partial orders:
ERC sets and antimatroids
-/

namespace Core.Constraint.OT

open Core.Constraint.Evaluation

-- ============================================================================
-- § 1: ERCVal — The Three-Valued Alphabet
-- ============================================================================

/-- The three-valued alphabet for Elementary Ranking Conditions.

    - `W` (winner-preferring): the constraint prefers the winner
    - `L` (loser-preferring): the constraint prefers the loser
    - `e` (equal): the constraint does not distinguish the candidates -/
inductive ERCVal where
  | W : ERCVal
  | L : ERCVal
  | e : ERCVal
  deriving DecidableEq, Repr, Inhabited

instance : ToString ERCVal where
  toString
    | .W => "W"
    | .L => "L"
    | .e => "e"

-- ============================================================================
-- § 2: ERC — Elementary Ranking Condition
-- ============================================================================

/-- An Elementary Ranking Condition over `n` constraints.

    An ERC is a vector `Fin n → ERCVal` encoding the ranking requirements
    for one candidate to beat another. For each constraint `k`:
    - `α k = W` means constraint `k` prefers the winner
    - `α k = L` means constraint `k` prefers the loser
    - `α k = e` means constraint `k` is indifferent

    A ranking satisfies the ERC iff some W-constraint is ranked above
    all L-constraints. See `ERC.satisfiedBy` below. -/
def ERC (n : Nat) := Fin n → ERCVal

instance {n : Nat} : Inhabited (ERC n) := ⟨fun _ => .e⟩

instance {n : Nat} : DecidableEq (ERC n) := inferInstanceAs (DecidableEq (Fin n → ERCVal))

/-- The set of W-constraints in an ERC: those preferring the winner. -/
def ERC.wSet {n : Nat} (α : ERC n) : Set (Fin n) := { k | α k = .W }

/-- The set of L-constraints in an ERC: those preferring the loser. -/
def ERC.lSet {n : Nat} (α : ERC n) : Set (Fin n) := { k | α k = .L }

/-- The set of e-constraints in an ERC: those indifferent between candidates. -/
def ERC.eSet {n : Nat} (α : ERC n) : Set (Fin n) := { k | α k = .e }

/-- Decidable membership in W/L/e sets. -/
instance {n : Nat} (α : ERC n) (k : Fin n) : Decidable (k ∈ α.wSet) :=
  inferInstanceAs (Decidable (α k = .W))

instance {n : Nat} (α : ERC n) (k : Fin n) : Decidable (k ∈ α.lSet) :=
  inferInstanceAs (Decidable (α k = .L))

instance {n : Nat} (α : ERC n) (k : Fin n) : Decidable (k ∈ α.eSet) :=
  inferInstanceAs (Decidable (α k = .e))

/-- An ERC is **trivial** if it has no L-constraints — every ranking
    satisfies it. -/
def ERC.isTrivial {n : Nat} (α : ERC n) : Prop := ∀ k, α k ≠ .L

instance {n : Nat} (α : ERC n) : Decidable α.isTrivial :=
  Fintype.decidableForallFintype

/-- An ERC is **contradictory** if it has no W-constraints but has at
    least one L-constraint — no ranking can satisfy it. -/
def ERC.isContradictory {n : Nat} (α : ERC n) : Prop :=
  (∀ k, α k ≠ .W) ∧ (∃ k, α k = .L)

instance {n : Nat} (α : ERC n) : Decidable α.isContradictory :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- § 3: Ranking — Constraint Permutations
-- ============================================================================

/-- A ranking of `n` constraints, represented as a permutation of `Fin n`.

    `r i` is the constraint at rank position `i`, where position `0` is
    the highest-ranked (most dominant) constraint.

    Equivalently, `r.symm k` is the rank position of constraint `k` — a
    lower value means higher rank (more dominant). -/
def Ranking (n : Nat) := Equiv.Perm (Fin n)

instance {n : Nat} : Inhabited (Ranking n) := ⟨Equiv.refl _⟩

instance {n : Nat} : CoeFun (Ranking n) (fun _ => Fin n → Fin n) :=
  ⟨Equiv.toFun⟩

@[simp] theorem Ranking.symm_apply_apply {n : Nat} (r : Ranking n) (i : Fin n) :
    r.symm (r i) = i := Equiv.symm_apply_apply r i

@[simp] theorem Ranking.apply_symm_apply {n : Nat} (r : Ranking n) (i : Fin n) :
    r (r.symm i) = i := Equiv.apply_symm_apply r i

/-- Constraint `i` **dominates** constraint `j` under ranking `r`:
    `i` is ranked higher (lower position number) than `j`. -/
def dominates {n : Nat} (r : Ranking n) (i j : Fin n) : Prop :=
  r.symm i < r.symm j

instance {n : Nat} (r : Ranking n) (i j : Fin n) :
    Decidable (dominates r i j) :=
  inferInstanceAs (Decidable (_ < _))

/-- The identity ranking: constraint `0` is highest, `n-1` is lowest.
    This is the "default" ranking where index order equals rank order. -/
def Ranking.id (n : Nat) : Ranking n := Equiv.refl _

-- ============================================================================
-- § 4: Bridge — ViolationProfile → ERC
-- ============================================================================

/-- Construct an ERC from two violation profiles: the winner's and the
    loser's. For each constraint `k`:
    - `W` if the winner has strictly fewer violations (winner-preferring)
    - `L` if the winner has strictly more violations (loser-preferring)
    - `e` if violations are equal (indifferent)

    This is the fundamental bridge between OT's evaluation layer
    (`ViolationProfile`) and its inference layer (`ERC`). Every call
    to `mkTableau` that selects a winner implicitly generates ERCs for
    all winner-loser pairs via this function. -/
def ercOfProfiles {n : Nat} (winner loser : ViolationProfile n) : ERC n :=
  fun k =>
    if winner k < loser k then .W
    else if winner k > loser k then .L
    else .e

/-- The W-set of `ercOfProfiles` consists of constraints where the
    winner has strictly fewer violations. -/
theorem ercOfProfiles_w {n : Nat} (w l : ViolationProfile n) (k : Fin n) :
    (ercOfProfiles w l) k = .W ↔ w k < l k := by
  unfold ercOfProfiles; split_ifs with h₁ h₂ <;> simp_all

/-- The L-set of `ercOfProfiles` consists of constraints where the
    winner has strictly more violations. -/
theorem ercOfProfiles_l {n : Nat} (w l : ViolationProfile n) (k : Fin n) :
    (ercOfProfiles w l) k = .L ↔ l k < w k := by
  unfold ercOfProfiles
  split_ifs with h₁ h₂
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · exact ⟨fun _ => h₂, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩

/-- The e-set of `ercOfProfiles` consists of constraints where
    violations are equal. -/
theorem ercOfProfiles_e {n : Nat} (w l : ViolationProfile n) (k : Fin n) :
    (ercOfProfiles w l) k = .e ↔ w k = l k := by
  unfold ercOfProfiles
  split_ifs with h₁ h₂
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

-- ============================================================================
-- § 5: ERC from List — Readable Construction
-- ============================================================================

/-- Construct an ERC from a list of ERCVal, with a proof that the list
    has the right length. Enables readable ERC literals in study files:
    ```
    def myERC : ERC 4 := ercOfList [.W, .e, .L, .e]
    ``` -/
def ercOfList {n : Nat} (vs : List ERCVal) (h : vs.length = n := by decide)
    : ERC n :=
  fun i => vs.get ⟨i.val, by omega⟩

-- ============================================================================
-- § 6: Ranking from List — Bridge to Existing API
-- ============================================================================

/-- Construct a `Ranking n` from a function assigning rank positions to
    constraints. `f k` is the rank position of constraint `k` (0 = highest).

    Requires `f` to be a bijection (injective + surjective on `Fin n`). -/
noncomputable def Ranking.ofRankFn {n : Nat} (f : Fin n → Fin n)
    (hbij : Function.Bijective f) : Ranking n :=
  (Equiv.ofBijective f hbij).symm

/-- Swap the rank positions of two constraints. -/
def Ranking.swap {n : Nat} (r : Ranking n) (i j : Fin n) : Ranking n :=
  r.trans (Equiv.swap i j)

-- ============================================================================
-- § 7: ERC Satisfaction
-- ============================================================================

/-- A ranking `r` **satisfies** ERC `α` iff some W-constraint is ranked
    above all L-constraints.

    In the ranking `r`, position `0` is highest-ranked. `r i` is the
    constraint at position `i`, and `r.symm k` is the rank position of
    constraint `k`. So `r.symm w < r.symm l` means constraint `w` is
    ranked above constraint `l`.

    This is the semantic content of an ERC: it encodes a disjunction of
    dominance conditions. The ERC ⟨W, e, L, e⟩ says "constraint 0 must
    dominate constraint 2." The ERC ⟨W, W, L, e⟩ says "constraint 0 OR
    constraint 1 must dominate constraint 2." -/
def ERC.satisfiedBy {n : Nat} (r : Ranking n) (α : ERC n) : Prop :=
  ∀ l : Fin n, α l = .L → ∃ w : Fin n, α w = .W ∧ dominates r w l

instance {n : Nat} (r : Ranking n) (α : ERC n) :
    Decidable (α.satisfiedBy r) :=
  Fintype.decidableForallFintype

/-- A trivial ERC (no L-constraints) is satisfied by every ranking. -/
theorem ERC.trivial_satisfiedBy {n : Nat} (α : ERC n) (htriv : α.isTrivial)
    (r : Ranking n) : α.satisfiedBy r :=
  fun l hl => absurd hl (htriv l)

-- ============================================================================
-- § 8: ERC Set Satisfaction and Consistency
-- ============================================================================

/-- A ranking satisfies a set of ERCs iff it satisfies each one. -/
def ERCSet.satisfiedBy {n : Nat} (r : Ranking n)
    (E : List (ERC n)) : Prop :=
  ∀ α ∈ E, ERC.satisfiedBy r α

instance {n : Nat} (r : Ranking n) (E : List (ERC n)) :
    Decidable (ERCSet.satisfiedBy r E) :=
  List.decidableBAll _ E

/-- An ERC set is **consistent** iff there exists at least one ranking
    that satisfies all ERCs in the set. An inconsistent ERC set encodes
    contradictory ranking requirements.

    This is the decidable version — it searches over all `n!` rankings.
    For large `n`, use the ERC fusion algorithm instead. -/
def ERCSet.consistent {n : Nat} (E : List (ERC n)) : Prop :=
  ∃ r : Ranking n, ERCSet.satisfiedBy r E

/-- The set of rankings consistent with an ERC set — its **linear
    extensions** in the terminology of @cite{merchant-riggle-2016}. -/
def ERCSet.linearExtensions {n : Nat} (E : List (ERC n)) :
    Set (Ranking n) :=
  { r | ERCSet.satisfiedBy r E }

-- ============================================================================
-- § 9: Entailment
-- ============================================================================

/-- ERC set `E` **entails** ERC set `E'` iff every ranking satisfying
    `E` also satisfies `E'`. Equivalently, the linear extensions of `E`
    are a subset of the linear extensions of `E'`.

    This is the natural preorder on ERC sets. Two ERC sets are equivalent
    iff they entail each other — they have the same linear extensions
    and describe the same OT grammar. -/
def ERCSet.entails {n : Nat} (E E' : List (ERC n)) : Prop :=
  ∀ r : Ranking n, ERCSet.satisfiedBy r E → ERCSet.satisfiedBy r E'

/-- Entailment is reflexive. -/
theorem ERCSet.entails_refl {n : Nat} (E : List (ERC n)) :
    ERCSet.entails E E :=
  fun _ h => h

/-- Entailment is transitive. -/
theorem ERCSet.entails_trans {n : Nat} (E₁ E₂ E₃ : List (ERC n))
    (h₁₂ : ERCSet.entails E₁ E₂) (h₂₃ : ERCSet.entails E₂ E₃) :
    ERCSet.entails E₁ E₃ :=
  fun r hr => h₂₃ r (h₁₂ r hr)

/-- Adding an ERC to a set weakens the entailment (more requirements =
    fewer satisfying rankings = stronger set). -/
theorem ERCSet.entails_of_cons {n : Nat} (α : ERC n) (E : List (ERC n)) :
    ERCSet.entails (α :: E) E :=
  fun _ hr β hβ => hr β (List.mem_cons_of_mem α hβ)

/-- If every ERC in `E'` is already entailed by `E`, then `E` entails
    `E'`. This is the pointwise characterization. -/
theorem ERCSet.entails_of_forall_mem {n : Nat} (E E' : List (ERC n))
    (h : ∀ α ∈ E', ERCSet.entails E [α]) :
    ERCSet.entails E E' :=
  fun r hr α hα => h α hα r hr α (List.mem_cons.mpr (Or.inl rfl))

-- ============================================================================
-- § 10: Bridge — Tableau → ERC
-- ============================================================================

/-- Build an ERC from a winner-loser pair in a tableau.

    Given a tableau `t` with candidates and violation profiles, and
    a designated winner `w` and loser `l`, construct the ERC that
    encodes the ranking requirements for `w` to beat `l`.

    This is the fundamental bridge from OT evaluation to OT inference:
    every time a tableau selects a winner, it implicitly generates ERCs
    for all winner-loser pairs. -/
def tableauERC {C : Type} [DecidableEq C] {n : Nat}
    (t : Tableau C n) (w l : C) : ERC n :=
  ercOfProfiles (t.profile w) (t.profile l)

-- ============================================================================
-- § 11: Simple ERCs
-- ============================================================================

/-- A **simple ERC** has exactly one W and one L — it encodes a single
    dominance requirement `w ≫ l` (constraint `w` must dominate
    constraint `l`).

    Simple ERCs correspond to edges in the Hasse diagram of the ranking
    partial order. Sets of simple ERCs describe exactly the rankings
    representable as partial orders (@cite{merchant-riggle-2016} §1.1). -/
def ERC.isSimple {n : Nat} (α : ERC n) : Prop :=
  (∃! w, α w = .W) ∧ (∃! l, α l = .L)

/-- Construct a simple ERC asserting that constraint `i` must dominate
    constraint `j`. All other constraints are `e`. -/
def simpleERC {n : Nat} (i j : Fin n) : ERC n :=
  fun k => if k = i then .W else if k = j then .L else .e

/-- The W-position of a simple ERC. -/
@[simp] theorem simpleERC_apply_W {n : Nat} {i j : Fin n} :
    simpleERC i j i = .W := by simp [simpleERC]

/-- The L-position of a simple ERC. -/
@[simp] theorem simpleERC_apply_L {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    simpleERC i j j = .L := by
  simp only [simpleERC]; split_ifs with h
  · exact absurd h hij.symm
  · rfl

/-- A simple ERC `i ≫ j` is satisfied by ranking `r` iff `i` dominates
    `j` under `r`. -/
theorem simpleERC_satisfiedBy_iff {n : Nat} {i j : Fin n} (hij : i ≠ j)
    (r : Ranking n) :
    (simpleERC i j).satisfiedBy r ↔ dominates r i j := by
  constructor
  · intro h
    have hl : simpleERC i j j = .L := by
      simp only [simpleERC]; split_ifs with h₁ <;> [exact absurd h₁ hij.symm; rfl]
    obtain ⟨w, hw_val, hw_dom⟩ := h j hl
    have hw : w = i := by
      unfold simpleERC at hw_val
      by_contra hne
      simp [hne] at hw_val
      split_ifs at hw_val
    subst hw; exact hw_dom
  · intro hdom l hl
    have hl_eq : l = j := by
      unfold simpleERC at hl
      by_contra hne
      have hne_i : l ≠ i := by
        intro heq; subst heq; simp at hl
      simp [hne_i, hne] at hl
    subst hl_eq
    exact ⟨i, by simp [simpleERC], hdom⟩

/-- A simple ERC `i ≫ j` (with `i ≠ j`) is consistent: any ranking that
    places `i` strictly above `j` is a witness; the identity ranking
    works whenever the index order already has `i < j`, and a swap
    suffices otherwise. We pick a witness by transposing `(i, j)` if
    needed so that the resulting permutation puts `i` at a position
    less than `j`'s. -/
theorem simpleERC_consistent {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    ERCSet.consistent [simpleERC i j] := by
  -- Witness: the permutation swapping i and j, applied to the identity
  -- so that under the resulting ranking, i sits at position min(i.val, j.val)
  -- and j sits at position max(i.val, j.val).
  by_cases hlt : i.val < j.val
  · refine ⟨Ranking.id n, ?_⟩
    intro α hα
    simp only [List.mem_singleton] at hα; subst hα
    refine (simpleERC_satisfiedBy_iff hij _).mpr ?_
    -- dominates r i j ↔ r.symm i < r.symm j; for Ranking.id, r.symm = id.
    show (Ranking.id n).symm i < (Ranking.id n).symm j
    simpa [Ranking.id, Equiv.refl] using hlt
  · -- i.val > j.val (i ≠ j rules out equality)
    have hij_lt : j.val < i.val := by
      rcases Nat.lt_or_ge j.val i.val with h | h
      · exact h
      · -- h : i.val ≤ j.val, hlt : ¬ i.val < j.val ⇒ j.val ≤ i.val ⇒ i.val = j.val
        have heq : i.val = j.val := Nat.le_antisymm h (Nat.le_of_not_lt hlt)
        exact absurd (Fin.ext heq) hij
    refine ⟨(Equiv.swap i j : Ranking n), ?_⟩
    intro α hα
    simp only [List.mem_singleton] at hα; subst hα
    refine (simpleERC_satisfiedBy_iff hij _).mpr ?_
    -- (Equiv.swap i j).symm = Equiv.swap i j; (swap i j) i = j, (swap i j) j = i.
    -- So (swap i j).symm i = j, (swap i j).symm j = i, and j.val < i.val.
    show (Equiv.swap i j).symm i < (Equiv.swap i j).symm j
    rw [Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact hij_lt

end Core.Constraint.OT
