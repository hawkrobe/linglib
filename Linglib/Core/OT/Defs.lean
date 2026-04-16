import Linglib.Core.Logic.ConstraintEvaluation
import Mathlib.GroupTheory.Perm.Basic

/-!
# OT Definitions — ERCs, Rankings, and Bridges

Pure types for Optimality Theory's algebraic layer. This module defines:

- `ERCVal` — the three-valued alphabet {W, L, e} for Elementary Ranking
  Conditions
- `ERC n` — an ERC over `n` constraints (a vector of `ERCVal`)
- `Ranking n` — a constraint ranking (a permutation of `Fin n`)
- `ercOfProfiles` — the bridge from violation profiles to ERCs

These types connect the *evaluation* side of OT (`ViolationProfile`,
`Tableau`) to the *inference* side (ranking requirements, consistency,
typology). An ERC encodes the ranking requirements that make one
candidate beat another — the intermediate level between "a specific
ranking with specific evaluation functions" and "a violation profile
with no connection to which constraints matter."

## References

@cite{prince-2002} — Entailed ranking arguments (original ERC formulation)
@cite{merchant-riggle-2016} — OT grammars, beyond partial orders:
ERC sets and antimatroids
-/

namespace Core.OT

open Core.ConstraintEvaluation

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
    all L-constraints. See `ERC.satisfiedBy` in `Core.OT.ERC`. -/
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

end Core.OT
