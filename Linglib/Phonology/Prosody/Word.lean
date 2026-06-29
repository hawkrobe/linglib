import Linglib.Phonology.Prosody.Foot
import Linglib.Phonology.Prosody.Tree

/-!
# Prosodic words (ω)
[selkirk-1980] [nespor-vogel-1986] [liberman-prince-1977] [hayes-1995]

The canonical prosodic word ([selkirk-1980]; [nespor-vogel-1986]; [hayes-1995]): a
flat, **headed** constituent over feet and stray syllables — the level above the foot
in the prosodic hierarchy (σ < f < ω). Like the foot it is headed; its head is a
*foot* (the head foot), and its Designated Terminal Element — the primary-stressed σ —
is the head σ of that head foot (the head chain projects two levels;
[liberman-prince-1977]). Headedness is **definitional**: an ω always contains its head
foot, so the *minimal word* ([mccarthy-prince-1993]) — that an ω properly contains a
foot — holds by construction. Exhaustive parsing, foot binarity, and alignment are
violable constraints, not part of the type; stray (unfooted) syllables are real
([selkirk-1996]) and are exactly what `Parse-σ` penalizes.

Encoded as a **zipper**: the head foot is a distinguished field, with the other
daughters (a `Foot`, or an unfooted stray σ) to its left and right. The trochee/iamb
inventory and weight live on `Foot`; recursion (ω-over-ω) lives on `Prosody.Tree`. The
re-representations into the prosodic tree and the metrical grid recover the same head.

## Main definitions

* `Word` — a headed prosodic word: a head `Foot` with `before`/`after` daughters.
* `Word.feet` / `strays` / `headFoot` / `headSyllable` — the daughters and the ω-DTE.
* `Word.IsLeftHeaded` / `IsRightHeaded` / `IsExhaustive` — derived stress/parse predicates.
* `Word.toProsTree` / `toGrid` — re-representations recovering the head.

## Main results

* `Word.feet_ne_nil` — the minimal word ([mccarthy-prince-1993]): every ω contains a
  foot, free from definitional headedness.
-/

namespace Prosody

open Features.Prosody

/-- A grid prominence level ([liberman-prince-1977]; [hayes-1995]): the head σ of the
    head foot is `primary` (the ω-DTE), other foot-heads `secondary`, the rest
    `unstressed`. -/
inductive StressLevel where
  | unstressed | secondary | primary
  deriving DecidableEq, Repr

/-! ### The canonical prosodic word -/

/-- The canonical prosodic word ω ([selkirk-1980]; [hayes-1995]): a flat headed
    constituent over feet and stray syllables, encoded as a zipper around its head
    `head` foot. `before`/`after` carry the other daughters (a `Foot`, or an unfooted
    stray σ); the head foot is always present, so an ω contains a foot by construction
    (the minimal word). -/
structure Word (S : Type*) where
  before : List (Foot S ⊕ S)
  head   : Foot S
  after  : List (Foot S ⊕ S)
  deriving DecidableEq, Repr

namespace Word
variable {S : Type*}

/-- The daughters in linear order: a foot, or an unfooted stray σ. -/
def daughters (w : Word S) : List (Foot S ⊕ S) := w.before ++ .inl w.head :: w.after

/-- The feet (head foot included), left to right. -/
def feet (w : Word S) : List (Foot S) := w.daughters.filterMap Sum.getLeft?

/-- The stray (unfooted) syllables, left to right. -/
def strays (w : Word S) : List S := w.daughters.filterMap Sum.getRight?

/-- The head foot — the primary-stress bearer. -/
def headFoot (w : Word S) : Foot S := w.head

/-- The ω-DTE: the primary-stressed σ, the head σ of the head foot (the head chain,
    two levels; [liberman-prince-1977]). -/
def headSyllable (w : Word S) : S := w.head.headSyllable

/-! ### Derived stress and parse predicates -/

/-- Primary stress on the leftmost foot: no foot precedes the head foot (initial
    stray σ are still allowed). -/
def IsLeftHeaded (w : Word S) : Prop := w.before.filterMap Sum.getLeft? = []
/-- Primary stress on the rightmost foot. -/
def IsRightHeaded (w : Word S) : Prop := w.after.filterMap Sum.getLeft? = []
/-- Fully parsed — no stray syllables (`Parse-σ`-clean; `Parse-σ` itself is violable). -/
def IsExhaustive (w : Word S) : Prop := w.strays = []

instance (w : Word S) : Decidable w.IsLeftHeaded := by unfold IsLeftHeaded; infer_instance
instance (w : Word S) : Decidable w.IsRightHeaded := by unfold IsRightHeaded; infer_instance
instance [DecidableEq S] (w : Word S) : Decidable w.IsExhaustive := by
  unfold IsExhaustive; infer_instance

/-- **The minimal word** ([mccarthy-prince-1993]), free from definitional headedness:
    every ω contains a foot (its head foot). -/
theorem feet_ne_nil (w : Word S) : w.feet ≠ [] := by
  simp [feet, daughters, List.filterMap_append]

/-! ### Re-representations (preserving the head) -/

/-- A non-head daughter → a prosodic subtree: a (non-head) foot, or a stray σ-leaf. -/
def daughterTree (wt : S → Syllable.Weight) : (Foot S ⊕ S) → Tree
  | .inl f => Foot.toProsTree wt f
  | .inr s => .node (.syl (wt s) false) []

/-- Re-represent as a prosodic tree ([selkirk-1980]; [ito-mester-2003]): an `.ω` node
    over the daughters' subtrees, the **head foot** marked `isHead`, stray σ as
    `.σ`-leaves directly under ω ([selkirk-1996]; permitted by `Tree.Containment`).
    Composes `Foot.toProsTree`. -/
def toProsTree (wt : S → Syllable.Weight) (w : Word S) : Tree :=
  .node .om (w.before.map (daughterTree wt)
    ++ Foot.toProsTree wt w.head true :: w.after.map (daughterTree wt))

/-- A non-head daughter's grid row (foot-head → `secondary`, the rest `unstressed`). -/
def daughterGrid : (Foot S ⊕ S) → List StressLevel
  | .inl f => (Foot.toGrid f).map (fun b => if b then .secondary else .unstressed)
  | .inr _ => [.unstressed]

/-- Re-represent as the metrical grid ([hayes-1995]; [liberman-prince-1977]): one
    `StressLevel` per σ. The head foot's head σ is `primary` (the ω-DTE), other
    foot-heads `secondary`, the rest `unstressed`. `Foot.toGrid` is the within-foot
    row; this projects the word-head over it. -/
def toGrid (w : Word S) : List StressLevel :=
  w.before.flatMap daughterGrid
    ++ (Foot.toGrid w.head).map (fun b => if b then .primary else .unstressed)
    ++ w.after.flatMap daughterGrid

end Word

/-! ### Worked examples -/

-- (ˈσσ)σ : a trochee heading the word, then a stray σ — Pintupi-style.
private def w_trochStray : Word Nat := ⟨[], Foot.trochee 1 1, [.inr 1]⟩
example : w_trochStray.IsLeftHeaded ∧ ¬ w_trochStray.IsExhaustive := by decide
example : w_trochStray.feet = [Foot.trochee 1 1] := by decide
-- the head σ is the unique primary; the foot's weak σ and the stray are unstressed.
example : w_trochStray.toGrid = [.primary, .unstressed, .unstressed] := by decide

-- (σσ)(ˈσσ) : two trochees, primary on the second — secondary on the first.
private def w_twoFeet : Word Nat := ⟨[.inl (Foot.trochee 1 1)], Foot.trochee 1 1, []⟩
example : w_twoFeet.IsRightHeaded := by decide
example : w_twoFeet.toGrid = [.secondary, .unstressed, .primary, .unstressed] := by decide

end Prosody
