import Mathlib.Data.List.Basic

/-!
# Word models

The model-theoretic representation underlying logical characterizations of subregular
functions: a string viewed as a finite labeled linear order. A **word model** is the
relational signature `⟨D, L, R⟩` — a domain `D` of positions, unary labels `L`, and the
binary immediate-successor relation `R`; general precedence is the (FO-definable) transitive
closure of successor and is not part of the quantifier-free fragment.

The carrier is `List α` itself: a string *is* its word model. This is deliberately where
mathlib stops — it has strings (`List`/`FreeMonoid`) and automata (`DFA`, `MyhillNerode`)
but no model-theoretic word structure — and it keeps the logic layer directly composable
with `Subregular`'s string functions (`Subregular.IsInputStrictlyLocal`, `SFST`).

## Main definitions

* `Subregular.Logic.WordModel` — a string over `α`, viewed as `⟨D, label, succ⟩`.
* `WordModel.label?` — the unary label (symbol) at a position, `none` off the edge.
* `WordModel.Mem` — domain membership of a position.
* `WordModel.succ?` / `WordModel.pred?` — successor/predecessor as partial functions.

## Implementation notes

Positions are `ℕ` indices; a position is in-domain iff below `length`. Successor and
predecessor are *partial functions* (`Option ℕ`) rather than relations — this is what lets
the quantifier-free term language (`Logic/QFLogic.lean`) reach a bounded neighbourhood via
`succ`/`pred` chains without quantifiers, the syntactic source of strict locality.
-/

namespace Subregular.Logic

/-- A **word model**: a string over `α`, viewed model-theoretically as a finite linear
order of positions carrying unary labels and an immediate-successor relation. -/
abbrev WordModel (α : Type*) := List α

namespace WordModel
variable {α : Type*}

/-- The label (symbol) at position `n`, or `none` off the edge. -/
def label? (w : WordModel α) (n : ℕ) : Option α := w[n]?

/-- Position `n` lies in the domain. -/
def Mem (w : WordModel α) (n : ℕ) : Prop := n < w.length

instance (w : WordModel α) (n : ℕ) : Decidable (w.Mem n) := Nat.decLt _ _

/-- Successor as a partial function: the position after `n`, defined iff it is in range. -/
def succ? (w : WordModel α) (n : ℕ) : Option ℕ :=
  if n + 1 < w.length then some (n + 1) else none

/-- Predecessor as a partial function: the position before `n`, defined iff `n > 0`. -/
def pred? (w : WordModel α) : ℕ → Option ℕ
  | 0     => none
  | n + 1 => if n < w.length then some n else none

@[simp] theorem label?_eq_getElem? (w : WordModel α) (n : ℕ) : w.label? n = w[n]? := rfl

theorem succ?_eq_some_iff {w : WordModel α} {n m : ℕ} :
    w.succ? n = some m ↔ m = n + 1 ∧ n + 1 < w.length := by
  unfold succ?
  split <;> simp_all
  all_goals omega

/-- The successor structure depends only on the length. -/
theorem succ?_congr {w w' : WordModel α} (h : w.length = w'.length) :
    w.succ? = w'.succ? := by
  funext n
  simp [succ?, h]

/-- The predecessor structure depends only on the length. -/
theorem pred?_congr {w w' : WordModel α} (h : w.length = w'.length) :
    w.pred? = w'.pred? := by
  funext n
  cases n <;> simp [pred?, h]

theorem pred?_eq_some_iff {w : WordModel α} {n m : ℕ} :
    w.pred? n = some m ↔ n = m + 1 ∧ m < w.length := by
  cases n with
  | zero => simp [pred?]
  | succ k =>
    unfold pred?
    split <;> simp_all
    all_goals omega

@[simp] theorem mem_iff (w : WordModel α) (n : ℕ) : w.Mem n ↔ n < w.length := Iff.rfl

end WordModel

end Subregular.Logic
