module

public import Linglib.Core.Computability.Edge
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# CCG categories

The categories of combinatory categorial grammar are built from atoms by a rightward and a
leftward slash, each slash carrying one of Baldridge's modalities. Every category is uniquely an
atom, its *target*, followed by a sequence of *arguments*, slash–category pairs; Kuhlmann, Koller
and Satta write it `A|ₘXₘ ⋯ |₁X₁`, and the composition rules of every CCG formalism have the
form `X/Y Yβ ⇒ Xβ` over an argument sequence `β`. Categories are stated over an arbitrary type
`α` of atoms, so a grammar with featured atoms instantiates its own inventory.

## Main definitions

* `CCG.Modality`: the slash modalities, a bounded order with `dot = ⊥`, `star = ⊤`, and
  `diamond` and `cross` incomparable.
* `CCG.Cat`: categories over a type `α` of atoms.
* `CCG.Cat.Arg`, `CCG.Cat.pushArgs`: an argument, and the category `xβ`.
* `CCG.Cat.target`, `CCG.Cat.args`: the target and the arguments of a category.
* `CCG.Cat.equivTargetArgs`: a category is its target together with its arguments.
* `CCG.Cat.generalizedForwardComp`, `CCG.Cat.generalizedBackwardComp`: composition of degree `n`.
* `CCG.Cat.count`: the count of an atom.

## Main statements

* `CCG.Cat.generalizedForwardComp_eq_some_iff`: forward composition of degree `n` sends `x/y`
  and `yβ` to `xβ` for an argument sequence `β` of length `n`, and is undefined otherwise.

## Notation

* `X / Y`, `X \ Y`: slashes with the unrestricted modality `dot`, written unannotated as in
  Steedman's presentation.
* `X /⋄ Y`, `X \⋄ Y`, `X /× Y`, `X \× Y`, `X /⋆ Y`, `X \⋆ Y`: slashes with the annotated
  modality.

All are scoped to the `CCG` namespace. Because `/` overloads division, categories are written
fully parenthesized (`(S \ NP) / NP`).

## References

* [steedman-2000]
* [steedman-2019]
* [baldridge-2002]
* [kuhlmann-koller-satta-2015]
* [van-benthem-1986]
-/

@[expose] public section

namespace CCG

/-! ### Slash modalities -/

/-- The modality a slash carries, determining which rule classes it licenses. The order is
reverse inclusion of licenses, `s ≤ m` iff `s` licenses every rule class `m` does, so composition
gates on `s ≤ diamond` (harmonic) and `s ≤ cross` (crossing), while application is licensed by
every modality (`s ≤ ⊤`). -/
inductive Modality where
  /-- The unrestricted modality, written as an unannotated slash, combining by any rule. -/
  | dot
  /-- The order-preserving `⋄`, licensing application and harmonic composition. -/
  | diamond
  /-- The permuting `×`, licensing application and crossing composition. -/
  | cross
  /-- The modality `⋆`, licensing application only. -/
  | star
  deriving DecidableEq, Repr, Fintype

namespace Modality

instance : LE Modality where
  le a b := a = dot ∨ a = b ∨ b = star

instance : DecidableLE Modality := fun a b ↦
  inferInstanceAs (Decidable (a = dot ∨ a = b ∨ b = star))

instance : PartialOrder Modality where
  le_refl _ := Or.inr (Or.inl rfl)
  le_trans := by decide
  le_antisymm := by decide

instance : BoundedOrder Modality where
  top := star
  le_top _ := Or.inr (Or.inr rfl)
  bot := dot
  bot_le _ := Or.inl rfl

end Modality

/-! ### Categories -/

/-- CCG categories over a type `α` of atomic categories, built from atoms by directional
slashes that each carry a `Modality`. -/
inductive Cat (α : Type*) where
  /-- An atomic category. -/
  | atom : α → Cat α
  /-- `X/ₘY` looks right for a `Y` to give an `X`, at modality `m`. -/
  | rslash : Cat α → Modality → Cat α → Cat α
  /-- `X\ₘY` looks left for a `Y` to give an `X`, at modality `m`. -/
  | lslash : Cat α → Modality → Cat α → Cat α
  deriving Repr, DecidableEq

scoped notation:60 X "/" Y => Cat.rslash X Modality.dot Y
scoped notation:60 X "\\" Y => Cat.lslash X Modality.dot Y
scoped notation:60 X "/⋄" Y => Cat.rslash X Modality.diamond Y
scoped notation:60 X "\\⋄" Y => Cat.lslash X Modality.diamond Y
scoped notation:60 X "/×" Y => Cat.rslash X Modality.cross Y
scoped notation:60 X "\\×" Y => Cat.lslash X Modality.cross Y
scoped notation:60 X "/⋆" Y => Cat.rslash X Modality.star Y
scoped notation:60 X "\\⋆" Y => Cat.lslash X Modality.star Y

namespace Cat

variable {α : Type*}

/-! ### Targets and arguments -/

/-- An argument of a category, a slash–category pair. -/
structure Arg (α : Type*) where
  /-- The side the slash looks to, `right` for `/` and `left` for `\`. -/
  side : Edge
  /-- The modality of the slash. -/
  modality : Modality
  /-- The argument category. -/
  cat : Cat α
  deriving Repr, DecidableEq

/-- `x.push a` is `x` with `a` as its new outermost argument. -/
def push (x : Cat α) : Arg α → Cat α
  | ⟨.right, m, y⟩ => .rslash x m y
  | ⟨.left, m, y⟩ => .lslash x m y

@[simp] theorem push_right (x y : Cat α) (m : Modality) :
    x.push ⟨.right, m, y⟩ = .rslash x m y := rfl

@[simp] theorem push_left (x y : Cat α) (m : Modality) :
    x.push ⟨.left, m, y⟩ = .lslash x m y := rfl

/-- `x.pushArgs β` is the category `xβ`, which adds the arguments `β` to `x` innermost first, so
that `x.pushArgs [a₁, a₂]` has `a₂` as its outermost argument. -/
def pushArgs (x : Cat α) (β : List (Arg α)) : Cat α := β.foldl push x

@[simp] theorem pushArgs_nil (x : Cat α) : x.pushArgs [] = x := rfl

@[simp] theorem pushArgs_cons (x : Cat α) (a : Arg α) (β : List (Arg α)) :
    x.pushArgs (a :: β) = (x.push a).pushArgs β := rfl

@[simp] theorem pushArgs_append (x : Cat α) (β γ : List (Arg α)) :
    x.pushArgs (β ++ γ) = (x.pushArgs β).pushArgs γ := List.foldl_append

/-- The target of a category, its leftmost atom after stripping all arguments, which plays the
role of a function's return type. -/
def target : Cat α → α
  | .atom a => a
  | .rslash x _ _ => target x
  | .lslash x _ _ => target x

@[simp] theorem target_atom (a : α) : target (atom a) = a := rfl

@[simp] theorem target_rslash (x y : Cat α) (m : Modality) :
    target (rslash x m y) = target x := rfl

@[simp] theorem target_lslash (x y : Cat α) (m : Modality) :
    target (lslash x m y) = target x := rfl

@[simp] theorem target_push (x : Cat α) (a : Arg α) : (x.push a).target = x.target := by
  obtain ⟨_ | _, _, _⟩ := a <;> rfl

@[simp] theorem target_pushArgs (x : Cat α) (β : List (Arg α)) :
    (x.pushArgs β).target = x.target := by
  induction β generalizing x <;> simp [*]

/-- The arguments of a category, innermost first. -/
def args : Cat α → List (Arg α)
  | .atom _ => []
  | .rslash x m y => x.args ++ [⟨.right, m, y⟩]
  | .lslash x m y => x.args ++ [⟨.left, m, y⟩]

@[simp] theorem args_atom (a : α) : args (atom a) = [] := rfl

@[simp] theorem args_rslash (x y : Cat α) (m : Modality) :
    args (rslash x m y) = x.args ++ [⟨.right, m, y⟩] := rfl

@[simp] theorem args_lslash (x y : Cat α) (m : Modality) :
    args (lslash x m y) = x.args ++ [⟨.left, m, y⟩] := rfl

@[simp] theorem args_push (x : Cat α) (a : Arg α) : (x.push a).args = x.args ++ [a] := by
  obtain ⟨_ | _, _, _⟩ := a <;> rfl

@[simp] theorem args_pushArgs (x : Cat α) (β : List (Arg α)) :
    (x.pushArgs β).args = x.args ++ β := by
  induction β generalizing x <;> simp [*]

@[simp] theorem atom_target_pushArgs_args (c : Cat α) : (atom c.target).pushArgs c.args = c := by
  induction c with
  | atom => rfl
  | rslash x m y ih => simp [ih]
  | lslash x m y ih => simp [ih]

/-- Every category is uniquely its target followed by its arguments. -/
def equivTargetArgs : Cat α ≃ α × List (Arg α) where
  toFun c := (c.target, c.args)
  invFun p := (atom p.1).pushArgs p.2
  left_inv := atom_target_pushArgs_args
  right_inv p := by simp

theorem atom_pushArgs_eq_iff {a : α} {β : List (Arg α)} {c : Cat α} :
    (atom a).pushArgs β = c ↔ a = c.target ∧ β = c.args :=
  (equivTargetArgs.symm_apply_eq (x := (a, β))).trans Prod.ext_iff

/-! ### Type-raising

Type-raising is morpholexical in [steedman-2019], the work of case morphemes rather than a
syntactic rule, so these build the categories that raised lexical entries carry. -/

/-- `forwardTypeRaise x t` is `t / (t \ x)`, the forward-raised (`>T`) category of `x` at
target `t`. -/
def forwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t / (t \ x)

/-- `backwardTypeRaise x t` is `t \ (t / x)`, the backward-raised (`<T`) category of `x` at
target `t`. -/
def backwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t \ (t / x)

variable [DecidableEq α]

/-! ### The generalized composition schema -/

/-- `generalizedForwardComp n f g` is forward composition of degree `n` (`>Bⁿ`). When `f = X/Y`
and `g = Y|Z₁…|Zₙ`, the result is `X|Z₁…|Zₙ` with each argument keeping its own slash direction
and modality, and `none` otherwise. The schema is modality-blind, as in the grammars of
`Syntax/CCG/Grammar`, where rule control is per-grammar rather than lexical. -/
def generalizedForwardComp : ℕ → Cat α → Cat α → Option (Cat α)
  | 0, .rslash x _ y, z => if y = z then some x else none
  | n + 1, f, .rslash g m z => (generalizedForwardComp n f g).map (Cat.rslash · m z)
  | n + 1, f, .lslash g m z => (generalizedForwardComp n f g).map (Cat.lslash · m z)
  | _, _, _ => none

/-- `generalizedBackwardComp n g f` is backward composition of degree `n` (`<Bⁿ`), the mirror of
`generalizedForwardComp`. When `g = Y|Z₁…|Zₙ` and `f = X\Y`, the result is `X|Z₁…|Zₙ`, and
`none` otherwise. -/
def generalizedBackwardComp : ℕ → Cat α → Cat α → Option (Cat α)
  | 0, z, .lslash x _ y => if y = z then some x else none
  | n + 1, .rslash g m z, f => (generalizedBackwardComp n g f).map (Cat.rslash · m z)
  | n + 1, .lslash g m z, f => (generalizedBackwardComp n g f).map (Cat.lslash · m z)
  | _, _, _ => none

/-- An atomic primary fails forward composition, having no argument to cancel. -/
@[simp] theorem generalizedForwardComp_atom (n : ℕ) (x : α) (b : Cat α) :
    generalizedForwardComp n (atom x) b = none := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => cases b <;> simp [generalizedForwardComp, ih]

/-- A leftward primary fails forward composition at every degree. -/
@[simp] theorem generalizedForwardComp_lslash (n : ℕ) (x y : Cat α) (m : Modality)
    (b : Cat α) : generalizedForwardComp n (lslash x m y) b = none := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => cases b <;> simp [generalizedForwardComp, ih]

@[simp] theorem generalizedBackwardComp_atom (n : ℕ) (a : Cat α) (x : α) :
    generalizedBackwardComp n a (atom x) = none := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => cases a <;> simp [generalizedBackwardComp, ih]

/-- A rightward primary fails backward composition at every degree. -/
@[simp] theorem generalizedBackwardComp_rslash (n : ℕ) (a : Cat α) (x y : Cat α)
    (m : Modality) : generalizedBackwardComp n a (rslash x m y) = none := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => cases a <;> simp [generalizedBackwardComp, ih]

/-- An atomic secondary has no argument for composition of positive degree to pass on. -/
@[simp] theorem generalizedForwardComp_succ_atom (n : ℕ) (f : Cat α) (x : α) :
    generalizedForwardComp (n + 1) f (atom x) = none := rfl

@[simp] theorem generalizedBackwardComp_succ_atom (n : ℕ) (x : α) (b : Cat α) :
    generalizedBackwardComp (n + 1) (atom x) b = none := rfl

/-- Forward composition of degree `n` combines `x/y` with `yβ` into `xβ`, for `β` of
length `n`. -/
@[simp] theorem generalizedForwardComp_pushArgs (x y : Cat α) (m : Modality)
    (β : List (Arg α)) :
    generalizedForwardComp β.length (rslash x m y) (y.pushArgs β) = some (x.pushArgs β) := by
  induction β using List.reverseRecOn with
  | nil => simp [generalizedForwardComp]
  | append_singleton β a ih => obtain ⟨_ | _, _, _⟩ := a <;> simp [generalizedForwardComp, ih]

/-- Backward composition of degree `n` combines `yβ` with `x\y` into `xβ`, for `β` of
length `n`. -/
@[simp] theorem generalizedBackwardComp_pushArgs (x y : Cat α) (m : Modality)
    (β : List (Arg α)) :
    generalizedBackwardComp β.length (y.pushArgs β) (lslash x m y) = some (x.pushArgs β) := by
  induction β using List.reverseRecOn with
  | nil => simp [generalizedBackwardComp]
  | append_singleton β a ih => obtain ⟨_ | _, _, _⟩ := a <;> simp [generalizedBackwardComp, ih]

/-- Forward composition of degree `n` is defined exactly on a primary `x/y` and a secondary `yβ`
with `β` of length `n`, the rule form `X/Y Yβ ⇒ Xβ` of [kuhlmann-koller-satta-2015]. -/
theorem generalizedForwardComp_eq_some_iff {n : ℕ} {f g c : Cat α} :
    generalizedForwardComp n f g = some c ↔ ∃ x m y, ∃ β : List (Arg α),
      β.length = n ∧ f = rslash x m y ∧ g = y.pushArgs β ∧ c = x.pushArgs β := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · induction n generalizing g c with
    | zero =>
      cases f with
      | rslash x m y =>
        simp only [generalizedForwardComp, Option.ite_none_right_eq_some, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨x, m, y, [], rfl, rfl, rfl, rfl⟩
      | _ => simp at h
    | succ n ih =>
      cases g with
      | atom => simp at h
      | rslash g m' z =>
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨x, m, y, β, rfl, rfl, rfl, rfl⟩ := ih hc
        exact ⟨x, m, y, β ++ [⟨.right, m', z⟩], by simp, rfl, by simp, by simp⟩
      | lslash g m' z =>
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨x, m, y, β, rfl, rfl, rfl, rfl⟩ := ih hc
        exact ⟨x, m, y, β ++ [⟨.left, m', z⟩], by simp, rfl, by simp, by simp⟩
  · rintro ⟨x, m, y, β, rfl, rfl, rfl, rfl⟩
    exact generalizedForwardComp_pushArgs x y m β

/-- Backward composition of degree `n` is defined exactly on a secondary `yβ` and a primary
`x\y` with `β` of length `n`, the rule form `Yβ X\Y ⇒ Xβ`. -/
theorem generalizedBackwardComp_eq_some_iff {n : ℕ} {g f c : Cat α} :
    generalizedBackwardComp n g f = some c ↔ ∃ x m y, ∃ β : List (Arg α),
      β.length = n ∧ f = lslash x m y ∧ g = y.pushArgs β ∧ c = x.pushArgs β := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · induction n generalizing g c with
    | zero =>
      cases f with
      | lslash x m y =>
        simp only [generalizedBackwardComp, Option.ite_none_right_eq_some,
          Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨x, m, y, [], rfl, rfl, rfl, rfl⟩
      | _ => simp at h
    | succ n ih =>
      cases g with
      | atom => simp at h
      | rslash g m' z =>
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨x, m, y, β, rfl, rfl, rfl, rfl⟩ := ih hc
        exact ⟨x, m, y, β ++ [⟨.right, m', z⟩], by simp, rfl, by simp, by simp⟩
      | lslash g m' z =>
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨x, m, y, β, rfl, rfl, rfl, rfl⟩ := ih hc
        exact ⟨x, m, y, β ++ [⟨.left, m', z⟩], by simp, rfl, by simp, by simp⟩
  · rintro ⟨x, m, y, β, rfl, rfl, rfl, rfl⟩
    exact generalizedBackwardComp_pushArgs x y m β

/-! ### The count invariant -/

/-- The count of the atom `a` in a category ([van-benthem-1986]) adds `1` for each occurrence in
result position and subtracts `1` for each occurrence in argument position, so that every
combinatory rule preserves it (`CCG.Rule.count_eq`). -/
def count (a : α) : Cat α → ℤ
  | .atom b => if b = a then 1 else 0
  | .rslash x _ y => count a x - count a y
  | .lslash x _ y => count a x - count a y

@[simp] theorem count_atom (a b : α) : count a (atom b) = if b = a then 1 else 0 := rfl

@[simp] theorem count_rslash (a : α) (x y : Cat α) (m : Modality) :
    count a (rslash x m y) = count a x - count a y := rfl

@[simp] theorem count_lslash (a : α) (x y : Cat α) (m : Modality) :
    count a (lslash x m y) = count a x - count a y := rfl

end Cat

end CCG
