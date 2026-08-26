import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Function.Basic

/-!
# PIP — Plural Intensional Presuppositional predicate calculus

[keshet-abney-2024] [abney-keshet-2025]

PIP is first-order predicate calculus with set abstraction and equality,
whose domain consists of pluralities (sets of atoms, worlds among them),
supplemented by five eliminable constructs: bracketed *local* variables
`[x]` slated for unselective closure, summation `Σxφ`, formula labels
`X ≡ φ` and their uses `X`, world arguments on predicates, and
presuppositions `φ|ψ`. A discourse `φ₁, …, φₙ` means `Σw(φ₁ ∧ … ∧ φₙ)` and is
true iff that plurality of worlds is nonempty; it is felicitous iff its label
definitions form a function, it has no free non-local variables, and the
felicity operator `F` — defined on the presupposition operator and the
primitive connectives, with Karttunen's asymmetric conjunction — holds of
its closure. Truth and felicity are independent: `φ|ψ` is true iff `φ` is.

The syntax is the formal one of [abney-keshet-2025] (§2.4); the semantics
composes its translation `T_A` into set theory with evaluation, so `Σxφ`
denotes the union of the values of `x` under existential closure of the
other local variables of `φ`.

## Main definitions

* `Term`, `Formula` — the mutual syntax; `Term.locals`, `Formula.locals` the
  local variables.
* `Model` — atoms and the interpretation of predicates over pluralities.
* `Term.mem`, `Term.val`, `Formula.sat` — value and truth relative to a model
  and an assignment, with `closeOver` the existential closure over a list of
  variables.
* `Term.fel`, `Formula.fel` — the felicity operator `F`.
* `Formula.substLabel`, `Formula.expand`, `Formula.defs`,
  `Formula.expandSelf` — label assignment and expansion; `Formula.disj`,
  `Formula.impl`, `Formula.forall_` — the defined connectives.
* `Term.elim`, `Formula.elim` — the translation eliminating the PIP
  constructs.

## Main statements

* `Formula.sat_elim` — the PIP constructs are eliminable: the translation
  preserves truth.
* `Formula.fel_disj`, `Formula.fel_impl`, `Formula.fel_forall` — the derived
  felicity clauses.
* `Formula.sat_exists_iff_abs_nonempty` — `∃xφ` is true iff `⋃{x : φ}` is
  nonempty, when `φ` is false of the null plurality.
* `Term.fel_sigma_conj`, `Term.fel_sigma_conj_of_fel` — felicity of a
  discourse extended by a sentence reduces to the earlier discourse strictly
  implying the new sentence's felicity.
-/

namespace PIP

universe u v w

mutual
/-- Terms: external variables, bracketed local variables `[x]`, set
abstraction `⋃{x : φ}`, summation `Σxφ`, and a term with a presupposition
`τ|ψ`. -/
inductive Term (V : Type u) (L : Type v) (P : Type w)
  | var (x : V)
  | bvar (x : V)
  | abs (x : V) (φ : Formula V L P)
  | sigma (x : V) (φ : Formula V L P)
  | presup (t : Term V L P) (ψ : Formula V L P)
/-- Formulas: the constant `⊤`, predication, equality, negation,
conjunction, selective existential quantification, presupposition `φ|ψ`,
label definition `X ≡ φ`, and label use `X`. -/
inductive Formula (V : Type u) (L : Type v) (P : Type w)
  | top
  | atom {n : ℕ} (p : P) (ts : Fin n → Term V L P)
  | eq (s t : Term V L P)
  | neg (φ : Formula V L P)
  | conj (φ ψ : Formula V L P)
  | exists_ (x : V) (φ : Formula V L P)
  | presup (φ ψ : Formula V L P)
  | labelDef (X : L) (φ : Formula V L P)
  | label (X : L)
end

variable {V L P α : Type*}

/-- Disjunction, as `¬(¬φ ∧ ¬ψ)`. -/
def Formula.disj (φ ψ : Formula V L P) : Formula V L P := .neg (.conj (.neg φ) (.neg ψ))

/-- Implication, as `¬(φ ∧ ¬ψ)`. -/
def Formula.impl (φ ψ : Formula V L P) : Formula V L P := .neg (.conj φ (.neg ψ))

/-- Universal quantification, as `¬∃x¬φ`. -/
def Formula.forall_ (x : V) (φ : Formula V L P) : Formula V L P := .neg (.exists_ x (.neg φ))

section Locals

variable [DecidableEq V]

mutual
/-- The local variables of a term: bracketed occurrences at top level, with
summation and set abstraction binding theirs. -/
def Term.locals : Term V L P → List V
  | .var _ => []
  | .bvar x => [x]
  | .abs x φ => φ.locals.filter (· ≠ x)
  | .sigma _ _ => []
  | .presup t ψ => t.locals ++ ψ.locals
/-- The local variables of a formula. -/
def Formula.locals : Formula V L P → List V
  | .top => []
  | .atom _ ts => (List.finRange _).flatMap fun i => (ts i).locals
  | .eq s t => s.locals ++ t.locals
  | .neg φ => φ.locals
  | .conj φ ψ => φ.locals ++ ψ.locals
  | .exists_ x φ => φ.locals.filter (· ≠ x)
  | .presup φ ψ => φ.locals ++ ψ.locals
  | .labelDef _ _ => []
  | .label _ => []
end

end Locals

/-! ### Semantics -/

/-- A model: pluralities are sets of atoms `α`, and each predicate is
interpreted over tuples of pluralities (its first argument a world, by
convention). -/
structure Model (P α : Type*) where
  /-- The interpretation of predicates. -/
  I : P → ∀ {n : ℕ}, (Fin n → Set α) → Prop

/-- Existential closure of `Q` over the variables `xs`, starting from `g`. -/
def closeOver [DecidableEq V] (xs : List V) (g : V → Set α) (Q : (V → Set α) → Prop) : Prop :=
  match xs with
  | [] => Q g
  | x :: xs => ∃ d, closeOver xs (Function.update g x d) Q

/-- Universal closure of `Q` over the variables `xs`, starting from `g`. -/
def forallOver [DecidableEq V] (xs : List V) (g : V → Set α) (Q : (V → Set α) → Prop) : Prop :=
  match xs with
  | [] => Q g
  | x :: xs => ∀ d, forallOver xs (Function.update g x d) Q

section Semantics

variable [DecidableEq V]

theorem closeOver_congr {xs : List V} {g : V → Set α} {Q Q' : (V → Set α) → Prop}
    (h : ∀ h, Q h ↔ Q' h) : closeOver xs g Q ↔ closeOver xs g Q' := by
  induction xs generalizing g with
  | nil => exact h g
  | cons x xs ih => exact exists_congr fun d => ih

theorem forallOver_and {xs : List V} {g : V → Set α} {A B : (V → Set α) → Prop} :
    forallOver xs g (fun h => A h ∧ B h) ↔ forallOver xs g A ∧ forallOver xs g B := by
  induction xs generalizing g with
  | nil => exact Iff.rfl
  | cons x xs ih => simp only [forallOver, ih, forall_and]

mutual
/-- Membership in the value of a term: a variable's assignment, the union of
the abstracted values, the union of the summed values under closure of the
other local variables, and the body of a presupposed term. -/
def Term.mem (M : Model P α) (g : V → Set α) : Term V L P → α → Prop
  | .var x, a => a ∈ g x
  | .bvar x, a => a ∈ g x
  | .abs x φ, a => ∃ d, φ.sat M (Function.update g x d) ∧ a ∈ d
  | .sigma x φ, a =>
      ∃ d, closeOver (φ.locals.filter (· ≠ x)) (Function.update g x d) (fun h => φ.sat M h) ∧ a ∈ d
  | .presup t _, a => t.mem M g a
/-- Truth of a formula: classical, with presuppositions and label definitions
transparent and an unexpanded label false. -/
def Formula.sat (M : Model P α) (g : V → Set α) : Formula V L P → Prop
  | .top => True
  | .atom p ts => M.I p fun i => {a | (ts i).mem M g a}
  | .eq s t => {a | s.mem M g a} = {a | t.mem M g a}
  | .neg φ => ¬ φ.sat M g
  | .conj φ ψ => φ.sat M g ∧ ψ.sat M g
  | .exists_ x φ => ∃ d, φ.sat M (Function.update g x d)
  | .presup φ _ => φ.sat M g
  | .labelDef _ _ => True
  | .label _ => False
end

/-- The value of a term. -/
def Term.val (M : Model P α) (g : V → Set α) (t : Term V L P) : Set α := {a | t.mem M g a}

mutual
/-- Felicity of a term: `τ|ψ` needs `τ` and `ψ` felicitous and `ψ` true;
abstraction and summation need their bodies felicitous for every value. -/
def Term.fel (M : Model P α) (g : V → Set α) : Term V L P → Prop
  | .var _ => True
  | .bvar _ => True
  | .abs x φ => ∀ d, φ.fel M (Function.update g x d)
  | .sigma x φ =>
      ∀ d, forallOver (φ.locals.filter (· ≠ x)) (Function.update g x d) fun h => φ.fel M h
  | .presup t ψ => t.fel M g ∧ ψ.fel M g ∧ ψ.sat M g
/-- Felicity of a formula: the operator `F`, with Karttunen's asymmetric
conjunction — the first conjunct may satisfy the presuppositions of the
second. -/
def Formula.fel (M : Model P α) (g : V → Set α) : Formula V L P → Prop
  | .top => True
  | .atom _ ts => ∀ i, (ts i).fel M g
  | .eq s t => s.fel M g ∧ t.fel M g
  | .neg φ => φ.fel M g
  | .conj φ ψ => φ.fel M g ∧ (φ.sat M g → ψ.fel M g)
  | .exists_ x φ => ∀ d, φ.fel M (Function.update g x d)
  | .presup φ ψ => φ.fel M g ∧ ψ.fel M g ∧ ψ.sat M g
  | .labelDef _ _ => True
  | .label _ => False
end

variable (M : Model P α) (g : V → Set α)

@[simp] theorem Term.val_var (x : V) : (Term.var x : Term V L P).val M g = g x := rfl

@[simp] theorem Term.val_bvar (x : V) : (Term.bvar x : Term V L P).val M g = g x := rfl

theorem Term.val_sigma (x : V) (φ : Formula V L P) :
    (Term.sigma x φ).val M g =
      ⋃₀ {d | closeOver (φ.locals.filter (· ≠ x)) (Function.update g x d) fun h => φ.sat M h} := by
  ext a; simp [Term.val, Term.mem, Set.mem_sUnion]

/-! ### Derived clauses -/

theorem Formula.sat_disj (φ ψ : Formula V L P) :
    (φ.disj ψ).sat M g ↔ φ.sat M g ∨ ψ.sat M g :=
  show ¬(¬φ.sat M g ∧ ¬ψ.sat M g) ↔ _ from or_iff_not_and_not.symm

theorem Formula.sat_impl (φ ψ : Formula V L P) :
    (φ.impl ψ).sat M g ↔ (φ.sat M g → ψ.sat M g) :=
  show ¬(φ.sat M g ∧ ¬ψ.sat M g) ↔ _ from not_and_not_right

theorem Formula.sat_forall (x : V) (φ : Formula V L P) :
    (Formula.forall_ x φ).sat M g ↔ ∀ d, φ.sat M (Function.update g x d) :=
  show ¬(∃ d, ¬φ.sat M (Function.update g x d)) ↔ _ from not_exists_not

/-- `F(φ ∨ ψ)` iff `Fφ ∧ (¬φ → Fψ)`. -/
theorem Formula.fel_disj (φ ψ : Formula V L P) :
    (φ.disj ψ).fel M g ↔ φ.fel M g ∧ (¬ φ.sat M g → ψ.fel M g) :=
  show φ.fel M g ∧ (¬φ.sat M g → ψ.fel M g) ↔ _ from Iff.rfl

/-- `F(φ → ψ)` iff `Fφ ∧ (φ → Fψ)`. -/
theorem Formula.fel_impl (φ ψ : Formula V L P) :
    (φ.impl ψ).fel M g ↔ φ.fel M g ∧ (φ.sat M g → ψ.fel M g) :=
  show φ.fel M g ∧ (φ.sat M g → ψ.fel M g) ↔ _ from Iff.rfl

/-- `F(∀xφ)` iff `∀x Fφ`. -/
theorem Formula.fel_forall (x : V) (φ : Formula V L P) :
    (Formula.forall_ x φ).fel M g ↔ ∀ d, φ.fel M (Function.update g x d) :=
  show (∀ d, φ.fel M (Function.update g x d)) ↔ _ from Iff.rfl

/-- `∃xφ` is true iff `⋃{x : φ}` is nonempty, provided `φ` is false of the
null plurality — the standing assumption that predicates are false of the
null individual. -/
theorem Formula.sat_exists_iff_abs_nonempty (x : V) (φ : Formula V L P)
    (h : ¬ φ.sat M (Function.update g x ∅)) :
    (Formula.exists_ x φ).sat M g ↔ ((Term.abs x φ).val M g).Nonempty := by
  show (∃ d, φ.sat M (Function.update g x d)) ↔ ∃ a, ∃ d, φ.sat M (Function.update g x d) ∧ a ∈ d
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr fun he => h (he ▸ hd)
    exact ⟨a, d, hd, ha⟩
  · rintro ⟨_, d, hd, _⟩
    exact ⟨d, hd⟩

/-- Felicity of a discourse extended by a sentence: `F Σw(γ ∧ φ)` iff, for every
world and every value of the local variables, `Fγ ∧ (γ → Fφ)`. -/
theorem Term.fel_sigma_conj (w : V) (γ φ : Formula V L P) :
    (Term.sigma w (γ.conj φ)).fel M g ↔
      ∀ d, forallOver ((γ.conj φ).locals.filter (· ≠ w)) (Function.update g w d)
        fun h => γ.fel M h ∧ (γ.sat M h → φ.fel M h) := Iff.rfl

/-- Given that the discourse so far is felicitous for all values of the local
variables, the extended discourse is felicitous iff the discourse so far
strictly implies the felicity of the new sentence. -/
theorem Term.fel_sigma_conj_of_fel (w : V) (γ φ : Formula V L P)
    (hγ : ∀ d, forallOver ((γ.conj φ).locals.filter (· ≠ w)) (Function.update g w d)
      fun h => γ.fel M h) :
    (Term.sigma w (γ.conj φ)).fel M g ↔
      ∀ d, forallOver ((γ.conj φ).locals.filter (· ≠ w)) (Function.update g w d)
        fun h => γ.sat M h → φ.fel M h := by
  rw [Term.fel_sigma_conj]
  exact forall_congr' fun d => forallOver_and.trans (and_iff_right (hγ d))

/-! ### Labels -/

section Labels

variable [DecidableEq L]

mutual
/-- Replace the uses of label `X` by `ψ`. -/
def Term.substLabel (X : L) (ψ : Formula V L P) : Term V L P → Term V L P
  | .var x => .var x
  | .bvar x => .bvar x
  | .abs x φ => .abs x (Formula.substLabel X ψ φ)
  | .sigma x φ => .sigma x (Formula.substLabel X ψ φ)
  | .presup t χ => .presup (Term.substLabel X ψ t) (Formula.substLabel X ψ χ)
/-- Replace the uses of label `X` by `ψ`. -/
def Formula.substLabel (X : L) (ψ : Formula V L P) : Formula V L P → Formula V L P
  | .top => .top
  | .atom p ts => .atom p fun i => Term.substLabel X ψ (ts i)
  | .eq s t => .eq (Term.substLabel X ψ s) (Term.substLabel X ψ t)
  | .neg φ => .neg (Formula.substLabel X ψ φ)
  | .conj φ χ => .conj (Formula.substLabel X ψ φ) (Formula.substLabel X ψ χ)
  | .exists_ x φ => .exists_ x (Formula.substLabel X ψ φ)
  | .presup φ χ => .presup (Formula.substLabel X ψ φ) (Formula.substLabel X ψ χ)
  | .labelDef Y φ => .labelDef Y (Formula.substLabel X ψ φ)
  | .label Y => if Y = X then ψ else .label Y
end

/-- Expand a formula relative to a label assignment, given as the list of
definitions in the order they were made; later definitions may use earlier
ones, so they are substituted first. -/
def Formula.expand (A : List (L × Formula V L P)) (φ : Formula V L P) : Formula V L P :=
  A.foldr (fun d acc => Formula.substLabel d.1 d.2 acc) φ

mutual
/-- The label definitions occurring in a term, in order. -/
def Term.defs : Term V L P → List (L × Formula V L P)
  | .var _ => []
  | .bvar _ => []
  | .abs _ φ => φ.defs
  | .sigma _ φ => φ.defs
  | .presup t ψ => t.defs ++ ψ.defs
/-- The label definitions occurring in a formula, in order. -/
def Formula.defs : Formula V L P → List (L × Formula V L P)
  | .top => []
  | .atom _ ts => (List.finRange _).flatMap fun i => (ts i).defs
  | .eq s t => s.defs ++ t.defs
  | .neg φ => φ.defs
  | .conj φ ψ => φ.defs ++ ψ.defs
  | .exists_ _ φ => φ.defs
  | .presup φ ψ => φ.defs ++ ψ.defs
  | .labelDef X φ => (X, φ) :: φ.defs
  | .label _ => []
end

/-- The discourse translation: expand a discourse by its own label
definitions. -/
def Formula.expandSelf (φ : Formula V L P) : Formula V L P := φ.expand φ.defs

end Labels

/-! ### Eliminability -/

/-- Existential closure over a list of variables, as syntax. -/
def Formula.closeList (xs : List V) (φ : Formula V L P) : Formula V L P :=
  xs.foldr Formula.exists_ φ

theorem Formula.sat_closeList (xs : List V) (φ : Formula V L P) :
    ∀ g : V → Set α, (φ.closeList xs).sat M g ↔ closeOver xs g fun h => φ.sat M h := by
  induction xs with
  | nil => exact fun _ => Iff.rfl
  | cons x xs ih =>
    intro g
    show (∃ d, (φ.closeList xs).sat M (Function.update g x d)) ↔ ∃ d, closeOver xs _ _
    exact exists_congr fun d => ih _

mutual
/-- Translation into predicate calculus with set abstraction: brackets and
presuppositions are dropped, summation becomes abstraction over the closure
of the other local variables, label definitions become `⊤`. -/
def Term.elim : Term V L P → Term V L P
  | .var x => .var x
  | .bvar x => .var x
  | .abs x φ => .abs x φ.elim
  | .sigma x φ => .abs x (φ.elim.closeList (φ.locals.filter (· ≠ x)))
  | .presup t _ => t.elim
/-- Translation into predicate calculus with set abstraction. -/
def Formula.elim : Formula V L P → Formula V L P
  | .top => .top
  | .atom p ts => .atom p fun i => (ts i).elim
  | .eq s t => .eq s.elim t.elim
  | .neg φ => .neg φ.elim
  | .conj φ ψ => .conj φ.elim ψ.elim
  | .exists_ x φ => .exists_ x φ.elim
  | .presup φ _ => φ.elim
  | .labelDef _ _ => .top
  | .label X => .label X
end

mutual
/-- The translation preserves values. -/
theorem Term.mem_elim : ∀ (g : V → Set α) (t : Term V L P) (a : α),
    t.elim.mem M g a ↔ t.mem M g a
  | _, .var _, _ => Iff.rfl
  | _, .bvar _, _ => Iff.rfl
  | g, .abs x φ, a =>
      show (∃ d, φ.elim.sat M (Function.update g x d) ∧ a ∈ d) ↔ ∃ d, _ ∧ a ∈ d from
        exists_congr fun _ => and_congr_left' (Formula.sat_elim _ φ)
  | g, .sigma x φ, a =>
      show (∃ d, (φ.elim.closeList _).sat M (Function.update g x d) ∧ a ∈ d) ↔
          ∃ d, closeOver _ _ _ ∧ a ∈ d from
        exists_congr fun _ => and_congr_left'
          ((Formula.sat_closeList M _ _ _).trans (closeOver_congr fun h => Formula.sat_elim h φ))
  | g, .presup t _, a => Term.mem_elim g t a
/-- The PIP constructs are eliminable: the translation preserves truth. -/
theorem Formula.sat_elim : ∀ (g : V → Set α) (φ : Formula V L P), φ.elim.sat M g ↔ φ.sat M g
  | _, .top => Iff.rfl
  | g, .atom p ts => by
      show M.I p (fun i => {a | (ts i).elim.mem M g a}) ↔ M.I p (fun i => {a | (ts i).mem M g a})
      rw [show (fun i => {a | (ts i).elim.mem M g a}) = fun i => {a | (ts i).mem M g a} from
        funext fun i => Set.ext fun a => Term.mem_elim g (ts i) a]
  | g, .eq s t => by
      show {a | s.elim.mem M g a} = {a | t.elim.mem M g a} ↔ {a | s.mem M g a} = {a | t.mem M g a}
      rw [Set.ext fun a => Term.mem_elim g s a, Set.ext fun a => Term.mem_elim g t a]
  | g, .neg φ => not_congr (Formula.sat_elim g φ)
  | g, .conj φ ψ => and_congr (Formula.sat_elim g φ) (Formula.sat_elim g ψ)
  | g, .exists_ x φ => exists_congr fun _ => Formula.sat_elim _ φ
  | g, .presup φ _ => Formula.sat_elim g φ
  | _, .labelDef _ _ => Iff.rfl
  | _, .label _ => Iff.rfl
end

end Semantics

end PIP
