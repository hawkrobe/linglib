import Mathlib.Data.PFun
import Linglib.Semantics.Composition.Tree

/-!
# Partial interpretation

This file is [heim-kratzer-1998]'s composition engine on partial denotations. A function
denotes a partial function, mathlib's `PFun`, whose domain is the definedness condition the
book attaches to a lexical entry, and a node denotes a `Part` value of its type, defined when
its daughters are and the function among them is defined at its argument. Functional
Application in either order and Predicate Modification are the modes; a trace denotes the value
of its index and a binder abstracts over its index, the abstract being a partial function that
is undefined wherever the body is. Predicate Abstraction therefore needs no distributor, and the
undefined value is the abstract's own fallback, not a probe.

The book's distinction between uninterpretability and presupposition failure (§4.4.4) is the
difference between the engine returning no denotation and returning an undefined one:
`Uninterpretable` is decided by the types of the leaves alone (`uninterpretable_congr`), and
`PresupFailure` asks after the denotations. The definite article is the book's Fregean entry
(`the`), defined on the predicates true of exactly one individual.

## Main declarations

* `Ty.PDomain` and `PDenotation` are the partial domains and denotations.
* `Partial.interp` is the engine, with the modes `Partial.applyForward`, `Partial.applyBackward`
  and `Partial.pm`, and `Partial.binary` trying them in order.
* `Partial.Uninterpretable` and `Partial.PresupFailure` are the two ways of lacking a value, and
  `Partial.interp_map_fst_congr` shows the first depends on the leaves' types alone.
* `Partial.the` is the definite article, with `Partial.the_dom` its definedness condition.

## References

* [heim-kratzer-1998]
-/

namespace Semantics.Composition

/-- Partial denotation domains, as `Ty.Domain` but with functions the partial functions `→.`,
whose domain is a lexical entry's definedness condition. -/
abbrev Ty.PDomain (E W : Type) (ty : Ty) (D : Type := ℝ) : Type :=
  match ty with
  | .e => E
  | .t => Prop
  | .d => D
  | .n => ℕ
  | .v => Empty
  | .s => Empty
  | .fn a b => Ty.PDomain E W a D →. Ty.PDomain E W b D
  | .intens a => W →. Ty.PDomain E W a D

/-- A partial denotation is a semantic type with a possibly undefined value in its partial
domain. -/
abbrev PDenotation (E W : Type) (D : Type := ℝ) : Type :=
  (ty : Ty) × Part (Ty.PDomain E W ty D)

namespace Partial

open Syntax Tree
open scoped Assignment

variable {E W D : Type}

/-! ### Composition modes -/

/-- Forward functional application, the function being the left daughter. The node is defined
when both daughters are and the function is defined at the argument. -/
def applyForward (df da : PDenotation E W D) : Option (PDenotation E W D) :=
  match hf : df.1 with
  | .fn σ τ =>
    if ha : σ = da.1 then
      let f : Part (Ty.PDomain E W (σ ⇒ τ) D) := hf ▸ df.2
      let a : Part (Ty.PDomain E W σ D) := ha ▸ da.2
      some ⟨τ, f.bind fun fv ↦ a.bind fv⟩
    else none
  | _ => none

/-- Backward functional application, the function being the right daughter. -/
def applyBackward (da df : PDenotation E W D) : Option (PDenotation E W D) :=
  match hf : df.1 with
  | .fn σ τ =>
    if ha : σ = da.1 then
      let f : Part (Ty.PDomain E W (σ ⇒ τ) D) := hf ▸ df.2
      let a : Part (Ty.PDomain E W σ D) := ha ▸ da.2
      some ⟨τ, f.bind fun fv ↦ a.bind fv⟩
    else none
  | _ => none

/-- Predicate modification conjoins two partial predicates, the conjunction being defined where
both are. -/
def pm (d₁ d₂ : PDenotation E W D) : Option (PDenotation E W D) :=
  match h₁ : d₁.1, h₂ : d₂.1 with
  | .fn .e .t, .fn .e .t =>
    let p : Part (Ty.PDomain E W (.e ⇒ .t) D) := h₁ ▸ d₁.2
    let q : Part (Ty.PDomain E W (.e ⇒ .t) D) := h₂ ▸ d₂.2
    some ⟨.fn .e .t, p.bind fun P ↦ q.bind fun Q ↦
      Part.some fun x ↦ (P x).bind fun a ↦ (Q x).map fun b ↦ a ∧ b⟩
  | _, _ => none

/-- The modes a binary node tries, in order. -/
def binary (d₁ d₂ : PDenotation E W D) : Option (PDenotation E W D) :=
  applyForward d₁ d₂ <|> applyBackward d₁ d₂ <|> pm d₁ d₂

/-- The type a binary node composes to, a function of the daughters' types alone. -/
def tyBinary (σ τ : Ty) : Option Ty := tyForward σ τ <|> tyForward τ σ <|> tyPM σ τ

theorem applyForward_map_fst (d₁ d₂ : PDenotation E W D) :
    (applyForward d₁ d₂).map (·.1) = tyForward d₁.1 d₂.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold applyForward tyForward
  dsimp only
  split <;> (try split_ifs) <;> simp_all

theorem applyBackward_map_fst (d₁ d₂ : PDenotation E W D) :
    (applyBackward d₁ d₂).map (·.1) = tyForward d₂.1 d₁.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold applyBackward tyForward
  dsimp only
  split <;> (try split_ifs) <;> simp_all

theorem pm_map_fst (d₁ d₂ : PDenotation E W D) : (pm d₁ d₂).map (·.1) = tyPM d₁.1 d₂.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold pm tyPM
  dsimp only
  split <;> simp_all

theorem binary_map_fst (d₁ d₂ : PDenotation E W D) :
    (binary d₁ d₂).map (·.1) = tyBinary d₁.1 d₂.1 := by
  simp only [binary, tyBinary, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.map_or,
    applyForward_map_fst, applyBackward_map_fst, pm_map_fst]

/-! ### Evaluation on defined daughters

These are rewriting lemmas rather than `simp` lemmas, since the reducible `Ty.PDomain` keys a
concrete domain and a variable one differently for `simp`'s index. -/

/-- Forward application of a defined function to a defined argument evaluates the function. -/
theorem applyForward_some_some {σ τ : Ty} (f : Ty.PDomain E W (σ ⇒ τ) D)
    (a : Ty.PDomain E W σ D) :
    applyForward (⟨σ ⇒ τ, Part.some f⟩ : PDenotation E W D) ⟨σ, Part.some a⟩ =
      some ⟨τ, f a⟩ := by
  simp [applyForward]

/-- A binary node whose left daughter is a defined function over the right daughter's type
applies it forward. -/
theorem binary_some_some {σ τ : Ty} (f : Ty.PDomain E W (σ ⇒ τ) D)
    (a : Ty.PDomain E W σ D) :
    binary (⟨σ ⇒ τ, Part.some f⟩ : PDenotation E W D) ⟨σ, Part.some a⟩ = some ⟨τ, f a⟩ := by
  rw [binary, applyForward_some_some]; rfl

/-! ### Tree interpretation -/

/-- The value of an interpreted daughter at the type `τ`, which is undefined where the daughter
is uninterpretable or of another type. -/
def valueAt (τ : Ty) : Option (PDenotation E W D) → Part (Ty.PDomain E W τ D)
  | some ⟨ty, v⟩ => if h : ty = τ then h ▸ v else Part.none
  | none => Part.none

variable {C : Type} {L : Type*}

/-- The partial denotation of a tree under an assignment: a terminal denotes what its leaf
interpretation gives it, a non-branching node what its daughter does, a binary node what
`binary` composes, a trace the value of its index, and a binder the partial function
abstracting over its index in the body. -/
def interp (lex : L → Option (PDenotation E W D)) (g : Assignment E) :
    Tree C L → Option (PDenotation E W D)
  | .terminal _ w => lex w
  | .node _ (t :: []) => interp lex g t
  | .node _ (t₁ :: t₂ :: []) => do
    let d₁ ← interp lex g t₁
    let d₂ ← interp lex g t₂
    binary d₁ d₂
  | .node _ _ => none
  | .trace n _ => some ⟨.e, Part.some (g n)⟩
  | .bind n _ body =>
    (interp lex g body).map fun d ↦
      ⟨.fn .e d.1, Part.some fun x ↦ valueAt d.1 (interp lex (g[n ↦ x]) body)⟩

variable (lex lex' : L → Option (PDenotation E W D)) (g g' : Assignment E)

@[simp] theorem interp_terminal (c : C) (w : L) :
    interp lex g (.terminal c w : Tree C L) = lex w := rfl

@[simp] theorem interp_node_unary (c : C) (t : Tree C L) :
    interp lex g (.node c (t :: [])) = interp lex g t := rfl

@[simp] theorem interp_node_binary (c : C) (t₁ t₂ : Tree C L) :
    interp lex g (.node c (t₁ :: t₂ :: [])) =
      (interp lex g t₁).bind fun d₁ ↦ (interp lex g t₂).bind fun d₂ ↦ binary d₁ d₂ := rfl

@[simp] theorem interp_trace (n : ℕ) (c : C) :
    interp lex g (.trace n c : Tree C L) = some ⟨.e, Part.some (g n)⟩ := rfl

@[simp] theorem interp_bind (n : ℕ) (c : C) (body : Tree C L) :
    interp lex g (.bind n c body) = (interp lex g body).map fun d ↦
      ⟨.fn .e d.1, Part.some fun x ↦ valueAt d.1 (interp lex (g[n ↦ x]) body)⟩ := rfl

/-! ### Uninterpretability and presupposition failure -/

/-- A tree is uninterpretable when the engine assigns it no denotation. -/
def Uninterpretable (t : Tree C L) : Prop := interp lex g t = none

/-- A tree is a presupposition failure when its denotation is undefined. -/
def PresupFailure (t : Tree C L) : Prop := ∃ d, interp lex g t = some d ∧ ¬ d.2.Dom

/-- Whether a tree is interpretable, and at which type, depends only on the types of its
leaves, [heim-kratzer-1998]'s characterization of uninterpretability. -/
theorem interp_map_fst_congr (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1)) (t : Tree C L) :
    (interp lex g t).map (·.1) = (interp lex' g' t).map (·.1) := by
  induction t using Tree.recAux generalizing g g' with
  | terminal c w => exact h w
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => simp only [interp_node_unary]; exact ih t (by simp) g g'
    | [t₁, t₂] =>
      simp only [interp_node_binary]
      have h₁ := ih t₁ (by simp) g g'
      have h₂ := ih t₂ (by simp) g g'
      revert h₁ h₂
      cases interp lex g t₁ <;> cases interp lex' g' t₁ <;>
        cases interp lex g t₂ <;> cases interp lex' g' t₂ <;>
        intro h₁ h₂ <;> simp_all [binary_map_fst]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih =>
    simp only [interp_bind]
    have h := ih g g'
    revert h
    cases interp lex g body <;> cases interp lex' g' body <;> intro h <;> simp_all

/-- Uninterpretability is decided by the leaves' types alone. -/
theorem uninterpretable_congr (h : ∀ w, (lex w).map (·.1) = (lex' w).map (·.1)) (t : Tree C L) :
    Uninterpretable lex g t ↔ Uninterpretable lex' g' t := by
  have := interp_map_fst_congr lex lex' g g' h t
  constructor
  · intro hn; rw [hn] at this; exact Option.map_eq_none_iff.mp this.symm
  · intro hn; rw [hn] at this; exact Option.map_eq_none_iff.mp this

/-! ### The definite article -/

/-- A partial predicate holds of an individual when it is defined there and true. -/
def Holds (P : E →. Prop) (x : E) : Prop := ∃ h : (P x).Dom, (P x).get h

/-- [heim-kratzer-1998]'s Fregean entry for the definite article, which maps a predicate true of
exactly one individual to that individual and is undefined elsewhere. -/
noncomputable def the : Ty.PDomain E W ((.e ⇒ .t) ⇒ .e) D :=
  fun P ↦ ⟨∃! x, Holds P x, fun h ↦ Classical.choose h⟩

/-- The definite article is defined exactly on the predicates true of one individual. -/
theorem the_dom (P : E →. Prop) : (the (W := W) (D := D) P).Dom ↔ ∃! x, Holds P x := Iff.rfl

/-- A total predicate holds where it is true. -/
@[simp] theorem holds_lift (P : E → Prop) (x : E) : Holds (PFun.lift P) x ↔ P x := by
  simp [Holds, PFun.lift]

/-- On a total predicate true of exactly one individual, the definite article picks it. -/
theorem the_lift_eq_some {P : E → Prop} {a : E} (h : ∀ x, P x ↔ x = a) :
    the (W := W) (D := D) (PFun.lift P) = Part.some a := by
  have hu : ∃! x, Holds (PFun.lift P) x := ⟨a, (holds_lift P a).mpr ((h a).mpr rfl),
    fun y hy ↦ (h y).mp ((holds_lift P y).mp hy)⟩
  exact Part.eq_some_iff.mpr ⟨hu, (h _).mp ((holds_lift P _).mp (Classical.choose_spec hu).1)⟩

end Partial

end Semantics.Composition
