import Linglib.Syntax.Tree.Basic
import Linglib.Semantics.Composition.Ty
import Linglib.Semantics.Composition.Assignment
import Linglib.Semantics.Composition.Lexicon
import Linglib.Semantics.Modification.Basic

/-!
# Type-driven interpretation

This file is the composition engine of [heim-kratzer-1998]'s type-driven interpretation, with
the intensional application of [von-fintel-heim-2011] and the event identification of
[kratzer-1996], parameterized over an effect functor `M` in the style of
[bumford-charlow-2024]. A node denotes an `M`-computation in the domain of its semantic type,
a `Denotation`, and each composition principle lifts through the `Applicative` structure of
`M`, so the pure Heim and Kratzer engine is the instance `M = Id`. A terminal node denotes
what its leaf interpretation gives it, a string in a `Lexicon` or a fragment carrier through
its readings; a non-branching node denotes what its daughter does; a binary node composes by
functional application in either order, then intensional functional application, then
predicate modification, then event identification, whichever the daughters' types admit first;
a trace denotes its index's value under the assignment; and a binder abstracts over its index
by Predicate Abstraction, which is a capability of the effect (`PredAbs`) rather than a given.

## Main declarations

* `PredAbs` is the entity-distributor an effect needs for Predicate Abstraction; `Id` has one
  and scope effects do not.
* `tryFA`, `tryIFA`, `tryPM` and `tryEI` are the binary composition modes and `interpBinary`
  tries them in order; `tyBinary` is the type they compose to, a function of the daughters'
  types alone (`interpBinary_map_fst`).
* `interp` interprets a tree under an assignment, over any leaf type.
* `interp_congr_of_agree` and its corollaries are [heim-kratzer-1998]'s theorems on variable
  binding: interpretability and the composed type never depend on the assignment
  (`interp_map_fst_congr`), and a tree's denotation depends on it only at the traces free in
  the tree.
* `readings` composes a lexicon of sets of readings, the values the engine computes over the
  tree's resolutions; the engine on an unambiguous lexicon is the special case
  (`readings_eq_of_choice`) and a binary node's readings compose pointwise
  (`mem_readings_node_binary`).

## Implementation notes

Binary nodes sequence effects in linear order, the left daughter's first whichever daughter is
the function, so at `M = Cont R` surface scope is the default reading and inverse scope needs
a reordered evaluation (`Composition/Cont.lean`, `Studies/BumfordCharlow2024.lean`). Predicate
Abstraction needs a distributor `(E → M (Ty.Domain ty)) → M (E → Ty.Domain ty)`, which scope
effects lack, so under them `.bind` nodes fail and binding comes from the order of effects
instead; making the distributor optional turns that rivalry into a fact instance resolution
checks. The abstraction's fallback value `valueAt` is never reached, since types do not depend
on the assignment. The category parameter of a tree is ignored, composition being type-driven.

## References

* [heim-kratzer-1998]
* [von-fintel-heim-2011]
* [kratzer-1996]
* [bumford-charlow-2024]
-/

namespace Semantics.Composition.Tree

open Semantics.Composition
open scoped Assignment
open Semantics.Montague

/-! ### Predicate Abstraction as a capability -/

/-- An effect supports Predicate Abstraction when it has an entity-distributor, which commutes
`M` over entity-indexed families. `Id` and the Reader-like effects have one; scope effects such
as `Cont R` do not, since abstraction would have to run one continuation at every entity at
once, and record that by `dist? = none`. -/
class PredAbs (M : Type → Type) (E W : Type) (D : Type := ℝ) where
  dist? : Option (∀ ty : Ty, (E → M (Ty.Domain E W ty D)) → M (E → Ty.Domain E W ty D))

instance (E W D : Type) : PredAbs Id E W D := ⟨some fun _ f ↦ f⟩

/-! ### Composition modes -/

/-- Forward functional application, the function being the left daughter. -/
def applyForward {E W D : Type} {M : Type → Type} [Applicative M]
    (df da : Denotation E W M D) : Option (Denotation E W M D) :=
  match hf : df.1 with
  | .fn σ τ =>
    if ha : σ = da.1 then
      let f : M (Ty.Domain E W (σ ⇒ τ) D) := hf ▸ df.2
      let a : M (Ty.Domain E W σ D) := ha ▸ da.2
      some ⟨τ, f <*> a⟩
    else none
  | _ => none

/-- Backward functional application, the function being the right daughter; the left daughter
still sequences first. -/
def applyBackward {E W D : Type} {M : Type → Type} [Applicative M]
    (da df : Denotation E W M D) : Option (Denotation E W M D) :=
  match hf : df.1 with
  | .fn σ τ =>
    if ha : σ = da.1 then
      let f : M (Ty.Domain E W (σ ⇒ τ) D) := hf ▸ df.2
      let a : M (Ty.Domain E W σ D) := ha ▸ da.2
      some ⟨τ, (fun x g ↦ g x) <$> a <*> f⟩
    else none
  | _ => none

/-- Functional application in either order, forward first. -/
def tryFA {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  applyForward d1 d2 <|> applyBackward d1 d2

/-- Intensional functional application ([von-fintel-heim-2011]): a daughter expecting an
intension of type `⟨s,σ⟩` applies to the constant intension of a sister of type `σ`, in
either order, so that modals and attitude verbs take the intension of their sister. -/
def tryIFA {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  match hf : d1.1 with
  | .fn (.intens σ) τ =>
    if ha : σ = d2.1 then
      let f : M (Ty.Domain E W (.fn (.intens σ) τ) D) := hf ▸ d1.2
      let a : M (Ty.Domain E W σ D) := ha ▸ d2.2
      some ⟨τ, (fun fv av ↦ fv fun _ ↦ av) <$> f <*> a⟩
    else
      match hf' : d2.1 with
      | .fn (.intens σ') τ' =>
        if ha' : σ' = d1.1 then
          let f : M (Ty.Domain E W (.fn (.intens σ') τ') D) := hf' ▸ d2.2
          let a : M (Ty.Domain E W σ' D) := ha' ▸ d1.2
          some ⟨τ', (fun av fv ↦ fv fun _ ↦ av) <$> a <*> f⟩
        else none
      | _ => none
  | _ =>
    match hf : d2.1 with
    | .fn (.intens σ) τ =>
      if ha : σ = d1.1 then
        let f : M (Ty.Domain E W (.fn (.intens σ) τ) D) := hf ▸ d2.2
        let a : M (Ty.Domain E W σ D) := ha ▸ d1.2
        some ⟨τ, (fun av fv ↦ fv fun _ ↦ av) <$> a <*> f⟩
      else none
    | _ => none

/-- Predicate modification, the intersection of two `⟨e,t⟩` predicates. -/
def tryPM {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  match h1 : d1.1, h2 : d2.1 with
  | .fn .e .t, .fn .e .t =>
    let p1 : M (Ty.Domain E W (.e ⇒ .t) D) := h1 ▸ d1.2
    let p2 : M (Ty.Domain E W (.e ⇒ .t) D) := h2 ▸ d2.2
    some ⟨.fn .e .t, Modifier.intersective <$> p1 <*> p2⟩
  | _, _ => none

/-- Event identification ([kratzer-1996]): a role head of type `⟨e,⟨e,t⟩⟩` and an eventuality
predicate of type `⟨e,t⟩`, in either order, conjoin the predicate onto the head's event
argument. -/
def tryEI {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  match h1 : d1.1, h2 : d2.1 with
  | .fn .e (.fn .e .t), .fn .e .t =>
    let f : M (Ty.Domain E W (.e ⇒ .e ⇒ .t) D) := h1 ▸ d1.2
    let p : M (Ty.Domain E W (.e ⇒ .t) D) := h2 ▸ d2.2
    some ⟨.e ⇒ .e ⇒ .t, (fun fv pv x e ↦ fv x e ∧ pv e) <$> f <*> p⟩
  | .fn .e .t, .fn .e (.fn .e .t) =>
    let p : M (Ty.Domain E W (.e ⇒ .t) D) := h1 ▸ d1.2
    let f : M (Ty.Domain E W (.e ⇒ .e ⇒ .t) D) := h2 ▸ d2.2
    some ⟨.e ⇒ .e ⇒ .t, (fun pv fv x e ↦ fv x e ∧ pv e) <$> p <*> f⟩
  | _, _ => none

/-- The modes a binary node tries, in order. -/
def interpBinary {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  tryFA d1 d2 <|> tryIFA d1 d2 <|> tryPM d1 d2 <|> tryEI d1 d2

/-- The value of an interpreted daughter at the type `τ`, with the default `v` where the
daughter is uninterpretable or of another type. Types do not depend on the assignment
(`interp_map_fst_congr`), so under Predicate Abstraction the default is never reached
(`valueAt_of_map_fst`). -/
def valueAt {E W D : Type} {M : Type → Type} (τ : Ty) (v : M (Ty.Domain E W τ D)) :
    Option (Denotation E W M D) → M (Ty.Domain E W τ D)
  | some ⟨ty, val⟩ => if h : ty = τ then h ▸ val else v
  | none => v

/-! ### Types compose independently of values

The type a node composes to is a function of its daughters' types alone, by the modes in the
order `interpBinary` tries them; `tyBinary` is that function and `interpBinary_map_fst` the
agreement. -/

section Typing

variable {E W D : Type} {M : Type → Type} [Applicative M]

/-- The type forward application composes from a function type and an argument type. -/
def tyForward : Ty → Ty → Option Ty
  | .fn σ τ, σ' => if σ = σ' then some τ else none
  | _, _ => none

/-- The type intensional application composes, in the order `tryIFA` tries. -/
def tyIFA : Ty → Ty → Option Ty
  | .fn (.intens σ) τ, t₂ =>
    if σ = t₂ then some τ else
      match t₂ with
      | .fn (.intens σ') τ' => if σ' = .fn (.intens σ) τ then some τ' else none
      | _ => none
  | t₁, .fn (.intens σ) τ => if σ = t₁ then some τ else none
  | _, _ => none

/-- The type predicate modification composes. -/
def tyPM : Ty → Ty → Option Ty
  | .fn .e .t, .fn .e .t => some (.fn .e .t)
  | _, _ => none

/-- The type event identification composes. -/
def tyEI : Ty → Ty → Option Ty
  | .fn .e (.fn .e .t), .fn .e .t => some (.e ⇒ .e ⇒ .t)
  | .fn .e .t, .fn .e (.fn .e .t) => some (.e ⇒ .e ⇒ .t)
  | _, _ => none

/-- The type a binary node composes to, or none when no mode applies. -/
def tyBinary (σ τ : Ty) : Option Ty :=
  tyForward σ τ <|> tyForward τ σ <|> tyIFA σ τ <|> tyPM σ τ <|> tyEI σ τ

theorem applyForward_map_fst (d₁ d₂ : Denotation E W M D) :
    (applyForward d₁ d₂).map (·.1) = tyForward d₁.1 d₂.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold applyForward tyForward
  dsimp only
  split <;> (try split_ifs) <;> simp_all

theorem applyBackward_map_fst (d₁ d₂ : Denotation E W M D) :
    (applyBackward d₁ d₂).map (·.1) = tyForward d₂.1 d₁.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold applyBackward tyForward
  dsimp only
  split <;> (try split_ifs) <;> simp_all

theorem tryIFA_map_fst (d₁ d₂ : Denotation E W M D) :
    (tryIFA d₁ d₂).map (·.1) = tyIFA d₁.1 d₂.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold tryIFA tyIFA
  dsimp only
  split <;> (try split_ifs) <;> (try split) <;> (try split_ifs) <;> simp_all

theorem tryPM_map_fst (d₁ d₂ : Denotation E W M D) :
    (tryPM d₁ d₂).map (·.1) = tyPM d₁.1 d₂.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold tryPM tyPM
  dsimp only
  split <;> simp_all

theorem tryEI_map_fst (d₁ d₂ : Denotation E W M D) :
    (tryEI d₁ d₂).map (·.1) = tyEI d₁.1 d₂.1 := by
  obtain ⟨t₁, v₁⟩ := d₁; obtain ⟨t₂, v₂⟩ := d₂
  unfold tryEI tyEI
  dsimp only
  split <;> simp_all

theorem interpBinary_map_fst (d₁ d₂ : Denotation E W M D) :
    (interpBinary d₁ d₂).map (·.1) = tyBinary d₁.1 d₂.1 := by
  simp only [interpBinary, tryFA, tyBinary, Option.orElse_eq_orElse, Option.orElse_eq_or,
    Option.map_or, Option.or_assoc, applyForward_map_fst, applyBackward_map_fst, tryIFA_map_fst,
    tryPM_map_fst, tryEI_map_fst]

/-- No type is its own argument type, so forward application never applies when backward
does. -/
theorem tyForward_fn_self (σ τ : Ty) : tyForward σ (.fn σ τ) = none := by
  cases σ with
  | fn a b =>
    simp only [tyForward]
    split_ifs with h
    · have := congrArg sizeOf h
      simp only [Ty.fn.sizeOf_spec] at this
      omega
    · rfl
  | _ => rfl

/-- Intensional application never applies to extensional types. -/
theorem tyIFA_eq_none {σ τ : Ty} (h₁ : σ.Extensional) (h₂ : τ.Extensional) :
    tyIFA σ τ = none := by
  rcases h₁ with _ | _ | ⟨ha, _⟩ <;> rcases h₂ with _ | _ | ⟨ha', _⟩ <;>
    (try rcases ha with _ | _ | _) <;> (try rcases ha' with _ | _ | _) <;> rfl

theorem tryIFA_eq_none {d₁ d₂ : Denotation E W M D} (h₁ : d₁.1.Extensional)
    (h₂ : d₂.1.Extensional) : tryIFA d₁ d₂ = none :=
  Option.map_eq_none_iff.mp (by rw [tryIFA_map_fst]; exact tyIFA_eq_none h₁ h₂)

end Typing

/-! ### Tree interpretation -/

open Syntax

section TreeInterp

variable {C : Type}

/-- The denotation of a tree under an assignment, by the composition principles of
[heim-kratzer-1998]: a terminal denotes what its leaf interpretation gives it, a non-branching
node what its daughter does, a binary node what `interpBinary` composes, a trace the value of
its index, and a binder the abstraction over its index, when the effect has a distributor. -/
def interp {E W : Type} {M : Type → Type} [Applicative M] {D : Type} [PredAbs M E W D]
    {L : Type*} (lex : L → Option (Denotation E W M D)) (g : Assignment E) :
    Tree C L → Option (Denotation E W M D)
  | .terminal _ w => lex w
  | .node _ (t :: []) => interp lex g t
  | .node _ (t1 :: t2 :: []) => do
    let d1 ← interp lex g t1
    let d2 ← interp lex g t2
    interpBinary d1 d2
  | .node _ _ => none
  | .trace n _ => some ⟨.e, pure (g n)⟩
  | .bind n _ body => do
    let dist ← PredAbs.dist? (M := M) (E := E) (W := W) (D := D)
    let ⟨bodyTy, probeVal⟩ ← interp lex g body
    some ⟨.fn .e bodyTy, dist bodyTy fun x ↦ valueAt bodyTy probeVal (interp lex (g[n ↦ x]) body)⟩

end TreeInterp

/-! ### Reduction lemmas

One `@[simp]` lemma per constructor, so that a derivation reduces by `simp` toward its
composed denotation; the modes reduce at concrete types, since they case on `Ty`. -/

section Reduction

variable {C : Type} {E W D : Type} {M : Type → Type} [Applicative M] [PredAbs M E W D]
  {L : Type*}

@[simp] theorem interp_terminal (lex : L → Option (Denotation E W M D)) (g : Assignment E)
    (c : C) (w : L) :
    interp lex g (.terminal c w : Tree C L) = lex w := rfl

@[simp] theorem interp_node_unary (lex : L → Option (Denotation E W M D)) (g : Assignment E)
    (c : C) (t : Tree C L) :
    interp lex g (.node c (t :: [])) = interp lex g t := rfl

@[simp] theorem interp_trace (lex : L → Option (Denotation E W M D)) (g : Assignment E) (n : ℕ)
    (c : C) : interp lex g (.trace n c : Tree C L) = some ⟨.e, pure (g n)⟩ := rfl

@[simp] theorem interp_bind (lex : L → Option (Denotation E W M D)) (g : Assignment E) (n : ℕ)
    (c : C) (body : Tree C L) :
    interp lex g (.bind n c body) =
      (PredAbs.dist? (M := M) (E := E) (W := W) (D := D)).bind fun dist ↦
        (interp lex g body).bind fun d ↦
          some ⟨.fn .e d.1, dist d.1 fun x ↦ valueAt d.1 d.2 (interp lex (g[n ↦ x]) body)⟩ :=
  rfl

@[simp] theorem interp_node_binary (lex : L → Option (Denotation E W M D)) (g : Assignment E)
    (c : C) (t₁ t₂ : Tree C L) :
    interp lex g (.node c (t₁ :: t₂ :: []))
      = ((interp lex g t₁).bind fun d₁ =>
          (interp lex g t₂).bind fun d₂ => interpBinary d₁ d₂) := rfl

omit [PredAbs M E W D] in
/-- Forward application reduces at any types; backward application reduces only at concrete
types, since forward fires first whenever the left daughter is a function. -/
@[simp] theorem applyForward_fn {σ τ : Ty} (f : M (Ty.Domain E W (σ ⇒ τ) D))
    (x : M (Ty.Domain E W σ D)) :
    applyForward (⟨σ ⇒ τ, f⟩ : Denotation E W M D) ⟨σ, x⟩ = some ⟨τ, f <*> x⟩ := by
  simp only [applyForward, ↓reduceDIte]

omit [PredAbs M E W D] in
@[simp] theorem tryFA_forward {σ τ : Ty} (f : M (Ty.Domain E W (σ ⇒ τ) D))
    (x : M (Ty.Domain E W σ D)) :
    tryFA (⟨σ ⇒ τ, f⟩ : Denotation E W M D) ⟨σ, x⟩ = some ⟨τ, f <*> x⟩ := by
  simp only [tryFA, applyForward_fn]; rfl

omit [PredAbs M E W D] in
@[simp] theorem applyBackward_fn {σ τ : Ty} (x : M (Ty.Domain E W σ D))
    (f : M (Ty.Domain E W (σ ⇒ τ) D)) :
    applyBackward (⟨σ, x⟩ : Denotation E W M D) ⟨σ ⇒ τ, f⟩ =
      some ⟨τ, (fun x g ↦ g x) <$> x <*> f⟩ := by
  simp only [applyBackward, ↓reduceDIte]

omit [PredAbs M E W D] in
/-- Backward application reduces at any types too, since forward cannot apply to an argument
of the function's own argument type. -/
@[simp] theorem tryFA_backward {σ τ : Ty} (x : M (Ty.Domain E W σ D))
    (f : M (Ty.Domain E W (σ ⇒ τ) D)) :
    tryFA (⟨σ, x⟩ : Denotation E W M D) ⟨σ ⇒ τ, f⟩ = some ⟨τ, (fun x g ↦ g x) <$> x <*> f⟩ := by
  have h : applyForward (⟨σ, x⟩ : Denotation E W M D) ⟨σ ⇒ τ, f⟩ = none :=
    Option.map_eq_none_iff.mp (by rw [applyForward_map_fst]; exact tyForward_fn_self σ τ)
  simp only [tryFA, h, applyBackward_fn]; rfl

omit [PredAbs M E W D] in
/-- Two predicates compose by predicate modification, application failing on them. -/
@[simp] theorem interpBinary_pm (P Q : M (Ty.Domain E W (.e ⇒ .t) D)) :
    interpBinary (⟨.e ⇒ .t, P⟩ : Denotation E W M D) ⟨.e ⇒ .t, Q⟩ =
      some ⟨.e ⇒ .t, Modifier.intersective <$> P <*> Q⟩ := by
  have h : tryIFA (⟨.e ⇒ .t, P⟩ : Denotation E W M D) ⟨.e ⇒ .t, Q⟩ = none :=
    tryIFA_eq_none (.fn .e .t) (.fn .e .t)
  simp [interpBinary, tryFA, applyForward, applyBackward, h, tryPM]

end Reduction


/-! ### Assignment dependence and free variables

[heim-kratzer-1998]'s theorems on variable binding (§5.4.2): the denotation of a tree depends
on the assignment only at the traces free in it. Interpretability and the type composed do not
depend on the assignment at all (`interp_map_fst_congr`), so with total assignments their
theorem (9), that a tree with no free occurrence of the index `i` denotes alike under an
assignment and its modification at `i`, is `interp_update_of_not_mem_freeIndices`, and their
(10), that a closed tree denotes alike under every assignment, is `interp_congr_of_closed`. -/

section FreeVariables

variable {C : Type} {E W D : Type} {M : Type → Type} [Applicative M] [PredAbs M E W D]
  {L : Type*} (lex : L → Option (Denotation E W M D))

omit [Applicative M] [PredAbs M E W D] in
theorem valueAt_of_map_fst {τ : Ty} {v v' : M (Ty.Domain E W τ D)}
    {d : Option (Denotation E W M D)} (h : d.map (·.1) = some τ) :
    valueAt τ v d = valueAt τ v' d := by
  obtain _ | ⟨ty, val⟩ := d
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h; simp [valueAt]

/-- Whether a tree is interpretable, and at which type, does not depend on the assignment. -/
theorem interp_map_fst_congr (g g' : Assignment E) (t : Tree C L) :
    (interp lex g t).map (·.1) = (interp lex g' t).map (·.1) := by
  induction t using Tree.rec' generalizing g g' with
  | terminal c w => rfl
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => simp only [interp_node_unary]; exact ih t (by simp) g g'
    | [t₁, t₂] =>
      simp only [interp_node_binary]
      have h₁ := ih t₁ (by simp) g g'
      have h₂ := ih t₂ (by simp) g g'
      revert h₁ h₂
      cases interp lex g t₁ <;> cases interp lex g' t₁ <;>
        cases interp lex g t₂ <;> cases interp lex g' t₂ <;>
        intro h₁ h₂ <;> simp_all [interpBinary_map_fst]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih =>
    simp only [interp_bind]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (D := D) with
    | none => rfl
    | some dist =>
      have h := ih g g'
      revert h
      cases interp lex g body <;> cases interp lex g' body <;> intro h <;> simp_all

/-- The coincidence theorem: assignments agreeing on the traces free in a tree give it the
same denotation ([heim-kratzer-1998] §5.4.2). -/
theorem interp_congr_of_agree {g g' : Assignment E} {t : Tree C L}
    (h : ∀ i ∈ t.freeIndices, g i = g' i) : interp lex g t = interp lex g' t := by
  induction t using Tree.rec' generalizing g g' with
  | terminal c w => rfl
  | node c cs ih =>
    have hm : ∀ t ∈ cs, ∀ i ∈ t.freeIndices, g i = g' i := fun t ht i hi =>
      h i (Tree.mem_freeIndices_node.2 ⟨t, ht, hi⟩)
    match cs with
    | [] => rfl
    | [t] => simp only [interp_node_unary]; exact ih t (by simp) (hm t (by simp))
    | [t₁, t₂] =>
      simp only [interp_node_binary]
      rw [ih t₁ (by simp) (hm t₁ (by simp)), ih t₂ (by simp) (hm t₂ (by simp))]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => simp only [interp_trace]; rw [h n (by simp)]
  | bind n c body ih =>
    simp only [interp_bind]
    cases PredAbs.dist? (M := M) (E := E) (W := W) (D := D) with
    | none => rfl
    | some dist =>
      have hb : ∀ x, interp lex (g[n ↦ x]) body = interp lex (g'[n ↦ x]) body :=
        fun x ↦ ih fun i hi ↦ by
          by_cases hin : i = n
          · subst hin; simp
          · rw [Function.update_of_ne hin, Function.update_of_ne hin]
            exact h i (Finset.mem_erase.mpr ⟨hin, hi⟩)
      have ht := interp_map_fst_congr lex g g' body
      revert ht
      cases hg : interp lex g body <;> cases hg' : interp lex g' body <;> intro ht
      · rfl
      · simp at ht
      · simp at ht
      · rename_i d d'
        obtain ⟨τ, v⟩ := d; obtain ⟨τ', v'⟩ := d'
        simp only [Option.map_some, Option.some.injEq] at ht
        subst ht
        simp only [Option.bind_some, Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
        congr 1
        funext x
        rw [hb x]
        exact valueAt_of_map_fst (by rw [interp_map_fst_congr lex _ g' body, hg']; rfl)

/-- [heim-kratzer-1998]'s (9): a tree with no free trace at index `i` denotes alike under an
assignment and its modification at `i`. -/
theorem interp_update_of_not_mem_freeIndices {t : Tree C L} {i : ℕ}
    (h : i ∉ t.freeIndices) (g : Assignment E) (x : E) :
    interp lex (g[i ↦ x]) t = interp lex g t :=
  interp_congr_of_agree lex fun j hj ↦
    Function.update_of_ne (fun hji ↦ h (by subst hji; exact hj)) x g

/-- [heim-kratzer-1998]'s (10): a closed tree denotes alike under every assignment. -/
theorem interp_congr_of_closed {t : Tree C L} (h : t.Closed) (g g' : Assignment E) :
    interp lex g t = interp lex g' t :=
  interp_congr_of_agree lex fun i hi ↦ absurd (h ▸ hi) (Finset.notMem_empty i)

end FreeVariables

/-! ### Readings of an ambiguous lexicon

A word may have several available readings. A resolution of a tree chooses one reading for
each occurrence of a word, and the readings of the tree are the values the engine computes
over its resolutions. The engine on a lexicon with one reading per word is the special case
(`readings_eq_of_choice`), and a binary node's readings are the pointwise compositions of its
daughters' (`mem_readings_node_binary`). -/

section Readings

variable {C : Type} {L : Type*} {E W D : Type} {M : Type → Type} [Applicative M]
  [PredAbs M E W D]

/-- Interpretation commutes with relabelling the leaves. -/
theorem interp_map {L' : Type*} (lex : L' → Option (Denotation E W M D)) (f : L → L')
    (g : Assignment E) (t : Tree C L) : interp lex g (t.map f) = interp (lex ∘ f) g t := by
  induction t using Tree.rec' generalizing g with
  | terminal c w => rfl
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => exact ih t (by simp) g
    | [t₁, t₂] =>
      simp only [Tree.map_node, List.map, interp_node_binary, ih t₁ (by simp), ih t₂ (by simp)]
    | _ :: _ :: _ :: _ => rfl
  | trace n c => rfl
  | bind n c body ih => simp only [Tree.map_bind, interp_bind, ih]

variable (lex : L → Set (Denotation E W M D)) (g : Assignment E)

/-- The readings of a tree under a leaf interpretation giving each word a set of readings, the
values the engine computes over the resolutions of the tree, each occurrence of a word resolved
to one of its readings. -/
def readings (t : Tree C L) : Set (Denotation E W M D) :=
  {d | ∃ r : Tree C {p : L × Denotation E W M D // p.2 ∈ lex p.1},
    r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d}

variable {lex g}

/-- A value the engine computes under a choice of readings is the value of a resolved tree. -/
theorem exists_resolution_of_interp {choice : L → Option (Denotation E W M D)} {t : Tree C L}
    {d : Denotation E W M D} (h : interp choice g t = some d) :
    ∃ r : Tree C {p : L × Denotation E W M D // choice p.1 = some p.2},
      r.map (·.1.1) = t ∧ interp (fun p ↦ some p.1.2) g r = some d := by
  induction t using Tree.rec' generalizing g d with
  | terminal c w => exact ⟨.terminal c ⟨(w, d), h⟩, rfl, rfl⟩
  | node c cs ih =>
    match cs with
    | [] => exact absurd h (by simp [interp])
    | [t] =>
      obtain ⟨r, hr, hd⟩ := ih t (by simp) h
      exact ⟨.node c (r :: []), by simp [hr], hd⟩
    | [t₁, t₂] =>
      rw [interp_node_binary] at h
      obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨d₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r₁, hr₁, hd₁⟩ := ih t₁ (by simp) h₁
      obtain ⟨r₂, hr₂, hd₂⟩ := ih t₂ (by simp) h₂
      exact ⟨.node c (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
        by rw [interp_node_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩
    | _ :: _ :: _ :: _ => exact absurd h (by simp [interp])
  | trace n c => exact ⟨.trace n c, rfl, h⟩
  | bind n c body ih =>
    rw [interp_bind] at h
    obtain ⟨dist, hdist, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨τ, probe⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hd⟩ := ih hb
    have hres : ∀ g', interp choice g' body = interp (fun p ↦ some p.1.2) g' r := fun g' ↦ by
      rw [← hr, interp_map]
      exact congrFun (congrFun (congrArg _ (funext fun p ↦ p.2)) g') r
    refine ⟨.bind n c r, by simp [hr], ?_⟩
    rw [interp_bind, hdist, Option.bind_some, hd, Option.bind_some]
    simpa only [hres] using h

/-- A value the engine computes under a choice among the readings is a reading. -/
theorem interp_mem_readings {choice : L → Option (Denotation E W M D)}
    (hc : ∀ w d, choice w = some d → d ∈ lex w) {t : Tree C L} {d : Denotation E W M D}
    (h : interp choice g t = some d) : d ∈ readings lex g t := by
  obtain ⟨r, hr, hd⟩ := exists_resolution_of_interp h
  refine ⟨r.map fun p ↦ ⟨p.1, hc _ _ p.2⟩, ?_, ?_⟩
  · rw [Tree.map_map]; exact hr
  · rw [interp_map]; exact hd

/-- On a lexicon with one reading per word, the readings are the engine's values. -/
theorem readings_eq_of_choice (choice : L → Option (Denotation E W M D)) (t : Tree C L) :
    readings (fun w ↦ {d | choice w = some d}) g t = {d | interp choice g t = some d} := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ interp_mem_readings (fun _ _ h ↦ h) h⟩
  show interp choice g t = some d
  rw [← hr, interp_map]
  exact (congrFun (congrFun (congrArg _ (funext fun p ↦ p.2)) g) r).trans hd

@[simp] theorem readings_terminal (c : C) (w : L) : readings lex g (.terminal c w) = lex w := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ ⟨.terminal c ⟨(w, d), h⟩, rfl, rfl⟩⟩
  cases r with
  | terminal c' p =>
    simp only [Tree.map_terminal, Tree.terminal.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    cases Option.some.inj hd
    exact p.2
  | _ => simp at hr

@[simp] theorem readings_trace (n : ℕ) (c : C) :
    readings lex g (.trace n c) = {⟨.e, pure (g n)⟩} := by
  ext d
  refine ⟨fun ⟨r, hr, hd⟩ ↦ ?_, fun h ↦ ⟨.trace n c, rfl, h ▸ rfl⟩⟩
  cases r with
  | trace n' c' =>
    simp only [Tree.map_trace, Tree.trace.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact (Option.some.inj hd).symm
  | _ => simp at hr

/-- A binary node's readings are the pointwise compositions of its daughters'. -/
theorem mem_readings_node_binary {c : C} {t₁ t₂ : Tree C L} {d : Denotation E W M D} :
    d ∈ readings lex g (.node c (t₁ :: t₂ :: [])) ↔
      ∃ d₁ ∈ readings lex g t₁, ∃ d₂ ∈ readings lex g t₂, interpBinary d₁ d₂ = some d := by
  constructor
  · rintro ⟨r, hr, hd⟩
    cases r with
    | node c' cs =>
      simp only [Tree.map_node, Tree.node.injEq] at hr
      obtain ⟨rfl, hcs⟩ := hr
      obtain ⟨r₁, cs₁, rfl, rfl, hcs₁⟩ := List.map_eq_cons_iff.mp hcs
      obtain ⟨r₂, cs₂, rfl, rfl, hcs₂⟩ := List.map_eq_cons_iff.mp hcs₁
      obtain rfl := List.map_eq_nil_iff.mp hcs₂
      rw [interp_node_binary] at hd
      obtain ⟨d₁, h₁, hd⟩ := Option.bind_eq_some_iff.mp hd
      obtain ⟨d₂, h₂, hd⟩ := Option.bind_eq_some_iff.mp hd
      exact ⟨d₁, ⟨r₁, rfl, h₁⟩, d₂, ⟨r₂, rfl, h₂⟩, hd⟩
    | _ => simp at hr
  · rintro ⟨d₁, ⟨r₁, hr₁, hd₁⟩, d₂, ⟨r₂, hr₂, hd₂⟩, h⟩
    exact ⟨.node c (r₁ :: r₂ :: []), by simp [hr₁, hr₂],
      by rw [interp_node_binary, hd₁, hd₂, Option.bind_some, Option.bind_some, h]⟩

end Readings

end Semantics.Composition.Tree
