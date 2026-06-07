import Linglib.Syntax.Tree.Basic
import Linglib.Core.Logic.Intensional.Frame
import Linglib.Core.Logic.Intensional.Variables
import Linglib.Semantics.Composition.LexEntry
import Linglib.Semantics.Modification.Basic

/-!
# Type-Driven Interpretation

[heim-kratzer-1998]'s type-driven interpretation (Ch. 3-5;
[von-fintel-heim-2011], Ch. 1), parameterized over an effect functor `M`
in the style of [bumford-charlow-2024]: a node's denotation is an
`M`-computation `M (F.Denot ty)` (`TypedDenot`), and each composition
principle lifts through `M`'s `Applicative` structure. The pure
Heim & Kratzer engine is the `M = Id` instance (`TypedDenot`, `interp`
at a pure `Lexicon`) — true by construction, not by a bridge theorem.

Composition principles:
1. Terminal Nodes (TN): lexical lookup
2. Non-Branching Nodes (NN): identity
3. Functional Application (FA): `⟦α⟧ = ⟦β⟧(⟦γ⟧)` when types match
4. Intensional Functional Application (IFA): `⟦α⟧ = ⟦β⟧(^⟦γ⟧)` when
   β expects an intension `⟨s,σ⟩` and γ has type σ ([von-fintel-heim-2011] Step 10)
5. Predicate Modification (PM): combine two `⟨e,t⟩` predicates (Ch. 4)
6. Predicate Abstraction (PA): `⟦[n β]⟧^g = λx. ⟦β⟧^{g[n↦x]}` (Ch. 5)

Two effect-discipline choices, both visible rather than stipulated:

* **Binary nodes sequence effects in linear order** — the left daughter's
  effects fire first whichever daughter is the function. At `M = Cont R`
  this makes surface scope the default reading; inverse scope requires
  reordering the evaluation (QR, or `bind`-order permutation — see
  `Composition/Effects.lean`).
* **PA is a capability, not a given** (`PredAbs`): it needs an
  entity-distributor `(Entity → M (Denot ty)) → M (Entity → Denot ty)`,
  which `Id` has and scope-type effects lack. See the `PredAbs` docstring.
-/

namespace Semantics.Composition.Tree

open Core.Logic.Intensional
open Core.Logic.Intensional.Variables
open Semantics.Montague (Lexicon)

/-! ### Composition primitives -/

/-- A typed denotation: a linguistic type together with an `M`-computation
over its denotation domain. The default `M := Id` recovers the
[heim-kratzer-1998] carrier; effectful values supply `M` explicitly. -/
structure TypedDenot (F : Frame) (M : Type → Type := Id) where
  ty : Ty
  val : M (F.Denot ty)

/-- Capability for Predicate Abstraction under effect `M`: an
**entity-distributor** commuting `M` over entity-indexed families.

`dist? = none` records that an effect does not support PA. `Id` (and any
Reader-like effect) has a distributor; scope-type effects (`Cont R`) do
not — abstraction would have to run one continuation at every entity
simultaneously — so binding under such effects arises from `bind`-order
or the W ⊣ R adjunction instead (`Composition/Effects.lean` §4). Making
the distributor optional turns the QR/PA-vs-effect-sequencing rivalry
into a fact checked by instance resolution. -/
class PredAbs (M : Type → Type) (F : Frame) where
  dist? : Option (∀ ty : Ty, (F.Entity → M (F.Denot ty)) → M (F.Entity → F.Denot ty))

instance (F : Frame) : PredAbs Id F := ⟨some λ _ f => f⟩

def canApply (funTy argTy : Ty) : Option Ty :=
  match funTy with
  | .fn σ τ => if σ = argTy then some τ else none
  | _ => none

/-- TN: lexical lookup. -/
def interpTerminal (F : Frame) {M : Type → Type} (lex : Lexicon F M)
    (word : String) : Option (TypedDenot F M) :=
  (lex word).map λ entry => ⟨entry.ty, entry.denot⟩

/-- NN: identity. -/
def interpNonBranching {F : Frame} {M : Type → Type}
    (daughter : TypedDenot F M) : TypedDenot F M :=
  daughter

/-- FA: `⟦β⟧(⟦γ⟧)` -/
def interpFA {F : Frame} {σ τ : Ty}
    (f : F.Denot (σ ⇒ τ)) (x : F.Denot σ) : F.Denot τ :=
  f x

/-- Forward FA: the function is the left daughter `df`, the argument `da`. -/
def applyForward {F : Frame} {M : Type → Type} [Applicative M]
    (df da : TypedDenot F M) : Option (TypedDenot F M) :=
  match hf : df.ty with
  | .fn σ τ =>
    if ha : σ = da.ty then
      let f : M (F.Denot (σ ⇒ τ)) := hf ▸ df.val
      let a : M (F.Denot σ) := ha ▸ da.val
      some ⟨τ, f <*> a⟩
    else none
  | _ => none

/-- Backward FA: the function is the right daughter `df`, the argument `da`. The
left daughter `da` sequences first, hence the `(λ x g => g x)` combinator. -/
def applyBackward {F : Frame} {M : Type → Type} [Applicative M]
    (da df : TypedDenot F M) : Option (TypedDenot F M) :=
  match hf : df.ty with
  | .fn σ τ =>
    if ha : σ = da.ty then
      let f : M (F.Denot (σ ⇒ τ)) := hf ▸ df.val
      let a : M (F.Denot σ) := ha ▸ da.val
      some ⟨τ, (λ x g => g x) <$> a <*> f⟩
    else none
  | _ => none

/-- Try FA in both orders, sequencing effects in linear order (the left daughter's
effects fire first regardless of which daughter is the function): function on the
left (`applyForward`), else on the right (`applyBackward`). -/
def tryFA {F : Frame} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot F M) : Option (TypedDenot F M) :=
  applyForward d1 d2 <|> applyBackward d1 d2

/-- IFA: Intensional Functional Application ([von-fintel-heim-2011] Step 10).

    If β expects an intension `⟨s,σ⟩` as argument and γ has type σ,
    then `⟦α⟧ = ⟦β⟧(^⟦γ⟧)` — we wrap γ's denotation in `up` (rigid intension)
    before applying. This lets intensional operators (modals, attitude verbs)
    take the intension of their sister as argument via type-driven composition.

    Tries both orders (β,γ) and (γ,β); effects sequence in linear order. -/
def tryIFA {F : Frame} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot F M) : Option (TypedDenot F M) :=
  match hf : d1.ty with
  | .fn (.intens σ) τ =>
    if ha : σ = d2.ty then
      let f : M (F.Denot (.fn (.intens σ) τ)) := hf ▸ d1.val
      let a : M (F.Denot σ) := ha ▸ d2.val
      some ⟨τ, (λ fv av => fv (up av)) <$> f <*> a⟩
    else
      match hf' : d2.ty with
      | .fn (.intens σ') τ' =>
        if ha' : σ' = d1.ty then
          let f : M (F.Denot (.fn (.intens σ') τ')) := hf' ▸ d2.val
          let a : M (F.Denot σ') := ha' ▸ d1.val
          some ⟨τ', (λ av fv => fv (up av)) <$> a <*> f⟩
        else none
      | _ => none
  | _ =>
    match hf : d2.ty with
    | .fn (.intens σ) τ =>
      if ha : σ = d1.ty then
        let f : M (F.Denot (.fn (.intens σ) τ)) := hf ▸ d2.val
        let a : M (F.Denot σ) := ha ▸ d1.val
        some ⟨τ, (λ av fv => fv (up av)) <$> a <*> f⟩
      else none
    | _ => none

/-- PM: combine two `⟨e,t⟩` predicates. -/
def tryPM {F : Frame} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot F M) : Option (TypedDenot F M) :=
  match h1 : d1.ty, h2 : d2.ty with
  | .fn .e .t, .fn .e .t =>
    let p1 : M (F.Denot (.e ⇒ .t)) := h1 ▸ d1.val
    let p2 : M (F.Denot (.e ⇒ .t)) := h2 ▸ d2.val
    some ⟨.fn .e .t, Modifier.intersective <$> p1 <*> p2⟩
  | _, _ => none

/-- Binary node: try FA, then IFA, then PM. -/
def interpBinary {F : Frame} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot F M) : Option (TypedDenot F M) :=
  tryFA d1 d2 <|> tryIFA d1 d2 <|> tryPM d1 d2

/-! ### Tree interpretation -/

open Syntax

section TreeInterp

variable {C : Type}

/-- Interpret a tree under an assignment.

Implements [heim-kratzer-1998] Ch. 3-5 type-driven interpretation,
lifted through the effect functor `M`:
- **TN**: terminal → lexical lookup
- **NN**: unary node → identity
- **FA/IFA/PM**: binary node → try FA, then IFA, then PM
- **Traces/Pronouns**: `⟦tₙ⟧^g = pure (g n)`
- **Predicate Abstraction (PA)**: `⟦[n β]⟧^g = λx. ⟦β⟧^{g[n↦x]}`,
  available only when `M` has an entity-distributor (`PredAbs`)

PA is the key to quantifier scope under `M = Id`: after QR moves a
quantifier DP to a higher position, PA abstracts over the trace it
leaves behind, producing a predicate that the quantifier can take as
its scope argument. Under scope-type effects there is no distributor
(`PredAbs.dist? = none`), and `.bind` nodes fail — in-situ effect
sequencing replaces QR.

The category parameter `C` is ignored during interpretation — composition
is type-driven, not category-driven. This means the same function works
for `Tree Cat String` (UD-grounded), `Tree Unit String` (category-free),
or any other category system. -/
def interp (F : Frame) {M : Type → Type} [Applicative M] [PredAbs M F]
    (lex : Lexicon F M) (g : Core.Assignment F.Entity)
    : Tree C String → Option (TypedDenot F M)
  | .terminal _ w => interpTerminal F lex w
  | .node _ (t :: []) => (interp F lex g t).map interpNonBranching
  | .node _ (t1 :: t2 :: []) => do
    let d1 ← interp F lex g t1
    let d2 ← interp F lex g t2
    interpBinary d1 d2
  | .node _ _ => none
  | .trace n _ => some ⟨.e, pure (g n)⟩
  | .bind n _ body => do
    let dist ← PredAbs.dist? (M := M) (F := F)
    let ⟨bodyTy, probeVal⟩ ← interp F lex g body
    some ⟨.fn .e bodyTy, dist bodyTy λ (x : F.Entity) =>
      match interp F lex (g[n ↦ x]) body with
      | some ⟨ty, val⟩ => if h : ty = bodyTy then h ▸ val else probeVal
      | none => probeVal⟩

/-- Extract truth value from (pure) tree interpretation. Effectful roots
discharge through per-effect handlers instead (`Composition/Effects.lean`
§5). -/
def evalTree {F : Frame} [∀ (p : F.Denot .t), Decidable p]
    (lex : Lexicon F) (g : Core.Assignment F.Entity) (t : Tree C String)
    : Option Bool :=
  match interp F lex g t with
  | some ⟨.t, b⟩ => some (decide b)
  | _ => none

/-- Extract proposition (`s→t`) from (pure) tree interpretation.

    For intensional trees where the root denotes a proposition
    rather than a bare truth value — e.g., trees containing EXH
    or other propositional operators. Evaluate the result at a
    specific world to get a truth value. -/
def evalTreeProp {F : Frame} [∀ (p : F.Denot .t), Decidable p]
    (lex : Lexicon F) (g : Core.Assignment F.Entity) (t : Tree C String)
    : Option (F.Index → Bool) :=
  match interp F lex g t with
  | some ⟨.intens .t, p⟩ => some (λ w => decide (p w))
  | _ => none

end TreeInterp

section TypeMismatch

example : canApply .t .e = none := rfl
example : canApply .e .t = none := rfl
example : canApply (.fn .t .t) (.fn .e .t) = none := rfl
example : canApply (.fn .e .t) (.fn .t .t) = none := rfl

end TypeMismatch

section Properties

variable {M : Type → Type}

theorem interpNonBranching_id {F : Frame} (d : TypedDenot F M) :
    interpNonBranching d = d := rfl

theorem interpFA_type {F : Frame} {σ τ : Ty}
    (f : F.Denot (σ ⇒ τ)) (x : F.Denot σ)
    : (interpFA f x : F.Denot τ) = f x := rfl

theorem tryPM_preserves_type {F : Frame} [Applicative M] (d1 d2 : TypedDenot F M)
    (h1 : d1.ty = .fn .e .t) (h2 : d2.ty = .fn .e .t)
    : ∃ d, tryPM d1 d2 = some d ∧ d.ty = .fn .e .t := by
  cases d1 with | mk ty1 val1 =>
  cases d2 with | mk ty2 val2 =>
  simp only at h1 h2
  subst h1 h2
  exact ⟨_, rfl, rfl⟩

theorem interpBinary_eq {F : Frame} [Applicative M] (d1 d2 : TypedDenot F M) :
    interpBinary d1 d2 =
    (tryFA d1 d2 <|> tryIFA d1 d2 <|> tryPM d1 d2) := rfl

end Properties

/-! ### Reduction lemmas (the `interp` simp normal form)

Per-constructor `@[simp]` lemmas so a derivation reduces by `simp` toward its
composed denotation, instead of relying on opaque `rfl` over the whole engine
call. Mode reduction (`tryFA`/`interpBinary` over concrete types) is the
complementary layer, and is type-shape-specific because the modes case on `Ty`. -/

section Reduction

variable {C : Type} {F : Frame} {M : Type → Type} [Applicative M] [PredAbs M F]

@[simp] theorem interp_terminal (lex : Lexicon F M) (g : Core.Assignment F.Entity)
    (c : C) (w : String) :
    interp F lex g (.terminal c w : Tree C String) = interpTerminal F lex w := rfl

@[simp] theorem interp_node_binary (lex : Lexicon F M) (g : Core.Assignment F.Entity)
    (c : C) (t₁ t₂ : Tree C String) :
    interp F lex g (.node c (t₁ :: t₂ :: []))
      = ((interp F lex g t₁).bind fun d₁ =>
          (interp F lex g t₂).bind fun d₂ => interpBinary d₁ d₂) := rfl

omit [Applicative M] [PredAbs M F] in
@[simp] theorem interpTerminal_lookup (lex : Lexicon F M) (w : String) :
    interpTerminal F lex w = (lex w).map fun e => ⟨e.ty, e.denot⟩ := rfl

omit [PredAbs M F] in
/-- Forward FA reduces generally (abstract `σ τ`) — unblocked by the
`applyForward`/`applyBackward` split. (Backward FA stays type-shape-specific
because forward fires first when the left daughter is itself a function.) -/
@[simp] theorem applyForward_fn {σ τ : Ty} (f : M (F.Denot (σ ⇒ τ))) (x : M (F.Denot σ)) :
    applyForward (⟨σ ⇒ τ, f⟩ : TypedDenot F M) ⟨σ, x⟩ = some ⟨τ, f <*> x⟩ := by
  simp only [applyForward, ↓reduceDIte]

omit [PredAbs M F] in
@[simp] theorem tryFA_forward {σ τ : Ty} (f : M (F.Denot (σ ⇒ τ))) (x : M (F.Denot σ)) :
    tryFA (⟨σ ⇒ τ, f⟩ : TypedDenot F M) ⟨σ, x⟩ = some ⟨τ, f <*> x⟩ := by
  simp only [tryFA, applyForward_fn]; rfl

end Reduction

end Semantics.Composition.Tree
