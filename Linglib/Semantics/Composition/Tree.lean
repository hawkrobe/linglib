import Linglib.Syntax.Tree.Basic
import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Intensional.Variables
import Linglib.Semantics.Composition.LexEntry
import Linglib.Semantics.Modification.Basic

/-!
# Type-Driven Interpretation

[heim-kratzer-1998]'s type-driven interpretation (Ch. 3-5;
[von-fintel-heim-2011], Ch. 1), parameterized over an effect functor `M`
in the style of [bumford-charlow-2024]: a node's denotation is an
`M`-computation `M (Denot E W ty)` (`TypedDenot`), and each composition
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
7. Event Identification (EI): role head + eventuality predicate ([kratzer-1996])

Two effect-discipline choices, both visible rather than stipulated:

* **Binary nodes sequence effects in linear order** — the left daughter's
  effects fire first whichever daughter is the function. At `M = Cont R`
  this makes surface scope the default reading; inverse scope requires
  reordering the evaluation (QR, or `bind`-order permutation — see
  `Composition/Continuation.lean` and `Studies/BumfordCharlow2024.lean`).
* **PA is a capability, not a given** (`PredAbs`): it needs an
  entity-distributor `(E → M (Denot ty)) → M (E → Denot ty)`,
  which `Id` has and scope-type effects lack. See the `PredAbs` docstring.
-/

namespace Semantics.Composition.Tree

open Intensional
open Intensional.Variables
open Semantics.Montague (Lexicon)

/-! ### Composition primitives -/

/-- A typed denotation: a linguistic type together with an `M`-computation
over its denotation domain. The default `M := Id` recovers the
[heim-kratzer-1998] carrier; effectful values supply `M` explicitly. -/
structure TypedDenot (E W : Type) (M : Type → Type := Id) where
  ty : Ty
  val : M (Denot E W ty)

/-- Capability for Predicate Abstraction under effect `M`: an
**entity-distributor** commuting `M` over entity-indexed families.

`dist? = none` records that an effect does not support PA. `Id` (and any
Reader-like effect) has a distributor; scope-type effects (`Cont R`) do
not — abstraction would have to run one continuation at every entity
simultaneously — so binding under such effects arises from `bind`-order
or the W ⊣ R adjunction instead (`Studies/BumfordCharlow2024.lean`). Making
the distributor optional turns the QR/PA-vs-effect-sequencing rivalry
into a fact checked by instance resolution. -/
class PredAbs (M : Type → Type) (E W : Type) where
  dist? : Option (∀ ty : Ty, (E → M (Denot E W ty)) → M (E → Denot E W ty))

instance (E W : Type) : PredAbs Id E W := ⟨some λ _ f => f⟩

def canApply (funTy argTy : Ty) : Option Ty :=
  match funTy with
  | .fn σ τ => if σ = argTy then some τ else none
  | _ => none

/-- TN: lexical lookup. -/
def interpTerminal (E W : Type) {M : Type → Type} (lex : Lexicon E W M)
    (word : String) : Option (TypedDenot E W M) :=
  (lex word).map λ entry => ⟨entry.ty, entry.denot⟩

/-- NN: identity. -/
def interpNonBranching {E W : Type} {M : Type → Type}
    (daughter : TypedDenot E W M) : TypedDenot E W M :=
  daughter

/-- FA: `⟦β⟧(⟦γ⟧)` -/
def interpFA {E W : Type} {σ τ : Ty}
    (f : Denot E W (σ ⇒ τ)) (x : Denot E W σ) : Denot E W τ :=
  f x

/-- Forward FA: the function is the left daughter `df`, the argument `da`. -/
def applyForward {E W : Type} {M : Type → Type} [Applicative M]
    (df da : TypedDenot E W M) : Option (TypedDenot E W M) :=
  match hf : df.ty with
  | .fn σ τ =>
    if ha : σ = da.ty then
      let f : M (Denot E W (σ ⇒ τ)) := hf ▸ df.val
      let a : M (Denot E W σ) := ha ▸ da.val
      some ⟨τ, f <*> a⟩
    else none
  | _ => none

/-- Backward FA: the function is the right daughter `df`, the argument `da`. The
left daughter `da` sequences first, hence the `(λ x g => g x)` combinator. -/
def applyBackward {E W : Type} {M : Type → Type} [Applicative M]
    (da df : TypedDenot E W M) : Option (TypedDenot E W M) :=
  match hf : df.ty with
  | .fn σ τ =>
    if ha : σ = da.ty then
      let f : M (Denot E W (σ ⇒ τ)) := hf ▸ df.val
      let a : M (Denot E W σ) := ha ▸ da.val
      some ⟨τ, (λ x g => g x) <$> a <*> f⟩
    else none
  | _ => none

/-- Try FA in both orders, sequencing effects in linear order (the left daughter's
effects fire first regardless of which daughter is the function): function on the
left (`applyForward`), else on the right (`applyBackward`). -/
def tryFA {E W : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot E W M) : Option (TypedDenot E W M) :=
  applyForward d1 d2 <|> applyBackward d1 d2

/-- IFA: Intensional Functional Application ([von-fintel-heim-2011] Step 10).

    If β expects an intension `⟨s,σ⟩` as argument and γ has type σ,
    then `⟦α⟧ = ⟦β⟧(^⟦γ⟧)` — we wrap γ's denotation in `up` (rigid intension)
    before applying. This lets intensional operators (modals, attitude verbs)
    take the intension of their sister as argument via type-driven composition.

    Tries both orders (β,γ) and (γ,β); effects sequence in linear order. -/
def tryIFA {E W : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot E W M) : Option (TypedDenot E W M) :=
  match hf : d1.ty with
  | .fn (.intens σ) τ =>
    if ha : σ = d2.ty then
      let f : M (Denot E W (.fn (.intens σ) τ)) := hf ▸ d1.val
      let a : M (Denot E W σ) := ha ▸ d2.val
      some ⟨τ, (λ fv av => fv (up av)) <$> f <*> a⟩
    else
      match hf' : d2.ty with
      | .fn (.intens σ') τ' =>
        if ha' : σ' = d1.ty then
          let f : M (Denot E W (.fn (.intens σ') τ')) := hf' ▸ d2.val
          let a : M (Denot E W σ') := ha' ▸ d1.val
          some ⟨τ', (λ av fv => fv (up av)) <$> a <*> f⟩
        else none
      | _ => none
  | _ =>
    match hf : d2.ty with
    | .fn (.intens σ) τ =>
      if ha : σ = d1.ty then
        let f : M (Denot E W (.fn (.intens σ) τ)) := hf ▸ d2.val
        let a : M (Denot E W σ) := ha ▸ d1.val
        some ⟨τ, (λ av fv => fv (up av)) <$> a <*> f⟩
      else none
    | _ => none

/-- PM: combine two `⟨e,t⟩` predicates. -/
def tryPM {E W : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot E W M) : Option (TypedDenot E W M) :=
  match h1 : d1.ty, h2 : d2.ty with
  | .fn .e .t, .fn .e .t =>
    let p1 : M (Denot E W (.e ⇒ .t)) := h1 ▸ d1.val
    let p2 : M (Denot E W (.e ⇒ .t)) := h2 ▸ d2.val
    some ⟨.fn .e .t, Modifier.intersective <$> p1 <*> p2⟩
  | _, _ => none

/-- EI: Event Identification ([kratzer-1996]): a role head `⟨e,⟨e,t⟩⟩`
combines with an eventuality predicate `⟨e,t⟩`, conjoining the predicate
onto the head's event argument — `λx.λe. f(x)(e) ∧ g(e)`. Tried in both
orders; effects sequence in linear order. -/
def tryEI {E W : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot E W M) : Option (TypedDenot E W M) :=
  match h1 : d1.ty, h2 : d2.ty with
  | .fn .e (.fn .e .t), .fn .e .t =>
    let f : M (Denot E W (.e ⇒ .e ⇒ .t)) := h1 ▸ d1.val
    let p : M (Denot E W (.e ⇒ .t)) := h2 ▸ d2.val
    some ⟨.e ⇒ .e ⇒ .t, (λ fv pv => λ x e => fv x e ∧ pv e) <$> f <*> p⟩
  | .fn .e .t, .fn .e (.fn .e .t) =>
    let p : M (Denot E W (.e ⇒ .t)) := h1 ▸ d1.val
    let f : M (Denot E W (.e ⇒ .e ⇒ .t)) := h2 ▸ d2.val
    some ⟨.e ⇒ .e ⇒ .t, (λ pv fv => λ x e => fv x e ∧ pv e) <$> p <*> f⟩
  | _, _ => none

/-- Binary node: try FA, then IFA, then PM, then EI. -/
def interpBinary {E W : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : TypedDenot E W M) : Option (TypedDenot E W M) :=
  tryFA d1 d2 <|> tryIFA d1 d2 <|> tryPM d1 d2 <|> tryEI d1 d2

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
def interp (E W : Type) {M : Type → Type} [Applicative M] [PredAbs M E W]
    (lex : Lexicon E W M) (g : Core.Assignment E)
    : Tree C String → Option (TypedDenot E W M)
  | .terminal _ w => interpTerminal E W lex w
  | .node _ (t :: []) => (interp E W lex g t).map interpNonBranching
  | .node _ (t1 :: t2 :: []) => do
    let d1 ← interp E W lex g t1
    let d2 ← interp E W lex g t2
    interpBinary d1 d2
  | .node _ _ => none
  | .trace n _ => some ⟨.e, pure (g n)⟩
  | .bind n _ body => do
    let dist ← PredAbs.dist? (M := M) (E := E) (W := W)
    let ⟨bodyTy, probeVal⟩ ← interp E W lex g body
    some ⟨.fn .e bodyTy, dist bodyTy λ (x : E) =>
      match interp E W lex (g[n ↦ x]) body with
      | some ⟨ty, val⟩ => if h : ty = bodyTy then h ▸ val else probeVal
      | none => probeVal⟩

/-- Extract truth value from (pure) tree interpretation. Effectful roots
discharge through per-effect handlers instead (`handleScope` and kin in
`Studies/BumfordCharlow2024.lean`). -/
def evalTree {E W : Type} [∀ (p : Denot E W .t), Decidable p]
    (lex : Lexicon E W) (g : Core.Assignment E) (t : Tree C String)
    : Option Bool :=
  match interp E W lex g t with
  | some ⟨.t, b⟩ => some (decide b)
  | _ => none

/-- Extract proposition (`s→t`) from (pure) tree interpretation.

    For intensional trees where the root denotes a proposition
    rather than a bare truth value — e.g., trees containing EXH
    or other propositional operators. Evaluate the result at a
    specific world to get a truth value. -/
def evalTreeProp {E W : Type} [∀ (p : Denot E W .t), Decidable p]
    (lex : Lexicon E W) (g : Core.Assignment E) (t : Tree C String)
    : Option (W → Bool) :=
  match interp E W lex g t with
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

theorem interpNonBranching_id {E W : Type} (d : TypedDenot E W M) :
    interpNonBranching d = d := rfl

theorem interpFA_type {E W : Type} {σ τ : Ty}
    (f : Denot E W (σ ⇒ τ)) (x : Denot E W σ)
    : (interpFA f x : Denot E W τ) = f x := rfl

theorem tryPM_preserves_type {E W : Type} [Applicative M] (d1 d2 : TypedDenot E W M)
    (h1 : d1.ty = .fn .e .t) (h2 : d2.ty = .fn .e .t)
    : ∃ d, tryPM d1 d2 = some d ∧ d.ty = .fn .e .t := by
  cases d1 with | mk ty1 val1 =>
  cases d2 with | mk ty2 val2 =>
  simp only at h1 h2
  subst h1 h2
  exact ⟨_, rfl, rfl⟩

theorem interpBinary_eq {E W : Type} [Applicative M] (d1 d2 : TypedDenot E W M) :
    interpBinary d1 d2 =
    (tryFA d1 d2 <|> tryIFA d1 d2 <|> tryPM d1 d2 <|> tryEI d1 d2) := rfl

end Properties

/-! ### Reduction lemmas (the `interp` simp normal form)

Per-constructor `@[simp]` lemmas so a derivation reduces by `simp` toward its
composed denotation, instead of relying on opaque `rfl` over the whole engine
call. Mode reduction (`tryFA`/`interpBinary` over concrete types) is the
complementary layer, and is type-shape-specific because the modes case on `Ty`. -/

section Reduction

variable {C : Type} {E W : Type} {M : Type → Type} [Applicative M] [PredAbs M E W]

@[simp] theorem interp_terminal (lex : Lexicon E W M) (g : Core.Assignment E)
    (c : C) (w : String) :
    interp E W lex g (.terminal c w : Tree C String) = interpTerminal E W lex w := rfl

@[simp] theorem interp_node_binary (lex : Lexicon E W M) (g : Core.Assignment E)
    (c : C) (t₁ t₂ : Tree C String) :
    interp E W lex g (.node c (t₁ :: t₂ :: []))
      = ((interp E W lex g t₁).bind fun d₁ =>
          (interp E W lex g t₂).bind fun d₂ => interpBinary d₁ d₂) := rfl

omit [Applicative M] [PredAbs M E W] in
@[simp] theorem interpTerminal_lookup (lex : Lexicon E W M) (w : String) :
    interpTerminal E W lex w = (lex w).map fun e => ⟨e.ty, e.denot⟩ := rfl

omit [PredAbs M E W] in
/-- Forward FA reduces generally (abstract `σ τ`). Backward FA stays
type-shape-specific, since forward fires first when the left daughter is itself a
function. -/
@[simp] theorem applyForward_fn {σ τ : Ty} (f : M (Denot E W (σ ⇒ τ))) (x : M (Denot E W σ)) :
    applyForward (⟨σ ⇒ τ, f⟩ : TypedDenot E W M) ⟨σ, x⟩ = some ⟨τ, f <*> x⟩ := by
  simp only [applyForward, ↓reduceDIte]

omit [PredAbs M E W] in
@[simp] theorem tryFA_forward {σ τ : Ty} (f : M (Denot E W (σ ⇒ τ))) (x : M (Denot E W σ)) :
    tryFA (⟨σ ⇒ τ, f⟩ : TypedDenot E W M) ⟨σ, x⟩ = some ⟨τ, f <*> x⟩ := by
  simp only [tryFA, applyForward_fn]; rfl

end Reduction

end Semantics.Composition.Tree
