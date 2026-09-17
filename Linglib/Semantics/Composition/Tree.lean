import Linglib.Syntax.Tree.Basic
import Linglib.Semantics.Composition.Ty
import Linglib.Semantics.Composition.Assignment
import Linglib.Semantics.Composition.Lexicon
import Linglib.Semantics.Modification.Basic

/-!
# Type-Driven Interpretation

[heim-kratzer-1998]'s type-driven interpretation (Ch. 3-5;
[von-fintel-heim-2011], Ch. 1), parameterized over an effect functor `M`
in the style of [bumford-charlow-2024]: a node's denotation is an
`M`-computation `M (Ty.Domain E W ty)` (`Denotation`), and each composition
principle lifts through `M`'s `Applicative` structure. The pure
Heim & Kratzer engine is the `M = Id` instance (`Denotation`, `interp`
at a pure `Lexicon`) — true by construction, not by a bridge theorem.

Composition principles:
1. Terminal Nodes (TN): lexical lookup, over any leaf type: a `String` in a `Lexicon`, or a
   fragment carrier through its readings
2. Non-Branching Nodes (NN): identity
3. Functional Application (FA): `⟦α⟧ = ⟦β⟧(⟦γ⟧)` when types match
4. Intensional Functional Application (IFA): `⟦α⟧ = ⟦β⟧(^⟦γ⟧)` when
   β expects an intension `⟨s,σ⟩` and γ has type σ ([von-fintel-heim-2011] Step 10)
5. Predicate Modification (PM): combine two `⟨e,t⟩` predicates (Ch. 4)
6. Predicate Abstraction (PA): `⟦[n β]⟧^g = λx. ⟦β⟧^{g[n↦x]}` (Ch. 5)
7. Event Identification (EI): role head + eventuality predicate ([kratzer-1996])

The type a node composes to depends on its daughters' types alone (`tyBinary`,
`interp_map_fst_congr`), and a tree's denotation depends on the assignment only at the traces
free in it, [heim-kratzer-1998]'s theorems on variable binding (`interp_congr_of_agree`,
`interp_update_of_not_mem_freeIndices`, `interp_congr_of_closed`).

Two effect-discipline choices, both visible rather than stipulated:

* **Binary nodes sequence effects in linear order** — the left daughter's
  effects fire first whichever daughter is the function. At `M = Cont R`
  this makes surface scope the default reading; inverse scope requires
  reordering the evaluation (QR, or `bind`-order permutation — see
  `Composition/Cont.lean` and `Studies/BumfordCharlow2024.lean`).
* **PA is a capability, not a given** (`PredAbs`): it needs an
  entity-distributor `(E → M (Ty.Domain ty)) → M (E → Ty.Domain ty)`,
  which `Id` has and scope-type effects lack. See the `PredAbs` docstring.
-/

namespace Semantics.Composition.Tree

open Semantics.Composition
open scoped Assignment
open Semantics.Montague (Lexicon)

/-! ### Composition primitives -/

/-- Capability for Predicate Abstraction under effect `M`: an
**entity-distributor** commuting `M` over entity-indexed families.

`dist? = none` records that an effect does not support PA. `Id` (and any
Reader-like effect) has a distributor; scope-type effects (`Cont R`) do
not — abstraction would have to run one continuation at every entity
simultaneously — so binding under such effects arises from `bind`-order
or the W ⊣ R adjunction instead (`Studies/BumfordCharlow2024.lean`). Making
the distributor optional turns the QR/PA-vs-effect-sequencing rivalry
into a fact checked by instance resolution. -/
class PredAbs (M : Type → Type) (E W : Type) (D : Type := ℝ) where
  dist? : Option (∀ ty : Ty, (E → M (Ty.Domain E W ty D)) → M (E → Ty.Domain E W ty D))

instance (E W D : Type) : PredAbs Id E W D := ⟨some λ _ f => f⟩

def canApply (funTy argTy : Ty) : Option Ty :=
  match funTy with
  | .fn σ τ => if σ = argTy then some τ else none
  | _ => none

/-- TN: lexical lookup of a leaf, of any type, in its leaf interpretation. -/
def interpTerminal (E W : Type) {M : Type → Type} {D : Type} {L : Type*}
    (lex : L → Option (Denotation E W M D)) (w : L) : Option (Denotation E W M D) :=
  lex w

/-- NN: identity. -/
def interpNonBranching {E W D : Type} {M : Type → Type}
    (daughter : Denotation E W M D) : Denotation E W M D :=
  daughter

/-- FA: `⟦β⟧(⟦γ⟧)` -/
def interpFA {E W D : Type} {σ τ : Ty}
    (f : Ty.Domain E W (σ ⇒ τ) D) (x : Ty.Domain E W σ D) : Ty.Domain E W τ D :=
  f x

/-- Forward FA: the function is the left daughter `df`, the argument `da`. -/
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

/-- Backward FA: the function is the right daughter `df`, the argument `da`. The
left daughter `da` sequences first, hence the `(λ x g => g x)` combinator. -/
def applyBackward {E W D : Type} {M : Type → Type} [Applicative M]
    (da df : Denotation E W M D) : Option (Denotation E W M D) :=
  match hf : df.1 with
  | .fn σ τ =>
    if ha : σ = da.1 then
      let f : M (Ty.Domain E W (σ ⇒ τ) D) := hf ▸ df.2
      let a : M (Ty.Domain E W σ D) := ha ▸ da.2
      some ⟨τ, (λ x g => g x) <$> a <*> f⟩
    else none
  | _ => none

/-- Try FA in both orders, sequencing effects in linear order (the left daughter's
effects fire first regardless of which daughter is the function): function on the
left (`applyForward`), else on the right (`applyBackward`). -/
def tryFA {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  applyForward d1 d2 <|> applyBackward d1 d2

/-- IFA: Intensional Functional Application ([von-fintel-heim-2011] Step 10).

    If β expects an intension `⟨s,σ⟩` as argument and γ has type σ,
    then `⟦α⟧ = ⟦β⟧(^⟦γ⟧)` — γ's denotation is wrapped as a constant intension
    before applying. This lets intensional operators (modals, attitude verbs)
    take the intension of their sister as argument via type-driven composition.

    Tries both orders (β,γ) and (γ,β); effects sequence in linear order. -/
def tryIFA {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  match hf : d1.1 with
  | .fn (.intens σ) τ =>
    if ha : σ = d2.1 then
      let f : M (Ty.Domain E W (.fn (.intens σ) τ) D) := hf ▸ d1.2
      let a : M (Ty.Domain E W σ D) := ha ▸ d2.2
      some ⟨τ, (λ fv av => fv (fun _ => av)) <$> f <*> a⟩
    else
      match hf' : d2.1 with
      | .fn (.intens σ') τ' =>
        if ha' : σ' = d1.1 then
          let f : M (Ty.Domain E W (.fn (.intens σ') τ') D) := hf' ▸ d2.2
          let a : M (Ty.Domain E W σ' D) := ha' ▸ d1.2
          some ⟨τ', (λ av fv => fv (fun _ => av)) <$> a <*> f⟩
        else none
      | _ => none
  | _ =>
    match hf : d2.1 with
    | .fn (.intens σ) τ =>
      if ha : σ = d1.1 then
        let f : M (Ty.Domain E W (.fn (.intens σ) τ) D) := hf ▸ d2.2
        let a : M (Ty.Domain E W σ D) := ha ▸ d1.2
        some ⟨τ, (λ av fv => fv (fun _ => av)) <$> a <*> f⟩
      else none
    | _ => none

/-- PM: combine two `⟨e,t⟩` predicates. -/
def tryPM {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  match h1 : d1.1, h2 : d2.1 with
  | .fn .e .t, .fn .e .t =>
    let p1 : M (Ty.Domain E W (.e ⇒ .t) D) := h1 ▸ d1.2
    let p2 : M (Ty.Domain E W (.e ⇒ .t) D) := h2 ▸ d2.2
    some ⟨.fn .e .t, Modifier.intersective <$> p1 <*> p2⟩
  | _, _ => none

/-- EI: Event Identification ([kratzer-1996]): a role head `⟨e,⟨e,t⟩⟩`
combines with an eventuality predicate `⟨e,t⟩`, conjoining the predicate
onto the head's event argument — `λx.λe. f(x)(e) ∧ g(e)`. Tried in both
orders; effects sequence in linear order. -/
def tryEI {E W D : Type} {M : Type → Type} [Applicative M]
    (d1 d2 : Denotation E W M D) : Option (Denotation E W M D) :=
  match h1 : d1.1, h2 : d2.1 with
  | .fn .e (.fn .e .t), .fn .e .t =>
    let f : M (Ty.Domain E W (.e ⇒ .e ⇒ .t) D) := h1 ▸ d1.2
    let p : M (Ty.Domain E W (.e ⇒ .t) D) := h2 ▸ d2.2
    some ⟨.e ⇒ .e ⇒ .t, (λ fv pv => λ x e => fv x e ∧ pv e) <$> f <*> p⟩
  | .fn .e .t, .fn .e (.fn .e .t) =>
    let p : M (Ty.Domain E W (.e ⇒ .t) D) := h1 ▸ d1.2
    let f : M (Ty.Domain E W (.e ⇒ .e ⇒ .t) D) := h2 ▸ d2.2
    some ⟨.e ⇒ .e ⇒ .t, (λ pv fv => λ x e => fv x e ∧ pv e) <$> p <*> f⟩
  | _, _ => none

/-- Binary node: try FA, then IFA, then PM, then EI. -/
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
def interp (E W : Type) {M : Type → Type} [Applicative M] {D : Type} [PredAbs M E W D]
    {L : Type*} (lex : L → Option (Denotation E W M D)) (g : Assignment E)
    : Tree C L → Option (Denotation E W M D)
  | .terminal _ w => interpTerminal E W lex w
  | .node _ (t :: []) => (interp E W lex g t).map interpNonBranching
  | .node _ (t1 :: t2 :: []) => do
    let d1 ← interp E W lex g t1
    let d2 ← interp E W lex g t2
    interpBinary d1 d2
  | .node _ _ => none
  | .trace n _ => some ⟨.e, pure (g n)⟩
  | .bind n _ body => do
    let dist ← PredAbs.dist? (M := M) (E := E) (W := W) (D := D)
    let ⟨bodyTy, probeVal⟩ ← interp E W lex g body
    some ⟨.fn .e bodyTy,
      dist bodyTy fun x ↦ valueAt bodyTy probeVal (interp E W lex (g[n ↦ x]) body)⟩

/-- Extract truth value from (pure) tree interpretation. Effectful roots
discharge through per-effect handlers instead (`handleScope` and kin in
`Studies/BumfordCharlow2024.lean`). -/
def evalTree {E W D : Type} [∀ (p : Ty.Domain E W .t D), Decidable p] {L : Type*}
    (lex : L → Option (Denotation E W Id D)) (g : Assignment E) (t : Tree C L)
    : Option Bool :=
  match interp E W lex g t with
  | some ⟨.t, b⟩ => some (decide b)
  | _ => none

/-- Extract proposition (`s→t`) from (pure) tree interpretation.

    For intensional trees where the root denotes a proposition
    rather than a bare truth value — e.g., trees containing EXH
    or other propositional operators. Evaluate the result at a
    specific world to get a truth value. -/
def evalTreeProp {E W D : Type} [∀ (p : Ty.Domain E W .t D), Decidable p] {L : Type*}
    (lex : L → Option (Denotation E W Id D)) (g : Assignment E) (t : Tree C L)
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

theorem interpNonBranching_id {E W D : Type} (d : Denotation E W M D) :
    interpNonBranching d = d := rfl

theorem interpFA_type {E W D : Type} {σ τ : Ty}
    (f : Ty.Domain E W (σ ⇒ τ) D) (x : Ty.Domain E W σ D)
    : (interpFA f x : Ty.Domain E W τ D) = f x := rfl

theorem tryPM_preserves_type {E W D : Type} [Applicative M] (d1 d2 : Denotation E W M D)
    (h1 : d1.1 = .fn .e .t) (h2 : d2.1 = .fn .e .t)
    : ∃ d, tryPM d1 d2 = some d ∧ d.1 = .fn .e .t := by
  cases d1 with | mk ty1 val1 =>
  cases d2 with | mk ty2 val2 =>
  simp only at h1 h2
  subst h1 h2
  exact ⟨_, rfl, rfl⟩

theorem interpBinary_eq {E W D : Type} [Applicative M] (d1 d2 : Denotation E W M D) :
    interpBinary d1 d2 =
    (tryFA d1 d2 <|> tryIFA d1 d2 <|> tryPM d1 d2 <|> tryEI d1 d2) := rfl

end Properties

/-! ### Reduction lemmas (the `interp` simp normal form)

Per-constructor `@[simp]` lemmas so a derivation reduces by `simp` toward its
composed denotation, instead of relying on opaque `rfl` over the whole engine
call. Mode reduction (`tryFA`/`interpBinary` over concrete types) is the
complementary layer, and is type-shape-specific because the modes case on `Ty`. -/

section Reduction

variable {C : Type} {E W D : Type} {M : Type → Type} [Applicative M] [PredAbs M E W D]
  {L : Type*}

@[simp] theorem interp_terminal (lex : L → Option (Denotation E W M D)) (g : Assignment E)
    (c : C) (w : L) :
    interp E W lex g (.terminal c w : Tree C L) = interpTerminal E W lex w := rfl

@[simp] theorem interp_node_unary (lex : L → Option (Denotation E W M D)) (g : Assignment E)
    (c : C) (t : Tree C L) :
    interp E W lex g (.node c (t :: [])) = (interp E W lex g t).map interpNonBranching := rfl

@[simp] theorem interp_trace (lex : L → Option (Denotation E W M D)) (g : Assignment E) (n : ℕ)
    (c : C) : interp E W lex g (.trace n c : Tree C L) = some ⟨.e, pure (g n)⟩ := rfl

@[simp] theorem interp_bind (lex : L → Option (Denotation E W M D)) (g : Assignment E) (n : ℕ)
    (c : C) (body : Tree C L) :
    interp E W lex g (.bind n c body) =
      (PredAbs.dist? (M := M) (E := E) (W := W) (D := D)).bind fun dist ↦
        (interp E W lex g body).bind fun d ↦
          some ⟨.fn .e d.1, dist d.1 fun x ↦ valueAt d.1 d.2 (interp E W lex (g[n ↦ x]) body)⟩ :=
  rfl

@[simp] theorem interp_node_binary (lex : L → Option (Denotation E W M D)) (g : Assignment E)
    (c : C) (t₁ t₂ : Tree C L) :
    interp E W lex g (.node c (t₁ :: t₂ :: []))
      = ((interp E W lex g t₁).bind fun d₁ =>
          (interp E W lex g t₂).bind fun d₂ => interpBinary d₁ d₂) := rfl

omit [Applicative M] [PredAbs M E W D] in
@[simp] theorem interpTerminal_lookup (lex : L → Option (Denotation E W M D)) (w : L) :
    interpTerminal E W lex w = lex w := rfl

omit [PredAbs M E W D] in
/-- Forward FA reduces generally (abstract `σ τ`). Backward FA stays
type-shape-specific, since forward fires first when the left daughter is itself a
function. -/
@[simp] theorem applyForward_fn {σ τ : Ty} (f : M (Ty.Domain E W (σ ⇒ τ) D))
    (x : M (Ty.Domain E W σ D)) :
    applyForward (⟨σ ⇒ τ, f⟩ : Denotation E W M D) ⟨σ, x⟩ = some ⟨τ, f <*> x⟩ := by
  simp only [applyForward, ↓reduceDIte]

omit [PredAbs M E W D] in
@[simp] theorem tryFA_forward {σ τ : Ty} (f : M (Ty.Domain E W (σ ⇒ τ) D))
    (x : M (Ty.Domain E W σ D)) :
    tryFA (⟨σ ⇒ τ, f⟩ : Denotation E W M D) ⟨σ, x⟩ = some ⟨τ, f <*> x⟩ := by
  simp only [tryFA, applyForward_fn]; rfl

end Reduction

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

end Typing

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
    (interp E W lex g t).map (·.1) = (interp E W lex g' t).map (·.1) := by
  induction t using Tree.recAux generalizing g g' with
  | terminal c w => rfl
  | node c cs ih =>
    match cs with
    | [] => rfl
    | [t] => simp only [interp_node_unary, Option.map_map]; exact ih t (by simp) g g'
    | [t₁, t₂] =>
      simp only [interp_node_binary]
      have h₁ := ih t₁ (by simp) g g'
      have h₂ := ih t₂ (by simp) g g'
      revert h₁ h₂
      cases interp E W lex g t₁ <;> cases interp E W lex g' t₁ <;>
        cases interp E W lex g t₂ <;> cases interp E W lex g' t₂ <;>
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
      cases interp E W lex g body <;> cases interp E W lex g' body <;> intro h <;> simp_all

/-- The coincidence theorem: assignments agreeing on the traces free in a tree give it the
same denotation ([heim-kratzer-1998] §5.4.2). -/
theorem interp_congr_of_agree {g g' : Assignment E} {t : Tree C L}
    (h : ∀ i ∈ t.freeIndices, g i = g' i) : interp E W lex g t = interp E W lex g' t := by
  induction t using Tree.recAux generalizing g g' with
  | terminal c w => rfl
  | node c cs ih =>
    have hm : ∀ t ∈ cs, ∀ i ∈ t.freeIndices, g i = g' i := fun t ht i hi =>
      h i (by rw [Tree.freeIndices_node, Tree.mem_freeIndicesList]; exact ⟨t, ht, hi⟩)
    match cs with
    | [] => rfl
    | [t] => simp only [interp_node_unary]; rw [ih t (by simp) (hm t (by simp))]
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
      have hb : ∀ x, interp E W lex (g[n ↦ x]) body = interp E W lex (g'[n ↦ x]) body :=
        fun x ↦ ih fun i hi ↦ by
          by_cases hin : i = n
          · subst hin; simp
          · rw [Function.update_of_ne hin, Function.update_of_ne hin]
            exact h i (Finset.mem_erase.mpr ⟨hin, hi⟩)
      have ht := interp_map_fst_congr lex g g' body
      revert ht
      cases hg : interp E W lex g body <;> cases hg' : interp E W lex g' body <;> intro ht
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
    interp E W lex (g[i ↦ x]) t = interp E W lex g t :=
  interp_congr_of_agree lex fun j hj ↦
    Function.update_of_ne (fun hji ↦ h (by subst hji; exact hj)) x g

/-- [heim-kratzer-1998]'s (10): a closed tree denotes alike under every assignment. -/
theorem interp_congr_of_closed {t : Tree C L} (h : t.Closed) (g g' : Assignment E) :
    interp E W lex g t = interp E W lex g' t :=
  interp_congr_of_agree lex fun i hi ↦ absurd (h ▸ hi) (Finset.notMem_empty i)

end FreeVariables

end Semantics.Composition.Tree
