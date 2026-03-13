import Linglib.Core.Continuation
import Linglib.Theories.Semantics.Composition.WriterMonad
import Linglib.Theories.Semantics.Composition.Tree
import Linglib.Theories.Semantics.Composition.QuantifierComposition
import Linglib.Theories.Semantics.Lexical.Expressives.Basic
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Theories.Semantics.Reference.Binding
import Linglib.Theories.Semantics.Montague.Variables

/-!
# Effect-Driven Interpretation
@cite{bumford-charlow-2024}

@cite{bumford-charlow-2024} propose that diverse semantic phenomena — scope,
binding, conventional implicatures, indeterminacy — are all instances of
**algebraic effects** within the Functor → Applicative → Monad hierarchy.
The grammar's composition rules are built from **meta-combinators** (F̄, F̃,
A, J) that systematically lift basic modes of combination to work in the
presence of effects.

This file formalizes the core of their framework and bridges it to existing
linglib infrastructure:

| Effect | Paper name | Type | linglib type |
|--------|-----------|------|-------------|
| Scope | C | `(α → ρ) → ρ` | `Cont R A` |
| CI / supplementation | W | `α × List P` | `Writer P A` |
| Input (binding) | R | `ι → α` | `Reader` (Binding.lean) |
| Output (antecedents) | W | `α × ι` | `Prod` |
| Indeterminacy | S | `{α}` | — (universe issues) |

## Organization

- **§1** Lean typeclass instances for `Cont` and `Writer`
- **§2** Meta-combinators: F̄, F̃, A, J (the paper's core contribution)
- **§3** Generalized Application and hierarchy theorems
- **§4** The W ⊣ R adjunction for binding
- **§5** Effect operations and handlers
- **§6** Bridge theorems
-/

namespace Semantics.Composition.Effects

open Core.Continuation
open Semantics.Composition.WriterMonad
open Semantics.Composition.Tree
open Semantics.Composition.QuantifierComposition
open Semantics.Lexical.Expressives
open Semantics.Lexical.Determiner.Quantifier
open Semantics.Reference.Binding
open Semantics.Montague
open Semantics.Montague.Variables

-- ════════════════════════════════════════════════════════════════════
-- §1 Lean Typeclass Instances
-- ════════════════════════════════════════════════════════════════════

/-! ### §1 Typeclass instances for existing types

Register `Functor`, `Applicative`, and `Monad` instances for linglib's
`Cont R` and `Writer P` types, delegating to existing operations.

Note: `Cont R A := (A → R) → R` requires `R : Type` (not
universe-polymorphic) for Lean's `Monad` class. -/

section ContInstances

variable {R : Type}

instance : Functor (Cont R) where
  map := Cont.map

instance : Pure (Cont R) where
  pure := Cont.pure

instance : Bind (Cont R) where
  bind := Cont.bind

instance : Seq (Cont R) where
  seq mf mx := Cont.bind mf (λ f => Cont.map f (mx ()))

instance : Monad (Cont R) where

instance : LawfulMonad (Cont R) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
  bind_pure_comp _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl
  bind_map _ _ := rfl
  pure_seq _ _ := rfl
  seq_pure _ _ := rfl
  seq_assoc _ _ _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  map_pure _ _ := rfl

end ContInstances

section WriterInstances

variable {P : Type}

instance : Functor (Writer P) where
  map f m := Writer.map f m

instance : Pure (Writer P) where
  pure a := Writer.pure a

instance : Bind (Writer P) where
  bind m f := Writer.bind m f

instance : Seq (Writer P) where
  seq mf mx := Writer.app mf (mx ())

instance : Monad (Writer P) where

end WriterInstances

-- ════════════════════════════════════════════════════════════════════
-- §2 Meta-Combinators
-- ════════════════════════════════════════════════════════════════════

/-! ### §2 Meta-combinators

@cite{bumford-charlow-2024}'s central contribution: **meta-combinators**
that build higher-order modes of combination from basic ones. Given any
binary combinator `(∗) :: σ → τ → ω` (e.g., function application), these
produce new combinators that work when one or both daughters carry effects.

| Meta-combinator | Effectful daughters | Hierarchy | Paper ref |
|----------------|-------------------|-----------|-----------|
| F̄ (Map Left) | left | Functor | Figure 4 |
| F̃ (Map Right) | right | Functor | Figure 4 |
| A (Structured App) | both | Applicative | Figure 7 |
| J (Join) | both + nested | Monad | Figure 8 |
| C (Co-unit) | adjoint pair | Adjunction | Figure 10 |

F̄, F̃, A, and J are parameterized over any effect type Σ for which the
appropriate typeclass (Functor/Applicative/Monad) holds. C is defined in §4,
parameterized over an adjunction (specifically W ⊣ R). -/

section MetaCombinators

variable {σ τ ω : Type}

/-- **F̄** (Map Left): lift a binary combinator when the left daughter
    carries an effect.

    @cite{bumford-charlow-2024} eq. 2.17a, Figure 4:
    `F̄(∗) E₁ E₂ := (λa. a ∗ E₂) • E₁` -/
def mapL {F : Type → Type} [Functor F]
    (star : σ → τ → ω) (e₁ : F σ) (e₂ : τ) : F ω :=
  (fun a => star a e₂) <$> e₁

/-- **F̃** (Map Right): lift a binary combinator when the right daughter
    carries an effect.

    @cite{bumford-charlow-2024} eq. 2.17b, Figure 4:
    `F̃(∗) E₁ E₂ := (λb. E₁ ∗ b) • E₂` -/
def mapR {F : Type → Type} [Functor F]
    (star : σ → τ → ω) (e₁ : σ) (e₂ : F τ) : F ω :=
  (fun b => star e₁ b) <$> e₂

/-- **A** (Structured Application): lift when both daughters carry effects
    of the same type, merging them into a single layer.

    @cite{bumford-charlow-2024} eq. 3.10, Figure 7:
    `A(∗) E₁ E₂ := η(∗) ⊛ E₁ ⊛ E₂` -/
def structuredApp {F : Type → Type} [Applicative F]
    (star : σ → τ → ω) (e₁ : F σ) (e₂ : F τ) : F ω :=
  pure star <*> e₁ <*> e₂

/-- **J** (Join): monadic flattening for when the basic combinator
    produces a nested effect `F(F ω)`.

    @cite{bumford-charlow-2024} eq. 4.22, Figure 8:
    `J(∗) E₁ E₂ := μ(E₁ ∗ E₂)` where μ is monadic join. -/
def joinMode {F : Type → Type} [Monad F]
    (star : σ → τ → F ω) (e₁ : F σ) (e₂ : F τ) : F ω :=
  structuredApp star e₁ e₂ >>= id

-- ────────────────────────────────────────────────────
-- Meta-combinator theorems
-- ────────────────────────────────────────────────────

variable {α β : Type}

/-- Forward application: `f > x := f x`. -/
@[reducible] def fa' (f : α → β) (x : α) : β := f x

/-- Backward application: `x < f := f x`. -/
@[reducible] def ba' (x : α) (f : α → β) : β := f x

/-- **F̃(>) = fmap.** Map Right applied to forward application is
    functorial map — the forward mapping operation `(•>)`.

    @cite{bumford-charlow-2024} eq. 2.18. -/
theorem mapR_fa_eq_fmap {F : Type → Type} [Functor F]
    (f : α → β) (e₂ : F α) :
    mapR fa' f e₂ = f <$> e₂ := rfl

/-- **F̄(<) = fmap.** Map Left applied to backward application is
    functorial map — the backward mapping operation `(•<)`.

    @cite{bumford-charlow-2024} eq. 2.18. -/
theorem mapL_ba_eq_fmap {F : Type → Type} [Functor F]
    (e₁ : F α) (f : α → β) :
    mapL ba' e₁ f = f <$> e₁ := rfl

/-- **Eq. 3.6: (•) = η + (⊛).** The functorial map decomposes as
    pure (η) the function, then applicatively sequence (⊛).

    @cite{bumford-charlow-2024} eq. 3.6: `k • m := η k ⊛ m` -/
theorem fmap_eq_pure_ap {F : Type → Type}
    [Applicative F] [LawfulApplicative F] {α β : Type}
    (f : α → β) (m : F α) :
    f <$> m = pure f <*> m := by
  rw [pure_seq]

/-- Structured Application with a pure left reduces to Map Right:
    `A(∗)(η a)(E₂) = F̃(∗)(a)(E₂)`.

    Follows from the Homomorphism and Identity laws for applicatives
    (@cite{bumford-charlow-2024} eq. 3.4). -/
theorem structuredApp_pure_left {F : Type → Type}
    [Applicative F] [LawfulApplicative F]
    (star : σ → τ → ω) (a : σ) (e₂ : F τ) :
    structuredApp star (pure a) e₂ = mapR star a e₂ := by
  simp only [structuredApp, mapR, seq_pure, map_pure, pure_seq]

end MetaCombinators

-- ════════════════════════════════════════════════════════════════════
-- §3 Generalized Application
-- ════════════════════════════════════════════════════════════════════

/-! ### §3 Generalized Application and hierarchy theorems

The meta-combinators instantiated to forward application (>) yield the
familiar hierarchy of composition rules:

- **FA**: ordinary function application (the identity functor, no effects)
- **Functorial map**: pure function + effectful argument = F̃(>)
- **Applicative ap**: both effectful = A(>)
- **Monadic bind**: sequenced effects

H&K's FA is the base case — the identity functor applied to ordinary
(effect-free) meanings. -/

section GeneralizedApplication

variable {α β : Type}

/-- Functorial application: pure function, effectful argument.

    This is the `(•)` map operation from @cite{bumford-charlow-2024}
    eq. 2.3, with the forward variant `(•>)` from Figure 3. -/
def fApp {F : Type → Type} [Functor F] (f : α → β) (ma : F α) : F β := f <$> ma

/-- Applicative application: both function and argument effectful.

    This is `(⊛)` from @cite{bumford-charlow-2024} eq. 3.3 — the
    applicative functor's sequencing operation. -/
def aApp {F : Type → Type} [Applicative F] (mf : F (α → β)) (ma : F α) : F β :=
  mf <*> ma

/-- Monadic application: both effectful, with sequencing.

    Enabled by `(≫=)` from @cite{bumford-charlow-2024} Ch. 4. Every
    monad determines an applicative via eq. 4.19a:
    `F ⊛ X = F ≫= λf. f • X`. -/
def mApp {F : Type → Type} [Monad F] (mf : F (α → β)) (ma : F α) : F β :=
  mf >>= (λ f => f <$> ma)

/-- FA is functorial application for the identity functor. -/
theorem fApp_id_is_fa (f : α → β) (a : α) :
    @fApp α β Id _ f a = f a := rfl

/-- For lawful monads, monadic application agrees with applicative. -/
theorem mApp_eq_aApp {F : Type → Type} [Monad F] [LawfulMonad F]
    (mf : F (α → β)) (ma : F α) :
    mApp mf ma = aApp mf ma := by
  simp only [mApp, aApp, bind_map]

/-- Applicative application with `pure f` reduces to functorial map. -/
theorem aApp_pure_left {F : Type → Type} [Applicative F] [LawfulApplicative F]
    (f : α → β) (ma : F α) :
    aApp (pure f) ma = fApp f ma := by
  simp only [aApp, fApp, pure_seq]

/-- Applicative application = Structured Application applied to FA.

    `(⊛)` is `A(>)` — the meta-combinator A instantiated to forward
    application (@cite{bumford-charlow-2024} eq. 3.10). -/
theorem aApp_eq_structuredApp_fa {F : Type → Type}
    [Applicative F] [LawfulApplicative F]
    (mf : F (α → β)) (ma : F α) :
    aApp mf ma = structuredApp fa' mf ma := by
  simp only [aApp, structuredApp]
  have : (pure fa' <*> mf) = mf := by rw [pure_seq]; exact id_map mf
  rw [this]

end GeneralizedApplication

-- ════════════════════════════════════════════════════════════════════
-- §4 The W ⊣ R Adjunction
-- ════════════════════════════════════════════════════════════════════

/-! ### §4 The W ⊣ R adjunction for binding

@cite{bumford-charlow-2024} §5.1 proposes that binding arises from an
**adjunction** between the output effect W (= product) and the input
effect R (= reader). The adjunction W ⊣ R says that functions out of
pairs `α × ι → β` are isomorphic to curried functions `α → ι → β` —
this is just currying.

The **co-unit** ε of this adjunction — which takes a pair `⟨f, x⟩` and
applies `f` to `x` — IS the binding mechanism. When an antecedent stores
itself via `▷(x) = ⟨x, x⟩` and the sentence body uses the bound variable,
the co-unit ε yields the **W combinator** `W κ x = κ x x` from
`Binding.lean`.

Note: the paper's W (product) is distinct from linglib's `Writer P A`
(accumulating list log). The product W models single-referent storage;
the `Writer` models CI accumulation. -/

section WRAdjunction

variable {ι α β : Type}

/-- **Φ** (currying): convert from uncurried to curried form.

    @cite{bumford-charlow-2024} eq. 5.3: `Φ := λcaλx. c ⟨a, x⟩` -/
def Φ (c : α × ι → β) (a : α) (x : ι) : β := c (a, x)

/-- **Ψ** (uncurrying): convert from curried to uncurried form.

    @cite{bumford-charlow-2024} eq. 5.3: `Ψ := λk⟨a, x⟩. k a x` -/
def Ψ (k : α → ι → β) (p : α × ι) : β := k p.1 p.2

/-- Φ and Ψ are inverses (curry-uncurry round-trip). -/
theorem Φ_Ψ_id (k : α → ι → β) : Φ (Ψ k) = k := rfl

/-- Ψ and Φ are inverses (uncurry-curry round-trip). -/
theorem Ψ_Φ_id (c : α × ι → β) : Ψ (Φ c) = c := by
  funext ⟨_, _⟩; rfl

/-- **η** (unit) of W ⊣ R: `η a x = ⟨a, x⟩`.

    @cite{bumford-charlow-2024} eq. 5.4: `η := Φ id` -/
def adj_η (a : α) (x : ι) : α × ι := (a, x)

/-- **ε** (co-unit) of W ⊣ R: `ε ⟨f, x⟩ = f x`.

    @cite{bumford-charlow-2024} eq. 5.4: `ε := Ψ id`

    The co-unit extracts the value by applying the stored function
    to the stored referent — this IS binding resolution. -/
def adj_ε (p : (ι → α) × ι) : α := p.1 p.2

/-- η = Φ(id) -/
theorem adj_η_eq : @adj_η ι α = Φ id := rfl

/-- ε = Ψ(id) -/
theorem adj_ε_eq : @adj_ε ι α = Ψ id := rfl

/-- The co-unit applied to reflexive binding yields the W combinator.

    When an antecedent `x` stores itself (via `▷(x) = ⟨x, x⟩`) and the
    sentence body `κ` has been partially applied to `x`, we get
    `ε(κ x, x) = κ x x = W κ x`.

    This connects @cite{bumford-charlow-2024}'s adjunction-based binding
    to the W combinator in `Binding.lean`. -/
theorem adj_counit_yields_W (κ : ι → ι → β) (x : ι) :
    adj_ε (κ x, x) = W κ x := rfl

/-- H&K assignment-based binding and the adjunction co-unit agree
    for reflexive binding: both produce `body(binder, binder)`.

    This connects the adjunction (§5.1 of the paper) to the existing
    `hk_bs_reflexive_equiv` theorem in `Binding.lean`. -/
theorem adj_binding_agrees_with_hk {m : Model} (n : Nat)
    (body : m.Entity → m.Entity → Bool)
    (binder : m.Entity) (g : Assignment m) :
    adj_ε (body binder, binder) = body (g[n ↦ binder] n) (g[n ↦ binder] n) := by
  show body binder binder = body (g[n ↦ binder] n) (g[n ↦ binder] n)
  simp only [update_same]

end WRAdjunction

section CounitCombinator

/-! #### The C meta-combinator

@cite{bumford-charlow-2024} eq. 5.8, Figure 10: the **co-unit** meta-combinator
uses the adjunction's ε to compose W-computations (antecedent storage) with
R-computations (pronoun resolution). For W ⊣ R, C reduces to unpacking the
stored referent and feeding it to the reader function. -/

variable {ι σ τ ω : Type}

/-- **C** (Co-unit): the adjunction-based meta-combinator for binding.

    @cite{bumford-charlow-2024} eq. 5.8, Figure 10:
    `C(∗) E₁ E₂ := ε((λl. (λr. l ∗ r) • E₂) • E₁)`

    For the W ⊣ R adjunction (§5.1), where W α = α × ι (product)
    and R α = ι → α (reader), the two fmap operations compose the
    binary combinator with both computations, and ε extracts the result:
    `C(∗) ⟨s, i⟩ f = s ∗ f(i)` -/
def counitApp (star : σ → τ → ω) (e₁ : σ × ι) (e₂ : ι → τ) : ω :=
  star e₁.1 (e₂ e₁.2)

/-- C decomposes as ε applied to the doubly-mapped product.

    The general formula maps `(λr. l ∗ r)` over E₂ (R-fmap = ∘),
    maps the result over E₁ (W-fmap on the first component),
    then applies ε to extract the value. -/
theorem counitApp_via_adj_ε (star : σ → τ → ω) (e₁ : σ × ι) (e₂ : ι → τ) :
    counitApp star e₁ e₂ = adj_ε (star e₁.1 ∘ e₂, e₁.2) := rfl

/-- C with reflexive storage `▷(x) = ⟨x, x⟩` and identity reader yields W.

    When an antecedent stores itself and the pronoun is the identity
    reader, C(>) reduces to the W combinator from `Binding.lean`:
    `C(>) ⟨κ x, x⟩ id = κ x x = W κ x`.

    This connects @cite{bumford-charlow-2024}'s adjunction mechanism
    (their central §5 contribution) to the classical duplicator
    combinator that underlies binding. -/
theorem counitApp_reflexive_is_W (κ : ι → ι → ω) (x : ι) :
    counitApp fa' (κ x, x) id = W κ x := rfl

end CounitCombinator

-- ════════════════════════════════════════════════════════════════════
-- §5 Effect Operations and Handlers
-- ════════════════════════════════════════════════════════════════════

/-! ### §5 Effect operations and handlers

Named operations from @cite{bumford-charlow-2024}, connecting existing
linglib infrastructure to the effect/handler pattern.

**Effects** (introduce computational context):
- `aside`: Log a CI proposition (= `Writer.tell`)

**Handlers** (eliminate computational context):
- `handleScope`: Lower a `Cont` to its result (= `Cont.lower`)
- `handleCI`: Extract at-issue value and CI log from `Writer` -/

section EffectOps

variable {R : Type} {P : Type} {α : Type}

/-- Log a CI proposition as a side-effect. Alias for `Writer.tell`. -/
def aside (p : P) : Writer P Unit := Writer.tell p

/-- Handle the scope effect by evaluating with the identity continuation.
    Alias for `Cont.lower`. -/
def handleScope (m : Cont R R) : R := Cont.lower m

/-- Handle CI effects by extracting the value and accumulated log. -/
def handleCI (m : Writer P α) : α × List P := (m.val, m.log)

end EffectOps

-- ════════════════════════════════════════════════════════════════════
-- §6 Bridge Theorems
-- ════════════════════════════════════════════════════════════════════

/-! ### §6 Bridge theorems

Connect the effect framework to existing linglib constructions, proving
that independently-developed linglib modules are instances of the
effect-driven architecture. -/

section WriterBridge

variable {P A B : Type}

/-- `Writer.app` is applicative application (⊛) for the Writer monad.

    This connects `WriterMonad.lean`'s monadic application to the
    effect hierarchy. -/
theorem writer_app_is_seq (mf : Writer P (A → B)) (mx : Writer P A) :
    Writer.app mf mx = (mf <*> mx) := by
  exact Writer.ext rfl rfl

/-- Lowering a Cont is handling the scope effect. -/
theorem cont_lower_is_handleScope {R : Type} (m : Cont R R) :
    Cont.lower m = handleScope m := rfl

end WriterBridge

section CIBridge

variable {W : Type}

/-- A `TwoDimProp` embeds into a `Writer (W → Bool) (W → Bool)`:
    the at-issue content is the value, the CI is the log.

    This connects @cite{potts-2005}'s two-dimensional semantics to
    @cite{bumford-charlow-2024}'s Writer effect (their W constructor
    in Table 2). -/
def twoDimToWriter (p : TwoDimProp W) : Writer (W → Bool) (W → Bool) :=
  ⟨p.atIssue, [p.ci]⟩

/-- CI projection through negation follows from the Writer architecture:
    `map` transforms the value but leaves the log untouched. -/
theorem twoDim_neg_ci_via_writer (p : TwoDimProp W) :
    (twoDimToWriter (TwoDimProp.neg p)).log = (twoDimToWriter p).log := rfl

/-- The at-issue content of negation is pointwise negation of the original. -/
theorem twoDim_neg_val_via_writer (p : TwoDimProp W) :
    (twoDimToWriter (TwoDimProp.neg p)).val = λ w => !p.atIssue w := rfl

end CIBridge

section ScopeBridge

/-- A generalized quantifier IS a `Cont Bool Entity` value.

    @cite{bumford-charlow-2024} Ch. 4: the continuation monad is the
    algebraic effect for scope-taking. A GQ `(e → t) → t` IS
    `Cont Bool Entity` by definition. -/
def gqAsCont {m : Model} (gq : (m.Entity → Bool) → Bool) : Cont Bool m.Entity :=
  gq

/-- A `Cont Bool Entity` value IS a generalized quantifier. -/
def contAsGQ {m : Model} (c : Cont Bool m.Entity) : (m.Entity → Bool) → Bool :=
  c

/-- Round-trip: GQ → Cont → GQ is identity. -/
theorem gq_cont_roundtrip {m : Model} (gq : (m.Entity → Bool) → Bool) :
    contAsGQ (gqAsCont gq) = gq := rfl

/-- `every_sem` applied to a restrictor is a `Cont Bool Entity` value. -/
def every_as_cont (restrictor : toyModel.Entity → Bool) :
    Cont Bool toyModel.Entity :=
  gqAsCont (every_sem toyModel restrictor)

/-- `some_sem` applied to a restrictor is a `Cont Bool Entity` value. -/
def some_as_cont (restrictor : toyModel.Entity → Bool) :
    Cont Bool toyModel.Entity :=
  gqAsCont (some_sem toyModel restrictor)

/-- Lowering a scope-taking quantifier = applying it to the scope. -/
theorem scope_lower_eq_gq_id (restrictor scope' : toyModel.Entity → Bool) :
    handleScope (gqAsCont (every_sem toyModel restrictor) |>.bind
      (λ x => Cont.pure (scope' x))) =
    every_sem toyModel restrictor scope' := rfl

/-- Scope resolution via Cont agrees with QR tree for "every student sleeps". -/
theorem scope_agrees_with_qr_everyStudentSleeps :
    handleScope (gqAsCont (every_sem toyModel student_sem) |>.bind
      (λ x => Cont.pure (ToyLexicon.sleeps_sem x))) =
    (evalTree quantLex QuantifierComposition.g₀ tree_everyStudentSleeps).get! := by
  native_decide

/-- Scope resolution via Cont agrees with QR tree for "some student sleeps". -/
theorem scope_agrees_with_qr_someStudentSleeps :
    handleScope (gqAsCont (some_sem toyModel student_sem) |>.bind
      (λ x => Cont.pure (ToyLexicon.sleeps_sem x))) =
    (evalTree quantLex QuantifierComposition.g₀ tree_someStudentSleeps).get! := by
  native_decide

/-- Surface scope (∀>∃) via continuation composition agrees with QR. -/
theorem scope_surface_agrees_with_qr :
    (handleScope (gqAsCont (every_sem toyModel person_sem) |>.bind
      (λ x => gqAsCont (some_sem toyModel person_sem) |>.bind
        (λ y => Cont.pure (ToyLexicon.sees_sem y x))))) =
    (evalTree quantLex QuantifierComposition.g₀ tree_surface).get! := by
  native_decide

/-- Inverse scope (∃>∀) via continuation composition agrees with QR. -/
theorem scope_inverse_agrees_with_qr :
    (handleScope (gqAsCont (some_sem toyModel person_sem) |>.bind
      (λ y => gqAsCont (every_sem toyModel person_sem) |>.bind
        (λ x => Cont.pure (ToyLexicon.sees_sem y x))))) =
    (evalTree quantLex QuantifierComposition.g₀ tree_inverse).get! := by
  native_decide

/-- The two scope orderings via Cont yield genuinely different readings,
    matching `scope_readings_differ` from `QuantifierComposition.lean`. -/
theorem cont_scope_readings_differ :
    (handleScope (gqAsCont (every_sem toyModel person_sem) |>.bind
      (λ x => gqAsCont (some_sem toyModel person_sem) |>.bind
        (λ y => Cont.pure (ToyLexicon.sees_sem y x))))) ≠
    (handleScope (gqAsCont (some_sem toyModel person_sem) |>.bind
      (λ y => gqAsCont (every_sem toyModel person_sem) |>.bind
        (λ x => Cont.pure (ToyLexicon.sees_sem y x))))) := by
  native_decide

/-- Surface scope reading = true in the toy model. -/
theorem surface_scope_via_cont :
    handleScope (gqAsCont (every_sem toyModel person_sem) |>.bind
      (λ x => gqAsCont (some_sem toyModel person_sem) |>.bind
        (λ y => Cont.pure (ToyLexicon.sees_sem y x)))) = true := by
  native_decide

/-- Inverse scope reading = false in the toy model. -/
theorem inverse_scope_via_cont :
    handleScope (gqAsCont (some_sem toyModel person_sem) |>.bind
      (λ y => gqAsCont (every_sem toyModel person_sem) |>.bind
        (λ x => Cont.pure (ToyLexicon.sees_sem y x)))) = false := by
  native_decide

end ScopeBridge

end Semantics.Composition.Effects
