import Linglib.Semantics.Composition.Continuation
import Linglib.Semantics.Composition.WriterMonad
import Mathlib.Data.Set.Functor
import Linglib.Semantics.Composition.Tree
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Reference.Binding
import Linglib.Core.Logic.Intensional.Defs
import Linglib.Core.Logic.Intensional.Variables
import Linglib.Fragments.English.Toy
import Linglib.Semantics.Composition.LexEntry

/-!
# [bumford-charlow-2024]: Effect-Driven Interpretation

[bumford-charlow-2024] cast diverse semantic phenomena — scope, binding,
conventional implicature, indeterminacy — as algebraic effects in the
Functor → Applicative → Monad hierarchy, with **meta-combinators** lifting
the basic modes of combination into the presence of effects. This study
formalizes that framework over linglib's effect carriers:

| Effect | Type | linglib carrier |
|--------|------|-----------------|
| Scope | `(α → ρ) → ρ` | `Cont R A` (`Composition/Continuation`) |
| CI / supplementation | `α × List P` | `Writer (List P) A` (`Composition/WriterMonad`) |
| Input (binding) | `ι → α` | Reader (`Reference/Binding`) |
| Output (antecedent) | `α × ι` | `Prod` |
| Indeterminacy | `{α}` | `Set` |

## Main declarations

* `F̄`/`F̃` (Functor), `A` (Applicative), `J` (Monad), `counitApp` (the W⊣R
  co-unit `C`) — modes of combination lifting application into effects.
* The W⊣R adjunction `Φ`/`Ψ`/`adj_η`/`adj_ε`: binding is the co-unit.
* `binding_C_agrees_with_hk` and the three-way unification: adjunction
  binding ≡ Heim-Kratzer assignment binding ≡ the `W` combinator.

## Crossover

[bumford-charlow-2024] §5.2: crossover is inherited from the
*non-commutativity of the W⊣R adjunction*. `counitApp` fires the co-unit
`ε` only when the W (antecedent) is the **left** daughter. With the
pronoun's R on the left, scope may still invert — the antecedent outscopes
the pronoun — yet binding never resolves: "anaphoric ships passing in the
night." There is no recovery mechanism; the account is *categorical*.

The `Crossover` namespace (§10) formalizes this: the dissociation
(`scope_inversion_no_binding`), the structural derivation (`combine`/`derive`,
returning either the bound co-unit reading or the Reader-retaining residual),
and the phenomenon-neutral bridge `derive_bound_iff_precedes` — the bound
reading derives iff the antecedent linearly precedes the pronoun. The
Owusu/Chierchia *bí*/*biara* functional-reading asymmetry ([owusu-2022] §3.3.2,
[chierchia-2001]) is one instance; superiority and primary/secondary crossover
are others over the same `derive`.

This diverges from [shan-barker-2006], whose left-to-right `Scope` rule
admits a marked right-to-left `Z` variant that recovers weak crossover as a
*gradient*, defeasible reading (their continuation-level mechanism: a binder
must take effect at the pronoun's continuation level, so crossing fails to
unify under `Down`). Formalizing the S&B continuation calculus and the
non-coincidence theorem between the two accounts is deferred — there is no
S&B substrate in linglib yet.

## Implementation notes

Scope-as-bind-order (`scope_ambiguity_is_bind_order` et al.) lives with the
`Cont` monad in `Composition/Continuation`; this study consumes it.
The eject combinators (`Ū`/`Ũ`/`⊿`) of Figure 10 are not formalized.
-/

namespace BumfordCharlow2024

open Semantics.Composition
open Semantics.Composition.Continuation
open Semantics.Composition.Tree
open Pragmatics.Expressives
open Quantification.Quantifier
open Semantics.Reference.Binding
open Core.Logic.Intensional
open Core.Logic.Intensional.Variables
open Semantics.Montague
open Semantics.Montague.ToyLexicon (student_sem person_sem)

-- ════════════════════════════════════════════════════════════════════
-- §1 Lean Typeclass Instances
-- ════════════════════════════════════════════════════════════════════

/-! ### §1 Typeclass instances for existing types

The W effect is mathlib's `Writer (List P)` (= `WriterT (List P) Id`), whose
`Functor`/`Applicative`/`Monad` instances come from mathlib, with
`LawfulMonad` and the `val`/`log`/`tell` surface in
`Composition/WriterMonad.lean`. The `Cont R` instances live with the
type in `Composition/Continuation.lean`. -/

-- ════════════════════════════════════════════════════════════════════
-- §2 Meta-Combinators
-- ════════════════════════════════════════════════════════════════════

/-! ### §2 Meta-combinators

central contribution: **meta-combinators**
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

    eq. 2.17a, Figure 4:
    `F̄(∗) E₁ E₂ := (λa. a ∗ E₂) • E₁` -/
def mapL {F : Type → Type} [Functor F]
    (star : σ → τ → ω) (e₁ : F σ) (e₂ : τ) : F ω :=
  (fun a => star a e₂) <$> e₁

/-- **F̃** (Map Right): lift a binary combinator when the right daughter
    carries an effect.

    eq. 2.17b, Figure 4:
    `F̃(∗) E₁ E₂ := (λb. E₁ ∗ b) • E₂` -/
def mapR {F : Type → Type} [Functor F]
    (star : σ → τ → ω) (e₁ : σ) (e₂ : F τ) : F ω :=
  (fun b => star e₁ b) <$> e₂

/-- **A** (Structured Application): lift when both daughters carry effects
    of the same type, merging them into a single layer.

    eq. 3.10, Figure 7:
    `A(∗) E₁ E₂ := η(∗) ⊛ E₁ ⊛ E₂` -/
def structuredApp {F : Type → Type} [Applicative F]
    (star : σ → τ → ω) (e₁ : F σ) (e₂ : F τ) : F ω :=
  pure star <*> e₁ <*> e₂

/-- **J** (Join): monadic flattening for when the basic combinator
    produces a nested effect `F(F ω)`.

    eq. 4.22, Figure 8:
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

    eq. 2.18. -/
theorem mapR_fa_eq_fmap {F : Type → Type} [Functor F]
    (f : α → β) (e₂ : F α) :
    mapR fa' f e₂ = f <$> e₂ := rfl

/-- **F̄(<) = fmap.** Map Left applied to backward application is
    functorial map — the backward mapping operation `(•<)`.

    eq. 2.18. -/
theorem mapL_ba_eq_fmap {F : Type → Type} [Functor F]
    (e₁ : F α) (f : α → β) :
    mapL ba' e₁ f = f <$> e₁ := rfl

/-- **Eq. 3.6: (•) = η + (⊛).** The functorial map decomposes as
    pure (η) the function, then applicatively sequence (⊛).

    eq. 3.6: `k • m := η k ⊛ m` -/
theorem fmap_eq_pure_ap {F : Type → Type}
    [Applicative F] [LawfulApplicative F] {α β : Type}
    (f : α → β) (m : F α) :
    f <$> m = pure f <*> m := by
  rw [pure_seq]

/-- Structured Application with a pure left reduces to Map Right:
    `A(∗)(η a)(E₂) = F̃(∗)(a)(E₂)`.

    Follows from the Homomorphism and Identity laws for applicatives
    (eq. 3.4). -/
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

    This is the `(•)` map operation from
    eq. 2.3, with the forward variant `(•>)` from Figure 3. -/
def fApp {F : Type → Type} [Functor F] (f : α → β) (ma : F α) : F β := f <$> ma

/-- Applicative application: both function and argument effectful.

    This is `(⊛)` from eq. 3.3 — the
    applicative functor's sequencing operation. -/
def aApp {F : Type → Type} [Applicative F] (mf : F (α → β)) (ma : F α) : F β :=
  mf <*> ma

/-- Monadic application: both effectful, with sequencing.

    Enabled by `(≫=)` from Ch. 4. Every
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
    application (eq. 3.10). -/
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

§5.1 proposes that binding arises from an
**adjunction** between the output effect W (= product) and the input
effect R (= reader). The adjunction W ⊣ R says that functions out of
pairs `α × ι → β` are isomorphic to curried functions `α → ι → β` —
this is just currying.

The **co-unit** ε of this adjunction — which takes a pair `⟨f, x⟩` and
applies `f` to `x` — IS the binding mechanism. When an antecedent stores
itself via `▷(x) = ⟨x, x⟩` and the sentence body uses the bound variable,
the co-unit ε yields the **W combinator** `W κ x = κ x x` from
`Binding.lean`.

Note: the paper's W (product) is distinct from `Writer (List P) A`
(accumulating list log). The product W models single-referent storage;
the `Writer` models CI accumulation. -/

section WRAdjunction

variable {ι α β : Type}

/-- **Φ** (currying): convert from uncurried to curried form.

    eq. 5.3: `Φ := λcaλx. c ⟨a, x⟩` -/
def Φ (c : α × ι → β) (a : α) (x : ι) : β := c (a, x)

/-- **Ψ** (uncurrying): convert from curried to uncurried form.

    eq. 5.3: `Ψ := λk⟨a, x⟩. k a x` -/
def Ψ (k : α → ι → β) (p : α × ι) : β := k p.1 p.2

/-- Φ and Ψ are inverses (curry-uncurry round-trip). -/
theorem Φ_Ψ_id (k : α → ι → β) : Φ (Ψ k) = k := rfl

/-- Ψ and Φ are inverses (uncurry-curry round-trip). -/
theorem Ψ_Φ_id (c : α × ι → β) : Ψ (Φ c) = c := by
  funext ⟨_, _⟩; rfl

/-- **η** (unit) of W ⊣ R: `η a x = ⟨a, x⟩`.

    eq. 5.4: `η := Φ id` -/
def adj_η (a : α) (x : ι) : α × ι := (a, x)

/-- **ε** (co-unit) of W ⊣ R: `ε ⟨f, x⟩ = f x`.

    eq. 5.4: `ε := Ψ id`

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

    This connects adjunction-based binding
    to the W combinator in `Binding.lean`. -/
theorem adj_counit_yields_W (κ : ι → ι → β) (x : ι) :
    adj_ε (κ x, x) = W κ x := rfl

/-- H&K assignment-based binding and the adjunction co-unit agree
    for reflexive binding: both produce `body(binder, binder)`.

    This connects the adjunction (§5.1 of the paper) to the existing
    `hk_bs_reflexive_equiv` theorem in `Binding.lean`. -/
theorem adj_binding_agrees_with_hk {E : Type} (n : Nat)
    (body : E → E → Prop)
    (binder : E) (g : Core.Assignment E) :
    adj_ε (body binder, binder) = body (g[n ↦ binder] n) (g[n ↦ binder] n) := by
  show body binder binder = body (g[n ↦ binder] n) (g[n ↦ binder] n)
  simp only [Function.update_self]

end WRAdjunction

section CounitCombinator

/-! #### The C meta-combinator

eq. 5.8, Figure 10: the **co-unit** meta-combinator
uses the adjunction's ε to compose W-computations (antecedent storage) with
R-computations (pronoun resolution). For W ⊣ R, C reduces to unpacking the
stored referent and feeding it to the reader function. -/

variable {ι σ τ ω : Type}

/-- **C** (Co-unit): the adjunction-based meta-combinator for binding.

    eq. 5.8, Figure 10:
    `C(∗) E₁ E₂ := ε((λl. (λr. l ∗ r) • E₂) • E₁)`

    For the W ⊣ R adjunction (§5.1), where W α = α × ι (product)
    and R α = ι → α (reader), the two fmap operations compose the
    binary combinator with both computations, and ε extracts the result:
    `C(∗) ⟨s, i⟩ f = s ∗ f(i)`

    **Crossover** (§5.2): The type signature encodes the crossover
    constraint — the W effect (antecedent, `σ × ι`) must be the left
    daughter and the R effect (pronoun, `ι → τ`) the right daughter.
    Swapping them produces a type error, not a binding failure: there
    is no well-typed `counitApp star (e₂ : ι → τ) (e₁ : σ × ι)`. -/
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

    This connects adjunction mechanism
    (their central §5 contribution) to the classical duplicator
    combinator that underlies binding. -/
theorem counitApp_reflexive_is_W (κ : ι → ι → ω) (x : ι) :
    counitApp fa' (κ x, x) id = W κ x := rfl

end CounitCombinator

-- ════════════════════════════════════════════════════════════════════
-- §5 Effect Operations and Handlers
-- ════════════════════════════════════════════════════════════════════

/-! ### §5 Effect operations and handlers

Named operations from, connecting existing
linglib infrastructure to the effect/handler pattern.

**Effects** (introduce computational context):
- `aside`: Log a CI proposition (= `Writer.tell`)

**Handlers** (eliminate computational context):
- `handleScope`: Lower a `Cont` to its result (= `Cont.lower`)
- `handleCI`: Extract at-issue value and CI log from `Writer` -/

section EffectOps

variable {R : Type} {P : Type} {α : Type}

/-- Log a CI proposition as a side-effect. Alias for `Writer.tell`. -/
def aside (p : P) : Writer (List P) Unit := Writer.tell p

/-- Handle the scope effect by evaluating with the identity continuation.
    Alias for `Cont.lower`. -/
def handleScope (m : Cont R R) : R := Cont.lower m

/-- Handle CI effects by extracting the value and accumulated log. -/
def handleCI (m : Writer (List P) α) : α × List P := (m.val, m.log)

end EffectOps

section PredAbsInstances

/-! #### PA capability under effects

`Tree.PredAbs` records which effects admit Predicate Abstraction. The
negative instances are theoretical content, not bookkeeping: they state
in the type system that QR/PA-style binding is unavailable under these
effects, so scope and binding must come from effect sequencing instead
(`bind`-order, the W ⊣ R adjunction of §4). -/

/-- Scope effects do not support Predicate Abstraction: a distributor
`(Entity → Cont R α) → Cont R (Entity → α)` would have to run one
continuation at every entity simultaneously. Binding under scope arises
from `bind`-order instead (§7). -/
instance {R E W : Type} : Tree.PredAbs (Cont R) E W := ⟨none⟩

/-- CI effects do not support Predicate Abstraction: the log of
`⟦β⟧^{g[n↦x]}` may vary with `x`, so no log-respecting distributor
exists. CI content composes around abstraction, not through it. -/
instance {ω E W : Type} : Tree.PredAbs (Writer ω) E W := ⟨none⟩

end PredAbsInstances

-- ════════════════════════════════════════════════════════════════════
-- §6 Bridge Theorems
-- ════════════════════════════════════════════════════════════════════

/-! ### §6 Bridge theorems

Connect the effect framework to existing linglib constructions, proving
that independently-developed linglib modules are instances of the
effect-driven architecture. -/

section WriterBridge

-- `Writer`'s monadic application IS `<*>` (mathlib's `WriterT` instance),
-- so no bridge theorem is needed for the W effect.

/-- Lowering a Cont is handling the scope effect. -/
theorem cont_lower_is_handleScope {R : Type} (m : Cont R R) :
    Cont.lower m = handleScope m := rfl

end WriterBridge

section CIBridge

variable {W : Type}

/-- A `TwoDimProp` embeds into a `Writer (List (W → Prop)) (W → Prop)`:
    the at-issue content is the value, the CI is the log.

    This connects [potts-2005]'s two-dimensional semantics to
    Writer effect (their W constructor
    in Table 2). -/
def twoDimToWriter (p : TwoDimProp W) : Writer (List (W → Prop)) (W → Prop) :=
  Writer.mk p.atIssue ([p.ci])

-- ────────────────────────────────────────────────────
-- CI projection universality
-- ────────────────────────────────────────────────────

/-- **CI projection universality.** Any operation that acts via `<$>`
    (i.e., transforms the value but leaves the log untouched)
    automatically preserves all CI content.

    This is the general principle behind CI projection through negation,
    conditionals, and questions: they are all Functor maps on the Writer.
    Projection is not a special property of each operator — it is the
    Functor law.

    Specializes to `twoDim_neg_ci_via_writer` when `f = fun p w => !p w`. -/
theorem ci_projection_universal {W A B : Type}
    (f : A → B) (m : Writer (List (W → Prop)) A) :
    (f <$> m).log = m.log := rfl

/-- CI projection through negation follows from the Writer architecture:
    `map` transforms the value but leaves the log untouched. -/
theorem twoDim_neg_ci_via_writer (p : TwoDimProp W) :
    (twoDimToWriter (TwoDimProp.neg p)).log = (twoDimToWriter p).log := rfl

/-- The at-issue content of negation is pointwise negation of the original. -/
theorem twoDim_neg_val_via_writer (p : TwoDimProp W) :
    (twoDimToWriter (TwoDimProp.neg p)).val = λ w => ¬ p.atIssue w := rfl

-- ────────────────────────────────────────────────────
-- Running the CI Writer (shunting)
-- ────────────────────────────────────────────────────

/-- Run a CI Writer by conjoining all log entries with the value.

    This is the Writer counterpart of shunting (↓ from
    [kirk-giannini-2024]): peripheral content is folded into
    the at-issue dimension via conjunction, and the CI dimension
    becomes trivial. The result is a `TwoDimProp` with all information
    in the at-issue dimension.

    For a single-CI Writer (the standard case from `twoDimToWriter`),
    this computes `atIssue w && ci w` — identical to the `shunt`
    function in `Semantics.Quotation.MixedQuotation`.

    For multi-CI Writers (e.g., "that bastard John met that jerk Pete"
    with two CI entries), this conjoins all CIs into at-issue content. -/
def runCIWriter {W : Type} (m : Writer (List (W → Prop)) (W → Prop)) : TwoDimProp W :=
  { atIssue := λ w => m.log.foldl (λ acc ci => acc ∧ ci w) (m.val w)
  , ci := λ _ => True }

/-- Running a CI Writer consumes the log: the result has trivial CI. -/
theorem runCIWriter_trivial_ci {W : Type} (m : Writer (List (W → Prop)) (W → Prop)) (w : W) :
    (runCIWriter m).ci w ↔ True := Iff.rfl

/-- Running a Writer with an empty log preserves the value unchanged. -/
theorem runCIWriter_empty_log {W : Type} (val : W → Prop) (w : W) :
    (runCIWriter (Writer.mk val ([]))).atIssue w = val w := rfl

/-- Running a Writer with a trivially-true log entry preserves the
    value unchanged.

    Pure quotation = clearing the log to `[λ _ => True]`. Running
    such a Writer recovers the original at-issue content. -/
theorem runCIWriter_trivial_log {W : Type} (val : W → Prop) (w : W) :
    (runCIWriter (Writer.mk val ([λ _ => True]))).atIssue w ↔ val w := by
  simp [runCIWriter]

-- ────────────────────────────────────────────────────
-- Single-CI round-trip (TwoDimProp ↔ Writer)
-- ────────────────────────────────────────────────────

/-- **Single-CI round-trip.** Embedding a `TwoDimProp` into Writer then
    running conjoins the at-issue and CI dimensions — exactly the
    shunting operation ↓ from [kirk-giannini-2024].

    This is definitionally equal to `shunt` from
    `Semantics.Quotation.MixedQuotation`. -/
theorem runCIWriter_twoDim {W : Type} (p : TwoDimProp W) (w : W) :
    (runCIWriter (twoDimToWriter p)).atIssue w ↔ (p.atIssue w ∧ p.ci w) := Iff.rfl

/-- Function-level version: the round-trip is shunting as a function,
    not just at a single world. -/
theorem runCIWriter_twoDim_fn {W : Type} (p : TwoDimProp W) :
    (runCIWriter (twoDimToWriter p)).atIssue = λ w => p.atIssue w ∧ p.ci w := rfl

-- ────────────────────────────────────────────────────
-- Multi-CI compositionality
-- ────────────────────────────────────────────────────

/-- **Log compositionality.** Running a Writer whose log is a
    concatenation = running the first part, then folding the rest on top.

    This is the multi-CI generalization of shunting. When `Writer.bind`
    sequences two CI-producing computations (e.g., "that bastard John
    met that jerk Pete"), their logs are concatenated. Running the result
    conjoins all CIs into the at-issue dimension.

    Follows from `List.foldl_append`. -/
theorem runCIWriter_log_append {W : Type}
    (val : W → Prop) (cis₁ cis₂ : List (W → Prop)) (w : W) :
    (runCIWriter (Writer.mk val (cis₁ ++ cis₂))).atIssue w =
    cis₂.foldl (λ acc ci => acc ∧ ci w)
      ((runCIWriter (Writer.mk val cis₁)).atIssue w) := by
  simp [runCIWriter, List.foldl_append]

/-- **Idempotency.** Running, re-embedding, and running again = running once.

    After `runCIWriter` consumes the log, the CI dimension is trivial.
    Re-embedding (via `twoDimToWriter`) creates a `[fun _ => true]` log.
    Running again conjoins with `true`, which is the identity.

    This is the retraction property: `runCIWriter ∘ twoDimToWriter` is
    idempotent on the image of `runCIWriter`. -/
theorem runCIWriter_idempotent {W : Type}
    (m : Writer (List (W → Prop)) (W → Prop)) (w : W) :
    (runCIWriter (twoDimToWriter (runCIWriter m))).atIssue w ↔
    (runCIWriter m).atIssue w := by
  simp [runCIWriter, twoDimToWriter]

end CIBridge

section ScopeBridge

/-- A generalized quantifier IS a `Cont Prop Entity` value.

    Ch. 4: the continuation monad is the
    algebraic effect for scope-taking. A GQ `(e → t) → t` IS
    `Cont Prop Entity` by definition. -/
def gqAsCont {E : Type} (gq : (E → Prop) → Prop) : Cont Prop E :=
  gq

/-- A `Cont Prop Entity` value IS a generalized quantifier. -/
def contAsGQ {E : Type} (c : Cont Prop E) : (E → Prop) → Prop :=
  c

/-- Round-trip: GQ → Cont → GQ is identity. -/
theorem gq_cont_roundtrip {E : Type} (gq : (E → Prop) → Prop) :
    contAsGQ (gqAsCont gq) = gq := rfl

/-- `every_sem` applied to a restrictor is a `Cont Prop Entity` value. -/
def every_as_cont (restrictor : ToyEntity → Prop) :
    Cont Prop ToyEntity :=
  gqAsCont (every_sem restrictor)

/-- `some_sem` applied to a restrictor is a `Cont Prop Entity` value. -/
def some_as_cont (restrictor : ToyEntity → Prop) :
    Cont Prop ToyEntity :=
  gqAsCont (some_sem restrictor)

/-- Lowering a scope-taking quantifier = applying it to the scope. -/
theorem scope_lower_eq_gq_id (restrictor scope' : ToyEntity → Prop) :
    handleScope (gqAsCont (every_sem restrictor) |>.bind
      (λ x => Cont.pure (scope' x))) =
    every_sem restrictor scope' := rfl

/-- Scope resolution via Cont agrees with direct GQ application for
    "every student sleeps": the Cont derivation produces the same Prop. -/
theorem scope_agrees_with_qr_everyStudentSleeps :
    handleScope (gqAsCont (every_sem student_sem) |>.bind
      (λ x => Cont.pure (ToyLexicon.sleeps_sem x))) =
    every_sem student_sem ToyLexicon.sleeps_sem := rfl

/-- Scope resolution via Cont agrees with direct GQ application for
    "some student sleeps". -/
theorem scope_agrees_with_qr_someStudentSleeps :
    handleScope (gqAsCont (some_sem student_sem) |>.bind
      (λ x => Cont.pure (ToyLexicon.sleeps_sem x))) =
    some_sem student_sem ToyLexicon.sleeps_sem := rfl

/-- Surface scope (∀>∃) via continuation composition agrees with direct
    GQ application. -/
theorem scope_surface_agrees_with_qr :
    handleScope (gqAsCont (every_sem person_sem) |>.bind
      (λ x => gqAsCont (some_sem person_sem) |>.bind
        (λ y => Cont.pure (ToyLexicon.sees_sem y x)))) =
    every_sem person_sem
      (λ x => some_sem person_sem (λ y => ToyLexicon.sees_sem y x)) := rfl

/-- Inverse scope (∃>∀) via continuation composition agrees with direct
    GQ application. -/
theorem scope_inverse_agrees_with_qr :
    handleScope (gqAsCont (some_sem person_sem) |>.bind
      (λ y => gqAsCont (every_sem person_sem) |>.bind
        (λ x => Cont.pure (ToyLexicon.sees_sem y x)))) =
    some_sem person_sem
      (λ y => every_sem person_sem (λ x => ToyLexicon.sees_sem y x)) := rfl

/-- Surface scope reading holds in the toy model. -/
theorem surface_scope_via_cont :
    handleScope (gqAsCont (every_sem person_sem) |>.bind
      (λ x => gqAsCont (some_sem person_sem) |>.bind
        (λ y => Cont.pure (ToyLexicon.sees_sem y x)))) := by
  intro x hpx
  cases x with
  | john => exact ⟨.mary, trivial, trivial⟩
  | mary => exact ⟨.john, trivial, trivial⟩
  | _ => exact absurd hpx id

/-- Inverse scope reading does not hold in the toy model. -/
theorem inverse_scope_via_cont :
    ¬handleScope (gqAsCont (some_sem person_sem) |>.bind
      (λ y => gqAsCont (every_sem person_sem) |>.bind
        (λ x => Cont.pure (ToyLexicon.sees_sem y x)))) := by
  intro ⟨y, _, hy⟩
  cases y with
  | john => exact absurd (hy .john trivial) id
  | mary => exact absurd (hy .mary trivial) id
  | _ => exact absurd (by assumption : person_sem _) id

/-- The two scope orderings via Cont yield genuinely different readings,
    matching `HeimKratzer1998.scope_readings_differ`. -/
theorem cont_scope_readings_differ :
    (handleScope (gqAsCont (every_sem person_sem) |>.bind
      (λ x => gqAsCont (some_sem person_sem) |>.bind
        (λ y => Cont.pure (ToyLexicon.sees_sem y x))))) ≠
    (handleScope (gqAsCont (some_sem person_sem) |>.bind
      (λ y => gqAsCont (every_sem person_sem) |>.bind
        (λ x => Cont.pure (ToyLexicon.sees_sem y x))))) := by
  intro h
  have hS := surface_scope_via_cont
  have hI := inverse_scope_via_cont
  rw [h] at hS
  exact hI hS

end ScopeBridge

section TreeEngine

/-! #### The tree engine under effects

`Tree.interp` is polymorphic over the effect functor: the same type-driven
engine that implements H&K at `M = Id` lifts through any `[Applicative M]`.
At the FA mode that lifting is literally the meta-combinator **A** — a
framework-level identity, no toy lexicon required. Worked tree-level
derivations at `M = Cont` (scope) and `M = Writer` (CI) live in
`Studies/BumfordCharlow2024.lean` alongside the toy-model demonstrations. -/

/-! The engine's FA mode applies the function daughter to the argument through
`Applicative`'s `<*>` — the substrate lemma `Tree.tryFA_forward`. With
`aApp_eq_structuredApp_fa`, this composes into "FA = meta-combinator **A** at
forward application": the H&K engine and the effect calculus share one application
operation. -/

end TreeEngine

section BindingBridge

/-! #### Binding via the C meta-combinator

Worked derivation connecting C (eq. 5.8) to
existing binding infrastructure over the toy model.

The **W combinator** `W κ x = κ x x` is the shared link between three
independent binding mechanisms:

- **C** (co-unit meta-combinator): `C(<) ▷(x) body = W body x`
- **H&K** (assignment-based): `body (g[n↦x] n) (g[n↦x] n) = W body x`
- **[charlow-2018]'s Reader join**: `denotGJoin body = W body`
  (proven in `Charlow2018.lean:denotGJoin_is_W`)

The derivation follows §5.1: the subject
stores itself as an antecedent via `▷(x) = ⟨x, x⟩` (a W-computation),
the reflexive pronoun is the identity reader (an R-computation), and
C resolves the binding by feeding the stored referent to the reader. -/

/-- Antecedent storage: `▷(x) = ⟨x, x⟩`.

    eq. 5.1b: an entity stores its
    referent in the W (product) effect, making it available for
    downstream binding via the co-unit ε. -/
def store {α : Type} (x : α) : α × α := (x, x)

/-- C(<) with storage yields the W combinator.

    Backward-application variant of `counitApp_reflexive_is_W`:
    `C(<) ▷(x) body = body x x = W body x`. -/
theorem counitApp_ba_store_is_W {ι β : Type} (body : ι → ι → β) (x : ι) :
    counitApp ba' (store x) body = W body x := rfl

/-- Reflexive binding: "John sees himself" via C.

    The subject stores itself (`▷(john) = ⟨john, john⟩`), the reflexive
    pronoun resolves to the object via the identity reader, and C(<)
    merges them: `C(<) ▷(j) (λi. sees i) = sees j j = False`.

    The False result confirms the toy model has no reflexive seeing
    (John sees Mary and Mary sees John, but neither sees themselves). -/
theorem john_sees_himself_via_C :
    counitApp ba' (store ToyEntity.john)
      (λ i => ToyLexicon.sees_sem i) = False := rfl

/-- C-based binding agrees with H&K assignment-based binding:
    both compute `sees(g[1↦j](1), g[1↦j](1)) = sees(j, j)`.

    This connects adjunction mechanism
    to [heim-kratzer-1998]'s predicate abstraction. -/
theorem binding_C_agrees_with_hk (g : Core.Assignment ToyEntity) :
    counitApp ba' (store ToyEntity.john)
      (λ i => ToyLexicon.sees_sem i) =
    ToyLexicon.sees_sem (g[1 ↦ ToyEntity.john] 1)
                        (g[1 ↦ ToyEntity.john] 1) := by
  show ToyLexicon.sees_sem ToyEntity.john ToyEntity.john =
       ToyLexicon.sees_sem (g[1 ↦ ToyEntity.john] 1)
                           (g[1 ↦ ToyEntity.john] 1)
  simp only [Function.update_self]

/-- C and H&K agree for Mary as well: `C(<) ▷(m) (λi. sees i) = sees m m`. -/
theorem binding_C_agrees_with_hk_mary (g : Core.Assignment ToyEntity) :
    counitApp ba' (store ToyEntity.mary)
      (λ i => ToyLexicon.sees_sem i) =
    ToyLexicon.sees_sem (g[2 ↦ ToyEntity.mary] 2)
                        (g[2 ↦ ToyEntity.mary] 2) := by
  show ToyLexicon.sees_sem ToyEntity.mary ToyEntity.mary =
       ToyLexicon.sees_sem (g[2 ↦ ToyEntity.mary] 2)
                           (g[2 ↦ ToyEntity.mary] 2)
  simp only [Function.update_self]

end BindingBridge

-- ════════════════════════════════════════════════════════════════════
-- §7 General Scope Agreement: Cont ≡ GQ Application
-- ════════════════════════════════════════════════════════════════════

/-! ### §7 General scope agreement

The ScopeBridge section (§6) proved Cont ↔ QR agreement for the toy model
via `native_decide`. Here we prove the agreement is *structural*: it holds
for any type, any quantifier, and any predicate — not because we checked
all cases, but because the two approaches compute the same function.

The key insight: `Cont R E := (E → R) → R` is literally a generalized
quantifier. The identity function `gqAsCont` witnesses this — there is no
encoding, no coercion, no wrapper. So the Cont derivation *is* GQ
application by definition.

Scope ambiguity in the Cont framework is not a special mechanism: it is
the *order of monadic bind*. Surface scope = bind the subject first;
inverse scope = bind the object first. The bind order IS the scope order,
and `lower` IS GQ application.

This establishes Cont as a *general* scope framework, with QR trees as
one particular syntax for specifying bind order. -/

section GeneralScopeAgreement

/-! The generic scope-as-bind-order facts (`scope_ambiguity_is_bind_order`
et al.) now live with the `Cont` monad in `Composition/Continuation`; this
study consumes them. What remains here is the bridge to QR trees. -/

/-- **QR scope = Cont scope via lambdaAbsG**: the structural connection
    between QR trees and Cont derivations.

    In a QR tree `[Q [n body]]`, Predicate Abstraction produces
    `Q(λx. ⟦body⟧^{g[n↦x]})` = `Q(lambdaAbsG n body g)`.

    In a Cont derivation, `lower(bind(Q, λx. pure(body(g[n↦x]))))`
    = `Q(λx. body(g[n↦x]))` = `Q(lambdaAbsG n body g)`.

    Both compute the same thing: the quantifier applied to the
    predicate abstraction of its scope. QR and Cont differ only in
    how scope order is *specified* (tree structure vs bind order),
    not in what they *compute*. -/
theorem qr_cont_structural_agreement {E W : Type}
    (q : (E → Prop) → Prop)
    (body : DenotG E W .t) (n : Nat) (g : Core.Assignment E) :
    q (lambdaAbsG n body g) =
    Cont.lower (Cont.bind q (fun x => Cont.pure (body (g[n ↦ x])))) := rfl

end GeneralScopeAgreement

-- ════════════════════════════════════════════════════════════════════
-- §8 Three-Way Binding Unification
-- ════════════════════════════════════════════════════════════════════

/-! ### §8 Three-way binding unification

Three independently-developed binding mechanisms in linglib all compute
the same operation `f e e`:

| Source | Operation | Definition | File |
|--------|-----------|------------|------|
| [heim-kratzer-1998] | `denotGJoin` (μ) | `λg. f g g` | `Variables.lean` |
| [barker-shan-2014] | `W` (duplicator) | `W κ x = κ x x` | `Binding.lean` |
| | `adj_ε` (co-unit) | `ε(f e, e) = (f e) e` | `Effects.lean` §4 |

The individual two-way bridges exist:
- `denotGJoin_is_W` (`Charlow2018.lean`)
- `adj_counit_yields_W` (`Effects.lean` §4)

Here we close the triangle with a single three-way theorem. -/

section BindingUnification

/-- **Three-way W**: the duplicator, Reader join, and adjunction co-unit
    all compute `f e e`. This is the universal binding mechanism.

    The identity is *definitional*: the three frameworks are not merely
    extensionally equal but intensionally identical up to
    currying/pairing. -/
theorem w_three_way {E A : Type} (f : E → E → A) (e : E) :
    (fun g => f g g) e = W f e ∧ W f e = adj_ε (f e, e) := ⟨rfl, rfl⟩

/-- Specialization for Montague assignments: `denotGJoin` = `W` = `adj_ε`
    when applied to assignment-dependent meanings. -/
theorem binding_unification {E : Type} {A : Type}
    (f : Core.Assignment E → Core.Assignment E → A) (g : Core.Assignment E) :
    denotGJoin f g = W f g ∧ W f g = adj_ε (f g, g) := ⟨rfl, rfl⟩

/-- Closing the triangle directly: `denotGJoin` = `adj_ε ∘ ⟨f·, ·⟩`.

    ```
        denotGJoin ──── rfl ────→ W
              \                    |
               \                   |
           rfl  \              rfl |
                 ↘                 ↓
                   adj_ε ∘ ⟨f·, ·⟩
    ``` -/
theorem binding_triangle {E : Type} {A : Type}
    (f : Core.Assignment E → Core.Assignment E → A) (g : Core.Assignment E) :
    denotGJoin f g = adj_ε (f g, g) := rfl

end BindingUnification

-- ════════════════════════════════════════════════════════════════════
-- §9 Indeterminacy Effect (Set Monad)
-- ════════════════════════════════════════════════════════════════════

/-! ### §9 Indeterminacy effect

The **indeterminacy** effect — labeled `S` in's
Table 2 — is the set monad `(S, η, ⫝̸)` from [charlow-2020],
formalized in `Studies/Charlow2020.lean`.

| Effect | η (pure) | ⫝̸ (bind) | Linguistic use |
|---|---|---|---|
| Scope (C) | `λκ. κ x` | `λκ. m(λa. f a κ)` | Quantifier scope |
| CI (W) | `⟨x, []⟩` | `⟨(f m.val).val, m.log ++ ...⟩` | Supplements |
| Binding (R) | `λ_. x` | `λe. f(m e) e` | Assignment-sensitivity |
| **Indeterminacy (S)** | **`{x}`** | **`⋃_{a ∈ m} f(a)`** | **Indefinites, focus, *wh*** |

The set monad's applicative instance is *pointwise composition* — the
standard mechanism of alternative semantics ([hamblin-1973b],
[kratzer-shimoyama-2002]). Its monadic bind is *scope-taking* — the
mechanism [charlow-2020] argues is needed for exceptional scope.

The applicative is strictly weaker: it cannot derive selectivity (§5.4 of
the paper) or the Binder Roof Constraint (§6.4). The monad can. -/

section IndeterminacyBridge

attribute [local instance] Set.monad

/-- The set monad's `pure` is the indeterminacy effect's `pure` — the
    singleton `{x}`, which as a `Set α = α → Prop` is `fun y => y = x`. -/
theorem indeterminacy_pure_is_singleton {A : Type} (x : A) :
    (pure x : Set A) = fun y => y = x := by
  ext y; exact Iff.rfl

/-- The set monad's `>>=` is the indeterminacy effect's `bind` — for
    `m : Set A` (= `A → Prop`) and `f : A → Set B`, the result at `b`
    is `∃ a, m a ∧ f a b`. -/
theorem indeterminacy_bind_is_seq {A B : Type}
    (m : Set A) (f : A → Set B) :
    m >>= f = {b | ∃ a, m a ∧ f a b} := by
  ext b
  simp only [Set.bind_def, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  rfl

/-- **Indeterminacy obeys ASSOCIATIVITY** — the property [charlow-2020]
    leans on to derive exceptional scope. Mathlib's `bind_assoc` for
    `Set`. Distinguishes the full monad from the mere applicative;
    without it, indefinites cannot iteratively scope out of nested
    islands ([charlow-2020] eq. 34, Figure 7). -/
theorem indeterminacy_associativity {A B C : Type}
    (m : Set A) (f : A → Set B) (g : B → Set C) :
    (m >>= f) >>= g = m >>= (fun a => f a >>= g) :=
  bind_assoc m f g

end IndeterminacyBridge

-- ════════════════════════════════════════════════════════════════════
-- §10 Crossover: the scope×binding dissociation
-- ════════════════════════════════════════════════════════════════════

/-! ### §10 Crossover

[bumford-charlow-2024] §5.2 derive weak crossover from the **non-commutativity of
the W⊣R co-unit**: `counitApp` fires ε only with the antecedent (W) as the left
daughter, so scope (which may invert freely) and binding-availability **dissociate**
— the antecedent must linearly *precede* the pronoun, "even while semantic scope
may be arbitrarily inverted." This is phenomenon-neutral; weak crossover, the
Owusu/Chierchia functional-reading asymmetry (below), superiority ([shan-barker-2006]:
raised-*wh* trace = W, in-situ *wh* = R), and primary/secondary crossover are all
instances over the one derivation. -/

namespace Crossover

/-! #### The two outcomes of combining an antecedent (W) and a pronoun (R)

The pronoun is a Reader `pro : ι → ω`; the antecedent is a stored referent `a : ι`
(W). The co-unit discharges the Reader — feeding `a` into `pro`'s index — only with
the antecedent as the LEFT daughter. The result records which happened: a bound
reading loses the Reader; a crossover keeps it. -/

/-- Antecedent-left: the co-unit binds the pronoun's index to the antecedent
(`= counitApp`, the C combinator). The Reader is discharged. -/
def coUnitBinds {ι ω : Type} (star : ι → ω → ω) (a : ι) (pro : ι → ω) : ω :=
  counitApp star (store a) pro

/-- Pronoun-left: the antecedent is carried but the pronoun reads its own FREE index
— never the antecedent ("ships passing in the night"). The Reader **persists**
(result `ι → ω`). -/
def shipsPassing {ι ω : Type} (star : ι → ω → ω) (a : ι) (pro : ι → ω) : ι → ω :=
  fun i => star a (pro i)

theorem coUnitBinds_is_counitApp {ι ω : Type}
    (star : ι → ω → ω) (a : ι) (pro : ι → ω) :
    coUnitBinds star a pro = counitApp star (store a) pro := rfl

/-- `ε ⟨pro, a⟩ = pro a`: the antecedent binds the pronoun's index. -/
theorem coUnitBinds_eval {ι ω : Type} (star : ι → ω → ω) (a : ι) (pro : ι → ω) :
    coUnitBinds star a pro = star a (pro a) := rfl

theorem shipsPassing_at {ι ω : Type}
    (star : ι → ω → ω) (a : ι) (pro : ι → ω) (i : ι) :
    shipsPassing star a pro i = star a (pro i) := rfl

/-- The residual differs at two indices, so it is not a constant (bound) reading —
the Reader is not dischargeable (the "R constructor remains open" of §5.14). -/
theorem shipsPassing_reader_persists :
    ∃ (ι ω : Type) (star : ι → ω → ω) (a : ι) (pro : ι → ω) (i j : ι),
      shipsPassing star a pro i ≠ shipsPassing star a pro j :=
  ⟨Bool, Bool, fun _ b => b, true, id, false, true, by decide⟩

/-- **The dissociation**: even with the antecedent quantified wide (W outscoping R),
the pronoun reads its free index for *every* antecedent — binding never happens.
Binding-availability depends on the antecedent/pronoun order alone, not on scope. -/
theorem scope_inversion_no_binding {ι ω : Type} (pro : ι → ω) (i : ι) :
    ∀ a : ι, shipsPassing (fun _ b => b) a pro i = pro i :=
  fun _ => rfl

/-! #### The derivation from structure, over real linear positions -/

/-- A daughter in a binding configuration. -/
inductive Daughter (ι ω : Type)
  | antecedent (a : ι)        -- W
  | pronoun (pro : ι → ω)     -- R

/-- The reading the grammar derives: a bound value (Reader discharged) or a crossover
residual (Reader retained). -/
inductive Reading (ι ω : Type)
  | bound (v : ω)
  | crossover (residual : ι → ω)

def Reading.isBound {ι ω : Type} : Reading ι ω → Bool
  | .bound _ => true
  | .crossover _ => false

/-- Combine two ordered daughters STRUCTURALLY: W-left-R-right fires the co-unit
(`coUnitBinds`); R-left-W-right is crossover, the residual being `shipsPassing`.
(Same-role pairs are not binder+pronoun configs.) -/
def combine {ι ω : Type} (star : ι → ω → ω) :
    Daughter ι ω → Daughter ι ω → Option (Reading ι ω)
  | .antecedent a, .pronoun pro => some (.bound (coUnitBinds star a pro))
  | .pronoun pro, .antecedent a => some (.crossover (shipsPassing star a pro))
  | _, _ => none

/-- Order the W (at `wPos`) and R (at `rPos`) by real linear position, then combine. -/
def derive {ι ω : Type} (star : ι → ω → ω) (a : ι) (pro : ι → ω)
    (wPos rPos : Nat) : Option (Reading ι ω) :=
  if wPos < rPos then combine star (.antecedent a) (.pronoun pro)
                 else combine star (.pronoun pro) (.antecedent a)

/-- **The crossover bridge**: the bound reading derives iff the antecedent linearly
precedes the pronoun. The `<` is on real positions, `combine` is structural, and the
equivalence is proven — mutating `combine`'s W-left arm breaks it. -/
theorem derive_bound_iff_precedes {ι ω : Type} (star : ι → ω → ω) (a : ι)
    (pro : ι → ω) (wPos rPos : Nat) :
    (∃ v, derive star a pro wPos rPos = some (.bound v)) ↔ wPos < rPos := by
  unfold derive; split <;> simp [combine] <;> omega

/-- When the antecedent precedes, the derived reading is the co-unit binding. -/
theorem derive_precedes_eq_bound {ι ω : Type} (star : ι → ω → ω) (a : ι)
    (pro : ι → ω) (wPos rPos : Nat) (h : wPos < rPos) :
    derive star a pro wPos rPos = some (.bound (coUnitBinds star a pro)) := by
  simp [derive, h, combine]

/-- When the pronoun precedes (crossover), the derived reading retains the Reader,
its residual exactly `shipsPassing`. -/
theorem derive_crossover_residual {ι ω : Type} (star : ι → ω → ω) (a : ι)
    (pro : ι → ω) (wPos rPos : Nat) (h : ¬ wPos < rPos) :
    derive star a pro wPos rPos = some (.crossover (shipsPassing star a pro)) := by
  simp [derive, h, combine]

/-! #### Instance: the Owusu/Chierchia functional-reading asymmetry

[owusu-2022] §3.3.2 (after [chierchia-2001]): the Akan indefinite *bí*'s skolem
index is a pronoun (R), bound by *biara* 'every' (the antecedent, W). Akan SVO fixes
the linear order, and the subject/object asymmetry computes via the bridge. -/

inductive Arg | subject | object
  deriving DecidableEq, Repr

/-- Akan SVO linear order: the subject precedes the object. -/
def svoPos : Arg → Nat
  | .subject => 0
  | .object => 1

/-- *bí*-OBJECT: *biara* (W) is the subject (0), *bí* (R) the object (1); `0 < 1`, so
the functional reading derives — the co-unit binding. The attested ambiguity. -/
theorem bi_object_functional {ι ω : Type}
    (star : ι → ω → ω) (a : ι) (pro : ι → ω) :
    derive star a pro (svoPos .subject) (svoPos .object) =
      some (.bound (coUnitBinds star a pro)) :=
  derive_precedes_eq_bound _ _ _ _ _ (by decide)

/-- *bí*-SUBJECT: *biara* (W) is the object (1), *bí* (R) the subject (0); `¬(1 < 0)`,
so the functional reading does NOT derive — weak crossover. -/
theorem bi_subject_crossover {ι ω : Type}
    (star : ι → ω → ω) (a : ι) (pro : ι → ω) :
    ¬ ∃ v, derive star a pro (svoPos .object) (svoPos .subject) =
      some (.bound v) := by
  rw [derive_bound_iff_precedes]; decide

end Crossover

end BumfordCharlow2024
