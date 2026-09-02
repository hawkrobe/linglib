import Linglib.Semantics.Composition.Cont
import Linglib.Semantics.Composition.Writer
import Mathlib.Data.Set.Functor
import Linglib.Semantics.Composition.Tree
import Linglib.Studies.HeimKratzer1998
import Linglib.Pragmatics.Expressives.Basic
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Reference.Binding
import Linglib.Semantics.Composition.Ty
import Linglib.Semantics.Composition.Assignment
import Linglib.Fragments.English.Toy
import Linglib.Semantics.Composition.LexEntry

/-!
# Bumford and Charlow 2024: effect-driven interpretation

Scope, binding, supplementary content and indeterminacy are treated here as computational effects,
and the modes of combination as operations lifting ordinary application into their presence. This
file formalizes that framework over the project's carriers: a scope-taker is a continuation, a
supplement is a writer with a log of side propositions, a pronoun is a function from an antecedent,
an antecedent is a value paired with itself, and an indeterminate expression is a set. Each effect
enters the grammar through the class it satisfies — functor, applicative, monad — and the modes of
combination are the liftings of an arbitrary binary combinator through those classes, each
subsuming the one below it.

Binding is not a rule of its own but the co-unit of an adjunction: storing an antecedent is left
adjoint to reading one, and the co-unit cancels the two against each other. Three binding
mechanisms formalized independently elsewhere in the project — assignment-based predicate
abstraction, the duplicator combinator, and this co-unit — turn out to compute one operation.

The adjunction is not symmetric, and crossover follows: the co-unit fires only with the antecedent
as the left daughter, so an antecedent must precede the pronoun it binds even where semantic scope
inverts freely. The bound reading is derived exactly when the antecedent's position precedes the
pronoun's, with the Akan subject/object asymmetry as one instance.

## Main definitions

* `mapL`, `mapR`, `structuredApp`, `joinMode`, `counitApp` — the modes of combination lifting a
  binary combinator into a functor, an applicative, a monad and an adjunction
* `Φ`, `Ψ`, `adj_η`, `adj_ε` — the storing/reading adjunction with its unit and co-unit
* `derive` — the reading a binding configuration receives, given its daughters' positions

## Main results

* `mapR_fa_eq_fmap`, `aApp_eq_structuredApp_fa`, `mApp_eq_aApp` — each mode subsumes the last
* `adj_counit_yields_W`, `binding_unification` — co-unit, duplicator and assignment-based binding
  are one operation
* `cont_blocks_qr` — under the scope effect movement and abstraction derive nothing, so scope comes
  from the order of binds alone
* `ci_projection_universal` — projection of supplementary content is the functor law
* `derive_bound_iff_precedes` — the pronoun is bound exactly when its antecedent precedes it

## References

* [bumford-charlow-2024]
* [barker-shan-2014]
* [charlow-2020]
* [heim-kratzer-1998]
* [owusu-2022]
* [potts-2005]
-/
namespace BumfordCharlow2024

open Semantics.Composition
open scoped Assignment
open Semantics.Composition.Tree
open Pragmatics.Expressives
open Quantification
open Reference.Binding
open Semantics.Composition
open Semantics.Montague
open Semantics.Montague.ToyLexicon (student_sem person_sem)

/-! ### The carriers

The supplement effect is `Writer (List P)` and the scope effect is `Cont R`, both mathlib monads;
their linguistic surface (`val`, `log`, `tell`, `ContT.eval`) is in `Composition/`. -/

/-! ### Modes of combination

A mode of combination takes a binary combinator `(∗) : σ → τ → ω` and produces one that works when
a daughter carries an effect: mapping over the left daughter or the right one needs a functor,
combining two effectful daughters an applicative, and flattening the effect a computation itself
returns a monad. The adjunction mode is defined further below. -/

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

/-! ### The hierarchy of applications

At forward application the modes give the familiar sequence: ordinary application on effect-free
meanings, a map when only the argument is effectful, an applicative application when both are, and
a bind when the effects are sequenced. Each subsumes the previous one. -/

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

    Every monad determines an applicative this way (eq. 4.19a):
    `F ⊛ X = F ≫= λf. X ≫= λx. η (f x)`. -/
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

/-! ### Storing and reading

Binding arises from an adjunction between storing a referent (a product) and reading one (a
function from the referent): functions out of a pair are isomorphic to curried functions, which is
currying. The co-unit of that adjunction takes a pair of a reader and a stored referent and applies
the one to the other, and that is the binding mechanism — when an antecedent stores itself, the
co-unit yields the duplicator `W κ x = κ x x`.

The storing effect here is a product, carrying one referent; it is not the writer above, which
accumulates a log. -/

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
    `ε(κ x, x) = κ x x = W κ x`. -/
theorem adj_counit_yields_W (κ : ι → ι → β) (x : ι) :
    adj_ε (κ x, x) = W κ x := rfl

/-- Assignment-based binding and the adjunction's co-unit agree for a reflexive: both produce
    `body(binder, binder)`. -/
theorem adj_binding_agrees_with_hk {E : Type} (n : Nat)
    (body : E → E → Prop)
    (binder : E) (g : Assignment E) :
    adj_ε (body binder, binder) = body (g[n ↦ binder] n) (g[n ↦ binder] n) := by
  show body binder binder = body (g[n ↦ binder] n) (g[n ↦ binder] n)
  simp only [Function.update_self]

end WRAdjunction

section CounitCombinator

/-! ### The co-unit mode of combination -/

variable {ι σ τ ω : Type}

/-- **C** (Co-unit): the adjunction-based meta-combinator for binding.

    eq. 5.8, Figure 10:
    `C(∗) E₁ E₂ := ε((λl. (λr. l ∗ r) • E₂) • E₁)`

    For the storing/reading adjunction, where the stored effect is `α × ι` (product)
    and R α = ι → α (reader), the two fmap operations compose the
    binary combinator with both computations, and ε extracts the result:
    `C(∗) ⟨s, i⟩ f = s ∗ f(i)`

    **Crossover**: the type signature encodes the crossover
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
    `C(>) ⟨κ x, x⟩ id = κ x x = W κ x`. -/
theorem counitApp_reflexive_is_W (κ : ι → ι → ω) (x : ι) :
    counitApp fa' (κ x, x) id = W κ x := rfl

end CounitCombinator

/-! ### Predicate abstraction under effects -/

section PredAbsInstances

/-! `Tree.PredAbs` records which effects admit predicate abstraction. The negative instances say
in the type system that abstraction-based binding is unavailable under these effects, so scope and
binding must come from the order of binds or from the adjunction's co-unit instead. -/

/-- Scope effects do not support Predicate Abstraction: a distributor
`(Entity → Cont R α) → Cont R (Entity → α)` would have to run one
continuation at every entity simultaneously. Binding under scope arises
from the order of binds instead. -/
instance {R E W D : Type} : Tree.PredAbs (Cont R) E W D := ⟨none⟩

/-- CI effects do not support Predicate Abstraction: the log of
`⟦β⟧^{g[n↦x]}` may vary with `x`, so no log-respecting distributor
exists. CI content composes around abstraction, not through it. -/
instance {ω E W D : Type} : Tree.PredAbs (Writer ω) E W D := ⟨none⟩

end PredAbsInstances

/-! ### Supplementary content -/

section CIBridge

variable {W : Type}

/-- A `TwoDimProp` embeds into a `Writer (List (W → Prop)) (W → Prop)`:
    the at-issue content is the value, the CI is the log.

    This is [potts-2005]'s two-dimensional semantics as the writer effect (the book's `W`
    constructor). -/
def twoDimToWriter (p : TwoDimProp W) : Writer (List (W → Prop)) (W → Prop) :=
  Writer.mk p.atIssue ([p.ci])

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

/-- Run a CI Writer by conjoining all log entries with the value.

    This is the Writer counterpart of shunting (↓ from
    [kirk-giannini-2024]): peripheral content is folded into
    the at-issue dimension via conjunction, and the CI dimension
    becomes trivial. The result is a `TwoDimProp` with all information
    in the at-issue dimension.

    For a single-CI Writer (the standard case from `twoDimToWriter`),
    this computes `atIssue w && ci w` — identical to the `shunt`
    function `KirkGiannini2024.shunt`.

    For multi-CI Writers (e.g., "that bastard John met that jerk Pete"
    with two CI entries), this conjoins all CIs into at-issue content. -/
def runCIWriter {W : Type} (m : Writer (List (W → Prop)) (W → Prop)) : TwoDimProp W :=
  { atIssue := λ w => m.log.foldl (λ acc ci => acc ∧ ci w) (m.val w)
  , ci := λ _ => True }

/-- **Single-CI round-trip.** Embedding a `TwoDimProp` into Writer then
    running conjoins the at-issue and CI dimensions — exactly the
    shunting operation ↓ from [kirk-giannini-2024].

    This is definitionally equal to `shunt` from
    `KirkGiannini2024.shunt`. -/
theorem runCIWriter_twoDim {W : Type} (p : TwoDimProp W) (w : W) :
    (runCIWriter (twoDimToWriter p)).atIssue w ↔ (p.atIssue w ∧ p.ci w) := Iff.rfl

end CIBridge

section ScopeBridge

/-- A generalized quantifier read as a scope-taking computation. The function is returned
unchanged: `(E → Prop) → Prop` is `Cont Prop E`, and the definition only tells the elaborator to
see it that way. -/
def gqAsCont {E : Type} (gq : (E → Prop) → Prop) : Cont Prop E := gq

/-- Lowering a quantifier applied to a scope is quantifier application. -/
theorem eval_bind_pure {E : Type} (q : Cont Prop E) (scope' : E → Prop) :
    ContT.eval (q >>= λ x => pure (scope' x)) = q scope' := rfl

/-- Surface scope reading holds in the toy model. -/
theorem surface_scope_via_cont :
    ContT.eval (gqAsCont (every_sem person_sem) >>= λ x =>
      gqAsCont (some_sem person_sem) >>= λ y =>
        pure (ToyLexicon.sees_sem y x)) := by
  intro x hpx
  cases x with
  | john => exact ⟨.mary, trivial, trivial⟩
  | mary => exact ⟨.john, trivial, trivial⟩
  | _ => exact absurd hpx id

/-- Inverse scope reading does not hold in the toy model. -/
theorem inverse_scope_via_cont :
    ¬ ContT.eval (gqAsCont (some_sem person_sem) >>= λ y =>
      gqAsCont (every_sem person_sem) >>= λ x =>
        pure (ToyLexicon.sees_sem y x)) := by
  intro ⟨y, _, hy⟩
  cases y with
  | john => exact absurd (hy .john trivial) id
  | mary => exact absurd (hy .mary trivial) id
  | _ => exact absurd (by assumption : person_sem _) id

/-- The two scope orderings via Cont yield genuinely different readings,
    matching `HeimKratzer1998.scope_readings_differ`. -/
theorem cont_scope_readings_differ :
    ContT.eval (gqAsCont (every_sem person_sem) >>= λ x =>
      gqAsCont (some_sem person_sem) >>= λ y =>
        pure (ToyLexicon.sees_sem y x)) ≠
    ContT.eval (gqAsCont (some_sem person_sem) >>= λ y =>
      gqAsCont (every_sem person_sem) >>= λ x =>
        pure (ToyLexicon.sees_sem y x)) := by
  intro h
  have hS := surface_scope_via_cont
  have hI := inverse_scope_via_cont
  rw [h] at hS
  exact hI hS

end ScopeBridge

section TreeEngine

/-! ### The tree engine under effects

`Tree.interp` is polymorphic over the effect functor: the same type-driven
engine that implements H&K at `M = Id` lifts through any `[Applicative M]`.
At the FA mode that lifting is literally the meta-combinator **A** — a
framework-level identity, no toy lexicon required. -/

open HeimKratzer1998 in
/-- **The scope effect forecloses QR**: at `M = Cont Prop` the engine has
no entity-distributor (`PredAbs (Cont R) := ⟨none⟩`), so the
inverse-scope QR derivation that `interp` computes at `M = Id`
(`HeimKratzer1998.interp_computes_inverse`) fails outright. The reading
reordering the binds derives is unreachable by movement and abstraction
under the scope effect: Cont and QR are not notational variants. -/
theorem cont_blocks_qr :
    interp ToyEntity Unit (M := Cont Prop)
      (Lexicon.lift (Cont Prop) quantLex) g₀ tree_inverse = none := rfl

open HeimKratzer1998 in
/-- Surface-scope QR fails equally: any PA (`.bind`) node is stuck under
`Cont`. Scope under the effect comes only from the order of binds, never from movement. -/
theorem cont_blocks_qr_surface :
    interp ToyEntity Unit (M := Cont Prop)
      (Lexicon.lift (Cont Prop) quantLex) g₀ tree_surface = none := rfl

/-! The engine's FA mode applies the function daughter to the argument through
`Applicative`'s `<*>` — the substrate lemma `Tree.tryFA_forward`. With
`aApp_eq_structuredApp_fa`, this composes into "FA = meta-combinator **A** at
forward application": the H&K engine and the effect calculus share one application
operation. -/

end TreeEngine

section BindingBridge

/-! ### Binding by the co-unit

The duplicator `W κ x = κ x x` is the shared link between three independent binding mechanisms:

- **C** (co-unit meta-combinator): `C(<) ▷(x) body = W body x`
- **H&K** (assignment-based): `body (g[n↦x] n) (g[n↦x] n) = W body x`
- **the reader join**: `denotGJoin body = W body`

In the derivation below the subject stores itself as an antecedent, `▷(x) = ⟨x, x⟩`; the reflexive
pronoun is the identity reader; and the co-unit resolves the binding by feeding the stored referent
to the reader. -/

/-- Antecedent storage `▷(x) = ⟨x, x⟩` (eq. 5.1b): an entity stores its own referent, making it
    available to the co-unit downstream. -/
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
    both compute `sees(g[1↦j](1), g[1↦j](1)) = sees(j, j)`. -/
theorem binding_C_agrees_with_hk (g : Assignment ToyEntity) :
    counitApp ba' (store ToyEntity.john)
      (λ i => ToyLexicon.sees_sem i) =
    ToyLexicon.sees_sem (g[1 ↦ ToyEntity.john] 1)
                        (g[1 ↦ ToyEntity.john] 1) := by
  show ToyLexicon.sees_sem ToyEntity.john ToyEntity.john =
       ToyLexicon.sees_sem (g[1 ↦ ToyEntity.john] 1)
                           (g[1 ↦ ToyEntity.john] 1)
  simp only [Function.update_self]

end BindingBridge

/-! ### Scope as bind order

A continuation `(E → R) → R` is a generalized quantifier, with no encoding in between, so a
continuation derivation is quantifier application and scope ambiguity is the order in which the
binds are sequenced rather than a mechanism of its own. Movement and abstraction are one syntax for
specifying that order. -/

section GeneralScopeAgreement

/-! The generic scope-as-bind-order facts are the `ContT.eval_*` simp
set in `Composition/Cont.lean`; the theorems above are definitional instances of them. What
remains here is the bridge to movement-and-abstraction trees. -/

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
    (q : Cont Prop E)
    (body : DenotG E W .t) (n : Nat) (g : Assignment E) :
    q (lambdaAbsG n body g) =
    ContT.eval (q >>= λ x => pure (body (g[n ↦ x]))) := rfl

end GeneralScopeAgreement

/-! ### One binding operation

Assignment-based binding, the duplicator combinator and the adjunction's co-unit all compute `f e e`
— the two-way bridges between them exist elsewhere in the project, and the theorems here close the
triangle. -/

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
    (f : Assignment E → Assignment E → A) (g : Assignment E) :
    denotGJoin f g = W f g ∧ W f g = adj_ε (f g, g) := ⟨rfl, rfl⟩

end BindingUnification

/-! ### Indeterminacy

Indeterminate expressions denote sets. The applicative instance is the pointwise composition of
alternative semantics; the monadic bind is scope-taking, and it is the bind that [charlow-2020]
argues is needed for exceptional scope, since the applicative alone cannot deliver it. -/

section IndeterminacyBridge

attribute [local instance] Set.monad

/-- The set monad's `>>=` is the indeterminacy effect's `bind` — for
    `m : Set A` (= `A → Prop`) and `f : A → Set B`, the result at `b`
    is `∃ a, m a ∧ f a b`. -/
theorem indeterminacy_bind_is_seq {A B : Type}
    (m : Set A) (f : A → Set B) :
    m >>= f = {b | ∃ a, m a ∧ f a b} := by
  ext b
  simp only [Set.bind_def, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  rfl

end IndeterminacyBridge

/-! ### Crossover

Crossover is inherited from the asymmetry of the adjunction. The co-unit fires only with the
antecedent as the left daughter, so scope and the availability of binding come apart: the
antecedent must precede the pronoun, however the scopes invert. The derivation is
phenomenon-neutral — weak crossover, the functional-reading asymmetry below, and superiority are
instances of it. [barker-shan-2014] derive crossover from an ordering constraint too, but by
keeping two continuation layers that never merge rather than by letting the two effects cancel. -/

namespace Crossover

/-! ### Binding and its failure

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

/-- `ε ⟨pro, a⟩ = pro a`: the antecedent binds the pronoun's index. -/
theorem coUnitBinds_eval {ι ω : Type} (star : ι → ω → ω) (a : ι) (pro : ι → ω) :
    coUnitBinds star a pro = star a (pro a) := rfl

/-- The residual differs at two indices, so it is not a constant (bound) reading —
the Reader is not dischargeable: the pronoun's request for an antecedent remains open. -/
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

/-! ### The derivation over linear positions -/

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

/-! ### The Akan functional-reading asymmetry

The skolem index of the Akan indefinite *bí* is a pronoun, bound by *biara* 'every' as its
antecedent ([owusu-2022], after [chierchia-2001]). Akan is verb-medial, so the two arguments' order
is fixed and the subject/object asymmetry follows from the derivation above. -/

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
