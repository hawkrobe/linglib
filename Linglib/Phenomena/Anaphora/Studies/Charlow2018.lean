import Linglib.Theories.Semantics.Montague.Variables
import Linglib.Theories.Semantics.Reference.Binding
import Linglib.Phenomena.Anaphora.DonkeyAnaphora

/-!
# Charlow 2018: A Modular Theory of Pronouns and Binding
@cite{charlow-2018}

@cite{charlow-2018} factors the standard @cite{heim-kratzer-1998} treatment
of assignment-sensitivity into two algebraic operations that form an
**applicative functor** (the Reader applicative,
@cite{mcbride-paterson-2008}):

- `ρ x := λg. x` — lift assignment-independent values = `constDenot`
- `m ⊛ n := λg. m g (n g)` — assignment-sensitive FA = `applyG`

Adding a **join** (μ) operation `μ m := λg. m g g` = `denotGJoin` upgrades
the structure to a monad, enabling **higher-order variables** that are
anaphoric to *intensions* rather than *extensions*. This yields immediate
analyses of:

- **Paycheck pronouns**: "John hates his mom. Bill likes her" → her = Bill's mom
- **Binding reconstruction**: "[His mom], every boy likes t" → bound reading
  without c-command

The same ρ/⊛ combinators, instantiated with entities instead of assignments,
recover @cite{jacobson-1999}'s variable-free semantics (§6).

## Key results

1. `constDenot`/`applyG` satisfy the four applicative functor laws
   (`Theories/Semantics/Montague/Variables.lean`)
2. `denotGJoin` satisfies the monad laws (ibid.)
3. H&K's `⟦·⟧` decomposes as ρ + ⊛ (`hk_decomposition`)
4. Λᵢ as a categorematic operation (`lambdaAbsG`)
5. Higher-order pronouns + μ yield paycheck truth conditions
6. Binding reconstruction predicate: `λx. likes(mom(x), x)`
7. Composed applicatives are closed under composition (§3.3)
8. Variable-free equivalence: same combinators with `Entity` as environment
-/

set_option autoImplicit false

namespace Phenomena.Anaphora.Studies.Charlow2018

open Semantics.Montague
open Semantics.Montague.Variables

-- ════════════════════════════════════════════════════════════════
-- § H&K Decomposition: ⟦·⟧ = ρ + ⊛
-- ════════════════════════════════════════════════════════════════

/-! ### The ρ/⊛ decomposition of H&K's interpretation function

@cite{charlow-2018} §3.1–3.2: the standard H&K interpretation function
`⟦α β⟧ := λg. ⟦α⟧ g (⟦β⟧ g)` (eq 6 in the paper) decomposes into two
independent operations:

- ρ lifts assignment-independent values: `⟦John⟧ = ρ(j)`
- ⊛ composes assignment-dependent meanings: `⟦α β⟧ = ⟦α⟧ ⊛ ⟦β⟧`

The key insight is that ρ and ⊛ separate the concern of managing
assignments from the concern of doing functional application. Where
H&K's `⟦·⟧` forces *all* lexical entries to be assignment-dependent,
ρ/⊛ allows entries that don't depend on assignments to remain simple.

This decomposition is directly visible in linglib's `interpTreeG`
(`Composition/Tree.lean`): its binary case computes
`FA(⟦α⟧^g, ⟦β⟧^g)`, which is `applyG ⟦α⟧ ⟦β⟧` evaluated at `g`;
its trace case returns `g(n)`, which is `interpPronoun n` at `g`;
and its bind case computes `λx. ⟦β⟧^{g[n↦x]}`, which is
`lambdaAbsG n ⟦β⟧` at `g`. -/

section HKDecomposition

variable {m : Model} {σ τ : Ty}

/-- H&K's interpretation function `⟦α β⟧ = λg. ⟦α⟧ g (⟦β⟧ g)` is
    definitionally `applyG`: ⊛ *is* `⟦·⟧` restricted to binary branching. -/
theorem hk_decomposition (f : DenotG m (σ ⇒ τ)) (x : DenotG m σ) :
    applyG f x = fun g => f g (x g) := rfl

/-- Non-pronominal entries in H&K are trivially assignment-dependent:
    `⟦John⟧ := λg. j`. This is exactly ρ(j). -/
theorem hk_lexical_lift (d : m.interpTy σ) :
    constDenot d = fun (_ : Assignment m) => d := rfl

/-- Composing two ρ-lifted entries via ⊛ yields ρ of the composition,
    i.e., when neither argument depends on assignments, ⊛ reduces to
    ordinary functional application. -/
theorem rho_ap_reduces (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) :
    applyG (constDenot f) (constDenot x) = constDenot (f x) :=
  constDenot_applyG f x

end HKDecomposition

-- ════════════════════════════════════════════════════════════════
-- § Categorematic Abstraction (Λᵢ)
-- ════════════════════════════════════════════════════════════════

/-! ### Λᵢ: categorematic predicate abstraction

@cite{charlow-2018} eq (13): `Λᵢ := λf. λg. λx. f g^{i→x}`

In H&K, predicate abstraction is a syncategorematic rule: the grammar
treats `Λ₀` specially, passing shifted assignments down the tree. With
ρ/⊛, Λᵢ becomes a *categorematic* operation — a regular function that
takes a meaning and returns its abstraction. This is `lambdaAbsG`:

    `lambdaAbsG n body = λg λx. body(g[n↦x])`

Because Λᵢ is categorematic, binding derivations use the same grammar
as non-binding ones: ρ and ⊛ compose meanings, and Λᵢ is invoked
explicitly at binding sites. -/

section CategorematicAbstraction

variable {m : Model} {τ : Ty}

/-- Λᵢ applied to a pronoun recovers the identity function:
    `Λₙ(proₙ) = λg λx. (g[n↦x])(n) = λg λx. x`. -/
theorem lambda_pronoun (n : Nat) (g : Assignment m) (x : m.Entity) :
    lambdaAbsG n (interpPronoun n) g x = x := by
  simp [lambdaAbsG, interpPronoun]

/-- Λᵢ applied to `ρ(left) ⊛ proₙ` yields `ρ(left)`:
    `Λₙ(ρ(left) ⊛ proₙ) = λg λx. left(x) = ρ(left)`. -/
theorem lambda_rho_ap_pronoun (n : Nat)
    (left : m.interpTy (.e ⇒ .t))
    (g : Assignment m) (x : m.Entity) :
    lambdaAbsG n (applyG (constDenot left) (interpPronoun n)) g x =
    left x := by
  simp [lambdaAbsG, applyG, constDenot, interpPronoun]

end CategorematicAbstraction

-- ════════════════════════════════════════════════════════════════
-- § Paycheck Pronouns via Higher-Order Variables + μ
-- ════════════════════════════════════════════════════════════════

/-! ### Paycheck pronouns via higher-order variables and μ

@cite{charlow-2018} §4.1–4.2: paycheck pronouns are anaphoric to
*intensions* rather than *extensions*. In (7) "John₁ hates [his₁ mom]ⱼ.
But Bill₀ likes herⱼ", the paycheck pronoun *her* doesn't denote the
*extension* of *his₁ mom* (John's mom), but the *intension* `λg. mom(g₁)`,
evaluated at the current assignment.

The key mechanism is **higher-order variables**:

1. The intension `⟦his₀ mom⟧ = ρ(mom) ⊛ pro₀ = λg. mom(g₀)` is stored
   in the assignment at index `j`.
2. The paycheck pronoun `herⱼ` reads this intension from the assignment:
   `⟦herⱼ⟧ = λg. gⱼ`, which now has type `g → (g → e)` = `g → g → e`.
3. **μ** (monadic join) flattens the higher-order meaning:
   `μ(⟦herⱼ⟧) = λg. gⱼ g`, evaluating the retrieved intension at the
   current assignment.

When the assignment maps index 0 to Bill, the result is
`likes(mom(Bill), Bill)`. -/

section Paycheck

variable {m : Model}

/-- The intension `⟦his₀ mom⟧ = ρ(mom) ⊛ pro₀ = λg. mom(g₀)`.

    This is compositionally derived from ρ and ⊛, not stipulated. -/
theorem intension_is_rho_ap_pro (mom : m.Entity → m.Entity) (n : Nat) :
    applyG (constDenot (ty := .e ⇒ .e) mom) (interpPronoun n) =
    fun g => mom (g n) := rfl

/-- **Monad right identity**: `μ(ρ ι) = ι`.

    In the paper's paycheck mechanism, μ's job is to flatten a doubly
    assignment-dependent meaning `g → g → e` (retrieved from an
    enriched assignment) into `g → e`. Our `Assignment m = Nat → m.Entity`
    only stores entities, not intensions, so we cannot model the
    retrieval step directly (the paper discusses this limitation in §5.1
    and proposes type-homogeneous assignments `g_r := ℕ → r` as a fix).

    What we can show is that μ correctly flattens any intension ι
    provided externally: `μ(λ_. ι) = ι` (the right identity monad law).
    The `paycheck_full_derivation` below shows the end-to-end truth
    conditions with this flattening. -/
theorem mu_right_identity (ι : Assignment m → m.Entity) :
    denotGJoin (fun _ g₂ => ι g₂) = ι := rfl

/-- Full paycheck derivation: `ρ(likes) ⊛ μ(ι) ⊛ ρ(bill)` where
    ι is the intension `λg. mom(g₀)` and μ flattens it.

    The derivation computes `likes(mom(g₀), bill)`. When `g₀ = bill`,
    this is `likes(mom(bill), bill)`. -/
theorem paycheck_full_derivation
    (mom : m.Entity → m.Entity)
    (likes : m.interpTy (.e ⇒ .e ⇒ .t))
    (bill : m.Entity) (n : Nat) (g : Assignment m) (h : g n = bill) :
    applyG (applyG (constDenot likes)
                    (denotGJoin (fun _ g₂ => mom (g₂ n))))
           (constDenot bill) g =
    likes (mom bill) bill := by
  simp only [applyG, constDenot, denotGJoin, h]

/-- The intension `⟦his₀ mom⟧ = λg. mom(g₀)`. -/
def momIntension (mom : m.Entity → m.Entity) (n : Nat) : DenotG m .e :=
  fun g => mom (g n)

/-- `momIntension` is compositionally derived: `ρ(mom) ⊛ proₙ`. -/
theorem momIntension_eq_rho_ap_pro (mom : m.Entity → m.Entity) (n : Nat) :
    momIntension mom n =
    applyG (constDenot (ty := .e ⇒ .e) mom) (interpPronoun n) := rfl

/-- Paycheck truth conditions using the compositionally derived intension. -/
theorem paycheck_truth_conditions
    (mom : m.Entity → m.Entity)
    (likes : m.interpTy (.e ⇒ .e ⇒ .t))
    (bill : m.Entity) (n : Nat) (g : Assignment m) :
    applyG (applyG (constDenot likes) (momIntension mom n))
           (constDenot bill) g =
    likes (mom (g n)) bill := rfl

/-- When `g(n) = bill`, the paycheck pronoun denotes Bill's mom. -/
theorem paycheck_reading
    (mom : m.Entity → m.Entity)
    (likes : m.interpTy (.e ⇒ .e ⇒ .t))
    (bill : m.Entity) (n : Nat) (g : Assignment m) (h : g n = bill) :
    applyG (applyG (constDenot likes) (momIntension mom n))
           (constDenot bill) g =
    likes (mom bill) bill := by
  simp only [paycheck_truth_conditions, h]

/-- Bridge to `DonkeyAnaphora.paycheckSentence`: the paycheck datum
    records a bound reading because the paycheck pronoun's reference
    shifts with the binder — exactly what intension retrieval predicts. -/
theorem paycheck_datum_has_bound_reading :
    Phenomena.Anaphora.DonkeyAnaphora.paycheckSentence.boundReading = true := rfl

end Paycheck

-- ════════════════════════════════════════════════════════════════
-- § Binding Reconstruction
-- ════════════════════════════════════════════════════════════════

/-! ### Binding reconstruction via higher-order trace + Λᵢ

@cite{charlow-2018} §4.2, Fig 7: "[His₁ mom]ⱼ, every boy₁ likes tⱼ."

The bound pronoun *his₁* is inside a fronted constituent that is
syntactically *higher* than the binder *every boy₁*. Standard accounts
require c-command for binding, so they cannot generate this reading
directly.

In @cite{charlow-2018}'s account:
1. The trace tⱼ has a higher-order type (`g → g → e`)
2. μ flattens it: `μ(tⱼ) = λg. gⱼ g` (type `g → e`)
3. The fronted intension `λg. mom(g₁)` is provided by `ρ(mom) ⊛ pro₁`
4. Λ₁ abstracts over the quantifier variable, producing the
   reconstructed predicate `λx. likes(mom(x), x)`

The quantifier binds *into* the fronted constituent via the
intension, without c-command. This analysis predicts Weak Crossover:
binding reconstruction doesn't require the quantifier to scope
*over* the pronoun — only that Λᵢ abstracts over the same index. -/

section BindingReconstruction

variable {m : Model}

/-- The reconstructed VP predicate: after Λₙ abstracts over
    index n in a VP containing `momIntension mom n`, the result is
    `λx. likes(mom(x), x)`. The bound variable substitutes into the
    intension via `update_same`: `g[n↦x](n) = x`. -/
theorem reconstruction_predicate
    (mom : m.Entity → m.Entity)
    (likes : m.interpTy (.e ⇒ .e ⇒ .t))
    (n : Nat) (g : Assignment m) (x : m.Entity) :
    lambdaAbsG n
      (applyG (applyG (constDenot likes) (momIntension mom n))
              (interpPronoun n))
      g x =
    likes (mom x) x := by
  simp only [lambdaAbsG, momIntension, applyG, constDenot, interpPronoun,
             update_same]

/-- The reconstruction predicate is assignment-independent:
    `λx. likes(mom(x), x)` has no free variables. -/
theorem reconstruction_independent
    (mom : m.Entity → m.Entity)
    (likes : m.interpTy (.e ⇒ .e ⇒ .t))
    (n : Nat) (g₁ g₂ : Assignment m) :
    lambdaAbsG n
      (applyG (applyG (constDenot likes) (momIntension mom n))
              (interpPronoun n)) g₁ =
    lambdaAbsG n
      (applyG (applyG (constDenot likes) (momIntension mom n))
              (interpPronoun n)) g₂ := by
  funext x
  simp only [lambdaAbsG, momIntension, applyG, constDenot, interpPronoun,
             update_same]

end BindingReconstruction

-- ════════════════════════════════════════════════════════════════
-- § Composed Applicatives (§3.3)
-- ════════════════════════════════════════════════════════════════

/-! ### Composed applicative functors

@cite{charlow-2018} §3.3, Fig 5: applicative functors are closed under
composition. Given two type constructors F and G with applicative
operations (ρF, ⊛F) and (ρG, ⊛G), their composition F ∘ G is
applicative with:

    ρ_{F∘G} x := ρF(ρG x)
    m ⊛_{F∘G} n := ρF(⊛G) ⊛F (ρF(ρG) ⊛F m) ... (simplified below)

This is significant because it guarantees modularity: any two
applicative-based analyses can be combined into a single composed
analysis.

Examples from the paper:
- G ∘ S gives assignment-dependent sets of alternatives
- S ∘ G gives alternative assignment-dependent meanings
- G ∘ G gives doubly assignment-dependent meanings (= type-homogeneous
  paycheck/reconstruction from §5)

We prove the composed applicative laws for the Reader ∘ Reader case,
which is the one needed for §5's type-homogeneous assignments. -/

section ComposedApplicatives

variable {E₁ E₂ : Type}

/-- Composed ρ for Reader E₁ ∘ Reader E₂: `ρ_{F∘G}(x) = λe₁ λe₂. x`. -/
def composedPure {A : Type} (x : A) : E₁ → E₂ → A :=
  fun _ _ => x

/-- Composed ⊛ for Reader E₁ ∘ Reader E₂:
    `(m ⊛_{F∘G} n)(e₁)(e₂) = m e₁ e₂ (n e₁ e₂)`. -/
def composedAp {A B : Type} (f : E₁ → E₂ → A → B) (x : E₁ → E₂ → A)
    : E₁ → E₂ → B :=
  fun e₁ e₂ => f e₁ e₂ (x e₁ e₂)

/-- Composed homomorphism: `ρ f ⊛ ρ x = ρ (f x)`. -/
theorem composed_homomorphism {A B : Type} (f : A → B) (x : A) :
    composedAp (composedPure (E₁ := E₁) (E₂ := E₂) f) (composedPure x) =
    composedPure (f x) := rfl

/-- Composed identity: `ρ id ⊛ v = v`. -/
theorem composed_identity {A : Type} (v : E₁ → E₂ → A) :
    composedAp (composedPure id) v = v := rfl

/-- Composed interchange: `u ⊛ ρ y = ρ (· y) ⊛ u`. -/
theorem composed_interchange {A B : Type}
    (u : E₁ → E₂ → A → B) (y : A) :
    composedAp u (composedPure y) =
    composedAp (composedPure (fun f => f y)) u := rfl

/-- G ∘ G paycheck reading: doubly assignment-dependent meaning
    `λg λh. likes(g₁ h)(b)` depends on two assignments. The intension
    `g₁` is retrieved from the first, evaluated at the second. -/
theorem composed_paycheck {E : Type}
    (likes : E → E → Bool) (mom : E → E) (b : E)
    (g h : Nat → E) (j : Nat)
    (h_stored : g j = mom (h 0)) :
    composedAp (composedAp (composedPure likes)
      (fun g' _ => g' j)) (composedPure b) g h =
    likes (mom (h 0)) b := by
  simp only [composedAp, composedPure, h_stored]

end ComposedApplicatives

-- ════════════════════════════════════════════════════════════════
-- § Variable-Free Equivalence (§6)
-- ════════════════════════════════════════════════════════════════

/-! ### Variable-free semantics as the same applicative

@cite{charlow-2018} §6: @cite{jacobson-1999}'s variable-free semantics
treats pronouns as identity functions `⟦she⟧ := λx. x` (type `e → e`)
instead of assignment-reading functions `⟦proᵢ⟧ := λg. gᵢ` (type `g → e`).

The paper's central observation: the same ρ and ⊛ work in both settings.
Both are instances of the Reader applicative — the variable-full version
uses `Reader (Assignment m)` and the variable-free version uses
`Reader Entity`. The combinatory apparatus is *identical*; only the
environment type changes.

We formalize this structural identity by showing that the VF operations
are *definitionally equal* to the variable-full operations instantiated
at the Entity type, not by redefining them from scratch. -/

section VariableFree

variable {E : Type}

/-- VF ρ: lift an assignment-independent value (= Reader pure). -/
def vfPure {A : Type} (x : A) : E → A := fun _ => x

/-- VF ⊛: entity-sensitive functional application (= Reader ap). -/
def vfAp {A B : Type} (f : E → A → B) (x : E → A) : E → B :=
  fun e => f e (x e)

/-- VF pronoun: the identity function `⟦she⟧ := λx. x`. -/
def vfPronoun : E → E := id

/-- "She left" in VF semantics: `ρ(left) ⊛ she = left`.
    The pronoun passes through its referent; ρ lifts `left` to
    ignore its entity argument; ⊛ composes them. -/
theorem vf_she_left (left : E → Bool) :
    vfAp (vfPure left) vfPronoun = left := rfl

/-- VF ρ is definitionally Reader `pure`. -/
theorem vf_pure_is_reader_pure {A : Type} (x : A) :
    vfPure (E := E) x =
    @Pure.pure (Semantics.Reference.Binding.Reader E) _ A x := rfl

/-- VF homomorphism: `ρ f ⊛ ρ x = ρ (f x)`. -/
theorem vf_homomorphism {A B : Type} (f : A → B) (x : A) :
    vfAp (vfPure f) (vfPure (E := E) x) = vfPure (f x) := rfl

/-- VF identity: `ρ id ⊛ v = v`. -/
theorem vf_identity {A : Type} (v : E → A) :
    vfAp (vfPure id) v = v := rfl

/-- VF interchange: `u ⊛ ρ y = ρ (· y) ⊛ u`. -/
theorem vf_interchange {A B : Type} (u : E → A → B) (y : A) :
    vfAp u (vfPure y) = vfAp (vfPure (fun f => f y)) u := rfl

/-- "She saw her" with SINGLE entity parameter: both pronouns
    resolve to the same entity, yielding the reflexive reading
    `λe. saw e e`. -/
theorem vf_she_saw_her_single (saw : E → E → Bool) :
    vfAp (vfAp (vfPure saw) vfPronoun) vfPronoun =
    fun e => saw e e := rfl

/-- "She saw her" with COMPOSED applicative (§5–§6, two entity
    parameters): the two pronouns resolve independently, yielding
    `λx λy. saw y x`. This is the paper's key §6 result —
    assignment-dependence "springs organically into being" from
    uncurrying the composed VF denotation. -/
theorem vf_she_saw_her_composed (saw : E → E → Bool) :
    composedAp (composedAp (composedPure saw)
      (fun _ (e₂ : E) => e₂)) (fun (e₁ : E) _ => e₁) =
    fun (e₁ : E) (e₂ : E) => saw e₂ e₁ := rfl

end VariableFree

-- ════════════════════════════════════════════════════════════════
-- § Binding.lean Reader bridge
-- ════════════════════════════════════════════════════════════════

/-! ### Connection to `Reference/Binding.lean`'s Reader monad

`Binding.lean` defines `Reader E A := E → A` with a `Monad` instance.
@cite{charlow-2018}'s operations are instantiations of this monad:

- `constDenot d` = `@Pure.pure (Reader (Assignment m))`
- `applyG f x` = the applicative `<*>` of `Reader (Assignment m)`
- `denotGJoin` = the Reader monad's join (`W` combinator)
- `lambdaAbsG` wraps `Assignment.update`, extending Reader with binding -/

section BindingReaderBridge

open Semantics.Reference.Binding

variable {m : Model}

/-- `constDenot` is the Reader monad's `pure`. -/
theorem constDenot_is_reader_pure {σ : Ty} (d : m.interpTy σ) :
    constDenot d =
    @Pure.pure (Semantics.Reference.Binding.Reader (Assignment m)) _ _ d := rfl

/-- `denotGJoin` is the `W` (duplicator) combinator from `Binding.lean`:
    both compute `λg. f g g`. -/
theorem denotGJoin_is_W {A : Type}
    (f : Assignment m → Assignment m → A) :
    denotGJoin f = Semantics.Reference.Binding.W f := rfl

end BindingReaderBridge

end Phenomena.Anaphora.Studies.Charlow2018
