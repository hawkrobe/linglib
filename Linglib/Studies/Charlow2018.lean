import Mathlib.Data.Set.Functor
import Linglib.Core.Logic.Intensional.Defs
import Linglib.Core.Logic.Intensional.Variables
import Linglib.Core.Logic.Assignment
import Linglib.Semantics.Composition.Continuation
import Linglib.Semantics.Reference.Binding

/-!
# [charlow-2018]: A Modular Theory of Pronouns and Binding

Simon Charlow (2018). "A modular theory of pronouns and binding."
Manuscript, Rutgers University. <https://lingbuzz.net/lingbuzz/003720>

## Thesis

The standard [heim-kratzer-1998] treatment of assignment-sensitivity
factors into two algebraic operations (§3.1, eqs 11–12):

* `ρ x := λg. x` — lift assignment-independent values
* `m ⊛ n := λg. m g (n g)` — assignment-friendly functional application

These form an **applicative functor** ([mcbride-paterson-2008]) for
`G a := g → a`, satisfying the four laws of §3.3 (Homomorphism,
Identity, Interchange, Composition). The modularization (i) keeps the
lexicon maximally simple — nothing is assignment-sensitive unless it
really is — and (ii) makes predicate abstraction `Λᵢ` categorematic
(eq. 13), eliminating H&K's syncategorematic rule.

Adding a **join** `μ m := λg. m g g` (eq. 19) upgrades the structure to
a monad (§4.3), enabling **higher-order variables** anaphoric to
*intensions* rather than *extensions* — yielding immediate analyses of
paycheck pronouns (Fig. 6) and binding reconstruction (Fig. 7) with the
unitary pronoun semantics `⟦proᵢ⟧ := λg. gᵢ`.

§3.3 shows applicative functors are *already implicit* in existing
semantic theory: Hamblin alternative semantics is the Set applicative
(eqs 14–15), and Shan & Barker's continuation-based composition is the
Cont applicative (eqs 16–17). Applicatives compose (Fig. 5) — unlike
monads (§4.3 end: `S ∘ G` is not monadic) — which §5 exploits: with
type-homogeneous assignments `gᵣ := ℕ → r` (§5.2), the composed
applicative `G_e ∘ G_{g_e→e}` handles paychecks *without* monads.
§6 plays us out with variable-free semantics ([jacobson-1999]): the
same ρ/⊛ with `Entity` as the environment type, where composing the VF
applicative with itself makes assignment-dependence "spring organically
into being."

## Organization (following the paper)

* **§3.1–3.2** — ρ/⊛, the four laws, H&K decomposition, categorematic Λᵢ
* **§3.3** — applicatives already in semantic theory: Set, Cont, composition
* **§4** — μ, higher-order variables: paychecks, binding reconstruction
* **§5** — typed assignments `gᵣ`; composed-applicative paychecks
* **§6** — variable-free semantics as Reader Entity
* **Bridges** — `Core`'s `DenotG` apparatus and `Reference/Binding`'s Reader monad
-/

set_option autoImplicit false

namespace Charlow2018

open Core.Logic.Intensional
open Core.Logic.Intensional.Variables

/-! ## §3.1–3.2 Getting modular: ρ and ⊛

Eqs (11)–(12): instead of treating all lexical values as trivially
assignment-dependent, invoke `ρ` to lift any `x` into a constant
function from assignments, and `⊛` for assignment-friendly functional
application on demand. The four applicative functor laws (§3.3 table)
hold definitionally for `G a := g → a`. -/

section ReaderApplicative

variable {E A B C : Type}

/-- ρ (eq. 11): lift a value into the Reader space — `ρ x := λg. x`. -/
def readerPure (x : A) : E → A := fun _ => x

/-- ⊛ (eq. 12): assignment-friendly functional application —
`m ⊛ n := λg. m g (n g)`. -/
def readerAp (f : E → A → B) (x : E → A) : E → B :=
  fun e => f e (x e)

/-- **Homomorphism** (§3.3): `ρ f ⊛ ρ x = ρ (f x)`. -/
theorem reader_homomorphism (f : A → B) (x : A) :
    readerAp (readerPure (E := E) f) (readerPure x) = readerPure (f x) := rfl

/-- **Identity** (§3.3): `ρ(λx.x) ⊛ v = v`. -/
theorem reader_identity (v : E → A) :
    readerAp (readerPure id) v = v := rfl

/-- **Interchange** (§3.3): `u ⊛ ρ y = ρ(λf. f y) ⊛ u`. -/
theorem reader_interchange (u : E → A → B) (y : A) :
    readerAp u (readerPure y) = readerAp (readerPure (fun f => f y)) u := rfl

/-- **Composition** (§3.3): `ρ(∘) ⊛ u ⊛ v ⊛ w = u ⊛ (v ⊛ w)`. -/
theorem reader_composition (u : E → B → C) (v : E → A → B) (w : E → A) :
    readerAp (readerAp (readerAp (readerPure Function.comp) u) v) w =
    readerAp u (readerAp v w) := rfl

end ReaderApplicative

/-! ### The ρ/⊛ decomposition of H&K's interpretation function

§3.1–3.2: the standard H&K interpretation function
`⟦α β⟧ := λg. ⟦α⟧ g (⟦β⟧ g)` decomposes into ρ (for trivially
assignment-dependent lexical entries: `⟦John⟧ = ρ(j)`) and ⊛ (for
binary branching). This decomposition is directly visible in linglib's
`interp` (`Composition/Tree.lean`): its binary case computes
`FA(⟦α⟧^g, ⟦β⟧^g)`, which is `applyG ⟦α⟧ ⟦β⟧` evaluated at `g`. -/

section HKDecomposition

variable {E W : Type} {σ τ : Ty}

/-- H&K's interpretation function `⟦α β⟧ = λg. ⟦α⟧ g (⟦β⟧ g)` is
definitionally `applyG`: ⊛ *is* `⟦·⟧` restricted to binary branching. -/
theorem hk_decomposition (f : DenotG E W (σ ⇒ τ)) (x : DenotG E W σ) :
    applyG f x = fun g => f g (x g) := rfl

/-- Non-pronominal entries in H&K are trivially assignment-dependent:
`⟦John⟧ := λg. j`. This is exactly ρ(j). -/
theorem hk_lexical_lift (d : Denot E W σ) :
    constDenot d = fun (_ : Core.Assignment E) => d := rfl

/-- Composing two ρ-lifted entries via ⊛ yields ρ of the composition. -/
theorem rho_ap_reduces (f : Denot E W (σ ⇒ τ)) (x : Denot E W σ) :
    applyG (constDenot f) (constDenot x) = constDenot (f x) :=
  constDenot_applyG f x

/-- `Core`'s `constDenot` IS the paper's ρ. -/
theorem constDenot_is_readerPure {σ : Ty} (d : Denot E W σ) :
    constDenot d = readerPure d := rfl

/-- `Core`'s `applyG` IS the paper's ⊛. -/
theorem applyG_is_readerAp {σ τ : Ty}
    (f : DenotG E W (σ ⇒ τ)) (x : DenotG E W σ) :
    applyG f x = readerAp f x := rfl

end HKDecomposition

/-! ### Λᵢ: categorematic predicate abstraction

Eq. (13): `Λᵢ := λf. λg. λx. f g^{i→x}`. In H&K, predicate abstraction
is a syncategorematic rule; with ρ/⊛ there is no grammatical default
about how assignments get passed around, so Λᵢ becomes a *categorematic*
operation — linglib's `lambdaAbsG`. -/

section CategorematicAbstraction

variable {E W : Type} {τ : Ty}

/-- Λᵢ applied to a pronoun recovers the identity function:
`Λₙ(proₙ) = λg λx. x`. -/
theorem lambda_pronoun (n : Nat) (g : Core.Assignment E) (x : E) :
    lambdaAbsG (W := W) n (interpPronoun n) g x = x := by
  simp [lambdaAbsG, interpPronoun]

/-- Λᵢ applied to `ρ(left) ⊛ proₙ` yields `ρ(left)`:
`Λₙ(ρ(left) ⊛ proₙ) = λg λx. left(x) = ρ(left)`. -/
theorem lambda_rho_ap_pronoun (n : Nat)
    (left : Denot E W (.e ⇒ .t))
    (g : Core.Assignment E) (x : E) :
    lambdaAbsG n (applyG (constDenot left) (interpPronoun n)) g x =
    left x := by
  simp [lambdaAbsG, applyG, constDenot, interpPronoun]

end CategorematicAbstraction

/-! ## §3.3 Applicatives already in semantic theory

"Applicative functors can be factored out of a great deal of existing
semantic theory." Two examples, then the composition property. -/

/-! ### The Set applicative (eqs 14–15)

Hamblin alternative semantics restated as an applicative for sets
`S a := a → t`: `ρ x := {x}` and `m ⊛ n := {f x | f ∈ m, x ∈ n}`.
Operations are mathlib's `Set` `pure`/`<*>`; the application-form simp
lemmas serve consumers that treat `Set A = A → Prop`. The monadic
extension of this applicative — and why the *monad* matters for
exceptional scope — is [charlow-2020], formalized in
`Studies/Charlow2020.lean`. -/

section SetApplicative

variable {A B C : Type}

/-- Set ρ (eq. 14): the singleton `{x}`. Mathlib's `Set` applicative
`pure`. -/
def setPure (x : A) : Set A := pure x

/-- Set ⊛ (eq. 15): pointwise application across sets,
`{f x | f ∈ m, x ∈ n}`. Mathlib's `Set` applicative `<*>` (`Set.seq`). -/
def setAp (m : Set (A → B)) (n : Set A) : Set B := m <*> n

@[simp] theorem mem_setPure (x y : A) : y ∈ setPure x ↔ y = x := Iff.rfl

/-- Application-form characterisation of `setPure` (consumers treat
`Set A = A → Prop`). -/
@[simp] theorem setPure_apply (x y : A) : setPure x y ↔ y = x := Iff.rfl

@[simp] theorem mem_setAp (m : Set (A → B)) (n : Set A) (b : B) :
    b ∈ setAp m n ↔ ∃ f, f ∈ m ∧ ∃ x, x ∈ n ∧ f x = b := by
  simp only [setAp, Set.seq_eq_set_seq, Set.mem_seq_iff]

/-- Application-form characterisation of `setAp`. -/
@[simp] theorem setAp_apply (m : Set (A → B)) (n : Set A) (b : B) :
    setAp m n b ↔ ∃ f, m f ∧ ∃ x, n x ∧ f x = b := mem_setAp m n b

/-- **Homomorphism** for Set: `{f} ⊛ {x} = {f x}`. -/
theorem set_homomorphism (f : A → B) (x : A) :
    setAp (setPure f) (setPure x) = setPure (f x) := by
  ext b; simp only [mem_setAp, mem_setPure]; aesop

/-- **Identity** for Set: `{id} ⊛ v = v`. -/
theorem set_identity (v : Set A) :
    setAp (setPure id) v = v := by
  ext b; simp only [mem_setAp, mem_setPure]; aesop

/-- **Interchange** for Set: `u ⊛ {y} = {(fun f => f y)} ⊛ u`. -/
theorem set_interchange (u : Set (A → B)) (y : A) :
    setAp u (setPure y) = setAp (setPure (fun f => f y)) u := by
  ext b; simp only [mem_setAp, mem_setPure]; aesop

/-- **Composition** for Set: `{∘} ⊛ u ⊛ v ⊛ w = u ⊛ (v ⊛ w)`. -/
theorem set_composition (u : Set (B → C)) (v : Set (A → B)) (w : Set A) :
    setAp (setAp (setAp (setPure Function.comp) u) v) w =
    setAp u (setAp v w) := by
  ext c; simp only [mem_setAp, mem_setPure]; aesop

end SetApplicative

/-! ### The Cont applicative (eqs 16–17)

Shan & Barker's continuation-based composition is built on two
combinators (Lift/Scope) that directly instantiate the applicative
functor for continuations `Cᵣ a := (a → r) → r`. The operations are
definitionally `Cont.pure` and the `<*>` derived from
`Composition/Continuation.lean`'s monad instance. -/

section ContinuationApplicative

open Semantics.Composition.Continuation

variable {R A B : Type}

/-- Eq. (16): `ρ x := λκ. κ x` = `Cont.pure`. -/
theorem cont_pure_eq (x : A) :
    (fun (κ : A → R) => κ x) = Cont.pure x := rfl

/-- Eq. (17): `m ⊛ n := λκ. m(λf. n(λx. κ(f x)))` = Cont `<*>`. -/
theorem cont_ap_eq (m : Cont R (A → B)) (n : Cont R A) :
    (fun (κ : B → R) => m (fun f => n (fun x => κ (f x)))) =
    Cont.bind m (fun f => Cont.map f n) := rfl

end ContinuationApplicative

/-! ### Composed applicatives (Fig. 5)

Given two applicative type constructors F and G, their composition
F ∘ G is applicative. For `Reader E₁ ∘ Reader E₂`:

```
ρ_{F∘G}(x) = λe₁ λe₂. x
(m ⊛_{F∘G} n)(e₁)(e₂) = m e₁ e₂ (n e₁ e₂)
```

This closure guarantees modularity: any two applicative-based analyses
combine without additional machinery. `G ∘ S` yields
assignment-dependent alternative sets; `S ∘ G` alternative
assignment-dependent meanings; `G ∘ G` doubly assignment-dependent
meanings (the §5 paycheck composite). Monads, by contrast, are NOT
closed under composition (§4.3 end: `S ∘ G` is not monadic). -/

section ComposedApplicatives

variable {E₁ E₂ A B C : Type}

/-- Composed ρ for `Reader E₁ ∘ Reader E₂`. -/
def composedPure (x : A) : E₁ → E₂ → A :=
  fun _ _ => x

/-- Composed ⊛ for `Reader E₁ ∘ Reader E₂`. -/
def composedAp (f : E₁ → E₂ → A → B) (x : E₁ → E₂ → A) : E₁ → E₂ → B :=
  fun e₁ e₂ => f e₁ e₂ (x e₁ e₂)

theorem composed_homomorphism (f : A → B) (x : A) :
    composedAp (composedPure (E₁ := E₁) (E₂ := E₂) f) (composedPure x) =
    composedPure (f x) := rfl

theorem composed_identity (v : E₁ → E₂ → A) :
    composedAp (composedPure id) v = v := rfl

theorem composed_interchange (u : E₁ → E₂ → A → B) (y : A) :
    composedAp u (composedPure y) =
    composedAp (composedPure (fun f => f y)) u := rfl

theorem composed_composition (u : E₁ → E₂ → B → C)
    (v : E₁ → E₂ → A → B) (w : E₁ → E₂ → A) :
    composedAp (composedAp (composedAp (composedPure Function.comp) u) v) w =
    composedAp u (composedAp v w) := rfl

end ComposedApplicatives

/-! ## §4 Getting higher-order: paychecks and reconstruction

Higher-order variables (eq. 18: `pro ::= g → e | g → pro`) are
anaphoric to *intensions* rather than *extensions*. The flattener μ
(eq. 19: `μ m := λg. m g g`) converts a higher-order meaning to a
garden-variety one. ρ, ⊛, and μ together form a monad (§4.3) — the
Reader monad.

The `Core.Assignment E = Nat → E` type can only store
entities, not intensions; §5.1 proposes type-homogeneous assignments
`gᵣ := ℕ → r` to fix this (next section). Here we show the paycheck
truth conditions using externally-provided intensions. -/

section Paycheck

variable {E W : Type}

/-- The intension `⟦his₀ mom⟧ = ρ(mom) ⊛ pro₀ = λg. mom(g₀)`. -/
def momIntension (mom : E → E) (n : Nat) : DenotG E W .e :=
  fun g => mom (g n)

/-- `momIntension` is compositionally derived: `ρ(mom) ⊛ proₙ`. -/
theorem momIntension_eq_rho_ap_pro (mom : E → E) (n : Nat) :
    momIntension (W := W) mom n =
    applyG (constDenot (ty := .e ⇒ .e) mom) (interpPronoun n) := rfl

/-- Paycheck truth conditions: `likes(mom(g n), bill)`. -/
theorem paycheck_truth_conditions
    (mom : E → E)
    (likes : Denot E W (.e ⇒ .e ⇒ .t))
    (bill : E) (n : Nat) (g : Core.Assignment E) :
    applyG (applyG (constDenot likes) (momIntension mom n))
           (constDenot bill) g =
    likes (mom (g n)) bill := rfl

/-- When `g(n) = bill`, the paycheck pronoun denotes Bill's mom. -/
theorem paycheck_reading
    (mom : E → E)
    (likes : Denot E W (.e ⇒ .e ⇒ .t))
    (bill : E) (n : Nat) (g : Core.Assignment E) (h : g n = bill) :
    applyG (applyG (constDenot likes) (momIntension mom n))
           (constDenot bill) g =
    likes (mom bill) bill := by
  simp only [paycheck_truth_conditions, h]

end Paycheck

/-! ### Binding reconstruction via higher-order trace + Λᵢ (Fig. 7)

"[His₁ mom]ⱼ, every boy₁ likes tⱼ." The bound pronoun *his₁* is inside
a fronted constituent syntactically *higher* than the binder *every
boy₁*. The analysis uses Λ₁ to abstract over the quantifier variable,
producing the reconstructed predicate `λx. likes(mom(x), x)` without
LF c-command — and without triggering Weak Crossover, since the
bound-into expression *originates* lower than the binder. -/

section BindingReconstruction

variable {E W : Type}

/-- The reconstructed VP predicate: `λx. likes(mom(x), x)`. -/
theorem reconstruction_predicate
    (mom : E → E)
    (likes : Denot E W (.e ⇒ .e ⇒ .t))
    (n : Nat) (g : Core.Assignment E) (x : E) :
    lambdaAbsG n
      (applyG (applyG (constDenot likes) (momIntension mom n))
              (interpPronoun n))
      g x =
    likes (mom x) x := by
  simp only [lambdaAbsG, momIntension, applyG, constDenot, interpPronoun,
             Function.update_self]

/-- The reconstruction predicate is assignment-independent. -/
theorem reconstruction_independent
    (mom : E → E)
    (likes : Denot E W (.e ⇒ .e ⇒ .t))
    (n : Nat) (g₁ g₂ : Core.Assignment E) :
    lambdaAbsG n
      (applyG (applyG (constDenot likes) (momIntension mom n))
              (interpPronoun n)) g₁ =
    lambdaAbsG n
      (applyG (applyG (constDenot likes) (momIntension mom n))
              (interpPronoun n)) g₂ := by
  funext x
  simp only [lambdaAbsG, momIntension, applyG, constDenot, interpPronoun,
             Function.update_self]

end BindingReconstruction

/-! ## §5 Stepping back, to applicatives: typed assignments

§5.1–5.2: type-homogeneous assignments `gᵣ := ℕ → r` avoid the
inconsistency worries of a single polymorphic assignment type (Muskens
1995). Each type `r` gets its own assignment sort: `gₑ` maps indices
to individuals, `g_{gₑ→e}` to individual concepts. The composed
applicative `Gₑ ∘ G_{gₑ→e}` then handles paycheck pronouns *without*
monadic μ: the paycheck pronoun reads an intension from the
intension-assignment and evaluates it at the entity-assignment.
"We needn't exploit the extra power of monads to treat paychecks and
reconstruction; the only price is needing multiple assignments to
extract propositional content from certain utterances." -/

section TypedAssignments

variable {E : Type}

/-- Type-homogeneous assignment over carrier `r` (§5.2: `gᵣ := ℕ → r`).
Equal to `Core.Assignment r`; aliased to read naturally in the paycheck
composition where `r` ranges over both entity and intension carriers
within one derivation. -/
abbrev TypedAssignment (r : Type) := Core.Assignment r

/-- Self-contained paycheck derivation via composed `Gₑ ∘ G_{gₑ→e}`.

The intension-assignment `gᵢ` maps index `j` to the intension
`λh. mom(h 0)` (= "his₀ mom"). The entity-assignment `gₑ` maps index 0
to Bill. The paycheck pronoun `herⱼ` reads from `gᵢ` and evaluates at
`gₑ`, yielding `mom(bill)` — "virtually identical to what we
monadically derived in Figure 6, but depending on two assignments
rather than one." -/
theorem typed_paycheck
    (likes : E → E → Bool) (mom : E → E) (bill : E)
    (j : Nat) (gᵢ : TypedAssignment (TypedAssignment E → E))
    (gₑ : TypedAssignment E)
    (h_intension : gᵢ j = fun h => mom (h 0))
    (h_bill : gₑ 0 = bill) :
    composedAp (composedAp (composedPure likes)
      (fun gᵢ' gₑ' => gᵢ' j gₑ')) (composedPure bill) gᵢ gₑ =
    likes (mom bill) bill := by
  simp only [composedAp, composedPure, h_intension, h_bill]

/-- The intension `λh. mom(h 0)` is compositionally derived as
`ρ(mom) ⊛ pro₀` in the inner `Gₑ` applicative. -/
theorem typed_intension_is_rho_ap_pro (mom : E → E) :
    readerAp (readerPure (E := TypedAssignment E) mom) (fun h => h 0) =
    fun h => mom (h 0) := rfl

/-- `G ∘ G` paycheck reading with `Core.Assignment` sorts: the doubly
assignment-dependent meaning `λg λh. likes(g₁ h)(b)` depends on two
assignments. -/
theorem composed_paycheck
    (likes : E → E → Bool) (mom : E → E) (b : E)
    (g : Nat → E) (h : Nat → E) (j : Nat)
    (h_stored : g j = mom (h 0)) :
    composedAp (composedAp (composedPure likes)
      (fun g' _ => g' j)) (composedPure b) g h =
    likes (mom (h 0)) b := by
  simp only [composedAp, composedPure, h_stored]

end TypedAssignments

/-! ## §6 A bit of variable-free semantics to play us out

[jacobson-1999]'s variable-free semantics treats pronouns as identity
functions `⟦she⟧ := λx. x` (type `e → e`). The composition apparatus
is structurally identical to the assignment-sensitive version — ρ and
⊛ with `Entity` as the environment type instead of assignments
("we've only replaced g-dependent e's with e-dependent e's").

The striking observation: composing the VF applicative with itself
(`Reader E ∘ Reader E`) yields two-pronoun readings where the pronouns
resolve independently — uncurrying the result produces
assignment-dependence "organically." -/

section VariableFree

variable {E : Type}

/-- VF pronoun: the identity function `⟦she⟧ := λx. x`. -/
def vfPronoun : E → E := id

/-- "She left" in VF: `ρ(left) ⊛ she = left`. -/
theorem vf_she_left (left : E → Bool) :
    readerAp (readerPure left) vfPronoun = left := rfl

/-- "She saw her" with a single entity parameter: both pronouns resolve
to the same entity, yielding `λe. saw e e` (reflexive reading). -/
theorem vf_she_saw_her_single (saw : E → E → Bool) :
    readerAp (readerAp (readerPure saw) vfPronoun) vfPronoun =
    fun e => saw e e := rfl

/-- "She saw her" with the composed applicative (two entity
parameters): the two pronouns resolve independently, yielding
`λx λy. saw y x`. Assignment-dependence "springs organically into
being" from uncurrying. -/
theorem vf_she_saw_her_composed (saw : E → E → Bool) :
    composedAp (composedAp (composedPure saw)
      (fun _ (e₂ : E) => e₂)) (fun (e₁ : E) _ => e₁) =
    fun (e₁ : E) (e₂ : E) => saw e₂ e₁ := rfl

end VariableFree

/-! ## Bridge to `Reference/Binding.lean`'s Reader monad

The paper's operations are instantiations of the Reader monad from
`Binding.lean`:

* `constDenot d` = Reader pure at `Core.Assignment E`
* `applyG f x` = Reader `<*>` at `Core.Assignment E`
* `denotGJoin` (μ) = the W combinator
* VF `readerPure` = Reader pure at Entity -/

section ReaderBridge

open Semantics.Reference.Binding

variable {E W : Type}

/-- `constDenot` is the Reader monad's `pure`. -/
theorem constDenot_is_reader_pure {σ : Ty} (d : Denot E W σ) :
    constDenot d =
    @Pure.pure (Semantics.Reference.Binding.Reader (Core.Assignment E)) _ _ d := rfl

/-- VF `readerPure` is also the Reader monad's `pure`. -/
theorem readerPure_is_reader_monad_pure {A : Type} (x : A) :
    readerPure (E := E) x =
    @Pure.pure (Semantics.Reference.Binding.Reader E) _ A x := rfl

/-- `denotGJoin` (the paper's μ, eq. 19) is the `W` (duplicator)
combinator from `Binding.lean`. -/
theorem denotGJoin_is_W {A : Type}
    (f : Core.Assignment E → Core.Assignment E → A) :
    denotGJoin f = Semantics.Reference.Binding.W f := rfl

end ReaderBridge

end Charlow2018
