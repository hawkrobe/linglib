import Linglib.Theories.Semantics.Montague.Variables
import Linglib.Theories.Semantics.Reference.Binding
import Linglib.Theories.Semantics.Composition.Applicative
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
recover @cite{jacobson-1999}'s variable-free semantics (§6). The generic
applicative operations (`readerPure`, `readerAp`, `composedPure`, `composedAp`,
`vfPronoun`) and their laws live in `Composition/Applicative.lean`; this file
bridges them to the Montague `Model`/`DenotG` infrastructure.

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
9. Typed assignments make the paycheck derivation self-contained (§5)
-/

set_option autoImplicit false

namespace Phenomena.Anaphora.Studies.Charlow2018

open Semantics.Montague
open Semantics.Montague.Variables
open Semantics.Composition.Applicative

-- ════════════════════════════════════════════════════════════════
-- § H&K Decomposition: ⟦·⟧ = ρ + ⊛
-- ════════════════════════════════════════════════════════════════

/-! ### The ρ/⊛ decomposition of H&K's interpretation function

@cite{charlow-2018} §3.1–3.2: the standard H&K interpretation function
`⟦α β⟧ := λg. ⟦α⟧ g (⟦β⟧ g)` decomposes into two
independent operations:

- ρ lifts assignment-independent values: `⟦John⟧ = ρ(j)`
- ⊛ composes assignment-dependent meanings: `⟦α β⟧ = ⟦α⟧ ⊛ ⟦β⟧`

This decomposition is directly visible in linglib's `interp`
(`Composition/Tree.lean`): its binary case computes
`FA(⟦α⟧^g, ⟦β⟧^g)`, which is `applyG ⟦α⟧ ⟦β⟧` evaluated at `g`. -/

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

/-- Composing two ρ-lifted entries via ⊛ yields ρ of the composition. -/
theorem rho_ap_reduces (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) :
    applyG (constDenot f) (constDenot x) = constDenot (f x) :=
  constDenot_applyG f x

/-- `constDenot` IS `readerPure` (from `Applicative.lean`). -/
theorem constDenot_is_readerPure {σ : Ty} (d : m.interpTy σ) :
    constDenot d = readerPure d := rfl

/-- `applyG` IS `readerAp` (from `Applicative.lean`). -/
theorem applyG_is_readerAp {σ τ : Ty}
    (f : DenotG m (σ ⇒ τ)) (x : DenotG m σ) :
    applyG f x = readerAp f x := rfl

end HKDecomposition

-- ════════════════════════════════════════════════════════════════
-- § Categorematic Abstraction (Λᵢ)
-- ════════════════════════════════════════════════════════════════

/-! ### Λᵢ: categorematic predicate abstraction

@cite{charlow-2018} eq (13): `Λᵢ := λf. λg. λx. f g^{i→x}`

In H&K, predicate abstraction is a syncategorematic rule. With ρ/⊛,
Λᵢ becomes a *categorematic* operation — `lambdaAbsG`. -/

section CategorematicAbstraction

variable {m : Model} {τ : Ty}

/-- Λᵢ applied to a pronoun recovers the identity function:
    `Λₙ(proₙ) = λg λx. x`. -/
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
*intensions* rather than *extensions*. The key mechanism is
**higher-order variables** + the monadic join μ (`denotGJoin`).

The `Assignment m = Nat → m.Entity` type can only store entities, not
intensions. @cite{charlow-2018} §5.1 proposes type-homogeneous assignments
`gᵣ := ℕ → r` to fix this — see `typed_paycheck` in `Applicative.lean`
for the self-contained derivation. Here we show the paycheck truth
conditions using externally-provided intensions. -/

section Paycheck

variable {m : Model}

/-- The intension `⟦his₀ mom⟧ = ρ(mom) ⊛ pro₀ = λg. mom(g₀)`. -/
def momIntension (mom : m.Entity → m.Entity) (n : Nat) : DenotG m .e :=
  fun g => mom (g n)

/-- `momIntension` is compositionally derived: `ρ(mom) ⊛ proₙ`. -/
theorem momIntension_eq_rho_ap_pro (mom : m.Entity → m.Entity) (n : Nat) :
    momIntension mom n =
    applyG (constDenot (ty := .e ⇒ .e) mom) (interpPronoun n) := rfl

/-- Paycheck truth conditions: `likes(mom(g n), bill)`. -/
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
    records a bound reading — exactly what intension retrieval predicts. -/
theorem paycheck_datum_has_bound_reading :
    Phenomena.Anaphora.DonkeyAnaphora.paycheckSentence.boundReading = true := rfl

end Paycheck

-- ════════════════════════════════════════════════════════════════
-- § Binding Reconstruction
-- ════════════════════════════════════════════════════════════════

/-! ### Binding reconstruction via higher-order trace + Λᵢ

@cite{charlow-2018} §4.2, Fig 7: "[His₁ mom]ⱼ, every boy₁ likes tⱼ."

The bound pronoun *his₁* is inside a fronted constituent that is
syntactically *higher* than the binder *every boy₁*. The analysis
uses Λ₁ to abstract over the quantifier variable, producing the
reconstructed predicate `λx. likes(mom(x), x)` without c-command. -/

section BindingReconstruction

variable {m : Model}

/-- The reconstructed VP predicate: `λx. likes(mom(x), x)`. -/
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

/-- The reconstruction predicate is assignment-independent. -/
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
-- § Composed Applicatives (§3.3) — Paper-Specific Bridge
-- ════════════════════════════════════════════════════════════════

/-! ### Composed applicative: G ∘ G paycheck

Generic composed applicative operations and all four laws live in
`Composition/Applicative.lean`. Here we bridge to the paper's
specific paycheck example using entities. -/

section ComposedPaycheck

/-- G ∘ G paycheck reading: doubly assignment-dependent meaning
    `λg λh. likes(g₁ h)(b)` depends on two assignments. -/
theorem composed_paycheck {E : Type}
    (likes : E → E → Bool) (mom : E → E) (b : E)
    (g h : Nat → E) (j : Nat)
    (h_stored : g j = mom (h 0)) :
    composedAp (composedAp (composedPure likes)
      (fun g' _ => g' j)) (composedPure b) g h =
    likes (mom (h 0)) b := by
  simp only [composedAp, composedPure, h_stored]

end ComposedPaycheck

-- ════════════════════════════════════════════════════════════════
-- § Variable-Free Bridge
-- ════════════════════════════════════════════════════════════════

/-! ### Connection to `Reference/Binding.lean`'s Reader monad

@cite{charlow-2018}'s operations are instantiations of the Reader monad
from `Binding.lean`:

- `constDenot d` = Reader pure at `Assignment m`
- `applyG f x` = Reader `<*>` at `Assignment m`
- `denotGJoin` = the W combinator (`Binding.lean`)
- VF `readerPure` = Reader pure at Entity -/

section ReaderBridge

open Semantics.Reference.Binding

variable {m : Model}

/-- `constDenot` is the Reader monad's `pure`. -/
theorem constDenot_is_reader_pure {σ : Ty} (d : m.interpTy σ) :
    constDenot d =
    @Pure.pure (Semantics.Reference.Binding.Reader (Assignment m)) _ _ d := rfl

/-- VF `readerPure` is also the Reader monad's `pure`. -/
theorem readerPure_is_reader_monad_pure {A : Type} (x : A) :
    readerPure (E := m.Entity) x =
    @Pure.pure (Semantics.Reference.Binding.Reader m.Entity) _ A x := rfl

/-- `denotGJoin` is the `W` (duplicator) combinator from `Binding.lean`. -/
theorem denotGJoin_is_W {A : Type}
    (f : Assignment m → Assignment m → A) :
    denotGJoin f = Semantics.Reference.Binding.W f := rfl

end ReaderBridge

end Phenomena.Anaphora.Studies.Charlow2018
