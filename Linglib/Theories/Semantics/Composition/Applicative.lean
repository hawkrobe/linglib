import Linglib.Theories.Semantics.Composition.Continuation
import Linglib.Core.Assignment

/-!
# Applicative Functors in Natural Language Semantics
@cite{charlow-2018} @cite{mcbride-paterson-2008}

Three applicative functors — Reader, Set, and Cont — recur across
natural language semantics. @cite{charlow-2018} shows they share a
common algebraic structure (a type constructor `F` with `ρ :: a → F a`
and `⊛ :: F(a → b) → F a → F b` satisfying four laws), and that this
structure is **closed under composition**.

| Applicative | `F a` | ρ | ⊛ | Linguistic use |
|---|---|---|---|---|
| Reader `E` | `E → a` | `λ_. x` | `λe. f e (x e)` | Assignment-sensitivity |
| Set | `a → Prop` | `{x}` | `{f x \| f ∈ m, x ∈ n}` | Alternatives/Hamblin |
| Cont `R` | `(a → R) → R` | `λκ. κ x` | `λκ. m(λf. n(λx. κ(f x)))` | Scope-taking |

## Key results

1. Reader satisfies the four applicative functor laws (§3.3)
2. Composed applicatives F ∘ G are applicative (§3.3, all 4 laws)
3. Variable-free semantics (@cite{jacobson-1999}) = Reader Entity (§6)
4. Set applicative satisfies all 4 laws; the Hamblin functional
   `(W → Bool) → Bool` (Rooth focus values, Karttunen-style answers)
   = `Cont Bool W` definitionally
5. Cont applicative operations = `Cont.pure`/`Cont.bind`+`Cont.map` (§3.3)
6. Typed assignment family `Gᵣ` for intensional variables (§5)
-/

set_option autoImplicit false

namespace Semantics.Composition.Applicative

-- ════════════════════════════════════════════════════════════════
-- §1 Reader Applicative
-- ════════════════════════════════════════════════════════════════

/-! ### Reader applicative

The Reader applicative for environment type `E`:
- `F a := E → a`
- `ρ x := λ_. x` (constant function)
- `m ⊛ n := λe. m e (n e)` (evaluate both at the same environment)

This is the foundation of assignment-sensitive composition
(@cite{charlow-2018} §3.1–3.2). The four applicative functor laws
hold definitionally. -/

section ReaderApplicative

variable {E A B C : Type}

/-- ρ: lift a value into the Reader space (`pure`/`return`). -/
def readerPure (x : A) : E → A := fun _ => x

/-- ⊛: compose two environment-dependent meanings (`<*>`/`ap`). -/
def readerAp (f : E → A → B) (x : E → A) : E → B :=
  fun e => f e (x e)

theorem reader_homomorphism (f : A → B) (x : A) :
    readerAp (readerPure (E := E) f) (readerPure x) = readerPure (f x) := rfl

theorem reader_identity (v : E → A) :
    readerAp (readerPure id) v = v := rfl

theorem reader_interchange (u : E → A → B) (y : A) :
    readerAp u (readerPure y) = readerAp (readerPure (fun f => f y)) u := rfl

theorem reader_composition (u : E → B → C) (v : E → A → B) (w : E → A) :
    readerAp (readerAp (readerAp (readerPure Function.comp) u) v) w =
    readerAp u (readerAp v w) := rfl

end ReaderApplicative

-- ════════════════════════════════════════════════════════════════
-- §2 Composed Applicatives
-- ════════════════════════════════════════════════════════════════

/-! ### Composed applicative functors

@cite{charlow-2018} §3.3, Fig 5: Given two applicative type constructors
F and G, their composition F ∘ G is applicative. For Reader E₁ ∘ Reader E₂:

    ρ_{F∘G}(x) = λe₁ λe₂. x
    (m ⊛_{F∘G} n)(e₁)(e₂) = m e₁ e₂ (n e₁ e₂)

This closure property guarantees modularity: any two applicative-based
analyses can be combined without additional machinery. Examples:
- G ∘ S: assignment-dependent sets of alternatives
- S ∘ G: alternative assignment-dependent meanings
- G ∘ G: doubly assignment-dependent meanings (§5, paycheck/reconstruction) -/

section ComposedApplicatives

variable {E₁ E₂ A B C : Type}

/-- Composed ρ for Reader E₁ ∘ Reader E₂. -/
def composedPure (x : A) : E₁ → E₂ → A :=
  fun _ _ => x

/-- Composed ⊛ for Reader E₁ ∘ Reader E₂. -/
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

/-- The **Composition** law — the fourth applicative functor law.
    Previously missing from the linglib formalization. -/
theorem composed_composition (u : E₁ → E₂ → B → C)
    (v : E₁ → E₂ → A → B) (w : E₁ → E₂ → A) :
    composedAp (composedAp (composedAp (composedPure Function.comp) u) v) w =
    composedAp u (composedAp v w) := rfl

end ComposedApplicatives

-- ════════════════════════════════════════════════════════════════
-- §3 Variable-Free Semantics
-- ════════════════════════════════════════════════════════════════

/-! ### Variable-free semantics as Reader Entity

@cite{charlow-2018} §6: @cite{jacobson-1999}'s variable-free semantics
treats pronouns as identity functions `⟦she⟧ := λx. x` (type `e → e`).
The composition apparatus is structurally identical to the assignment-
sensitive version — `readerPure` and `readerAp` — with `Entity` as the
environment type instead of assignments.

The paper's striking observation: composing the VF applicative with itself
(`Reader E ∘ Reader E`) yields two-pronoun readings where the pronouns
resolve independently. Uncurrying the result produces assignment-dependence
"organically" (§6). -/

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

/-- "She saw her" with composed applicative (two entity parameters):
    the two pronouns resolve independently, yielding `λx λy. saw y x`.
    Assignment-dependence "springs organically into being" from
    uncurrying (@cite{charlow-2018} §6). -/
theorem vf_she_saw_her_composed (saw : E → E → Bool) :
    composedAp (composedAp (composedPure saw)
      (fun _ (e₂ : E) => e₂)) (fun (e₁ : E) _ => e₁) =
    fun (e₁ : E) (e₂ : E) => saw e₂ e₁ := rfl

end VariableFree

-- ════════════════════════════════════════════════════════════════
-- §4 Set Applicative
-- ════════════════════════════════════════════════════════════════

/-! ### Set applicative

@cite{charlow-2018} §3.3 eqs (14)–(15): Alternative semantics of the
@cite{hamblin-1973b} variety uses an applicative functor for sets:

    S a := a → Prop
    ρ x := {x}                          = `setPure`
    m ⊛ n := {f x | f ∈ m, x ∈ n}      = `setAp`

A Hamblin question denotation `(W → Bool) → Bool` is definitionally
`Cont Bool W` (both expand to `(W → Bool) → Bool`), connecting the
Set and Cont perspectives. -/

section SetApplicative

variable {A B C : Type}

/-- Set ρ: the singleton set `{x}`. -/
def setPure (x : A) : A → Prop := fun y => y = x

/-- Set ⊛: pointwise function application across sets.
    `{f x | f ∈ m, x ∈ n}` -/
def setAp (m : (A → B) → Prop) (n : A → Prop) : B → Prop :=
  fun b => ∃ f, m f ∧ ∃ x, n x ∧ f x = b

/-- **Homomorphism**: `{f} ⊛ {x} = {f x}`. -/
theorem set_homomorphism (f : A → B) (x : A) :
    setAp (setPure f) (setPure x) = setPure (f x) := by
  funext b; apply propext; simp only [setAp, setPure]; constructor
  · rintro ⟨g, rfl, y, rfl, rfl⟩; rfl
  · intro hb; exact ⟨f, rfl, x, rfl, hb.symm⟩

/-- **Identity**: `{id} ⊛ v = v`. -/
theorem set_identity (v : A → Prop) :
    setAp (setPure id) v = v := by
  funext b; apply propext; simp only [setAp, setPure]; constructor
  · rintro ⟨g, rfl, x, hx, rfl⟩; exact hx
  · intro hb; exact ⟨id, rfl, b, hb, rfl⟩

/-- **Interchange**: `u ⊛ {y} = {(fun f => f y)} ⊛ u`. -/
theorem set_interchange (u : (A → B) → Prop) (y : A) :
    setAp u (setPure y) = setAp (setPure (fun f => f y)) u := by
  funext b; apply propext; simp only [setAp, setPure]; constructor
  · intro ⟨f, hf, x, hxy, hfxb⟩
    exact ⟨fun f => f y, rfl, f, hf, hxy ▸ hfxb⟩
  · intro ⟨g, hgy, f, hf, hgfb⟩
    subst hgy; exact ⟨f, hf, y, rfl, hgfb⟩

/-- **Composition**: `{∘} ⊛ u ⊛ v ⊛ w = u ⊛ (v ⊛ w)`. -/
theorem set_composition (u : (B → C) → Prop) (v : (A → B) → Prop)
    (w : A → Prop) :
    setAp (setAp (setAp (setPure Function.comp) u) v) w =
    setAp u (setAp v w) := by
  funext c; apply propext; simp only [setAp, setPure]; constructor
  · rintro ⟨k, ⟨h, ⟨co, rfl, g, hg, rfl⟩, f, hf, rfl⟩, x, hx, rfl⟩
    exact ⟨g, hg, f x, ⟨f, hf, x, hx, rfl⟩, rfl⟩
  · rintro ⟨g, hg, _, ⟨f, hf, x, hx, rfl⟩, rfl⟩
    exact ⟨fun x => g (f x),
      ⟨Function.comp g, ⟨Function.comp, rfl, g, hg, rfl⟩, f, hf, rfl⟩,
      x, hx, rfl⟩

end SetApplicative

-- ════════════════════════════════════════════════════════════════
-- §5 Continuation Applicative
-- ════════════════════════════════════════════════════════════════

/-! ### Continuation applicative

@cite{charlow-2018} §3.3 eqs (16)–(17): scope-taking expressions use
the continuation applicative `Cᵣ a := (a → r) → r`. The operations
are definitionally `Cont.pure` and the derived `<*>` from
`Core/Continuation.lean`. -/

section ContinuationApplicative

open Semantics.Composition.Continuation

variable {R A B : Type}

/-- Eq (16): `ρ x := λκ. κ x` = `Cont.pure`. -/
theorem cont_pure_eq (x : A) :
    (fun (κ : A → R) => κ x) = Cont.pure x := rfl

/-- Eq (17): `m ⊛ n := λκ. m(λf. n(λx. κ(f x)))` = Cont `<*>`. -/
theorem cont_ap_eq (m : Cont R (A → B)) (n : Cont R A) :
    (fun (κ : B → R) => m (fun f => n (fun x => κ (f x)))) =
    Cont.bind m (fun f => Cont.map f n) := rfl

end ContinuationApplicative

-- ════════════════════════════════════════════════════════════════
-- §6 Typed Assignment Family
-- ════════════════════════════════════════════════════════════════

/-! ### Typed assignment family Gᵣ

@cite{charlow-2018} §5.1: type-homogeneous assignments `gᵣ := ℕ → r`
avoid consistency problems of a single polymorphic assignment type.
Each type `r` gets its own assignment type:
- `gₑ`: maps indices to individuals
- `g_{gₑ→e}`: maps indices to individual concepts (intensions)

The composed applicative `Gₑ ∘ G_{gₑ→e}` handles paycheck pronouns
without monadic join (§5.2): the paycheck pronoun reads an intension
from the intension-assignment and evaluates it at the entity-assignment. -/

section TypedAssignments

variable {E : Type}

/-- Type-homogeneous assignment over carrier `r`. Equal to `Core.Assignment r`;
    aliased here to read naturally in the Charlow paycheck composition where
    `r` ranges over both entity and intension carriers within one derivation. -/
abbrev TypedAssignment (r : Type) := Core.Assignment r

/-- Self-contained paycheck derivation via composed `Gₑ ∘ G_{gₑ→e}`.

    The intension-assignment `gᵢ` maps index `j` to the intension
    `λh. mom(h 0)` (= "his₀ mom"). The entity-assignment `gₑ` maps
    index 0 to Bill. The paycheck pronoun `herⱼ` reads from `gᵢ` and
    evaluates at `gₑ`, yielding `mom(bill)`. -/
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

end TypedAssignments

end Semantics.Composition.Applicative
