module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Reference.Character

/-!
# Nominal denotations

A pronoun, a definite description, a demonstrative and a bound variable are one kind of
thing: a presuppositional, context-relative individual denotation, differing only in the
*selector* that chooses the individual (the assignment value, the iota, the demonstratum) and
in the intrinsic *presupposition* (φ-features, uniqueness, deixis), as Büring argues. A
`Nominal` is that common shape. Resolving it against a scope is `presupOfReferent` of the
selector at a context (`Nominal.resolve`), so a definite built from `presupOfReferent` is a
resolved `Nominal.ofReferent` by `rfl` (`ofReferent_resolve`), and the full denotation
restricts the resolved one to where the intrinsic presupposition holds (`Nominal.toTrivalent`),
which is where a pronoun's φ-features project. A character is the total nominal with no
presupposition (`Character.toNominal`), and it is directly referential exactly when that
nominal's selector is rigid at every context (`Character.isDirectlyReferential_iff`).
`Nominal Ctx W` is the presupposition-projecting partiality monad, lawful
(`instLawfulMonad`): `bind` threads the partial referent and projects the continuation's
presupposition through definedness of the head, so a re-selection such as possessive-of
composes as a Kleisli arrow while the head's presupposition rides along.

## Implementation notes

The selector is `Option`-valued against a context; the dynamic case, where a selector returns
a family of referents, is the functor-parameterised generalisation of this signature and is
left to the first dynamic consumer that needs it.

## References

* [buring-2012]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace Reference

open Presupposition

/-- A presuppositional, context-relative individual denotation.

`presup` is the intrinsic presupposition beyond definedness — φ-features for
a pronoun, deixis for a demonstrative, vacuous for a definite (whose only
presupposition is that the selector is defined). `selector` is the partial
choice of referent (`g i`, `ι`, the demonstratum) at a context and world. -/
structure Nominal (Ctx : Type*) (W : Type*) (E : Type*) where
  /-- Intrinsic presupposition beyond definedness (φ-features, deixis). -/
  presup : Ctx → W → Prop
  /-- The partial referent selector. -/
  selector : Ctx → W → Option E

namespace Nominal

variable {Ctx : Type*} {W : Type*} {E : Type*}

/-- The simplest nominal is a context-free referent selector with no intrinsic
presupposition, a bare iota or definite. `(ofReferent r).resolve scope ⟨⟩`
unfolds to `presupOfReferent r scope`, so any `presupOfReferent`-built
denotation is an `ofReferent` resolved (`ofReferent_resolve`). -/
def ofReferent (referent : W → Option E) : Nominal Unit W E where
  presup := fun _ _ => True
  selector := fun _ => referent

/-- Resolving a nominal against a `scope` at context `c` gives the trivalent proposition defined
where a referent is selected and applying `scope` to it there. It is `presupOfReferent` over
`nd.selector c`, so any `presupOfReferent`-built denotation is a `resolve`, by `rfl`. -/
noncomputable def resolve (nd : Nominal Ctx W E) (scope : E → W → Prop) (c : Ctx) :
    W → SignType :=
  presupOfReferent (nd.selector c) scope

/-- An `ofReferent` resolved is exactly the canonical `presupOfReferent` — the
bridge every definite denotation folds across. -/
theorem ofReferent_resolve (referent : W → Option E) (scope : E → W → Prop) :
    (ofReferent referent).resolve scope ⟨⟩ = presupOfReferent referent scope :=
  rfl

open Classical in
/-- The full denotation is `resolve` restricted to where the intrinsic presupposition holds,
the two presuppositions conjoined. For a definite the intrinsic presupposition is vacuous, so
`toTrivalent` and `resolve` agree; for a pronoun the conjoined presupposition is where the
φ-features project. -/
noncomputable def toTrivalent (nd : Nominal Ctx W E) (scope : E → W → Prop) (c : Ctx) :
    W → SignType :=
  {w | nd.presup c w}.indicator (nd.resolve scope c)

section Values

variable {nd : Nominal Ctx W E} {scope : E → W → Prop} {c : Ctx} {w : W}

@[simp] theorem resolve_eq_zero_iff : nd.resolve scope c w = 0 ↔ nd.selector c w = none :=
  presupOfReferent_eq_zero_iff

@[simp] theorem toTrivalent_eq_zero_iff :
    nd.toTrivalent scope c w = 0 ↔ (nd.presup c w → nd.selector c w = none) := by
  simp [toTrivalent]

end Values

/-! ### Monad structure

`Nominal Ctx W` is the presupposition-projecting partiality monad: `bind`
threads the partial referent (`Option.bind`) and accumulates presuppositions,
projecting the continuation's presupposition through definedness of the head
(`Option.elim`). This is what lets a re-selection (e.g. possessive-of) compose
as a Kleisli arrow while a head's intrinsic presupposition (φ-features, deixis)
rides along. -/

instance : Monad (Nominal Ctx W) where
  pure a := { presup := fun _ _ => True, selector := fun _ _ => some a }
  bind nd k :=
    { presup := fun c w =>
        nd.presup c w ∧ (nd.selector c w).elim True (fun e => (k e).presup c w)
      selector := fun c w => (nd.selector c w).bind (fun e => (k e).selector c w) }

/-- A `Nominal` is determined by its presupposition and its selector. -/
@[ext] theorem ext {nd₁ nd₂ : Nominal Ctx W E}
    (hp : nd₁.presup = nd₂.presup) (hs : nd₁.selector = nd₂.selector) : nd₁ = nd₂ := by
  cases nd₁; cases nd₂; cases hp; cases hs; rfl

universe u
variable {α β γ : Type u}

@[simp] theorem pure_selector (a : α) (c : Ctx) (w : W) :
    (pure a : Nominal Ctx W α).selector c w = some a := rfl

@[simp] theorem pure_presup (a : α) (c : Ctx) (w : W) :
    (pure a : Nominal Ctx W α).presup c w = True := rfl

@[simp] theorem bind_selector (nd : Nominal Ctx W α)
    (k : α → Nominal Ctx W β) (c : Ctx) (w : W) :
    (nd >>= k).selector c w = (nd.selector c w).bind (fun e => (k e).selector c w) := rfl

@[simp] theorem bind_presup (nd : Nominal Ctx W α)
    (k : α → Nominal Ctx W β) (c : Ctx) (w : W) :
    (nd >>= k).presup c w =
      (nd.presup c w ∧ (nd.selector c w).elim True (fun e => (k e).presup c w)) := rfl

private theorem bind_pure' (nd : Nominal Ctx W α) : nd >>= pure = nd := by
  ext c w <;>
    simp only [bind_presup, bind_selector, pure_presup, pure_selector] <;>
    cases nd.selector c w <;> simp

/-- In the monad laws left identity feeds a pure referent to its continuation, right identity
re-selects by `pure`, and associativity is what makes possessive nesting
(*John's mother's friend*) free. -/
instance : LawfulMonad (Nominal Ctx W) := LawfulMonad.mk' (Nominal Ctx W)
  (id_map := fun nd ↦ bind_pure' nd)
  (pure_bind := fun a k ↦ by ext c w <;> simp)
  (bind_assoc := fun nd k h ↦ by
    ext c w <;> simp only [bind_presup, bind_selector] <;> cases nd.selector c w <;>
      simp [and_assoc])

end Nominal

/-! ### Characters as nominals -/

namespace Character

variable {C W E : Type*}

/-- A character is a nominal denotation that is total and has no presupposition. -/
def toNominal (χ : Character C W E) : Nominal C W E where
  presup _ _ := True
  selector c w := some (χ c w)

@[simp] theorem toNominal_presup (χ : Character C W E) (c : C) (w : W) :
    χ.toNominal.presup c w = True :=
  rfl

@[simp] theorem toNominal_selector (χ : Character C W E) (c : C) (w : W) :
    χ.toNominal.selector c w = some (χ c w) :=
  rfl

/-- A character is directly referential iff its nominal's selector is rigid at every
context, so that the referent does not vary with the world of evaluation. -/
theorem isDirectlyReferential_iff (χ : Character C W E) :
    χ.IsDirectlyReferential ↔ ∀ c, IsRigid (χ.toNominal.selector c) :=
  forall_congr' fun _ ↦
    ⟨fun h ↦ h.map some, fun h ↦ h.of_comp_injective (Option.some_injective E)⟩

end Character

end Reference
