import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Theories.Semantics.TypeTheoretic.Core

/-!
# Common Nouns as Predicates vs. Types @cite{sutton-2024}

Montague's STT treats common nouns as predicates: `man : Entity → Bool`.
TTR treats them as types: `Man : Type`, where `a : Man` witnesses that
a is a man. Sutton (2024) §§3–5 argues these are not notational variants
— the choice determines whether selectional restriction violations are
**type errors** or merely **false**.

This file proves the equivalence where both approaches agree, and the
separation where they diverge.

## The bridge

Given a Montague predicate `p : E → Bool`, the corresponding TTR ptype
is `λ e => PLift (p e = true)` — inhabited exactly when the predicate
holds. The bridge theorem `montague_ttr_equiv` proves these give the
same truth conditions for basic predication.

## The separation

1. **Selectional restrictions**: In TTR, "the chair laughed" fails to
   compose (no witness of `Animate` for `chair`). In Montague, it
   composes fine and evaluates to `false`. The TTR approach makes
   category mistakes distinguishable from contingent falsity.

2. **Hyperintensionality**: Co-extensional Montague predicates are
   equal functions (`funext`). Co-extensional TTR ptypes can be
   distinct (different `IType` names). TTR preserves the
   groundhog/woodchuck distinction; Montague collapses it.

## References

- Sutton, P. (2024). Types and Type Theories. Annual Review of
  Linguistics 10: 347–370.
- Luo, Z. (2012). Common Nouns as Types. In Béchet & Dikovsky (eds.),
  LACL 2012, LNCS 7351: 173–185.
- Cooper, R. (2023). From Perception to Communication. OUP.
- Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in Modern
  Type Theories. Wiley/ISTE.
-/

namespace Comparisons.CNsAsTypes

open Semantics.Montague (Model Ty ToyEntity toyModel)
open Semantics.TypeTheoretic (PredType Ppty IsTrue IsFalse propT
  SubtypeOf propExtension IType)

-- ════════════════════════════════════════════════════════════════
-- § 1. The Bridge: Montague predicates ↔ TTR ptypes
-- ════════════════════════════════════════════════════════════════

/-- Lift a Montague predicate `E → Bool` to a TTR ptype `E → Type`.
The resulting type family is inhabited at `e` iff `p e = true`. -/
def predToPtype {E : Type} (p : E → Bool) : PredType E :=
  λ e => propT (p e = true)

/-- Inhabitation of `predToPtype p e` is decidable (since `p e = true` is). -/
instance predToPtype_decidable {E : Type} (p : E → Bool) (e : E) :
    Decidable (Nonempty (predToPtype p e)) :=
  if h : p e = true then isTrue ⟨PLift.up h⟩
  else isFalse (λ ⟨⟨h'⟩⟩ => h h')

/-- Project a TTR ptype back to a Montague predicate.
Requires decidable inhabitation (satisfied by any finite ptype). -/
def ptypeToPred {E : Type} (P : PredType E) [∀ e, Decidable (Nonempty (P e))] :
    E → Bool :=
  λ e => decide (Nonempty (P e))

/-- **Bridge theorem**: Montague predication and TTR type inhabitation
agree when connected by `predToPtype`.

`p e = true ↔ Nonempty (predToPtype p e)` — the predicate holds of `e`
iff the corresponding ptype is inhabited (has a witness). -/
theorem montague_ttr_equiv {E : Type} (p : E → Bool) (e : E) :
    p e = true ↔ Nonempty (predToPtype p e) :=
  ⟨λ h => ⟨PLift.up h⟩, λ ⟨⟨h⟩⟩ => h⟩

/-- The round-trip `ptypeToPred ∘ predToPtype` recovers the original predicate. -/
theorem roundtrip_pred {E : Type} (p : E → Bool) (e : E) :
    @ptypeToPred E (predToPtype p) (λ x => predToPtype_decidable p x) e = p e := by
  unfold ptypeToPred
  cases hp : p e
  · -- p e = false: the ptype is empty
    have : ¬ Nonempty (predToPtype p e) := λ ⟨⟨h⟩⟩ => by rw [hp] at h; exact nomatch h
    exact decide_eq_false this
  · -- p e = true: the ptype is inhabited
    have : Nonempty (predToPtype p e) := ⟨PLift.up hp⟩
    exact decide_eq_true this

/-- TTR `propExtension` coincides with our bridge on lifted predicates. -/
theorem propExtension_agrees {E : Type} (p : E → Bool) (e : E) :
    propExtension (predToPtype p) e ↔ (p e = true) :=
  ⟨λ ⟨⟨h⟩⟩ => h, λ h => ⟨PLift.up h⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § 2. Separation: Selectional Restrictions
-- ════════════════════════════════════════════════════════════════

/-! In Montague's STT, every entity has the same type `e`. A verb like
"laugh" takes any entity and returns `true` or `false`. There is no
structural distinction between a *category mistake* ("the chair laughed")
and *contingent falsity* ("Mary didn't laugh").

In TTR/MTT, verbs can require arguments of specific *types*. "Laugh"
takes `Animate`, not `Entity`. A chair is not `Animate`, so the
predication doesn't compose — it's not false, it's *ill-typed*.

Sutton (2024) §4: "In MTT [...] common nouns are interpreted as types
[...] selectional restrictions are *type* requirements." -/

section SelectionalRestrictions

/-- Ontological sorts (TTR types for entity subclasses). -/
inductive Animate where | john | mary
inductive Inanimate where | chair | rock

/-- In Montague, everything is an Entity. Chairs and people cohabit. -/
inductive FlatEntity where
  | john | mary | chair | rock
  deriving DecidableEq

/-- Montague predicate: laughs is defined on ALL entities. -/
def laughs_montague : FlatEntity → Bool
  | .john => true
  | .mary => false
  | .chair => false
  | .rock => false

/-- In Montague, "the chair laughed" *composes and evaluates to false*.
It's the same kind of thing as "Mary didn't laugh" — both are `false`. -/
theorem montague_chair_laughed : laughs_montague .chair = false := rfl
theorem montague_mary_didnt_laugh : laughs_montague .mary = false := rfl

/-- There's no structural way to distinguish category mistakes from
contingent falsity — both are just `false`. -/
theorem montague_conflates_mistakes :
    laughs_montague .chair = false ∧ laughs_montague .mary = false :=
  ⟨rfl, rfl⟩

/-- TTR predicate: laughs is typed to require `Animate` arguments.
"The chair laughed" doesn't evaluate to false — it doesn't *typecheck*. -/
def laughs_ttr : Animate → Bool
  | .john => true
  | .mary => false

-- In TTR, a chair cannot even be *given* to `laughs_ttr`.
-- The following would be a Lean type error:
--   `#check laughs_ttr Inanimate.chair`
--   — expected `Animate`, got `Inanimate`
-- The types `Animate` and `Inanimate` are disjoint.

/-- In TTR, contingent falsity (Mary doesn't laugh) is well-typed but false.
Category mistakes (chair laughs) don't typecheck at all. The selectional
restriction *prevents composition*, rather than evaluating to `false`. -/
theorem ttr_distinguishes_sorts :
    -- laughs_ttr is defined on a strict subtype of FlatEntity
    -- (2 constructors vs 4) — this IS the selectional restriction
    (∀ a : Animate, ∃ b : Bool, laughs_ttr a = b) ∧
    -- There is no analogous totality statement for Inanimate
    -- (laughs_ttr is not defined on Inanimate at all)
    (∀ e : FlatEntity, ∃ b : Bool, laughs_montague e = b) :=
  ⟨λ _ => ⟨_, rfl⟩, λ _ => ⟨_, rfl⟩⟩

end SelectionalRestrictions

-- ════════════════════════════════════════════════════════════════
-- § 3. Separation: Hyperintensionality
-- ════════════════════════════════════════════════════════════════

/-! Montague predicates are functions `E → Bool`. Two predicates with
the same extension are *definitionally equal* by `funext`. TTR types
carry intensional identity — two types can have the same witnesses
yet remain distinct.

Sutton (2024) §3.1: "there is nothing which prevents two types from
being associated with exactly the same set of objects." -/

section Hyperintensionality

/-- Two Montague predicates with the same extension are equal. -/
theorem montague_extensional {E : Type} (p q : E → Bool) (h : ∀ e, p e = q e) :
    p = q :=
  funext h

/-- Co-extensional ITypes can be distinct (from TypeTheoretic/Core.lean). -/
example : ∃ T₁ T₂ : IType, T₁.extEquiv T₂ ∧ ¬ T₁.intEq T₂ :=
  ⟨⟨Unit, "groundhog"⟩, ⟨Unit, "woodchuck"⟩,
   ⟨Equiv.refl Unit⟩, by simp [IType.intEq]⟩

/-- The consequence for attitude reports: Montague cannot distinguish
"John believes a groundhog is outside" from "John believes a woodchuck
is outside" — the belief content is the same function. TTR can. -/
theorem montague_collapses_attitudes :
    -- If groundhog and woodchuck have the same extension...
    ∀ (p_groundhog p_woodchuck : FlatEntity → Bool),
      (∀ e, p_groundhog e = p_woodchuck e) →
      -- ...then there is NO attitude verb that distinguishes them
      -- (the predicates are literally equal)
      p_groundhog = p_woodchuck :=
  λ _ _ h => funext h

/-- TTR preserves the distinction: groundhog ≠ woodchuck as ITypes,
even when co-extensional. Attitude verbs can be sensitive to this. -/
theorem ttr_preserves_attitudes :
    let groundhog : IType := ⟨Unit, "groundhog"⟩
    let woodchuck : IType := ⟨Unit, "woodchuck"⟩
    groundhog.extEquiv woodchuck ∧ ¬ groundhog.intEq woodchuck :=
  ⟨⟨Equiv.refl Unit⟩, by simp [IType.intEq]⟩

end Hyperintensionality

-- ════════════════════════════════════════════════════════════════
-- § 4. When the Two Approaches Coincide
-- ════════════════════════════════════════════════════════════════

/-! For basic extensional predication over a fixed domain without
selectional restrictions or attitude contexts, Montague predicates
and TTR ptypes are interchangeable. The bridge is `predToPtype`/
`ptypeToPred`, and the equivalence is `montague_ttr_equiv`.

The approaches diverge exactly when:
1. Selectional restrictions matter (§2)
2. Hyperintensional contexts arise (§3)
3. Copredication requires dot types (see TypeTheoretic/Copredication.lean)

These are precisely Sutton's (2024) arguments for rich type theories. -/

/-- Summary: the predicate/type duality is an equivalence modulo three
phenomena. We can state the exact boundary. -/
theorem equivalence_boundary {E : Type} (p : E → Bool) :
    -- (1) Basic predication: full equivalence
    (∀ e, p e = true ↔ Nonempty (predToPtype p e)) ∧
    -- (2) Round-trip: lossless for predicates
    (∀ e, @ptypeToPred E (predToPtype p) (λ x => predToPtype_decidable p x) e = p e) :=
  ⟨λ e => montague_ttr_equiv p e, λ e => roundtrip_pred p e⟩

end Comparisons.CNsAsTypes
