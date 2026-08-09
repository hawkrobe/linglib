import Mathlib.Logic.Equiv.Defs
import Linglib.Logic.Assignment

/-!
# Cooper (2023) — the TTR apparatus
[cooper-2023]

The book's type-theoretic DSL, shared by the chapter files. TTR's
metatheory is the ambient type theory: the judgment `a : T` is Lean's
native typing, record types are structures, subtyping is `Coe`, truth
is inhabitation, meet and join are `Prod` and `Sum`. This file keeps
the book's *names* for that identification plus the apparatus with
genuinely Cooper-specific content: intensional named types (`IType`,
§1.3), parametric — presuppositional — content (`Parametric`, §4.3),
and the compositional entries of §3.4 and §5.6.
-/

namespace Cooper2023.TTR

/-! ### Truth as inhabitation (§1.5) -/

/-- A TTR type is "true" (inhabited). §1.5. -/
abbrev IsTrue (T : Type) : Prop := Nonempty T

/-- A TTR type is "false" (empty). -/
abbrev IsFalse (T : Type) : Prop := IsEmpty T

/-- Truth and falsity are exclusive. -/
theorem true_false_exclusive (T : Type) : ¬ (IsTrue T ∧ IsFalse T) := by
  intro ⟨⟨t⟩, hE⟩
  exact hE.false t

/-- Lift a proposition to a type. Alias for `PLift`. -/
abbrev propT (p : Prop) : Type := PLift p

/-! ### Intensional types (§1.3)

Types are intensional: "there is nothing which prevents two types from
being associated with exactly the same set of objects". A name-tagged
wrapper makes the identity-beyond-extension explicit — the
`groundhog` ~ `woodchuck` distinction: same animals, different types. -/

/-- An intensional type: a named type that carries identity beyond its
extension (§1.3). -/
structure IType where
  /-- The underlying Lean type (extension carrier) -/
  carrier : Type
  /-- Intensional identity tag (e.g., a predicate name) -/
  name : String
  deriving Repr

/-- Two ITypes are extensionally equivalent when their carriers are
equivalent. -/
def IType.extEquiv (T₁ T₂ : IType) : Prop := Nonempty (T₁.carrier ≃ T₂.carrier)

/-- Two ITypes are intensionally identical when both name and carrier
match. -/
def IType.intEq (T₁ T₂ : IType) : Prop := T₁ = T₂

/-- Meet of intensional types: compose carriers and names. -/
def IType.meet (T₁ T₂ : IType) : IType where
  carrier := T₁.carrier × T₂.carrier
  name := T₁.name ++ " ∧ " ++ T₂.name

/-- Join of intensional types: sum carriers and compose names. -/
def IType.join (T₁ T₂ : IType) : IType where
  carrier := Sum T₁.carrier T₂.carrier
  name := T₁.name ++ " ∨ " ++ T₂.name

/-- Core TTR thesis: extensional equivalence does not entail intensional
identity — types are not sets. -/
theorem ext_equiv_not_implies_int_eq :
    ¬ (∀ T₁ T₂ : IType, T₁.extEquiv T₂ → T₁.intEq T₂) := by
  intro h
  have := h ⟨Bool, "groundhog"⟩ ⟨Bool, "woodchuck"⟩ ⟨Equiv.refl Bool⟩
  simp only [IType.intEq, IType.mk.injEq] at this
  exact absurd this.2 (by decide)

/-! ### Meet and join types (§2.3.3, Def 97) -/

/-- Meet type: `a : T₁ ∧ T₂` iff `a : T₁` and `a : T₂` — Lean's `Prod`. -/
abbrev MeetType (T₁ T₂ : Type) := T₁ × T₂

/-- Join type: `a : T₁ ∨ T₂` iff `a : T₁` or `a : T₂` — Lean's `Sum`. -/
abbrev JoinType (T₁ T₂ : Type) := Sum T₁ T₂

/-- Join preserves truth in both directions. -/
theorem join_true_iff {T₁ T₂ : Type} :
    IsTrue (JoinType T₁ T₂) ↔ IsTrue T₁ ∨ IsTrue T₂ :=
  ⟨λ ⟨s⟩ => match s with | .inl a => Or.inl ⟨a⟩ | .inr b => Or.inr ⟨b⟩,
   λ h => h.elim (λ ⟨a⟩ => ⟨Sum.inl a⟩) (λ ⟨b⟩ => ⟨Sum.inr b⟩)⟩

/-! ### Record-type subtyping (§1.4.3.5, ex 53)

A record type with more fields is a subtype of one with fewer fields
(more constraints, fewer witnesses); the projection is the
`extends`-generated forgetful map. -/

/-- ex (53) target: `[x:Ind, c₁:boy(x), y:Ind, c₂:dog(y)]`. -/
structure BoyAndDog (E : Type) (Boy Dog : E → Prop) where
  x : E
  c₁ : Boy x
  y : E
  c₂ : Dog y

/-- ex (53) source: the subtype with the additional `hug` field. -/
structure BoyHugsDog (E : Type) (Boy Dog : E → Prop) (Hug : E → E → Prop)
    extends BoyAndDog E Boy Dog where
  evt : Hug x y

/-! ### Modal type systems (Def 54) -/

/-- A modal type system: for each possibility and predicate, whether the
predicate has witnesses. Def 54; structurally a Kripke model. -/
abbrev ModalTypeSystem (W : Type) (Pred : Type) := W → Pred → Bool

/-! ### Compositional semantics (§3.4)

The semantic type hierarchy: `Ppty` and `Quant` are the TTR analogues
of Montague's ⟨e,t⟩ and ⟨⟨e,t⟩,t⟩. -/

/-- A property type: maps an individual to a type of situations.
§3.4, ex (30). -/
abbrev Ppty (E : Type) := E → Type

/-- A quantifier type: maps a property to a type. §3.4. -/
abbrev Quant (E : Type) := Ppty E → Type

/-- Common noun content: wrap a predicate as a property. §3.4, ex (30). -/
def semCommonNoun {E : Type} (p : E → Type) : Ppty E := p

/-- Proper name content as a generalized quantifier. §3.4, ex (33). -/
def semPropName {E : Type} (a : E) : Quant E := λ P => P a

/-- The existential witness record type. §3.4, ex (37). -/
structure ExistWitness (E : Type) (restr scope : Ppty E) where
  individual : E
  restrWit : restr individual
  scopeWit : scope individual

/-- Indefinite article content: maps a restrictor property to a
quantifier. §3.4, ex (37). -/
def semIndefArt {E : Type} (restr : Ppty E) : Quant E :=
  λ scope => ExistWitness E restr scope

/-- Copula "be" for predicate nominal constructions. §3.4, ex (78). -/
def semBe {E : Type} (Q : Quant E) : Ppty E :=
  λ x => Q (λ y => propT (x = y))

/-- Existential quantification as property-extension overlap. §3.4,
ex (55). -/
def existPQ {E : Type} (P Q : Ppty E) : Prop :=
  ∃ a : E, Nonempty (P a) ∧ Nonempty (Q a)

/-- Universal quantifier as a type. §5.6. -/
def semUniversal {E : Type} (restr scope : Ppty E) : Type :=
  (x : E) → restr x → scope x

/-! ### Parametric content (§4.2–4.3)

Content that depends on a context: a background type (the
presupposition) paired with a foreground function from satisfying
contexts to content. -/

/-- Parametric content. §4.3, (14). -/
structure Parametric (Content : Type*) where
  /-- Background type — what the context must provide (presupposition) -/
  Bg : Type*
  /-- Foreground — content given a context satisfying the background -/
  fg : Bg → Content

/-- Parametric property: context-dependent property. -/
abbrev PPpty (E : Type) := Parametric (Ppty E)

/-- A trivial parametric content: no presupposition (bg = Unit). -/
def Parametric.trivial {Content : Type*} (c : Content) : Parametric Content :=
  ⟨Unit, λ _ => c⟩

/-- A trivial parametric content yields the same value for any context. -/
theorem Parametric.trivial_fg {Content : Type*} (c : Content) (u : Unit) :
    (Parametric.trivial c).fg u = c := rfl

/-! ### Assignments (§4.6) -/

/-- Variable assignment: maps natural-number indices to individuals.
    Equal to `PartialAssign E`; the alias name is retained because
    the book's prose uses 𝔰/𝔩/𝔯/𝔴/𝔤 as named "assignments" rather than
    as partial functions, and the inheritance carries the
    `valued`/`valued_update_at` simp set into this file's consumers. -/
abbrev Assgnmnt (E : Type) := PartialAssign E

/-- An assignment with at least n bindings (all indices < n defined). -/
def Assgnmnt.hasBindings {E : Type} (g : Assgnmnt E) (n : Nat) : Prop :=
  ∀ i, i < n → (g i).isSome = true

/-- Merge two assignments (left-biased). -/
def Assgnmnt.merge {E : Type} (g₁ g₂ : Assgnmnt E) : Assgnmnt E :=
  λ i => (g₁ i).orElse (λ _ => g₂ i)

/-- Merge with empty on the left returns the right assignment. -/
theorem Assgnmnt.merge_empty_left {E : Type} (g : Assgnmnt E) :
    Assgnmnt.merge PartialAssign.empty g = g := by
  funext i; simp [Assgnmnt.merge, PartialAssign.empty, Option.orElse]

/-- Propositional context. -/
abbrev PropCntxt := Type

end Cooper2023.TTR
