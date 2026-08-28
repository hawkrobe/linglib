import Mathlib.Tactic.DeriveFintype
import Linglib.Data.Examples.Asudeh2022

/-!
# Asudeh 2022: Glue Semantics

Meanings are assembled by proof search in the implicational fragment of linear logic. A word
contributes meaning constructors `M : G`, a lambda term paired with a linear-logic formula whose
atoms are instantiated from the syntactic parse; implication elimination is functional
application and implication introduction functional abstraction, by Curry–Howard. Because the
logic lacks weakening and contraction, all and only the instantiated premises are consumed —
resource-sensitive composition, which subsumes bounded closure, Completeness and Coherence, the
Theta Criterion and their kin — and because it is commutative, word order does not determine
composition: the arguments of a head can be recurried by hypothetical reasoning. Syntax is
therefore autonomous and need not be isomorphic to semantics: Finnish *join vettä* and English
*I drank water* instantiate the same three premises from two and three words, and *Everybody
loves somebody* is syntactically unambiguous yet has two normal-form proofs, differing only in
the order in which the two hypotheses are discharged, which evaluate to the two scope readings
without quantifier raising or type shifting.

## Main definitions

* `GlueTy`, `Term`: linear-logic types over instantiated atoms, and intrinsically typed proofs
  with `Term.Linear` for exactly-once use of premises and hypotheses.
* `GlueTy.denote`, `Env`, `Term.eval`: the Curry–Howard evaluation of a proof into a meaning.
* `Logic.rules`, `resource_iff`: the substructural hierarchy and its resource logics.
* `recurry`, `finnish`, `english`, `surface`, `inverse`: the paper's proofs and lexicons.

## References

* [asudeh-2022]
* [girard-1987] — linear logic
* [klein-sag-1985] — bounded closure
* [kaplan-bresnan-1982] — Completeness and Coherence
* [heim-kratzer-1998] — the interpretive rival
-/

namespace Asudeh2022

open Data.Examples

/-! ### The Glue logic -/

/-- Formulas of the implicational fragment of linear logic over instantiated atoms. -/
inductive GlueTy (α : Type*)
  | atom (a : α)
  | lolli (A B : GlueTy α)
  deriving DecidableEq, Repr

infixr:25 " ⊸ " => GlueTy.lolli

variable {α : Type*}

/-- A proof in a context of premises, as a linear λ-term: a variable refers to a context
    position, application is implication elimination, and abstraction appends its hypothesis
    to the context and discharges it. -/
inductive Term : List (GlueTy α) → GlueTy α → Type _
  | var {Γ : List (GlueTy α)} (n : ℕ) {T : GlueTy α} (h : Γ[n]? = some T) : Term Γ T
  | app {Γ : List (GlueTy α)} {A B : GlueTy α} : Term Γ (A ⊸ B) → Term Γ A → Term Γ B
  | lam {Γ : List (GlueTy α)} (A : GlueTy α) {B : GlueTy α} : Term (Γ ++ [A]) B → Term Γ (A ⊸ B)

/-- The context positions a proof uses, with repetition. -/
def Term.uses {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → List ℕ
  | .var n _ => [n]
  | .app f a => f.uses ++ a.uses
  | .lam _ b => b.uses

/-- Every hypothesis is used exactly once. -/
def Term.HypLinear {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → Prop
  | .var _ _ => True
  | .app f a => f.HypLinear ∧ a.HypLinear
  | .lam _ b => b.uses.count Γ.length = 1 ∧ b.HypLinear

instance Term.decHypLinear {Γ : List (GlueTy α)} {T : GlueTy α} :
    (t : Term Γ T) → Decidable t.HypLinear
  | .var _ _ => isTrue trivial
  | .app f a => @instDecidableAnd _ _ (decHypLinear f) (decHypLinear a)
  | .lam _ b => @instDecidableAnd _ _ inferInstance (decHypLinear b)

/-- A proof consumes every premise and every hypothesis exactly once: no weakening and no
    contraction. -/
def Term.Linear {Γ : List (GlueTy α)} {T : GlueTy α} (t : Term Γ T) : Prop :=
  (∀ i < Γ.length, t.uses.count i = 1) ∧ t.HypLinear

instance {Γ : List (GlueTy α)} {T : GlueTy α} (t : Term Γ T) : Decidable t.Linear :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Curry–Howard evaluation -/

variable (D : α → Type)

/-- The type of meanings a formula pairs with. -/
def GlueTy.denote : GlueTy α → Type
  | .atom a => D a
  | .lolli A B => A.denote → B.denote

/-- Meanings for the premises of a context. -/
inductive Env : List (GlueTy α) → Type _
  | nil : Env []
  | cons {T : GlueTy α} {Γ : List (GlueTy α)} : T.denote D → Env Γ → Env (T :: Γ)

variable {D}

/-- The meaning at a context position. -/
def Env.get : {Γ : List (GlueTy α)} → Env D Γ → (n : ℕ) → {T : GlueTy α} →
    Γ[n]? = some T → T.denote D
  | _, .cons v _, 0, _, h => (Option.some.inj h) ▸ v
  | _, .cons _ ρ, n + 1, _, h => ρ.get n h

/-- Extend the meanings by one for a hypothesis. -/
def Env.snoc {T : GlueTy α} : {Γ : List (GlueTy α)} → Env D Γ → T.denote D → Env D (Γ ++ [T])
  | _, .nil, v => .cons v .nil
  | _, .cons u ρ, v => .cons u (ρ.snoc v)

/-- The meaning a proof assembles: application for elimination, abstraction for introduction. -/
def Term.eval {Γ : List (GlueTy α)} {T : GlueTy α} : Term Γ T → Env D Γ → T.denote D
  | .var n h, ρ => ρ.get n h
  | .app f a, ρ => f.eval ρ (a.eval ρ)
  | .lam _ b, ρ => λ v => b.eval (ρ.snoc v)

/-! ### The substructural hierarchy -/

/-- The structural rules whose presence or absence characterizes a logic. -/
inductive StructuralRule
  | weakening
  | contraction
  | commutativity
  deriving DecidableEq

/-- The logics of the hierarchy. -/
inductive Logic
  | lambek
  | linear
  | relevance
  | affine
  | intuitionistic
  deriving DecidableEq, Fintype

/-- The rules each logic admits: Lambek's L none, linear logic commutativity, relevance logic
    contraction as well, affine logic weakening instead, intuitionistic logic all three. -/
def Logic.rules : Logic → List StructuralRule
  | .lambek => []
  | .linear => [.commutativity]
  | .relevance => [.commutativity, .contraction]
  | .affine => [.commutativity, .weakening]
  | .intuitionistic => [.commutativity, .contraction, .weakening]

/-- A resource logic admits neither weakening nor contraction. -/
def Logic.Resource (l : Logic) : Prop := .weakening ∉ l.rules ∧ .contraction ∉ l.rules

instance (l : Logic) : Decidable l.Resource := inferInstanceAs (Decidable (_ ∧ _))

/-- The resource logics are Lambek's L and linear logic. -/
theorem resource_iff : ∀ l : Logic, l.Resource ↔ l = .lambek ∨ l = .linear := by decide

/-- Linear logic is the commutative resource logic: the logic of composition. -/
theorem commutative_resource_iff :
    ∀ l : Logic, l.Resource ∧ .commutativity ∈ l.rules ↔ l = .linear := by
  decide

/-! ### The paper's proofs -/

/-- The instantiated atoms of the paper's examples. -/
inductive Label
  | a | b | c | l | e | s | p | w | d
  deriving DecidableEq, Repr

open GlueTy (atom)

/-- *Alex likes Blake*: the head consumes its arguments in either order. -/
def likes : List (GlueTy Label) :=
  [atom Label.b ⊸ atom Label.a ⊸ atom Label.l, atom Label.a, atom Label.b]

/-- The single normal-form proof: apply *likes* to *Blake*, then to *Alex*. -/
def likesProof : Term likes (atom Label.l) :=
  .app (.app (.var 0 rfl) (.var 2 rfl)) (.var 1 rfl)

theorem likesProof_linear : likesProof.Linear := by decide

/-- Recurrying by hypothetical reasoning: from a head taking `a` then `b`, a proof taking `b`
    then `a`, with both hypotheses discharged. -/
def recurry :
    Term [atom Label.a ⊸ atom Label.b ⊸ atom Label.c]
      (atom Label.b ⊸ atom Label.a ⊸ atom Label.c) :=
  .lam (atom Label.b) (.lam (atom Label.a) (.app (.app (.var 0 rfl) (.var 2 rfl)) (.var 1 rfl)))

theorem recurry_linear : recurry.Linear := by decide

/-- The recurried proof means the same function with its arguments swapped. -/
theorem recurry_eval {D : Label → Type} (f : D .a → D .b → D .c) :
    recurry.eval (.cons f .nil) = λ u v => f v u :=
  rfl

/-- The meaning constructors each Finnish word contributes: *join* the speaker and the drinking,
    *vettä* the water. -/
def finnish : List (List (GlueTy Label)) :=
  [[atom Label.p, atom Label.w ⊸ atom Label.p ⊸ atom Label.d], [atom Label.w]]

/-- The English words contribute the same three constructors one each. -/
def english : List (List (GlueTy Label)) :=
  [[atom Label.p], [atom Label.w ⊸ atom Label.p ⊸ atom Label.d], [atom Label.w]]

/-- Two words and three words instantiate the same premises. -/
theorem finnish_english : finnish.flatten = english.flatten ∧ finnish.length ≠ english.length :=
  by decide

/-- The one normal-form proof of *I drank water* in either language. -/
def drinkProof : Term english.flatten (atom Label.d) :=
  .app (.app (.var 1 rfl) (.var 2 rfl)) (.var 0 rfl)

theorem drinkProof_linear : drinkProof.Linear := by decide

/-- *Everybody loves somebody* with both quantifiers' scope instantiated to the clause. -/
def loves : List (GlueTy Label) :=
  [atom Label.s ⊸ atom Label.e ⊸ atom Label.l, (atom Label.e ⊸ atom Label.l) ⊸ atom Label.l,
    (atom Label.s ⊸ atom Label.l) ⊸ atom Label.l]

/-- Surface scope: hypothesize the object, then the subject; discharge the object under *some*
    and the subject under *every*. -/
def surface : Term loves (atom Label.l) :=
  .app (.var 1 rfl) (.lam (atom Label.e)
    (.app (.var 2 rfl) (.lam (atom Label.s) (.app (.app (.var 0 rfl) (.var 4 rfl)) (.var 3 rfl)))))

/-- Inverse scope: the subject is discharged first, under *every*, and the object under
    *some*. -/
def inverse : Term loves (atom Label.l) :=
  .app (.var 2 rfl) (.lam (atom Label.s)
    (.app (.var 1 rfl) (.lam (atom Label.e) (.app (.app (.var 0 rfl) (.var 3 rfl)) (.var 4 rfl)))))

theorem surface_linear : surface.Linear := by decide

theorem inverse_linear : inverse.Linear := by decide

/-- Meanings for the scope example: entities for the two argument positions, propositions for
    the clause. -/
def scopeDomain (E : Type) : Label → Type
  | .l | .c | .d => Prop
  | _ => E

/-- The premises' meanings: *love*, and the two generalized quantifiers over persons. -/
def scopeEnv {E : Type} (person : E → Prop) (love : E → E → Prop) : Env (scopeDomain E) loves :=
  .cons love (.cons (λ Q => ∀ x, person x → Q x) (.cons (λ Q => ∃ y, person y ∧ Q y) .nil))

/-- The surface proof means that every person loves some person. -/
theorem surface_eval {E : Type} (person : E → Prop) (love : E → E → Prop) :
    surface.eval (scopeEnv person love) =
      ∀ x, person x → ∃ y, person y ∧ love y x :=
  rfl

/-- The inverse proof means that some person is loved by every person. -/
theorem inverse_eval {E : Type} (person : E → Prop) (love : E → E → Prop) :
    inverse.eval (scopeEnv person love) =
      ∃ y, person y ∧ ∀ x, person x → love y x :=
  rfl

/-- The two proofs are two readings: where each of two persons loves only the other, the surface
    reading holds and the inverse one fails. -/
theorem readings_differ :
    surface.eval (scopeEnv (λ _ : Bool => True) (· ≠ ·)) ∧
      ¬ inverse.eval (scopeEnv (λ _ : Bool => True) (· ≠ ·)) := by
  rw [surface_eval, inverse_eval]
  exact ⟨λ x _ => ⟨!x, trivial, Bool.not_ne_self x⟩, λ ⟨y, _, h⟩ => h y trivial rfl⟩

/-! ### The paper's examples -/

/-- The meaning constructors a row's words contribute. -/
def lexicon? (r : LinguisticExample) : Option (List (List (GlueTy Label))) :=
  match r.language, r.feature? "premises" with
  | "finn1318", some "speaker, drink, water" => some finnish
  | "stan1293", some "speaker, drink, water" => some english
  | _, _ => none

/-- Each word of the drinking sentences contributes its constructors, and the two lexicons
    instantiate the premises of the same proof. -/
theorem rows_lexicon :
    ∀ r ∈ Examples.all, ∀ lex ∈ lexicon? r,
      r.surfaceTokens.length = lex.length ∧ lex.flatten = english.flatten := by
  decide

end Asudeh2022
