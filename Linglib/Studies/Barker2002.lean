import Linglib.Semantics.Quantification.Defs
import Linglib.Semantics.Composition.Cont
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Linglib.Data.Examples.Barker2002

/-!
# Barker 2002: continuations and the nature of quantification

Quantificational noun phrases denote functions on their own continuations. Continuizing an
ordinary grammar hands every constituent its continuation, so that noun phrases come out as
generalized quantifiers, *everyone* and *someone* can be stated in situ, and their scope
falls out of the truth conditions rather than from movement, storage or type-shifting.
Each rule of arity two continuizes in two ways, one per priority order of its daughters,
which is where scope ambiguity comes from; making the clause an island is a matter of
handing the clause's continuation the finished clause. The paper's Simulation Theorem says
that on quantifier-free derivations the continuized grammar computes what the direct one
did, and its Integrity constraint that a constituent's quantifiers scope together, which
leaves *someone saw a friend of everyone* four readings instead of six. Generalized
coordination distributes the continuation over the conjuncts, with no polymorphic *and*.

Derivations are trees over the direct grammar with each binary node marked for priority;
the schema is `Deriv.continuize`, the direct meaning `Deriv.direct`, and the scope order a
prioritized derivation induces `Deriv.scopeOrder`. Transitive verbs take the object first,
so `saw m j` is *John saw Mary*.

## References

* [barker-2002]
* [montague-1973]
* [partee-rooth-1983]
* [heim-kratzer-1998]
-/

namespace Barker2002

open Quantification (Quantifier individual)

variable {α β γ E : Type}

/-! ### Derivations and the Continuation Schema -/

/-- A derivation: a lexical item of the direct grammar, a quantificational item stated only
in continuized terms, a rule of arity one or two applied to its daughters (a binary node
marked with which daughter takes priority), a clause closed off as a scope island, or a
coordination. -/
inductive Deriv : Type → Type 1
  | lex {α : Type} (a : α) : Deriv α
  | quant {α : Type} (label : String) (q : Cont Prop α) : Deriv α
  | unary {α β : Type} (M : α → β) (d : Deriv α) : Deriv β
  | binary {α β γ : Type} (M : α → β → γ) (first : Bool) (d₁ : Deriv α) (d₂ : Deriv β) :
      Deriv γ
  | island (d : Deriv Prop) : Deriv Prop
  | coord {α : Type} (d₁ d₂ : Deriv α) : Deriv α

namespace Deriv

/-- The Continuation Schema: a lexical item is a unit, a rule nests its daughters'
continuations in priority order, an island evaluates its clause, and coordination
distributes the continuation over the conjuncts. -/
def continuize : ∀ {α : Type}, Deriv α → Cont Prop α
  | _, lex a => pure a
  | _, quant _ q => q
  | _, unary M d => M <$> d.continuize
  | _, binary M true d₁ d₂ => M <$> d₁.continuize <*> d₂.continuize
  | _, binary M false d₁ d₂ => flip M <$> d₂.continuize <*> d₁.continuize
  | _, island d => ContT.reset d.continuize
  | _, coord d₁ d₂ => λ k => d₁.continuize k ∧ d₂.continuize k

/-- The meaning the direct grammar assigns, where it assigns one. -/
def direct : ∀ {α : Type}, Deriv α → Option α
  | _, lex a => some a
  | _, quant _ _ => none
  | _, unary M d => d.direct.map M
  | _, binary M _ d₁ d₂ => d₁.direct.bind λ x => d₂.direct.map (M x)
  | _, island d => d.direct
  | _, coord _ _ => none

/-- The quantificational items in the order they take scope; an island's are trapped. -/
def scopeOrder : ∀ {α : Type}, Deriv α → List String
  | _, lex _ => []
  | _, quant l _ => [l]
  | _, unary _ d => d.scopeOrder
  | _, binary _ true d₁ d₂ => d₁.scopeOrder ++ d₂.scopeOrder
  | _, binary _ false d₁ d₂ => d₂.scopeOrder ++ d₁.scopeOrder
  | _, island _ => []
  | _, coord d₁ d₂ => d₁.scopeOrder ++ d₂.scopeOrder

/-- The lemma behind the Simulation Theorem: a derivation the direct grammar interprets
hands any continuation its direct meaning. -/
theorem continuize_run {d : Deriv α} {a : α} (h : d.direct = some a) (k : α → Prop) :
    d.continuize.run k = k a := by
  induction d with
  | lex b => simp only [direct, Option.some.injEq] at h; subst h; rfl
  | quant => simp [direct] at h
  | unary M d ih =>
    simp only [direct, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact ih hb _
  | binary M first d₁ d₂ ih₁ ih₂ =>
    simp only [direct, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h
    cases first
    · exact (ih₂ hb₂ _).trans (ih₁ hb₁ _)
    · exact (ih₁ hb₁ _).trans (ih₂ hb₂ _)
  | island d ih => exact congrArg k (ih h id)
  | coord => simp [direct] at h

/-- The Simulation Theorem: at the trivial continuation the continuized grammar computes the
direct meaning. -/
theorem eval_continuize {d : Deriv Prop} {p : Prop} (h : d.direct = some p) :
    ContT.eval d.continuize = p :=
  continuize_run h id

/-- The sentence meaning: the continuized meaning at the trivial continuation. -/
def eval (d : Deriv Prop) : Prop := ContT.eval d.continuize

/-- Integrity: a daughter's quantifiers scope together, before or after the other
daughter's. -/
theorem scopeOrder_binary (M : α → β → γ) (first : Bool) (d₁ : Deriv α) (d₂ : Deriv β) :
    (binary M first d₁ d₂).scopeOrder = d₁.scopeOrder ++ d₂.scopeOrder ∨
      (binary M first d₁ d₂).scopeOrder = d₂.scopeOrder ++ d₁.scopeOrder := by
  cases first <;> simp [scopeOrder]

end Deriv

/-! ### The fragment -/

open Deriv

/-- S → NP VP, `VP(NP)`; `first` gives the subject priority. -/
def S (first : Bool) (np : Deriv E) (vp : Deriv (E → Prop)) : Deriv Prop :=
  binary (λ x P => P x) first np vp

/-- VP → Vt NP, `Vt(NP)`. -/
def VP (first : Bool) (vt : Deriv (E → E → Prop)) (obj : Deriv E) : Deriv (E → Prop) :=
  binary (λ R x => R x) first vt obj

/-- VP → Vs S, `Vs(S)`. -/
def VS (first : Bool) (vs : Deriv (Prop → E → Prop)) (s : Deriv Prop) : Deriv (E → Prop) :=
  binary (λ T p => T p) first vs s

/-- NP → Det N, `Det(N)`, determiners denoting choice functions. -/
def NP (first : Bool) (det : Deriv ((E → Prop) → E)) (n : Deriv (E → Prop)) : Deriv E :=
  binary (λ D P => D P) first det n

/-- N → Nr PPof, `Nr(PP)`. -/
def N (first : Bool) (nr : Deriv (E → E → Prop)) (pp : Deriv E) : Deriv (E → Prop) :=
  binary (λ R x => R x) first nr pp

/-- *everyone*: a universal over the continuation. -/
def everyone : Deriv E := quant "everyone" λ k => ∀ x, k x

/-- *someone*: an existential over the continuation. -/
def someone : Deriv E := quant "someone" λ k => ∃ x, k x

/-- *every* quantifies over choice functions; the restriction to proper choice functions is
left to the choice-function literature, as in the paper. -/
def every : Deriv ((E → Prop) → E) := quant "every" λ D => ∀ f, D f

/-- *a* as an existential over choice functions. -/
def a : Deriv ((E → Prop) → E) := quant "a" λ D => ∃ f, D f

/-- The expository *every*, typed as a generalized quantifier over the nominal. -/
def everyGQ (n : Deriv (E → Prop)) : Deriv E :=
  quant "every" λ k => n.continuize λ P => ∀ x, P x → k x

/-- The expository *a*. -/
def aGQ (n : Deriv (E → Prop)) : Deriv E :=
  quant "a" λ k => n.continuize λ P => ∃ x, P x ∧ k x

variable (j m : E) (left' slept' man' woman' : E → Prop) (saw' : E → E → Prop)
  (friendOf : E → E → Prop) (thought' : Prop → E → Prop) (the : (E → Prop) → E)

/-! ### Worked derivations -/

theorem john_left : eval (S false (lex j) (lex left')) = left' j := rfl

theorem everyone_left : eval (S false everyone (lex left')) = ∀ x, left' x :=
  rfl

/-- *John saw everyone*, in situ. -/
theorem john_saw_everyone :
    eval (S false (lex j) (VP true (lex saw') everyone)) = ∀ x, saw' x j :=
  rfl

/-- *Every man saw a woman* with VP priority: the inverse reading. -/
theorem every_man_saw_a_woman_inverse :
    eval (S false (everyGQ (lex man')) (VP true (lex saw') (aGQ (lex woman'))))
      = ∃ y, woman' y ∧ ∀ x, man' x → saw' y x := rfl

/-- With subject priority: the surface reading. -/
theorem every_man_saw_a_woman_surface :
    eval (S true (everyGQ (lex man')) (VP true (lex saw') (aGQ (lex woman'))))
      = ∀ x, man' x → ∃ y, woman' y ∧ saw' y x := rfl

/-- *John saw every man*: for every way of choosing a man, John saw him. -/
theorem john_saw_every_man :
    eval (S false (lex j) (VP true (lex saw') (NP true every (lex man')))) =
      ∀ f : (E → Prop) → E, saw' (f man') j := rfl

/-- *A man thought everyone saw Mary*: the island traps *everyone*. -/
theorem a_man_thought_everyone_saw_mary :
    eval (S false (aGQ (lex man'))
      (VS true (lex thought') (island (S false everyone (VP true (lex saw') (lex m)))))) =
      ∃ y, man' y ∧ thought' (∀ x, saw' m x) y := rfl

/-- *Someone saw the friend of the friend of everyone*: scope displacement is unbounded, and
both scopings are available. -/
theorem someone_saw_the_friend_of_the_friend_of_everyone (first : Bool) :
    eval (S first someone (VP true (lex saw')
      (NP true (lex the) (N true (lex friendOf)
        (NP true (lex the) (N true (lex friendOf) everyone)))))) =
      if first then ∃ x, ∀ y, saw' (the (friendOf (the (friendOf y)))) x
        else ∀ y, ∃ x, saw' (the (friendOf (the (friendOf y)))) x := by
  cases first <;> rfl

/-! ### The four scopings of *someone saw a friend of everyone* -/

/-- The derivation, with a priority bit at the S, VP, NP and N nodes. -/
def someoneSawAFriendOfEveryone (p : Fin 4 → Bool) : Deriv Prop :=
  S (p 0) someone (VP (p 1) (lex saw') (NP (p 2) a (N (p 3) (lex friendOf) everyone)))

theorem scoping_yfx :
    eval (someoneSawAFriendOfEveryone saw' friendOf ![true, true, true, true])
      = ∃ y, ∃ f : (E → Prop) → E, ∀ x, saw' (f (friendOf x)) y := rfl

theorem scoping_yxf :
    eval (someoneSawAFriendOfEveryone saw' friendOf ![true, true, false, true])
      = ∃ y, ∀ x, ∃ f : (E → Prop) → E, saw' (f (friendOf x)) y := rfl

theorem scoping_fxy :
    eval (someoneSawAFriendOfEveryone saw' friendOf ![false, true, true, true])
      = ∃ f : (E → Prop) → E, ∀ x, ∃ y, saw' (f (friendOf x)) y := rfl

theorem scoping_xfy :
    eval (someoneSawAFriendOfEveryone saw' friendOf ![false, true, false, true])
      = ∀ x, ∃ f : (E → Prop) → E, ∃ y, saw' (f (friendOf x)) y := rfl

/-- Integrity leaves four of the six orders: *a* and *everyone*, sharing the object, scope
together. -/
theorem scopeOrders (p : Fin 4 → Bool) :
    (someoneSawAFriendOfEveryone saw' friendOf p).scopeOrder ∈
      [["someone", "a", "everyone"], ["someone", "everyone", "a"],
        ["a", "everyone", "someone"], ["everyone", "a", "someone"]] := by
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;> cases h3 : p 3 <;>
    simp [someoneSawAFriendOfEveryone, S, VP, NP, N, scopeOrder, everyone, someone, a, h0, h1, h2,
      h3]

/-- The excluded orders split the object's quantifiers around the subject. -/
theorem no_split_scoping (p : Fin 4 → Bool) :
    (someoneSawAFriendOfEveryone saw' friendOf p).scopeOrder ≠ ["everyone", "someone", "a"] ∧
    (someoneSawAFriendOfEveryone saw' friendOf p).scopeOrder ≠ ["a", "someone", "everyone"] := by
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;> cases h3 : p 3 <;>
    simp [someoneSawAFriendOfEveryone, S, VP, NP, N, scopeOrder, everyone, someone, a, h0, h1, h2,
      h3]

/-! ### Generalized coordination -/

theorem john_left_and_slept :
    eval (S false (lex j) (coord (lex left') (lex slept'))) =
      (left' j ∧ slept' j) := rfl

theorem john_and_mary_left :
    eval (S false (coord (lex j) (lex m)) (lex left')) =
      (left' j ∧ left' m) := rfl

/-! ### The paper's examples -/

open Data.Examples (LinguisticExample)

/-- A reading named by its scope order, `someone > a > everyone`. -/
def order (s : String) : List String :=
  (s.toList.splitOn '>').map λ cs =>
    String.ofList ((cs.dropWhile (· = ' ')).reverse.dropWhile (· = ' ') |>.reverse)

/-- The readings the paper lists for *someone saw a friend of everyone* are exactly the scope
orders some prioritization of its derivation induces. -/
theorem rows_scopings : ∀ e ∈ Examples.all,
    e.feature? "derivation" = some "someone saw a friend of everyone" → ∀ r ∈ e.readings,
      (r.2 = .acceptable ↔ ∃ p : Fin 4 → Bool,
        (someoneSawAFriendOfEveryone (E := Unit) (λ _ _ => True) (λ _ _ => True) p).scopeOrder =
          order r.1) := by
  decide +kernel

end Barker2002
