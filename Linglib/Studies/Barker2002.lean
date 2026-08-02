import Linglib.Semantics.Quantification.Defs
import Linglib.Semantics.Composition.Cont

/-!
# Barker (2002): Continuations and the Nature of Quantification

Formalizes the continuized grammar of [barker-2002]: quantificational
NPs denote functions on their own continuations, so continuizing an
ordinary grammar derives generalized quantifiers, in-situ scope
displacement, and scope ambiguity, with no movement, storage, or
type-shifting. The file states the Continuation Schema at arity 2, the
fragment with its worked derivations, the scope-island rule with clause
boundedness, generalized coordination, and the Simulation Theorem,
following the paper's own proof. Barker's transitive verbs take the
object first: `saw m j` is "John saw Mary".

The fragment's determiners quantify over choice functions, as in the
paper's appendix; the generalized-quantifier pair the paper introduces
for exposition is kept for the derivations whose printed formulas need
it. The *the friend of* chains are not formalized.
-/

namespace Barker2002

open Quantification (Quantifier individual)

variable {α β γ E : Type} (np : Cont Prop E) (vp : Cont Prop (E → Prop))
variable (det : Cont Prop ((E → Prop) → E)) (n : Cont Prop (E → Prop))

/-! ### The grammar

Barker continuizes each lexical item to the unit `pure` and each binary
rule to two rules, one per evaluation order; the daughter evaluated
first takes priority and its quantifiers take wide scope. Since the
fragment's direct meanings are function application, the rules are bare
`<*>`, with priority as argument order. -/

/-- The S rule with priority to the VP. -/
def sRuleVP : Cont Prop Prop :=
  vp <*> np

/-- The S rule with priority to the subject. -/
def sRuleNP : Cont Prop Prop :=
  (λ x P => P x) <$> np <*> vp

/-- The VP rule, verb priority. -/
def vpRule (vt : Cont Prop (E → E → Prop)) (obj : Cont Prop E) :
    Cont Prop (E → Prop) :=
  vt <*> obj

/-- *everyone*: a universal over the continuation. -/
def everyone : Quantifier E := λ k => ∀ x, k x

/-- *someone*: an existential over the continuation. -/
def someone : Quantifier E := λ k => ∃ x, k x

/-- *every* quantifies over choice functions; Barker leaves the
restriction to proper choice functions to the choice-function
literature, and so do we. -/
def everyCF : Cont Prop ((E → Prop) → E) := λ D => ∀ f, D f

/-- *a* as an existential over choice functions. -/
def aCF : Cont Prop ((E → Prop) → E) := λ D => ∃ f, D f

/-- The NP rule, determiner priority. -/
def npRuleDet : Cont Prop E :=
  det <*> n

/-- The NP rule, nominal priority. -/
def npRuleN : Cont Prop E :=
  (λ P D => D P) <$> n <*> det

/-- The paper's expository *every*, typed as a generalized quantifier. -/
def everyGQ (n : Cont Prop (E → Prop)) : Quantifier E :=
  λ k => n (λ P => ∀ x, P x → k x)

/-- The paper's expository *a*. -/
def aGQ (n : Cont Prop (E → Prop)) : Quantifier E :=
  λ k => n (λ P => ∃ x, P x ∧ k x)

/-! ### The worked derivations

Sentences evaluate by applying the trivial continuation `λp.p` — the
substrate's `ContT.eval`. Nothing biases toward linear or inverse
scope: *Every man saw a woman* gets its inverse reading under VP
priority (the reading the paper prints) and its surface reading under
subject priority. -/

variable (j m : E) (left' slept' man' woman' : E → Prop) (saw' : E → E → Prop)
variable (friendOf : E → E → Prop)

/-- *John left*. -/
theorem john_left :
    ContT.eval (sRuleVP (individual j) (pure left')) = left' j := rfl

/-- *Everyone left*. -/
theorem everyone_left :
    ContT.eval (sRuleVP everyone (pure left')) = ∀ x, left' x := rfl

/-- *John saw everyone*, in situ. -/
theorem john_saw_everyone :
    ContT.eval (sRuleVP (individual j) (vpRule (pure saw') everyone)) =
    ∀ x, saw' x j := rfl

/-- *Every man saw a woman*, VP priority: the inverse reading. -/
theorem every_man_saw_a_woman_inverse :
    ContT.eval (sRuleVP (everyGQ (pure man'))
      (vpRule (pure saw') (aGQ (pure woman')))) =
    ∃ y, woman' y ∧ ∀ x, man' x → saw' y x := rfl

/-- *Every man saw a woman*, subject priority: the surface reading. -/
theorem every_man_saw_a_woman_surface :
    ContT.eval (sRuleNP (everyGQ (pure man'))
      (vpRule (pure saw') (aGQ (pure woman')))) =
    ∀ x, man' x → ∃ y, woman' y ∧ saw' y x := rfl

/-- *John saw every man*: for every way of choosing a man, John saw
him. -/
theorem john_saw_every_man :
    ContT.eval (sRuleVP (individual j)
      (vpRule (pure saw') (npRuleDet everyCF (pure man')))) =
    ∀ f : (E → Prop) → E, saw' (f man') j := rfl

/-- *Someone saw a friend of everyone*: subject wide, determiner over
nominal. -/
theorem someone_saw_a_friend_of_everyone_yfx :
    ContT.eval (sRuleNP someone (vpRule (pure saw')
      (npRuleDet aCF (pure friendOf <*> everyone)))) =
    ∃ y, ∃ f : (E → Prop) → E, ∀ x, saw' (f (friendOf x)) y := rfl

/-- Subject wide, nominal over determiner. -/
theorem someone_saw_a_friend_of_everyone_yxf :
    ContT.eval (sRuleNP someone (vpRule (pure saw')
      (npRuleN aCF (pure friendOf <*> everyone)))) =
    ∃ y, ∀ x, ∃ f : (E → Prop) → E, saw' (f (friendOf x)) y := rfl

/-- Object wide, determiner over nominal. -/
theorem someone_saw_a_friend_of_everyone_fxy :
    ContT.eval (sRuleVP someone (vpRule (pure saw')
      (npRuleDet aCF (pure friendOf <*> everyone)))) =
    ∃ f : (E → Prop) → E, ∀ x, ∃ y, saw' (f (friendOf x)) y := rfl

/-- Object wide, nominal over determiner. -/
theorem someone_saw_a_friend_of_everyone_xfy :
    ContT.eval (sRuleVP someone (vpRule (pure saw')
      (npRuleN aCF (pure friendOf <*> everyone)))) =
    ∀ x, ∃ f : (E → Prop) → E, ∃ y, saw' (f (friendOf x)) y := rfl

/-! ### Bounding scope displacement

Barker's island adjustment evaluates the clause and re-lifts it —
`ContT.reset` — so what escapes an island is a value, never a
scope-taker, and embedded quantifiers cannot outscope it; the
adjustment "can only be made for syntactic categories whose direct
(i.e., uncontinuized) type is t". -/

/-- The island-adjusted S rule: evaluate the clause, then re-lift. -/
def sRuleIsland : Cont Prop Prop :=
  ContT.reset (sRuleVP np vp)

/-- The clausal-complement rule, verb priority. -/
def vsRule (vs : Cont Prop (Prop → E → Prop)) (s : Cont Prop Prop) :
    Cont Prop (E → Prop) :=
  vs <*> s

variable (thought' : Prop → E → Prop)

/-- *A man thought everyone saw Mary*: *everyone* is trapped in the
complement. -/
theorem a_man_thought_everyone_saw_mary :
    ContT.eval (sRuleVP (aGQ (pure man'))
      (vsRule (pure thought')
        (sRuleIsland everyone (vpRule (pure saw') (individual m))))) =
    ∃ y, man' y ∧ thought' (∀ x, saw' m x) y := rfl

/-- A unit VP makes the matrix priority choice inert: "all scopings are
logically equivalent". -/
theorem sRule_priority_inert (P : E → Prop) :
    sRuleNP np (pure P) = sRuleVP np (pure P) := rfl

/-! ### Generalized coordination

One rule for every category: *and* distributes the continuation across
the conjuncts, with no conjoinable-type recursion — the meet of the
quantifier lattice. -/

/-- Coordination at any category: the continuation distributes across
the conjuncts. -/
def coord (l r : Cont Prop α) : Cont Prop α := λ k => l k ∧ r k

/-- *John left and slept*. -/
theorem john_left_and_slept :
    ContT.eval (sRuleVP (individual j) (coord (pure left') (pure slept'))) =
    (left' j ∧ slept' j) := rfl

/-- *John and Mary left*. -/
theorem john_and_mary_left :
    ContT.eval (sRuleVP (coord (individual j) (individual m)) (pure left')) =
    (left' j ∧ left' m) := rfl

/-! ### The Simulation Theorem

Continuization is conservative: a schema-derived meaning evaluates at
the trivial continuation to its direct meaning, under either priority.
The paper's "simulating" hypothesis — `c g = g m` for every
continuation `g` — says exactly that `c` is the unit
(`simulating_iff`), so its Lemma is the applicative unit laws and its
Theorem is the substrate's `eval_*` simp set; the quantificational
entries are exactly the non-units. -/

/-- Simulating in the paper's sense is being a unit. -/
theorem simulating_iff {c : Cont Prop α} {a : α} :
    (∀ g, c g = g a) ↔ c = pure a :=
  ⟨funext, λ h g => by subst h; rfl⟩

/-- "The result is the same, in the absence of quantification": a unit
daughter makes the priority choice inert. -/
theorem simulation_orders_agree (M : α → β → γ) (a : α) (c : Cont Prop β) :
    M <$> (pure a : Cont Prop α) <*> c = flip M <$> c <*> pure a := rfl

/-- A schema-derived sentence evaluates at the trivial continuation to
its direct meaning. -/
theorem simulation (M : α → β → Prop) (m₁ : α) (m₂ : β) :
    ContT.eval (M <$> (pure m₁ : Cont Prop α) <*> pure m₂) = M m₁ m₂ := rfl

end Barker2002
