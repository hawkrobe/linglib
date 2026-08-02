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

The Appendix's choice-function fragment is not formalized; the
determiners here are the ones the paper marks as expository.
-/

namespace Barker2002

open Quantification (Quantifier individual)

variable {α β γ E : Type}

/-! ### The grammar

Barker continuizes each lexical item to the unit `pure` and each binary
rule to two rules, one per evaluation order; the daughter evaluated
first takes priority and its quantifiers take wide scope. Since the
fragment's direct meanings are function application, the rules are bare
`<*>`, with priority as argument order. -/

/-- The S rule with priority to the VP. -/
def sRuleVP (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  vp <*> np

/-- The S rule with priority to the subject. -/
def sRuleNP (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  (λ x P => P x) <$> np <*> vp

/-- The VP rule, verb priority. -/
def vpRule (vt : Cont Prop (E → E → Prop)) (np : Cont Prop E) :
    Cont Prop (E → Prop) :=
  vt <*> np

/-- *everyone*: a universal over the continuation. -/
def everyone : Quantifier E := λ k => ∀ x, k x

/-- *someone*: an existential over the continuation. -/
def someone : Quantifier E := λ k => ∃ x, k x

/-- *every*: a universal from a continuized nominal. -/
def everyDet (n : Cont Prop (E → Prop)) : Quantifier E :=
  λ k => n (λ P => ∀ x, P x → k x)

/-- *a*: an existential from a continuized nominal. -/
def aDet (n : Cont Prop (E → Prop)) : Quantifier E :=
  λ k => n (λ P => ∃ x, P x ∧ k x)

/-! ### The worked derivations

Sentences evaluate by applying the trivial continuation `λp.p` — the
substrate's `ContT.lower`. Nothing biases toward linear or inverse
scope: *Every man saw a woman* gets its inverse reading under VP
priority (the reading the paper prints) and its surface reading under
subject priority. -/

variable (j m : E) (left' slept' man' woman' : E → Prop) (saw' : E → E → Prop)

/-- *John left*. -/
theorem john_left :
    ContT.lower (sRuleVP (individual j) (pure left')) = left' j := rfl

/-- *Everyone left*. -/
theorem everyone_left :
    ContT.lower (sRuleVP everyone (pure left')) = ∀ x, left' x := rfl

/-- *John saw everyone*, in situ. -/
theorem john_saw_everyone :
    ContT.lower (sRuleVP (individual j) (vpRule (pure saw') everyone)) =
    ∀ x, saw' x j := rfl

/-- *Every man saw a woman*, VP priority: the inverse reading. -/
theorem every_man_saw_a_woman_inverse :
    ContT.lower (sRuleVP (everyDet (pure man'))
      (vpRule (pure saw') (aDet (pure woman')))) =
    ∃ y, woman' y ∧ ∀ x, man' x → saw' y x := rfl

/-- *Every man saw a woman*, subject priority: the surface reading. -/
theorem every_man_saw_a_woman_surface :
    ContT.lower (sRuleNP (everyDet (pure man'))
      (vpRule (pure saw') (aDet (pure woman')))) =
    ∀ x, man' x → ∃ y, woman' y ∧ saw' y x := rfl

/-! ### Bounding scope displacement

Barker's island adjustment evaluates the clause and re-lifts it —
`ContT.reset` — so what escapes an island is a value, never a
scope-taker, and embedded quantifiers cannot outscope it; the
adjustment "can only be made for syntactic categories whose direct
(i.e., uncontinuized) type is t". -/

/-- The island-adjusted S rule: evaluate the clause, then re-lift. -/
def sRuleIsland (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  ContT.reset (sRuleVP np vp)

/-- The clausal-complement rule, verb priority. -/
def vsRule (vs : Cont Prop (Prop → E → Prop)) (s : Cont Prop Prop) :
    Cont Prop (E → Prop) :=
  vs <*> s

variable (thought' : Prop → E → Prop)

/-- *A man thought everyone saw Mary*: *everyone* is trapped in the
complement. -/
theorem a_man_thought_everyone_saw_mary :
    ContT.lower (sRuleVP (aDet (pure man'))
      (vsRule (pure thought')
        (sRuleIsland everyone (vpRule (pure saw') (individual m))))) =
    ∃ y, man' y ∧ thought' (∀ x, saw' m x) y := rfl

/-- A simulating VP makes the matrix priority choice inert: "all
scopings are logically equivalent". -/
theorem sRule_priority_inert (np : Cont Prop E) {vp : Cont Prop (E → Prop)}
    {P : E → Prop} (h : ∀ g, vp g = g P) :
    sRuleNP np vp = sRuleVP np vp := by
  funext κ
  exact (congrArg np (funext λ x => h (λ Q => κ (Q x)))).trans
    (h (λ Q => np (λ x => κ (Q x)))).symm

/-! ### Generalized coordination

One rule for every category: *and* distributes the continuation across
the conjuncts, with no conjoinable-type recursion. -/

/-- Coordination at any category: the continuation distributes across
the conjuncts. -/
def coord (l r : Cont Prop α) : Cont Prop α := λ k => l k ∧ r k

/-- *John left and slept*. -/
theorem john_left_and_slept :
    ContT.lower (sRuleVP (individual j) (coord (pure left') (pure slept'))) =
    (left' j ∧ slept' j) := rfl

/-- *John and Mary left*. -/
theorem john_and_mary_left :
    ContT.lower (sRuleVP (coord (individual j) (individual m)) (pure left')) =
    (left' j ∧ left' m) := rfl

/-! ### The Simulation Theorem

Continuization is conservative: evaluating a schema-derived meaning at
the trivial continuation recovers its direct meaning, under either
priority. The proofs follow the paper's Lemma, generalizing the trivial
continuation to an arbitrary `g`; the quantificational entries are
exactly the meanings that break the hypotheses. -/

/-- A unit meaning simulates its direct value. -/
theorem simulation_pure (a : α) (g : α → Prop) :
    (pure a : Cont Prop α) g = g a := rfl

/-- Priority-first combination preserves simulation. -/
theorem simulation_seq (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) (g : γ → Prop) :
    (M <$> c₁ <*> c₂) g = g (M m₁ m₂) := by
  show c₁ _ = _
  rw [h₁]
  exact h₂ _

/-- Priority-second combination preserves simulation. -/
theorem simulation_seq_flip (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) (g : γ → Prop) :
    (flip M <$> c₂ <*> c₁) g = g (M m₁ m₂) := by
  show c₂ _ = _
  rw [h₂]
  exact h₁ _

/-- "The result is the same, in the absence of quantification." -/
theorem simulation_orders_agree (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) :
    M <$> c₁ <*> c₂ = flip M <$> c₂ <*> c₁ := by
  funext g
  rw [simulation_seq M h₁ h₂ g, simulation_seq_flip M h₁ h₂ g]

/-- A simulating meaning evaluates at the trivial continuation to its
direct meaning. -/
theorem simulation (c : Cont Prop Prop) (p : Prop) (h : ∀ g, c g = g p) :
    ContT.lower c = p :=
  h id

end Barker2002
