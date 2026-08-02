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

/-! ### The Continuation Schema at arity 2

Barker's schema ((9) and (35) in the paper) continuizes a lexical item
to the unit `λb̄. b̄(⟦B⟧)` — the monadic `pure`, at NP type
`Quantification.individual` — and a binary rule with direct meaning `M`
to `n! = 2` rules, one per evaluation order. The daughter evaluated
first takes priority, his term: its quantifiers take wide scope. Both
instances are the applicative combination in its two argument orders,
`M <$> m₁ <*> m₂` and `flip M <$> m₂ <*> m₁`, and since the fragment's
direct meanings are all function application, its rules below are bare
`<*>`: priority is the argument order of continuized application. -/

/-! ### The grammar

In the fragment (Barker's (10) with the ambiguity of (18)), `S → NP VP`
interprets as `⟦VP⟧(⟦NP⟧)` and `VP → Vt NP` as `⟦Vt⟧(⟦NP⟧)`; the S rule
comes in both priorities, the VP rule with verb priority. The
quantificational NPs are his (13), the determiners his expository
(16). -/

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

Sentences evaluate by "applying to the trivial continuation" `λp.p` —
the substrate's `ContT.lower`. The theorems below are the paper's worked
examples ((11)–(17)): "nothing in the continuation mechanism itself
biases towards linear scope or inverse scope", so *Every man saw a
woman* gets its inverse reading under VP priority — the reading the
paper prints as (17c) — and its surface reading under subject priority,
which the paper derives but does not print. -/

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

Barker's island adjustment (20b) applies the clause's continuation to
the already-evaluated clause, so quantifiers inside can no longer see
material outside: *everyone* in (21) "is not able to take scope outside
of the embedded clause". The adjustment "can only be made for syntactic
categories whose direct (i.e., uncontinuized) type is t". -/

/-- The island-adjusted S rule: the continuation applies to the
evaluated clause. -/
def sRuleIsland (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  λ p => p (sRuleVP np vp id)

/-- The island rule is the substrate's `ContT.reset`. -/
theorem sRuleIsland_eq_reset (np : Cont Prop E) (vp : Cont Prop (E → Prop)) :
    sRuleIsland np vp = ContT.reset (sRuleVP np vp) := rfl

/-- What escapes an island is a value, never a scope-taker. -/
theorem sRuleIsland_simulates (np : Cont Prop E) (vp : Cont Prop (E → Prop))
    (g : Prop → Prop) :
    sRuleIsland np vp g = g (ContT.lower (sRuleVP np vp)) := rfl

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

/-- With the complement islanded, the matrix priority choice is inert. -/
theorem thought_island_priority_inert :
    sRuleNP (aDet (pure man'))
      (vsRule (pure thought')
        (sRuleIsland everyone (vpRule (pure saw') (individual m)))) =
    sRuleVP (aDet (pure man'))
      (vsRule (pure thought')
        (sRuleIsland everyone (vpRule (pure saw') (individual m)))) := rfl

/-! ### Generalized coordination

One rule for every category, Barker's (30): *and* "distributes the
continuation belonging to the coordinate structure across the
conjuncts", with no conjoinable-type recursion. The examples are his
(27). -/

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

Continuization is conservative (Barker's §5): on schema-derived
meanings, evaluation at the trivial continuation recovers the direct
meaning, for every choice of priority. The paper's Lemma generalizes
the trivial continuation to an arbitrary `g`, and the proofs below
follow that shape, discharging the daughters' hypotheses from the
innermost continuation out. The quantificational entries are exactly
the meanings that break the hypotheses — the paper's own delimitation. -/

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
