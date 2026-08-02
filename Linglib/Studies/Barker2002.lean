import Linglib.Semantics.Quantification.Defs
import Linglib.Semantics.Composition.Cont

/-!
# Barker (2002): Continuations and the Nature of Quantification

Formalizes [barker-2002]'s continuized grammar. The Continuation
Hypothesis (his (2)) is that quantificational NPs denote functions on
their own continuations; continuizing an ordinary grammar (the schema in
his (9)/(31)) then derives generalized quantifiers, in-situ scope
displacement, and scope ambiguity, with no movement, storage, or
type-shifting. This file follows the paper's own development: the arity-2
instances of the Continuation Schema (his (35)), his grammar (10) with
the quantificational entries (13) and the expository determiners (16),
his worked derivations (11)–(17), the priority ambiguity of (18), his
generalized coordination (30) with the examples in (27), and the §5
Simulation Theorem with its Lemma, proved by the paper's own
generalize-the-continuation argument.

Not formalized: the Appendix's choice-function fragment ((39)–(41)),
which retypes quantificational determiners over choice functions — the
paper flags (15)/(16) as expository and the Appendix as the real
fragment, so that half remains future work. Barker's transitive verbs
take their object first (`saw m j` is "John saw Mary"); all statements
below follow that convention.
-/

namespace Barker2002

open Quantification (Quantifier individual)

variable {α β γ E : Type}

/-! ### The Continuation Schema at arity 2

His (9)/(35): a lexical item continuizes to the unit `λb̄. b̄(⟦B⟧)` —
the monadic `pure`, which at NP type is `Quantification.individual` —
and a binary rule with direct meaning `M` continuizes to `n! = 2` rules,
one per evaluation order. The daughter evaluated first takes PRIORITY
(his term): its quantifiers take wide scope. -/

/-- The f-instance of the Continuation Schema (his (35)): priority to
the first daughter. -/
def priorityFirst (M : α → β → γ) (m₁ : Cont Prop α) (m₂ : Cont Prop β) :
    Cont Prop γ :=
  λ κ => m₁ (λ x₁ => m₂ (λ x₂ => κ (M x₁ x₂)))

/-- The g-instance of the Continuation Schema (his (35)): priority to
the second daughter. -/
def prioritySecond (M : α → β → γ) (m₁ : Cont Prop α) (m₂ : Cont Prop β) :
    Cont Prop γ :=
  λ κ => m₂ (λ x₂ => m₁ (λ x₁ => κ (M x₁ x₂)))

/-- Linglib note (not in the paper): the f-schema is the applicative
combination on `Cont Prop`, connecting Barker's rules to the substrate's
`lower_*` lemmas. -/
theorem priorityFirst_eq_seq (M : α → β → γ) (m₁ : Cont Prop α) (m₂ : Cont Prop β) :
    priorityFirst M m₁ m₂ = M <$> m₁ <*> m₂ := rfl

/-! ### The grammar

His (10): `S → NP VP` interprets as `⟦VP⟧(⟦NP⟧)` and `VP → Vt NP` as
`⟦Vt⟧(⟦NP⟧)`. Rule (10a) gives the VP priority (= his (18a)); (18b) is
the same syntax with subject priority. (10b) gives the verb priority. -/

/-- His (10a)/(18a): the S rule with VP priority — VP-internal
quantifiers outscope the subject. -/
def sRuleVP (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  prioritySecond (λ x P => P x) np vp

/-- His (18b): the S rule with subject priority — the subject takes
wide scope. -/
def sRuleNP (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  priorityFirst (λ x P => P x) np vp

/-- His (10b): the VP rule, verb priority. -/
def vpRule (vt : Cont Prop (E → E → Prop)) (np : Cont Prop E) :
    Cont Prop (E → Prop) :=
  priorityFirst (λ R x => R x) vt np

/-- His (13a): *everyone* wraps a universal around its continuation. -/
def everyone : Quantifier E := λ k => ∀ x, k x

/-- His (13b): *someone* wraps an existential around its continuation. -/
def someone : Quantifier E := λ k => ∃ x, k x

/-- His (16): expository *every* — takes a continuized nominal, returns
an NP meaning. (The paper's real fragment retypes determiners over
choice functions, his (39); not formalized here.) -/
def everyDet (n : Cont Prop (E → Prop)) : Quantifier E :=
  λ k => n (λ P => ∀ x, P x → k x)

/-- His (16): expository *a*/*some*. -/
def aDet (n : Cont Prop (E → Prop)) : Quantifier E :=
  λ k => n (λ P => ∃ x, P x ∧ k x)

/-! ### The worked derivations

The paper evaluates sentences by "applying to the trivial continuation"
`λp.p` (his (12)) — the substrate's `ContT.lower`. -/

variable (j m : E) (left' slept' man' woman' : E → Prop) (saw' : E → E → Prop)

/-- His (11)–(12): *John left* evaluates to `left j`. -/
theorem john_left :
    ContT.lower (sRuleVP (individual j) (pure left')) = left' j := rfl

/-- p. 220: *Everyone left* "smoothly evaluates to `∀x. left x`". -/
theorem everyone_left :
    ContT.lower (sRuleVP everyone (pure left')) = ∀ x, left' x := rfl

/-- His (14): *John saw everyone* evaluates to `∀x. saw x j` — in situ,
with "no type clash or asymmetry between quantificational NPs occurring
in subject and non-subject positions". -/
theorem john_saw_everyone :
    ContT.lower (sRuleVP (individual j) (vpRule (pure saw') everyone)) =
    ∀ x, saw' x j := rfl

/-- His (17c): *Every man saw a woman* under the VP-priority S rule is
**inverse** scope, `∃y. woman y ∧ ∀x. man x → saw y x` — the paper's
demonstration that "nothing in the continuation mechanism itself biases
towards linear scope or inverse scope". -/
theorem every_man_saw_a_woman_inverse :
    ContT.lower (sRuleVP (everyDet (pure man'))
      (vpRule (pure saw') (aDet (pure woman')))) =
    ∃ y, woman' y ∧ ∀ x, man' x → saw' y x := rfl

/-- His §2.4: the same sentence under the subject-priority rule (18b) is
surface scope. (The paper derives this reading via (18b) but does not
print the formula.) -/
theorem every_man_saw_a_woman_surface :
    ContT.lower (sRuleNP (everyDet (pure man'))
      (vpRule (pure saw') (aDet (pure woman')))) =
    ∀ x, man' x → ∃ y, woman' y ∧ saw' y x := rfl

/-! ### Bounding scope displacement (§2.5)

His (20b) adjusts the S rule so that the clause's continuation applies
to the already-evaluated clause: quantifiers inside can no longer see
material outside. The adjustment "can only be made for syntactic
categories whose direct (i.e., uncontinuized) type is t". -/

/-- His (20b): the island-adjusted S rule — the clause's continuation
applies to the evaluated clause. -/
def sRuleIsland (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  λ p => p (sRuleVP np vp id)

/-- Linglib note (not in the paper): (20b) is the substrate's
`ContT.reset` — lower the clause, then re-lift it. -/
theorem sRuleIsland_eq_reset (np : Cont Prop E) (vp : Cont Prop (E → Prop)) :
    sRuleIsland np vp = ContT.reset (sRuleVP np vp) := rfl

/-- The island output simulates its evaluated clause in the §5 sense:
what escapes an island is a value, never a scope-taker. -/
theorem sRuleIsland_simulates (np : Cont Prop E) (vp : Cont Prop (E → Prop)) :
    ∀ g, sRuleIsland np vp g = g (ContT.lower (sRuleVP np vp)) :=
  λ _ => rfl

/-- The Appendix's `VP → Vs S` rule, verb priority: `⟦Vs⟧(⟦S⟧)`. -/
def vsRule (vs : Cont Prop (Prop → E → Prop)) (s : Cont Prop Prop) :
    Cont Prop (E → Prop) :=
  priorityFirst (λ T p => T p) vs s

variable (thought' : Prop → E → Prop)

/-- His (21): *A man thought everyone saw Mary* with the embedded clause
islanded evaluates to his (21b), `∃y. man y ∧ thought(∀x. saw m x) y` —
*everyone* "is not able to take scope outside of the embedded clause". -/
theorem a_man_thought_everyone_saw_mary :
    ContT.lower (sRuleVP (aDet (pure man'))
      (vsRule (pure thought')
        (sRuleIsland everyone (vpRule (pure saw') (individual m))))) =
    ∃ y, man' y ∧ thought' (∀ x, saw' m x) y := rfl

/-- Clause-boundedness sharpened: with the embedded clause islanded, the
matrix priority choice is inert — his "all scopings of (21a) are
logically equivalent to (21b)". -/
theorem thought_island_priority_inert :
    sRuleNP (aDet (pure man'))
      (vsRule (pure thought')
        (sRuleIsland everyone (vpRule (pure saw') (individual m)))) =
    sRuleVP (aDet (pure man'))
      (vsRule (pure thought')
        (sRuleIsland everyone (vpRule (pure saw') (individual m)))) := rfl

/-! ### Generalized coordination (§4)

His (30): *and* "distributes the continuation belonging to the
coordinate structure across the conjuncts" — one rule for every
category, with no conjoinable-type recursion. -/

/-- His (30): coordination at any category. -/
def coord (l r : Cont Prop α) : Cont Prop α := λ k => l k ∧ r k

/-- His (27b): *John left and slept*. -/
theorem john_left_and_slept :
    ContT.lower (sRuleVP (individual j) (coord (pure left') (pure slept'))) =
    (left' j ∧ slept' j) := rfl

/-- His (27d): *John and Mary left* — NP coordination through the same
rule. -/
theorem john_and_mary_left :
    ContT.lower (sRuleVP (coord (individual j) (individual m)) (pure left')) =
    (left' j ∧ left' m) := rfl

/-! ### The Simulation Theorem (§5)

Continuization is conservative: on schema-derived meanings, evaluation
at the trivial continuation recovers the direct meaning, for **every**
choice of priority. The paper proves this via a Lemma generalizing the
trivial continuation to an arbitrary one — `m̂(λx.g(x)) = g(m)` — and
we follow that proof shape: the lexical case is definitional, and each
binary case discharges the daughters' hypotheses from the innermost
continuation out. -/

/-- §5's Lemma, lexical case: the unit satisfies `m̂(g) = g(m)`. -/
theorem simulation_pure (a : α) (g : α → Prop) :
    (pure a : Cont Prop α) g = g a := rfl

/-- §5's Lemma, arity-2 f-case: if both daughters simulate their direct
meanings, so does their priority-first combination. -/
theorem simulation_priorityFirst (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) :
    ∀ g, priorityFirst M c₁ c₂ g = g (M m₁ m₂) := by
  intro g
  show c₁ _ = _
  rw [h₁]
  exact h₂ _

/-- §5's Lemma, arity-2 g-case. -/
theorem simulation_prioritySecond (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) :
    ∀ g, prioritySecond M c₁ c₂ g = g (M m₁ m₂) := by
  intro g
  show c₂ _ = _
  rw [h₂]
  exact h₁ _

/-- §5's order-independence: on simulating daughters the two priorities
agree — "the result is the same, in the absence of quantification". The
quantificational entries (13) are exactly the meanings that break the
hypotheses, which is the paper's own delimitation of the theorem. -/
theorem simulation_orders_agree (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) :
    priorityFirst M c₁ c₂ = prioritySecond M c₁ c₂ := by
  funext g
  rw [simulation_priorityFirst M h₁ h₂ g, simulation_prioritySecond M h₁ h₂ g]

/-- §5's Simulation Theorem: a simulating sentence meaning evaluates at
the trivial continuation to its direct meaning. -/
theorem simulation (c : Cont Prop Prop) (p : Prop) (h : ∀ g, c g = g p) :
    ContT.lower c = p :=
  h id

end Barker2002
