import Linglib.Semantics.Quantification.Defs
import Linglib.Semantics.Composition.Cont

/-!
# Barker (2002): Continuations and the Nature of Quantification

Formalizes the continuized grammar of [barker-2002]: quantificational
NPs denote functions on their own continuations, so continuizing an
ordinary grammar derives generalized quantifiers, in-situ scope
displacement, and scope ambiguity, with no movement, storage, or
type-shifting. The file states his Continuation Schema at arity 2, his
fragment with its worked derivations, the scope-island rule with clause
boundedness, generalized coordination, and the §5 Simulation Theorem,
following the paper's own proof. His transitive verbs take the object
first: `saw m j` is "John saw Mary".

The Appendix's choice-function fragment ((39)–(41)) is not formalized;
the determiners here are the ones the paper marks as expository.
-/

namespace Barker2002

open Quantification (Quantifier individual)

variable {α β γ E : Type}

/-! ### The Continuation Schema at arity 2

His (9)/(35): a lexical item continuizes to the unit `λb̄. b̄(⟦B⟧)` —
the monadic `pure`, which at NP type is `Quantification.individual` —
and a binary rule with direct meaning `M` continuizes to `n! = 2` rules,
one per evaluation order. The daughter evaluated first takes priority
(his term): its quantifiers take wide scope. -/

/-- His (35), f-instance: priority to the first daughter. -/
def priorityFirst (M : α → β → γ) (m₁ : Cont Prop α) (m₂ : Cont Prop β) :
    Cont Prop γ :=
  λ κ => m₁ (λ x₁ => m₂ (λ x₂ => κ (M x₁ x₂)))

/-- His (35), g-instance: priority to the second daughter. -/
def prioritySecond (M : α → β → γ) (m₁ : Cont Prop α) (m₂ : Cont Prop β) :
    Cont Prop γ :=
  λ κ => m₂ (λ x₂ => m₁ (λ x₁ => κ (M x₁ x₂)))

/-- Linglib note: the f-schema is the applicative combination. -/
theorem priorityFirst_eq_seq (M : α → β → γ) (m₁ : Cont Prop α) (m₂ : Cont Prop β) :
    priorityFirst M m₁ m₂ = M <$> m₁ <*> m₂ := rfl

/-! ### The grammar

His (10): `S → NP VP` interprets as `⟦VP⟧(⟦NP⟧)` and `VP → Vt NP` as
`⟦Vt⟧(⟦NP⟧)`. Rule (10a) gives the VP priority (= his (18a)); (18b) is
the same syntax with subject priority. (10b) gives the verb priority. -/

/-- His (10a)/(18a): the S rule, VP priority. -/
def sRuleVP (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  prioritySecond (λ x P => P x) np vp

/-- His (18b): the S rule, subject priority. -/
def sRuleNP (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  priorityFirst (λ x P => P x) np vp

/-- His (10b): the VP rule, verb priority. -/
def vpRule (vt : Cont Prop (E → E → Prop)) (np : Cont Prop E) :
    Cont Prop (E → Prop) :=
  priorityFirst (λ R x => R x) vt np

/-- His (13a): *everyone*. -/
def everyone : Quantifier E := λ k => ∀ x, k x

/-- His (13b): *someone*. -/
def someone : Quantifier E := λ k => ∃ x, k x

/-- His (16): expository *every*. -/
def everyDet (n : Cont Prop (E → Prop)) : Quantifier E :=
  λ k => n (λ P => ∀ x, P x → k x)

/-- His (16): expository *a*/*some*. -/
def aDet (n : Cont Prop (E → Prop)) : Quantifier E :=
  λ k => n (λ P => ∃ x, P x ∧ k x)

/-! ### The worked derivations

Sentences evaluate by "applying to the trivial continuation" `λp.p`
(his (12)) — the substrate's `ContT.lower`. His (17c) demonstrates that
"nothing in the continuation mechanism itself biases towards linear
scope or inverse scope": the VP-priority rule yields the inverse
reading, and (18b) the surface reading, which the paper derives but
does not print. -/

variable (j m : E) (left' slept' man' woman' : E → Prop) (saw' : E → E → Prop)

/-- His (11)–(12): *John left*. -/
theorem john_left :
    ContT.lower (sRuleVP (individual j) (pure left')) = left' j := rfl

/-- p. 220: *Everyone left*. -/
theorem everyone_left :
    ContT.lower (sRuleVP everyone (pure left')) = ∀ x, left' x := rfl

/-- His (14): *John saw everyone*, in situ. -/
theorem john_saw_everyone :
    ContT.lower (sRuleVP (individual j) (vpRule (pure saw') everyone)) =
    ∀ x, saw' x j := rfl

/-- His (17c): *Every man saw a woman*, VP priority — the inverse reading. -/
theorem every_man_saw_a_woman_inverse :
    ContT.lower (sRuleVP (everyDet (pure man'))
      (vpRule (pure saw') (aDet (pure woman')))) =
    ∃ y, woman' y ∧ ∀ x, man' x → saw' y x := rfl

/-- The surface reading via (18b), derived but not printed in the paper. -/
theorem every_man_saw_a_woman_surface :
    ContT.lower (sRuleNP (everyDet (pure man'))
      (vpRule (pure saw') (aDet (pure woman')))) =
    ∀ x, man' x → ∃ y, woman' y ∧ saw' y x := rfl

/-! ### Bounding scope displacement (§2.5)

His (20b) adjusts the S rule so that the clause's continuation applies
to the already-evaluated clause: quantifiers inside can no longer see
material outside, so *everyone* in his (21) "is not able to take scope
outside of the embedded clause". The adjustment "can only be made for
syntactic categories whose direct (i.e., uncontinuized) type is t". -/

/-- His (20b): the island-adjusted S rule. -/
def sRuleIsland (np : Cont Prop E) (vp : Cont Prop (E → Prop)) : Cont Prop Prop :=
  λ p => p (sRuleVP np vp id)

/-- Linglib note: (20b) is the substrate's `ContT.reset`. -/
theorem sRuleIsland_eq_reset (np : Cont Prop E) (vp : Cont Prop (E → Prop)) :
    sRuleIsland np vp = ContT.reset (sRuleVP np vp) := rfl

/-- What escapes an island is a value, never a scope-taker. -/
theorem sRuleIsland_simulates (np : Cont Prop E) (vp : Cont Prop (E → Prop))
    (g : Prop → Prop) :
    sRuleIsland np vp g = g (ContT.lower (sRuleVP np vp)) := rfl

/-- The Appendix's `VP → Vs S` rule, verb priority. -/
def vsRule (vs : Cont Prop (Prop → E → Prop)) (s : Cont Prop Prop) :
    Cont Prop (E → Prop) :=
  priorityFirst (λ T p => T p) vs s

variable (thought' : Prop → E → Prop)

/-- His (21): *A man thought everyone saw Mary* evaluates to (21b). -/
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

/-- His (27d): *John and Mary left*. -/
theorem john_and_mary_left :
    ContT.lower (sRuleVP (coord (individual j) (individual m)) (pure left')) =
    (left' j ∧ left' m) := rfl

/-! ### The Simulation Theorem (§5)

Continuization is conservative: on schema-derived meanings, evaluation
at the trivial continuation recovers the direct meaning, for every
choice of priority. The paper's Lemma generalizes the trivial
continuation to an arbitrary `g`, and the proofs below follow that
shape, discharging the daughters' hypotheses from the innermost
continuation out. The quantificational entries (13) are exactly the
meanings that break the hypotheses — the paper's own delimitation. -/

/-- A unit meaning simulates its direct value. -/
theorem simulation_pure (a : α) (g : α → Prop) :
    (pure a : Cont Prop α) g = g a := rfl

/-- Priority-first combination preserves simulation. -/
theorem simulation_priorityFirst (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) (g : γ → Prop) :
    priorityFirst M c₁ c₂ g = g (M m₁ m₂) := by
  show c₁ _ = _
  rw [h₁]
  exact h₂ _

/-- Priority-second combination preserves simulation. -/
theorem simulation_prioritySecond (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) (g : γ → Prop) :
    prioritySecond M c₁ c₂ g = g (M m₁ m₂) := by
  show c₂ _ = _
  rw [h₂]
  exact h₁ _

/-- "The result is the same, in the absence of quantification." -/
theorem simulation_orders_agree (M : α → β → γ) {c₁ : Cont Prop α}
    {c₂ : Cont Prop β} {m₁ : α} {m₂ : β}
    (h₁ : ∀ g, c₁ g = g m₁) (h₂ : ∀ g, c₂ g = g m₂) :
    priorityFirst M c₁ c₂ = prioritySecond M c₁ c₂ := by
  funext g
  rw [simulation_priorityFirst M h₁ h₂ g, simulation_prioritySecond M h₁ h₂ g]

/-- A simulating meaning evaluates at the trivial continuation to its
direct meaning. -/
theorem simulation (c : Cont Prop Prop) (p : Prop) (h : ∀ g, c g = g p) :
    ContT.lower c = p :=
  h id

end Barker2002
