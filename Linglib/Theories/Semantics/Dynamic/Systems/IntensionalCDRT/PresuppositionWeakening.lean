/-
# Presupposition Weakening with SF (Mendes 2025 §2.2)

The Subordinate Future (SF) weakens existential presuppositions of
strong quantifiers in restrictors.

## Key Data (Portuguese)

With indicative, strong quantifiers presuppose existence:
  (17) #Cada/todo livro que a Maria ler será interessante.
       "Every book that Maria reads.IND will be interesting"
       → Presupposes Maria will read books (fails if uncertain)

With SF, the presupposition is weakened:
  (18) Cada/todo livro que a Maria ler será interessante.
       "Every book that Maria reads.SF will be interesting"
       → No existence presupposition (felicitous even if uncertain)

## Analysis

The SF introduces modal displacement:
- Indicative: ∀x[book(x) ∧ reads(m,x)] → interesting(x)
  - Strong quantifier presupposes non-empty restriction
- SF: ∀s₁∈hist(s₀): ∀x[book(x,s₁) ∧ reads(m,x,s₁)] → interesting(x,s₁)
  - Quantification over situations weakens to conditional existence

## References

- Mendes, A. (2025). Indefiniteness in future reference. S&P 18(10).
- Heim, I. (1983). On the projection problem for presuppositions.
- Beaver, D. (2001). Presupposition and Assertion in Dynamic Semantics.
-/

import Linglib.Theories.Semantics.Dynamic.Systems.IntensionalCDRT.Situations
import Linglib.Theories.Semantics.Dynamic.Systems.IntensionalCDRT.ModalDonkeyAnaphora
import Linglib.Theories.Semantics.Compositional.Core.Time

namespace DynamicSemantics.IntensionalCDRT.PresuppositionWeakening

open Core.Time
open TruthConditional.Core.Time
open DynamicSemantics.IntensionalCDRT
open DynamicSemantics.IntensionalCDRT.Situations
open DynamicSemantics.IntensionalCDRT.ModalDonkeyAnaphora


/--
A presupposition: a condition that must be satisfied for an expression
to have a defined truth value.

Following Heim (1983), presuppositions are definedness conditions on
the input context.
-/
def Presupposition (W : Type*) := W → Prop

/--
Existential presupposition: the restrictor of a quantifier is non-empty.

For "every book that Maria reads", this presupposes:
  ∃x. book(x) ∧ reads(maria, x)
-/
def existentialPresup {W E : Type*}
    (restrictor : E → W → Prop) : Presupposition W :=
  λ w => ∃ x, restrictor x w

/--
Strong quantifier: quantifiers that carry existential presupposition.

- "every", "each", "both" presuppose non-empty domain
- "some", "a" do not (they assert existence)
-/
inductive QuantifierStrength where
  | strong  -- every, each, both, most
  | weak    -- some, a, many, few
  deriving DecidableEq, Repr

/--
Strong quantifiers presuppose non-empty restrictor.
-/
def hasExistentialPresup : QuantifierStrength → Bool
  | .strong => true
  | .weak => false


/--
Indicative restrictor: evaluates the restrictor at the actual world.

"Every book that Maria reads.IND..."
→ Presupposes books exist that Maria reads in the actual world
-/
def indicativeRestrictor {W Time E : Type*}
    (restrictor : E → Situation W Time → Prop)
    (s : Situation W Time) : E → Prop :=
  λ x => restrictor x s

/--
SF restrictor: quantifies over historical alternatives.

"Every book that Maria reads.SF..."
→ Quantifies over situations where Maria might read books
→ No presupposition that she actually reads any
-/
def sfRestrictor {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → Situation W Time → Prop)
    (s₀ : Situation W Time) : E → Prop :=
  λ x => ∃ s₁ ∈ historicalBase history s₀, restrictor x s₁


/--
A context satisfies a presupposition if the presupposition holds
throughout the context.

Following Heim's context change semantics: presuppositions are
requirements on the input context.
-/
def satisfiesPresup {W E : Type*}
    (c : IContext W E) (p : Presupposition W) : Prop :=
  ∀ gw ∈ c, p gw.2

/--
A presupposition is locally satisfied if it holds at the evaluation world.
-/
def locallySatisfied {W : Type*}
    (p : Presupposition W) (w : W) : Prop :=
  p w

/--
A presupposition is weakened to a conditional presupposition.

Weak(P) = "if there are relevant entities, then P"

This is what SF achieves: instead of presupposing existence,
it makes the assertion conditional on existence.
-/
def weakenedPresup {W : Type*}
    (p : Presupposition W)
    (condition : W → Prop) : Presupposition W :=
  λ w => condition w → p w


/--
Indicative preserves existential presupposition.

With indicative mood in the restrictor, the strong quantifier's
existential presupposition projects.

"Cada livro que Maria ler.IND será interessante"
→ Presupposes ∃x. book(x) ∧ reads(maria, x)
-/
theorem indicative_preserves_presup {W Time E : Type*}
    (restrictor : E → Situation W Time → Prop)
    (s : Situation W Time)
    (h_presup : ∃ x, indicativeRestrictor restrictor s x) :
    ∃ x, restrictor x s := by
  obtain ⟨x, hx⟩ := h_presup
  exact ⟨x, hx⟩

/--
SF weakens existential presupposition.

With SF in the restrictor, existence is only presupposed *conditionally*
on the relevant situation obtaining.

"Cada livro que Maria ler.SF será interessante"
→ No categorical presupposition; existence conditional on future

Quantifying over historical alternatives means
we don't presuppose existence in any particular world.
-/
theorem sf_weakens_presup {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → Situation W Time → Prop)
    (s₀ : Situation W Time)
    -- Even without actual existence at s₀...
    (h_no_actual : ¬∃ x, restrictor x s₀)
    -- ...SF restrictor can still be satisfied (in other situations)
    (h_possible : ∃ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁) :
    ∃ x, sfRestrictor history restrictor s₀ x := by
  obtain ⟨s₁, h_s₁, x, hx⟩ := h_possible
  use x
  unfold sfRestrictor
  exact ⟨s₁, h_s₁, hx⟩

/--
SF makes strong quantifiers felicitous in uncertain contexts.

When the speaker is uncertain whether the restrictor will be satisfied,
SF is felicitous but indicative is not.
-/
theorem sf_felicitous_under_uncertainty {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → Situation W Time → Prop)
    (s₀ : Situation W Time)
    -- Speaker is uncertain: some alternatives have entities, some don't
    (h_uncertainty : (∃ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁) ∧
                     (∃ s₂ ∈ historicalBase history s₀, ¬∃ x, restrictor x s₂)) :
    -- SF restrictor can be non-empty (felicitous)
    (∃ x, sfRestrictor history restrictor s₀ x) ∧
    -- But there's no guarantee of actual existence (IND would fail)
    (∃ s ∈ historicalBase history s₀, ¬∃ x, restrictor x s) := by
  constructor
  · obtain ⟨⟨s₁, h_s₁, x, hx⟩, _⟩ := h_uncertainty
    use x
    unfold sfRestrictor
    exact ⟨s₁, h_s₁, hx⟩
  · exact h_uncertainty.2


/--
Relative clause with indicative.

"todo livro [que Maria ler.IND]"
"every book [that Maria reads.IND]"

Structure: ∀x[book(x) ∧ reads(m,x,s₀)] → ...
Presupposes existence of books Maria reads at s₀.
-/
def relClauseIND {W Time E : Type*}
    (noun : E → Situation W Time → Prop)      -- "book"
    (relClause : E → Situation W Time → Prop) -- "Maria reads"
    (s : Situation W Time) : E → Prop :=
  λ x => noun x s ∧ relClause x s

/--
Relative clause with SF.

"todo livro [que Maria ler.SF]"
"every book [that Maria reads.SF]"

Structure: ∀s₁∈hist(s₀): ∀x[book(x,s₁) ∧ reads(m,x,s₁)] → ...
No categorical existence presupposition.
-/
def relClauseSF {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (noun : E → Situation W Time → Prop)
    (relClause : E → Situation W Time → Prop)
    (s₀ : Situation W Time) : E → Prop :=
  λ x => ∃ s₁ ∈ historicalBase history s₀, noun x s₁ ∧ relClause x s₁

/--
SF in relative clause weakens strong quantifier presupposition.

This is the formal version of the contrast in (17)-(18).
-/
theorem relClause_sf_weakens_quantifier {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (noun relClause : E → Situation W Time → Prop)
    (s₀ : Situation W Time)
    -- At s₀, there are no relevant entities (would fail with IND)
    (h_none_actual : ¬∃ x, noun x s₀ ∧ relClause x s₀)
    -- But in some alternative, there are
    (h_some_possible : ∃ s₁ ∈ historicalBase history s₀, ∃ x, noun x s₁ ∧ relClause x s₁) :
    -- SF version has non-empty extension (felicitous with "every")
    ∃ x, relClauseSF history noun relClause s₀ x := by
  obtain ⟨s₁, h_s₁, x, hx⟩ := h_some_possible
  use x
  unfold relClauseSF
  exact ⟨s₁, h_s₁, hx⟩


/--
Modal displacement: SF introduces quantification over situations,
which "displaces" the existential presupposition.

Without SF: ∃x.P(x) presupposed, ∀x.P(x) → Q(x) asserted
With SF: ∀s∈hist. [∃x.P(x,s) presupposed within s, ∀x.P(x,s)→Q(x,s) asserted]

The presupposition is now *local* to each situation, not global.
-/
def modalDisplacement {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor nuclear : E → Situation W Time → Prop)
    (s₀ : Situation W Time) : Prop :=
  ∀ s₁ ∈ historicalBase history s₀,
    (∃ x, restrictor x s₁) →  -- Local existence (within s₁)
    ∀ x, restrictor x s₁ → nuclear x s₁

/--
Modal displacement captures SF semantics.

The universal quantifier with SF is equivalent to modal displacement:
quantifying over situations, with local existence conditions.
-/
theorem sf_is_modal_displacement {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor nuclear : E → Situation W Time → Prop)
    (s₀ : Situation W Time) :
    -- "Every x that P.SF will Q" ≈ Modal displacement
    modalDisplacement history restrictor nuclear s₀ ↔
    ∀ s₁ ∈ historicalBase history s₀,
      ∀ x, restrictor x s₁ → nuclear x s₁ := by
  unfold modalDisplacement
  constructor
  · intro h s₁ hs₁ x hx
    by_cases h_ex : ∃ x, restrictor x s₁
    · exact h s₁ hs₁ h_ex x hx
    · -- If no x satisfies restrictor, vacuously true
      exfalso
      exact h_ex ⟨x, hx⟩
  · intro h s₁ hs₁ _ x hx
    exact h s₁ hs₁ x hx


/--
Accommodation vs modal displacement.

Presupposition accommodation: Adding the presupposition to the context.
Modal displacement: Quantifying over situations where presupposition holds.

SF uses modal displacement, not accommodation.
-/
inductive PresuppositionStrategy where
  | accommodation     -- Add presup to context
  | localAccommodation -- Add presup locally (under operator)
  | modalDisplacement  -- Quantify over situations (SF)
  deriving DecidableEq, Repr

/--
SF employs modal displacement strategy.
-/
def sfStrategy : PresuppositionStrategy :=
  .modalDisplacement

/--
Modal displacement is weaker than global accommodation.

With modal displacement, we only require existence in *some* accessible
situations, not in all of them.
-/
theorem modal_displacement_weaker_than_accommodation {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → Situation W Time → Prop)
    (s₀ : Situation W Time)
    -- Global accommodation: existence everywhere
    (h_global : ∀ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁)
    -- Need at least one situation in the historical base
    (h_nonempty : ∃ s, s ∈ historicalBase history s₀)
    -- Implies local existence (trivially)
    : ∃ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁ := by
  obtain ⟨s₁, h_s₁⟩ := h_nonempty
  exact ⟨s₁, h_s₁, h_global s₁ h_s₁⟩

end DynamicSemantics.IntensionalCDRT.PresuppositionWeakening
