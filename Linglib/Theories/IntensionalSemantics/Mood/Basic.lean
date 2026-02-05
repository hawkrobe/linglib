/-
# Mood Semantics

Semantic operators for grammatical mood (IND, SUBJ).

## Core Idea (Mendes 2025)

Mood operators function like determiners for situations:
- **SUBJ** (Subjunctive): Introduces a new situation dref (like indefinite "a")
- **IND** (Indicative): Retrieves/uses an existing situation (like definite "the")

This parallels the indefinite/definite distinction:
- Indefinites introduce discourse referents
- Definites retrieve existing referents

## Insight

The "Subordinate Future" (SF) in Portuguese/Spanish:
- Uses present morphology for future reference in subordinate contexts
- Is actually **subjunctive** - introduces a situation dref
- This dref is retrieved by the main clause for temporal anchoring

Example (Portuguese):
  "Se Maria estiver em casa, ela vai atender."
  "If Maria be.SF at home, she will answer."

The SF "estiver" introduces a future situation s₁ ∈ hist(s₀).
The main clause "vai atender" is evaluated relative to s₁'s time.

## CDRT Connection

In CDRT (Muskens 1996), these operators compose dynamically:
- SUBJ introduces a situation variable and updates the context
- IND retrieves a situation from the context

## References

- Mendes, A. (2025). Indefiniteness in future reference. S&P 18(10).
- Iatridou, S. (2000). The grammatical ingredients of counterfactuality.
- Portner, P. (2018). Mood. Oxford Handbook of Modality and Mood.
- Giannakidou, A. (1998). Polarity Sensitivity as (Non)Veridical Dependency.
-/

import Linglib.Theories.TruthConditional.Core.Time

namespace IntensionalSemantics.Mood

open TruthConditional.Core.Time


/--
Grammatical mood categories.

Following the typological literature:
- **Indicative**: The default, "realis" mood
- **Subjunctive**: Non-default, "irrealis" mood (covers many subtypes)
- **Imperative**: Directive mood (not treated here)
-/
inductive GramMood where
  | indicative
  | subjunctive
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Subjunctive subtypes (for finer-grained analysis).

Different languages grammaticalize different subjunctive functions:
- Counterfactual: contrary-to-fact conditionals
- Dubitative: epistemic uncertainty
- Optative: wishes and desires
- Potential: epistemic/circumstantial possibility
-/
inductive SubjunctiveType where
  | counterfactual  -- contrary to fact
  | dubitative      -- epistemic uncertainty
  | optative        -- wishes
  | potential       -- possibility
  | subordinateFuture  -- Mendes' SF (present morphology, future reference)
  deriving DecidableEq, Repr, BEq


/--
Type of situation predicates: (situation, situation) → Prop

The two situations are:
- s: The "local" or "described" situation
- s': The "anchor" or "reference" situation
-/
abbrev SitPred (W Time : Type*) := Situation W Time → Situation W Time → Prop

/--
SUBJ operator (Mendes 2025, Definition on p.29).

⟦SUBJ^{s₁}_{s₀}⟧ = λP. [s₁ | s₁ ∈ hist(s₀)]; P(s₁)(s₀)

The subjunctive:
1. Introduces a new situation dref s₁
2. Constrains s₁ to be in the historical alternatives of s₀
3. Passes s₁ and s₀ to the embedded predicate P

Analogous to an indefinite for situations.
-/
def SUBJ {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : SitPred W Time)
    (s₀ : Situation W Time) : Prop :=
  ∃ s₁ : Situation W Time,
    s₁ ∈ historicalBase history s₀ ∧ P s₁ s₀

/--
IND operator (Mendes 2025, Definition on p.29).

⟦IND_{s₁,s₂}⟧ = λP. [| s₂ ≤ w_{s₁}]; P(s₂)(s₁)

The indicative:
1. Retrieves existing situations s₁ and s₂
2. Requires s₂'s world to be "part of" s₁'s world (same world)
3. Passes s₂ and s₁ to P

Analogous to a definite for situations.
-/
def IND {W Time : Type*}
    (P : SitPred W Time)
    (s₁ s₂ : Situation W Time) : Prop :=
  s₂.world = s₁.world ∧ P s₂ s₁

/--
Simplified IND: Just pass through with world check.

For cases where we're already working with a single world.
-/
def INDsimple {W Time : Type*}
    (P : Situation W Time → Prop)
    (s : Situation W Time) : Prop :=
  P s


/--
A situation context: a list of available situation drefs.

In CDRT, contexts track discourse referents. Here we track situations.
-/
structure SitContext (W Time : Type*) where
  /-- Available situation drefs -/
  situations : List (Situation W Time)
  /-- The "current" or "local" situation (for evaluation) -/
  current : Situation W Time
  deriving Repr

/--
Dynamic situation predicate: updates the situation context.
-/
abbrev DynSitPred (W Time : Type*) := SitContext W Time → SitContext W Time → Prop

/--
Dynamic SUBJ: introduces a situation and adds it to the context.

⟦SUBJ⟧_dyn = λP.λc. ∃s₁ ∈ hist(c.current). P({...c, situations := s₁ :: c.situations})
-/
def SUBJdyn {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : DynSitPred W Time)
    (c : SitContext W Time) : Prop :=
  ∃ s₁ : Situation W Time,
    s₁ ∈ historicalBase history c.current ∧
    ∃ c' : SitContext W Time,
      c'.situations = s₁ :: c.situations ∧
      c'.current = s₁ ∧
      P { situations := s₁ :: c.situations, current := s₁ } c'

/--
Dynamic IND: retrieves the most recent situation from context.

⟦IND⟧_dyn = λP.λc. c.situations.head? = some s → P(c)(c)
-/
def INDdyn {W Time : Type*}
    (P : DynSitPred W Time)
    (c : SitContext W Time) : Prop :=
  match c.situations with
  | [] => False  -- No situation to retrieve
  | s :: _ => c.current.world = s.world ∧ P c c


/--
Mood selection by embedding predicates.

Certain predicates select for specific moods in their complement:
- "know", "see" → typically indicative
- "want", "wish" → typically subjunctive
- "doubt", "deny" → subjunctive in many languages
-/
inductive MoodSelector where
  | indicativeSelecting   -- "know", "see", "believe"
  | subjunctiveSelecting  -- "want", "wish", "demand"
  | moodNeutral           -- "say", "think" (varies by language)
  deriving DecidableEq, Repr, BEq

/--
Does the selector prefer subjunctive?
-/
def prefersSubjunctive : MoodSelector → Bool
  | .indicativeSelecting => false
  | .subjunctiveSelecting => true
  | .moodNeutral => false  -- default to indicative


/--
Conditional with SF antecedent (Mendes 2025, main application).

"If Maria be.SF home, she will answer"

Structure:
1. SUBJ introduces s₁ ∈ hist(s₀) (the "if" situation)
2. Antecedent is evaluated at s₁
3. Consequent is temporally anchored to s₁

This explains why SF enables future reference: the subjunctive
introduces a future situation that the main clause can refer back to.
-/
def conditionalSF {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (antecedent : Situation W Time → Prop)  -- "Maria is home"
    (consequent : Situation W Time → Situation W Time → Prop)  -- "she answers"
    (s₀ : Situation W Time) : Prop :=
  SUBJ history (λ s₁ s₀' => antecedent s₁ → consequent s₁ s₀') s₀

/--
Standard indicative conditional (for comparison).

"If Maria is home, she answers"

Here the antecedent is evaluated at the same situation as the main clause.
No new situation is introduced.
-/
def conditionalIND {W Time : Type*}
    (antecedent : Situation W Time → Prop)
    (consequent : Situation W Time → Prop)
    (s : Situation W Time) : Prop :=
  antecedent s → consequent s


/--
Temporal shift (Mendes 2025).

The subjunctive future (SF) enables future reference because:
1. SUBJ introduces a situation s₁ in the historical alternatives
2. Historical alternatives can have times ≥ current time
3. The consequent is evaluated relative to τ(s₁), not τ(s₀)

This temporal shift gives SF its future-oriented interpretation.
-/
def temporalShift {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : Situation W Time → Prop)
    (s₀ : Situation W Time) : Prop :=
  ∃ s₁ : Situation W Time,
    s₁ ∈ historicalBase history s₀ ∧
    s₁.time ≥ s₀.time ∧  -- Future or present
    P s₁

/--
The future-oriented restriction: s₁ must be strictly after s₀.
-/
def futureShift {W Time : Type*} [LT Time] [LE Time]
    (history : WorldHistory W Time)
    (P : Situation W Time → Prop)
    (s₀ : Situation W Time) : Prop :=
  ∃ s₁ : Situation W Time,
    s₁ ∈ historicalBase history s₀ ∧
    s₁.time > s₀.time ∧  -- Strictly future
    P s₁


/--
SUBJ is existential: it introduces a situation.
-/
theorem subj_is_existential {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : SitPred W Time)
    (s₀ : Situation W Time) :
    SUBJ history P s₀ → ∃ s₁, P s₁ s₀ := by
  intro ⟨s₁, _, hP⟩
  exact ⟨s₁, hP⟩

/--
SUBJ constrains to historical base: the introduced situation
is in the historical alternatives.
-/
theorem subj_in_hist {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (P : SitPred W Time)
    (s₀ : Situation W Time) :
    SUBJ history P s₀ → ∃ s₁, s₁ ∈ historicalBase history s₀ ∧ P s₁ s₀ := by
  intro h
  exact h

/--
IND requires same world: the two situations must share a world.
-/
theorem ind_same_world {W Time : Type*}
    (P : SitPred W Time)
    (s₁ s₂ : Situation W Time) :
    IND P s₁ s₂ → s₂.world = s₁.world := by
  intro ⟨h, _⟩
  exact h

/--
SUBJ with reflexive history: if the history is reflexive,
the current situation is always an option.
-/
theorem subj_current_option {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (h_refl : history.reflexive)
    (P : SitPred W Time)
    (s₀ : Situation W Time)
    (h_P : P s₀ s₀) :
    SUBJ history P s₀ := by
  use s₀
  refine ⟨?_, h_P⟩
  -- s₀ ∈ historicalBase history s₀
  simp only [historicalBase, Set.mem_setOf_eq]
  exact ⟨h_refl s₀.world s₀.time, le_refl s₀.time⟩


/--
Non-veridicality (Giannakidou 1998):

A propositional operator F is non-veridical iff:
  F(p) does NOT entail p

The subjunctive is associated with non-veridical contexts because
SUBJ introduces a situation that may differ from the actual one.
-/
def nonVeridical {W Time : Type*}
    (F : (Situation W Time → Prop) → Situation W Time → Prop) : Prop :=
  ∃ (P : Situation W Time → Prop) (s : Situation W Time),
    F P s ∧ ¬P s

/--
SUBJ is non-veridical: the introduced situation may differ from actual.

This follows from the existential nature of SUBJ: it quantifies over
situations in the historical base, which includes non-actual futures.
-/
theorem subj_nonveridical {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    -- Need: history has an option distinct from the evaluation point
    (h_branching : ∃ s₀ s₁ : Situation W Time,
      s₁ ∈ historicalBase history s₀ ∧ s₀ ≠ s₁) :
    nonVeridical (λ P s₀ => SUBJ history (λ s₁ _ => P s₁) s₀) := by
  obtain ⟨s₀, s₁, h₁, hne⟩ := h_branching
  use (λ s => s = s₁), s₀
  refine ⟨⟨s₁, h₁, rfl⟩, ?_⟩
  -- ¬(s₀ = s₁)
  exact hne

end IntensionalSemantics.Mood
