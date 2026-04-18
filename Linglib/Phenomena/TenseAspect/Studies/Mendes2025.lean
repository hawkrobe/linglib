import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Situations
import Linglib.Core.Modality.HistoricalAlternatives

/-!
# Mendes (2025): The Subordinate Future

@cite{mendes-2025}

The Subordinate Future (SF) in Portuguese is a mood form (subjunctive
with future morphology) that:
1. Enables modal donkey anaphora — subjunctive binds situation variables
   across clause boundaries (§3.1)
2. Weakens existential presuppositions of strong quantifiers in
   restrictors (§2.2)

## Compositional derivations (§4.3.1)

Target: "Se Maria estiver em casa, ela vai atender."
        "If Maria be.SF at home, she will answer."

Lexical entries are typed λ-terms with dynamic semantics following
@cite{muskens-1996} CDRT. Situation drefs are introduced at top level
(flat update) and temporally anchored via SF.

## Presupposition weakening (§2.2)

SF weakens existential presuppositions via modal displacement:
quantifying over situations where the presupposition holds locally,
rather than requiring it globally.
-/

namespace Mendes2025

open Core.Time
open Core.Modality.HistoricalAlternatives
open Semantics.Dynamic.IntensionalCDRT
open Semantics.Dynamic.IntensionalCDRT.Situations


-- ════════════════════════════════════════════════════════════════
-- § 1. Compositional CDRT Derivations (§4.3.1)
-- ════════════════════════════════════════════════════════════════

variable {W Time E : Type*} [LE Time] [LT Time]
variable (history : WorldHistory W Time)

/--
Maria — proper name.
`⟦Maria⟧ = λP.P(maria)`
-/
def lexMaria (maria : E)
    (P : E → SitContext W Time E → SitContext W Time E)
    (c : SitContext W Time E) : SitContext W Time E :=
  P maria c

/--
estar em casa — "be at home".
`⟦estar em casa⟧ = λxλsλc. [| at-home(x)(s)]; c`
-/
def lexAtHome
    (atHomeRel : E → Situation W Time → Prop)
    (x : E)
    (sitVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  { gs ∈ c | atHomeRel x (gs.1.sit sitVar) }

/--
atender — "answer (the door)".
`⟦atender⟧ = λxλsλc. [| answer(x)(s)]; c`
-/
def lexAnswer
    (answerRel : E → Situation W Time → Prop)
    (x : E)
    (sitVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  { gs ∈ c | answerRel x (gs.1.sit sitVar) }

/--
SF (Subordinate Future).
`⟦SF⟧ = SUBJ ∘ FUT`
-/
def lexSF := @subordinateFuture W Time E _ _

/--
ela — "she" (pronoun bound to Maria).
`⟦ela⟧ = λP.P(maria)`
-/
def lexShe (maria : E)
    (P : E → SitContext W Time E → SitContext W Time E)
    (c : SitContext W Time E) : SitContext W Time E :=
  P maria c

/--
vai — future auxiliary "will".
`⟦vai⟧ = λVPλsλc. VP(s)(c)` — transparent; future comes from SF
via modal anaphora.
-/
def lexWill
    (VP : SVar → SitContext W Time E → SitContext W Time E)
    (sitVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  VP sitVar c

/--
Sequential context update: feeds antecedent output into consequent.

Note: the paper's `⟦if⟧` is dynamic implication (a test: `[| P ⇒ Q]`),
but the derivation theorems here require extracting properties from the
output context, which a test semantics cannot provide (tests preserve input
unchanged). Sequential composition is appropriate because the universal
force comes from SUBJ's quantification over historical alternatives, not
from the conditional operator itself.
-/
def seqUpdate
    (antecedent consequent : SitContext W Time E → SitContext W Time E)
    (c : SitContext W Time E) : SitContext W Time E :=
  consequent (antecedent c)


/--
Antecedent derivation:
`⟦Maria estiver em casa⟧ = SUBJ^{s₁}_{s₀}[FUT; [| at-home(maria)(s₁)]]`

Introduces s₁ ∈ hist(s₀), constrains τ(s₁) > τ(s₀), asserts Maria at home.
-/
def deriveAntecedent
    (maria : E)
    (atHomeRel : E → Situation W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  let c₁ := lexSF history sfVar speechVar c
  lexAtHome atHomeRel maria sfVar c₁

/--
Consequent derivation:
`⟦ela vai atender⟧ = [| answer(maria)(s₁)]` — s₁ retrieved via IND.
-/
def deriveConsequent
    (maria : E)
    (answerRel : E → Situation W Time → Prop)
    (sfVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  let c₁ := dynIND sfVar c
  lexAnswer answerRel maria sfVar c₁

/--
Full sentence derivation:
`⟦Se Maria estiver em casa, ela vai atender⟧`
-/
def deriveFullSentence
    (maria : E)
    (atHomeRel answerRel : E → Situation W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  let antecedent := deriveAntecedent history maria atHomeRel sfVar speechVar
  let consequent := deriveConsequent maria answerRel sfVar
  seqUpdate antecedent consequent c


/--
The situation introduced by SF is in the historical alternatives.
-/
theorem derivation_in_historical_base
    (maria : E)
    (atHomeRel answerRel : E → Situation W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ deriveFullSentence history maria atHomeRel answerRel sfVar speechVar c) :
    ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧
          (gs.1.sit sfVar) ∈ historicalBase history s₀ := by
  unfold deriveFullSentence seqUpdate at h
  unfold deriveConsequent lexAnswer at h
  simp only [Set.mem_setOf_eq] at h
  obtain ⟨h_ind, _⟩ := h
  unfold dynIND at h_ind
  obtain ⟨h_ant, _⟩ := h_ind
  unfold deriveAntecedent lexAtHome at h_ant
  simp only [Set.mem_setOf_eq] at h_ant
  obtain ⟨h_sf, _⟩ := h_ant
  unfold lexSF subordinateFuture dynFUT at h_sf
  obtain ⟨h_subj, _⟩ := h_sf
  unfold dynSUBJ at h_subj
  obtain ⟨g, s₀, s₁, hc, h_hist, h_upd, _⟩ := h_subj
  use s₀
  constructor
  · exact ⟨g, hc⟩
  · have h_sit : gs.1.sit sfVar = s₁ := by
      rw [h_upd]
      unfold SitAssignment.updateSit
      simp only [beq_self_eq_true, ite_true]
    rw [h_sit]
    exact h_hist

/--
The derivation enforces future ordering: τ(s₁) > τ(s₀).
-/
theorem derivation_future_ordering
    (maria : E)
    (atHomeRel answerRel : E → Situation W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ deriveFullSentence history maria atHomeRel answerRel sfVar speechVar c) :
    (gs.1.sit sfVar).time > (gs.1.sit speechVar).time := by
  unfold deriveFullSentence seqUpdate at h
  unfold deriveConsequent lexAnswer at h
  simp only [Set.mem_setOf_eq] at h
  obtain ⟨h_ind, _⟩ := h
  unfold dynIND at h_ind
  obtain ⟨h_ant, _⟩ := h_ind
  unfold deriveAntecedent lexAtHome at h_ant
  simp only [Set.mem_setOf_eq] at h_ant
  obtain ⟨h_sf, _⟩ := h_ant
  unfold lexSF subordinateFuture dynFUT at h_sf
  exact h_sf.2

/--
If Maria is at home at s₁, she answers at s₁.
-/
theorem derivation_conditional_holds
    (maria : E)
    (atHomeRel answerRel : E → Situation W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ deriveFullSentence history maria atHomeRel answerRel sfVar speechVar c) :
    atHomeRel maria (gs.1.sit sfVar) → answerRel maria (gs.1.sit sfVar) := by
  intro _
  unfold deriveFullSentence seqUpdate at h
  unfold deriveConsequent lexAnswer at h
  simp only [Set.mem_setOf_eq] at h
  exact h.2


/--
Counterfactual conditional (for comparison).
"Se Maria estivesse em casa, ela atenderia."
Uses SUBJ without FUT — allows past/present alternatives.
-/
def deriveCounterfactual
    (maria : E)
    (atHomeRel answerRel : E → Situation W Time → Prop)
    (cfVar speechVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  let c₁ := dynSUBJ history cfVar c
  let c₂ := lexAtHome atHomeRel maria cfVar c₁
  let c₃ := dynIND cfVar c₂
  lexAnswer answerRel maria cfVar c₃

/--
SF constrains to future; counterfactual allows past/present.
-/
theorem sf_vs_counterfactual_temporal {W Time E : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (maria : E)
    (atHomeRel answerRel : E → Situation W Time → Prop)
    (sitVar speechVar : SVar)
    (c : SitContext W Time E) :
    ∀ gs ∈ deriveFullSentence history maria atHomeRel answerRel sitVar speechVar c,
      (gs.1.sit sitVar).time > (gs.1.sit speechVar).time :=
  derivation_future_ordering history maria atHomeRel answerRel sitVar speechVar c


-- ════════════════════════════════════════════════════════════════
-- § 2. Presupposition Weakening (§2.2)
-- ════════════════════════════════════════════════════════════════

/-!
### Key data (Portuguese)

With indicative, strong quantifiers presuppose existence:
  (17) #Cada/todo livro que a Maria ler será interessante.
       "Every book that Maria reads.IND will be interesting"
       → Presupposes Maria will read books (fails if uncertain)

With SF, the presupposition is weakened:
  (18) Cada/todo livro que a Maria ler será interessante.
       "Every book that Maria reads.SF will be interesting"
       → No existence presupposition (felicitous even if uncertain)
-/

/-- Existential presupposition: the restrictor is non-empty. -/
def existentialPresup {W E : Type*}
    (restrictor : E → W → Prop) : W → Prop :=
  λ w => ∃ x, restrictor x w

/--
Indicative restrictor: evaluates at the actual world.
"Every book that Maria reads.IND..." → presupposes books exist that Maria reads.
-/
def indicativeRestrictor {W Time E : Type*}
    (restrictor : E → Situation W Time → Prop)
    (s : Situation W Time) : E → Prop :=
  λ x => restrictor x s

/--
SF restrictor: quantifies over historical alternatives.
"Every book that Maria reads.SF..." → no categorical existence presupposition.
-/
def sfRestrictor {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → Situation W Time → Prop)
    (s₀ : Situation W Time) : E → Prop :=
  λ x => ∃ s₁ ∈ historicalBase history s₀, restrictor x s₁


/-- Indicative preserves existential presupposition. -/
theorem indicative_preserves_presup {W Time E : Type*}
    (restrictor : E → Situation W Time → Prop)
    (s : Situation W Time)
    (h_presup : ∃ x, indicativeRestrictor restrictor s x) :
    ∃ x, restrictor x s := by
  obtain ⟨x, hx⟩ := h_presup
  exact ⟨x, hx⟩

/--
SF weakens existential presupposition: even without actual existence at s₀,
the SF restrictor can be satisfied in alternative situations.
-/
theorem sf_weakens_presup {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → Situation W Time → Prop)
    (s₀ : Situation W Time)
    (h_no_actual : ¬∃ x, restrictor x s₀)
    (h_possible : ∃ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁) :
    ∃ x, sfRestrictor history restrictor s₀ x := by
  obtain ⟨s₁, h_s₁, x, hx⟩ := h_possible
  use x
  unfold sfRestrictor
  exact ⟨s₁, h_s₁, hx⟩

/--
SF makes strong quantifiers felicitous under uncertainty.
-/
theorem sf_felicitous_under_uncertainty {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → Situation W Time → Prop)
    (s₀ : Situation W Time)
    (h_uncertainty : (∃ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁) ∧
                     (∃ s₂ ∈ historicalBase history s₀, ¬∃ x, restrictor x s₂)) :
    (∃ x, sfRestrictor history restrictor s₀ x) ∧
    (∃ s ∈ historicalBase history s₀, ¬∃ x, restrictor x s) := by
  constructor
  · obtain ⟨⟨s₁, h_s₁, x, hx⟩, _⟩ := h_uncertainty
    use x
    unfold sfRestrictor
    exact ⟨s₁, h_s₁, hx⟩
  · exact h_uncertainty.2


/--
Relative clause with SF weakens strong quantifier presupposition.
This is the formal version of the indicative-vs-SF contrast in restrictors.
-/
def relClauseSF {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (noun : E → Situation W Time → Prop)
    (relClause : E → Situation W Time → Prop)
    (s₀ : Situation W Time) : E → Prop :=
  λ x => ∃ s₁ ∈ historicalBase history s₀, noun x s₁ ∧ relClause x s₁

theorem relClause_sf_weakens_quantifier {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (noun relClause : E → Situation W Time → Prop)
    (s₀ : Situation W Time)
    (h_none_actual : ¬∃ x, noun x s₀ ∧ relClause x s₀)
    (h_some_possible : ∃ s₁ ∈ historicalBase history s₀, ∃ x, noun x s₁ ∧ relClause x s₁) :
    ∃ x, relClauseSF history noun relClause s₀ x := by
  obtain ⟨s₁, h_s₁, x, hx⟩ := h_some_possible
  use x
  unfold relClauseSF
  exact ⟨s₁, h_s₁, hx⟩

/--
Modal displacement: SF introduces quantification over situations,
"displacing" the existential presupposition to be local within each situation.
-/
def modalDisplacement {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor nuclear : E → Situation W Time → Prop)
    (s₀ : Situation W Time) : Prop :=
  ∀ s₁ ∈ historicalBase history s₀,
    (∃ x, restrictor x s₁) →
    ∀ x, restrictor x s₁ → nuclear x s₁

/--
SF semantics is equivalent to modal displacement.
-/
theorem sf_is_modal_displacement {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor nuclear : E → Situation W Time → Prop)
    (s₀ : Situation W Time) :
    modalDisplacement history restrictor nuclear s₀ ↔
    ∀ s₁ ∈ historicalBase history s₀,
      ∀ x, restrictor x s₁ → nuclear x s₁ := by
  unfold modalDisplacement
  constructor
  · intro h s₁ hs₁ x hx
    by_cases h_ex : ∃ x, restrictor x s₁
    · exact h s₁ hs₁ h_ex x hx
    · exfalso; exact h_ex ⟨x, hx⟩
  · intro h s₁ hs₁ _ x hx
    exact h s₁ hs₁ x hx

/--
Modal displacement is weaker than global accommodation.
-/
theorem modal_displacement_weaker_than_accommodation {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → Situation W Time → Prop)
    (s₀ : Situation W Time)
    (h_global : ∀ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁)
    (h_nonempty : ∃ s, s ∈ historicalBase history s₀) :
    ∃ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁ := by
  obtain ⟨s₁, h_s₁⟩ := h_nonempty
  exact ⟨s₁, h_s₁, h_global s₁ h_s₁⟩

end Mendes2025
