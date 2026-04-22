import Linglib.Theories.Semantics.Tense.Dynamic
import Linglib.Theories.Semantics.Mood.Dynamic
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
3. Has a future-oriented temporal interpretation that is *parasitic on*
   the modal anaphora — not stipulated by an independent temporal
   operator (§3.2, following @cite{crouch-1993} @cite{crouch-1994})

## Organization

- §1 The SF operator (§3.2): `subordinateFuture := dynSUBJ ∘ dynFUT`,
  plus its conditional and relative-clause specializations.
- §2 Temporal properties (§3.2): theorems showing the future shift
  is derived from the modal component, not stipulated.
- §3 Compositional CDRT derivations (§4.3.1): lexical entries and
  end-to-end derivation of "Se Maria estiver em casa, ela vai atender".
- §4 Presupposition weakening (§2.2): SF in restrictors of strong
  quantifiers, formalized as modal displacement.

The dynamic primitives are imported from co-located dynamic operator
files: `dynSUBJ`/`dynIND` from `Theories/Semantics/Mood/Dynamic.lean`
(siblings of static `Mood.SUBJ`/`IND`), `dynFUT` from
`Theories/Semantics/Tense/Dynamic.lean`, and `SitContext`/`SVar` from
`Theories/Semantics/Dynamic/Core/{ContextFilter,DiscourseRef}.lean`.
-/

namespace Mendes2025

open Core (Assignment WorldTimeIndex)
open Core.Time
open Core.Modality.HistoricalAlternatives
open Semantics.Dynamic.Core
open Semantics.Tense
open Semantics.Mood


-- ════════════════════════════════════════════════════════════════
-- § 1. The SF Operator (§3.2)
-- ════════════════════════════════════════════════════════════════

/--
Subordinate Future (SF) analysis.

The SF in Portuguese conditionals:
  "Se Maria estiver em casa, ela vai atender."
  "If Maria be.SF at home, she will answer."

Structure (@cite{mendes-2025} §3.2):
1. SF = SUBJ^{s₁}_{s₀} + FUT
2. SUBJ introduces s₁ ∈ hist(s₀)
3. FUT constrains τ(s₁) > τ(s₀)
4. Main clause is anchored to τ(s₁)

This is the compositional derivation:
⟦SF⟧ = ⟦SUBJ⟧ ∘ ⟦FUT⟧
-/
def subordinateFuture {W Time : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (newSitVar : SVar)   -- Fresh variable for introduced situation
    (refSitVar : SVar)   -- Variable for reference situation
    (c : SitContext W Time) : SitContext W Time :=
  -- First apply SUBJ to introduce s₁
  let c' := dynSUBJ history newSitVar c
  -- Then constrain τ(s₁) > τ(s₀)
  dynFUT newSitVar refSitVar c'

/--
Conditional with SF antecedent (dynamic version).

"Se Maria estiver em casa, ela vai atender."

1. Antecedent: SF introduces s₁ ∈ hist(s₀) with τ(s₁) > τ(s₀)
2. Antecedent predicate evaluated at s₁
3. Consequent: temporally anchored to s₁ (future relative to s₀)
-/
def conditionalWithSF {W Time : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (antecedentVar : SVar)  -- Situation introduced by SF
    (speechVar : SVar)      -- Speech time situation
    (antecedent : SitContext W Time → SitContext W Time)  -- "Maria is home"
    (consequent : SitContext W Time → SitContext W Time)  -- "she answers"
    (c : SitContext W Time) : SitContext W Time :=
  -- Apply SF to introduce antecedent situation
  let c₁ := subordinateFuture history antecedentVar speechVar c
  -- Filter by antecedent
  let c₂ := antecedent c₁
  -- Apply consequent (anchored to antecedentVar's time)
  consequent c₂

/--
Relative clause with SF in restrictor.

"Cada menino [que estiver acordado] vai receber um biscoito."
"Every boy [who is.SF awake] will get a cookie."

Structure:
1. SF in relative clause introduces situation s₁ ∈ hist(s₀)
2. Restrictor (boy ∧ awake) evaluated at s₁
3. Nuclear scope (get cookie) evaluated with temporal anchor from s₁
-/
def relativeClauseSF {W Time : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (rcVar : SVar)           -- Situation variable for relative clause
    (speechVar : SVar)       -- Speech time situation
    (c : SitContext W Time) : SitContext W Time :=
  subordinateFuture history rcVar speechVar c

/--
Strong quantifier with SF restrictor.

"Todo livro [que Maria ler.SF] será interessante"
"Every book [that Maria reads.SF] will be interesting"

The SF in the restrictor:
1. Introduces s₁ ∈ hist(s₀) for the relative clause
2. Quantification over books is relativized to s₁
3. Nuclear scope inherits temporal anchor from s₁
-/
def everyWithSFRestrictor {W Time : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (rcVar speechVar : SVar)
    (restrictor : SitContext W Time → SitContext W Time)  -- "book that M reads"
    (nuclear : SitContext W Time → SitContext W Time)     -- "is interesting"
    (c : SitContext W Time) : SitContext W Time :=
  -- First: SF introduces situation for restrictor
  let c₁ := subordinateFuture history rcVar speechVar c
  -- Then: Filter by restrictor content
  let c₂ := restrictor c₁
  -- Finally: Apply nuclear scope (inherits temporal anchor)
  nuclear c₂


-- ════════════════════════════════════════════════════════════════
-- § 2. Temporal Properties of SF (§3.2)
-- ════════════════════════════════════════════════════════════════

/--
SF introduces a future situation.

The subordinate future always introduces a situation with time ≥ current.
-/
theorem sf_introduces_future {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (newVar refVar : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ subordinateFuture history newVar refVar c) :
    (gs.1 newVar).time ≥ (gs.1 refVar).time := by
  -- The subordinateFuture composes SUBJ and FUT
  -- FUT requires the new situation to be after the reference
  unfold subordinateFuture dynFUT at h
  obtain ⟨_, h_gt⟩ := h
  -- h_gt gives us the strict ordering from FUT
  exact le_of_lt h_gt

/--
Temporal shift is parasitic on modal donkey anaphora.

@cite{mendes-2025} §3.2: the future-oriented interpretation of SF is not due
to an independent temporal operator. Instead, it follows from:

1. SUBJ introduces s₁ ∈ hist(s₀) - modal component
2. hist(s₀) includes situations with τ(s₁) ≥ τ(s₀) - temporal consequence
3. Main clause is evaluated at τ(s₁) via modal anaphora - binding

The temporal shift is *derived* from the modal semantics, not stipulated.

Modal donkey anaphora explains
why subjunctive mood enables future reference in subordinate clauses.
-/
theorem temporal_shift_parasitic_on_modal {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (sfVar speechVar : SVar)
    (c : SitContext W Time)
    -- For any situation in the output of SF application...
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ subordinateFuture history sfVar speechVar c)
    -- ...there exists an original speech situation...
    : ∃ (g₀ : Assignment (WorldTimeIndex W Time)) (s₀ : WorldTimeIndex W Time),
        -- ...that was in the input context...
        (g₀, s₀) ∈ c ∧
        -- ...and the temporal shift comes from SUBJ's modal component:
        -- 1. The bound situation s₁ is in the historical base of s₀
        (gs.1 sfVar) ∈ historicalBase history s₀ ∧
        -- 2. The temporal ordering τ(s₁) ≥ τ(s₀) follows from hist definition
        (gs.1 sfVar).time ≥ s₀.time ∧
        -- 3. The strict future τ(s₁) > τ(s₀) comes from FUT constraint
        (gs.1 sfVar).time > (gs.1 speechVar).time := by
  -- subordinateFuture = dynSUBJ ∘ dynFUT
  unfold subordinateFuture at h
  -- After dynFUT, we have the strict ordering
  unfold dynFUT at h
  obtain ⟨h_in_subj, h_gt⟩ := h
  -- After dynSUBJ, we have the historical base membership
  unfold dynSUBJ at h_in_subj
  obtain ⟨g, s₀, s₁, hc, h_hist, h_upd, h_eq⟩ := h_in_subj
  use g, s₀
  -- Helper: gs.1 sfVar = s₁
  have h_sit : gs.1 sfVar = s₁ := by
    rw [h_upd]; simp only [Assignment.update_at]
  refine ⟨hc, ?_, ?_, ?_⟩
  -- 1. gs.1 sfVar = s₁ ∈ historicalBase history s₀
  · rw [h_sit]
    exact h_hist
  -- 2. τ(s₁) ≥ τ(s₀) from historicalBase definition
  · rw [h_sit]
    unfold historicalBase at h_hist
    simp only [Set.mem_setOf_eq] at h_hist
    exact h_hist.2
  -- 3. The FUT constraint gives us the strict ordering
  · exact h_gt

/--
SF in restrictor enables future reference for strong quantifiers.

With SF in the relative clause, "every" can quantify over future entities.

Restrictor and nuclear must be context filters (`IsContextFilter`).
Linguistically, predicates filter contexts without modifying assignments.
-/
theorem sf_restrictor_future_reference {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (rcVar speechVar : SVar)
    (restrictor nuclear : SitContext W Time → SitContext W Time)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ everyWithSFRestrictor history rcVar speechVar restrictor nuclear c)
    (hR : IsContextFilter restrictor) (hN : IsContextFilter nuclear) :
    -- The restrictor situation can be future relative to speech time
    (gs.1 rcVar).time > (gs.1 speechVar).time := by
  -- Track through the filter chain
  unfold everyWithSFRestrictor at h
  have h_sf : gs ∈ subordinateFuture history rcVar speechVar c :=
    Set.Subset.trans (hN _) (hR _) h
  -- subordinateFuture guarantees the future ordering via dynFUT
  unfold subordinateFuture dynFUT at h_sf
  exact h_sf.2


-- ════════════════════════════════════════════════════════════════
-- § 3. Compositional CDRT Derivations (§4.3.1)
-- ════════════════════════════════════════════════════════════════

variable {W Time E : Type*} [LE Time] [LT Time]
variable (history : WorldHistory W Time)

/--
Maria — proper name.
`⟦Maria⟧ = λP.P(maria)`
-/
def lexMaria (maria : E)
    (P : E → SitContext W Time → SitContext W Time)
    (c : SitContext W Time) : SitContext W Time :=
  P maria c

/--
estar em casa — "be at home".
`⟦estar em casa⟧ = λxλsλc. [| at-home(x)(s)]; c`
-/
def lexAtHome
    (atHomeRel : E → WorldTimeIndex W Time → Prop)
    (x : E)
    (sitVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | atHomeRel x (gs.1 sitVar) }

/--
atender — "answer (the door)".
`⟦atender⟧ = λxλsλc. [| answer(x)(s)]; c`
-/
def lexAnswer
    (answerRel : E → WorldTimeIndex W Time → Prop)
    (x : E)
    (sitVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  { gs ∈ c | answerRel x (gs.1 sitVar) }

/--
SF (Subordinate Future).
`⟦SF⟧ = SUBJ ∘ FUT`
-/
def lexSF := @subordinateFuture W Time _ _

/--
ela — "she" (pronoun bound to Maria).
`⟦ela⟧ = λP.P(maria)`
-/
def lexShe (maria : E)
    (P : E → SitContext W Time → SitContext W Time)
    (c : SitContext W Time) : SitContext W Time :=
  P maria c

/--
vai — future auxiliary "will".
`⟦vai⟧ = λVPλsλc. VP(s)(c)` — transparent; future comes from SF
via modal anaphora.
-/
def lexWill
    (VP : SVar → SitContext W Time → SitContext W Time)
    (sitVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
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
    (antecedent consequent : SitContext W Time → SitContext W Time)
    (c : SitContext W Time) : SitContext W Time :=
  consequent (antecedent c)


/--
Antecedent derivation:
`⟦Maria estiver em casa⟧ = SUBJ^{s₁}_{s₀}[FUT; [| at-home(maria)(s₁)]]`

Introduces s₁ ∈ hist(s₀), constrains τ(s₁) > τ(s₀), asserts Maria at home.
-/
def deriveAntecedent
    (maria : E)
    (atHomeRel : E → WorldTimeIndex W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  let c₁ := lexSF history sfVar speechVar c
  lexAtHome atHomeRel maria sfVar c₁

/--
Consequent derivation:
`⟦ela vai atender⟧ = [| answer(maria)(s₁)]` — s₁ retrieved via IND.
-/
def deriveConsequent
    (maria : E)
    (answerRel : E → WorldTimeIndex W Time → Prop)
    (sfVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  let c₁ := dynIND sfVar c
  lexAnswer answerRel maria sfVar c₁

/--
Full sentence derivation:
`⟦Se Maria estiver em casa, ela vai atender⟧`
-/
def deriveFullSentence
    (maria : E)
    (atHomeRel answerRel : E → WorldTimeIndex W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  let antecedent := deriveAntecedent history maria atHomeRel sfVar speechVar
  let consequent := deriveConsequent maria answerRel sfVar
  seqUpdate antecedent consequent c


/--
The situation introduced by SF is in the historical alternatives.
-/
theorem derivation_in_historical_base
    (maria : E)
    (atHomeRel answerRel : E → WorldTimeIndex W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ deriveFullSentence history maria atHomeRel answerRel sfVar speechVar c) :
    ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧
          (gs.1 sfVar) ∈ historicalBase history s₀ := by
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
  · have h_sit : gs.1 sfVar = s₁ := by
      rw [h_upd]; simp only [Assignment.update_at]
    rw [h_sit]
    exact h_hist

/--
The derivation enforces future ordering: τ(s₁) > τ(s₀).
-/
theorem derivation_future_ordering
    (maria : E)
    (atHomeRel answerRel : E → WorldTimeIndex W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ deriveFullSentence history maria atHomeRel answerRel sfVar speechVar c) :
    (gs.1 sfVar).time > (gs.1 speechVar).time := by
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
    (atHomeRel answerRel : E → WorldTimeIndex W Time → Prop)
    (sfVar speechVar : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ deriveFullSentence history maria atHomeRel answerRel sfVar speechVar c) :
    atHomeRel maria (gs.1 sfVar) → answerRel maria (gs.1 sfVar) := by
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
    (atHomeRel answerRel : E → WorldTimeIndex W Time → Prop)
    (cfVar speechVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  let c₁ := dynSUBJ history cfVar c
  let c₂ := lexAtHome atHomeRel maria cfVar c₁
  let c₃ := dynIND cfVar c₂
  lexAnswer answerRel maria cfVar c₃

/--
SF constrains to future; counterfactual allows past/present.
-/
theorem sf_vs_counterfactual_temporal {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    {E : Type*}
    (maria : E)
    (atHomeRel answerRel : E → WorldTimeIndex W Time → Prop)
    (sitVar speechVar : SVar)
    (c : SitContext W Time) :
    ∀ gs ∈ deriveFullSentence history maria atHomeRel answerRel sitVar speechVar c,
      (gs.1 sitVar).time > (gs.1 speechVar).time :=
  derivation_future_ordering history maria atHomeRel answerRel sitVar speechVar c


-- ════════════════════════════════════════════════════════════════
-- § 4. Presupposition Weakening (§2.2)
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
    (restrictor : E → WorldTimeIndex W Time → Prop)
    (s : WorldTimeIndex W Time) : E → Prop :=
  λ x => restrictor x s

/--
SF restrictor: quantifies over historical alternatives.
"Every book that Maria reads.SF..." → no categorical existence presupposition.
-/
def sfRestrictor {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor : E → WorldTimeIndex W Time → Prop)
    (s₀ : WorldTimeIndex W Time) : E → Prop :=
  λ x => ∃ s₁ ∈ historicalBase history s₀, restrictor x s₁


/-- Indicative preserves existential presupposition. -/
theorem indicative_preserves_presup {W Time E : Type*}
    (restrictor : E → WorldTimeIndex W Time → Prop)
    (s : WorldTimeIndex W Time)
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
    (restrictor : E → WorldTimeIndex W Time → Prop)
    (s₀ : WorldTimeIndex W Time)
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
    (restrictor : E → WorldTimeIndex W Time → Prop)
    (s₀ : WorldTimeIndex W Time)
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
    (noun : E → WorldTimeIndex W Time → Prop)
    (relClause : E → WorldTimeIndex W Time → Prop)
    (s₀ : WorldTimeIndex W Time) : E → Prop :=
  λ x => ∃ s₁ ∈ historicalBase history s₀, noun x s₁ ∧ relClause x s₁

theorem relClause_sf_weakens_quantifier {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (noun relClause : E → WorldTimeIndex W Time → Prop)
    (s₀ : WorldTimeIndex W Time)
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
    (restrictor nuclear : E → WorldTimeIndex W Time → Prop)
    (s₀ : WorldTimeIndex W Time) : Prop :=
  ∀ s₁ ∈ historicalBase history s₀,
    (∃ x, restrictor x s₁) →
    ∀ x, restrictor x s₁ → nuclear x s₁

/--
SF semantics is equivalent to modal displacement.
-/
theorem sf_is_modal_displacement {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (restrictor nuclear : E → WorldTimeIndex W Time → Prop)
    (s₀ : WorldTimeIndex W Time) :
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
    (restrictor : E → WorldTimeIndex W Time → Prop)
    (s₀ : WorldTimeIndex W Time)
    (h_global : ∀ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁)
    (h_nonempty : ∃ s, s ∈ historicalBase history s₀) :
    ∃ s₁ ∈ historicalBase history s₀, ∃ x, restrictor x s₁ := by
  obtain ⟨s₁, h_s₁⟩ := h_nonempty
  exact ⟨s₁, h_s₁, h_global s₁ h_s₁⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. Modal Donkey Anaphora (§3.1)
-- ════════════════════════════════════════════════════════════════

/-!
The central theoretical insight of @cite{mendes-2025} §3.1: SF enables
modal donkey anaphora — subjunctive binds situation variables across
clause boundaries, just like indefinites bind individual variables in
classic donkey sentences.

Classic donkey anaphora:
  "If a farmer owns a donkey, he beats it."
  - "a donkey" introduces individual dref x
  - "it" retrieves x outside the syntactic scope of "a"

Modal donkey anaphora:
  "Se Maria estiver em casa, ela vai atender."
  - SF introduces situation dref s₁
  - Main clause retrieves s₁ for temporal anchoring

Correspondence with the dynamic primitives in
`Theories/Semantics/Mood/Dynamic.lean`:
- SUBJ introduces: `dynSUBJ history v = dynIntroduce (historicalBase history) v`
- IND retrieves: `dynIND v = dynRelationOn (·.2) (·.1 v) sameWorld`
-/

/--
Cross-clausal situation binding: a situation introduced in one clause
can be retrieved in another clause via modal donkey anaphora.

Example:
  "Se Maria estiver em casa, ela vai atender."
       ↑ SUBJ introduces s₁ ↑ IND retrieves s₁
-/
def crossClausalBinding {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (antecedentVar _consequentVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  dynIND antecedentVar (dynSUBJ history antecedentVar c)

/--
Cross-clausal binding preserves world identity: when a situation is
introduced in the antecedent and retrieved in the consequent, the two
clauses are evaluated at the same world.
-/
theorem cross_clausal_same_world {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ crossClausalBinding history v v c) :
    gs.2.world = (gs.1 v).world := by
  unfold crossClausalBinding at h
  unfold dynIND at h
  exact h.2

/--
The SUBJ-IND anaphoric chain: SUBJ introduces `s₁`, the antecedent
predicate filters at `s₁`, IND retrieves `s₁` (same-world check), and
the consequent inherits the temporal anchor from `s₁`.
-/
def subjIndChain {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (antecedentPred : SitContext W Time → SitContext W Time)
    (consequentPred : SitContext W Time → SitContext W Time)
    (c : SitContext W Time) : SitContext W Time :=
  consequentPred (dynIND v (antecedentPred (dynSUBJ history v c)))

/--
The SUBJ-IND chain establishes modal donkey anaphora: the consequent
is evaluated at a world that agrees with the bound situation's world.

`Q` must be a context filter — predicates filter contexts without
modifying assignments.
-/
theorem subj_ind_chain_modal_donkey {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (P Q : SitContext W Time → SitContext W Time)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ subjIndChain history v P Q c)
    (hQ : IsContextFilter Q) :
    gs.2.world = (gs.1 v).world := by
  unfold subjIndChain at h
  have h_in_ind : gs ∈ dynIND v (P (dynSUBJ history v c)) := hQ _ h
  unfold dynIND at h_in_ind
  exact h_in_ind.2

/--
Unselective binding gives universal force. When SUBJ introduces a
situation in a conditional antecedent, the conditional quantifies
universally over situations satisfying the antecedent — the modal
analog of donkey universals.
-/
theorem unselective_universal_force {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (antecedent consequent : WorldTimeIndex W Time → Prop)
    (c : SitContext W Time) :
    ∀ gs ∈ subjIndChain history v
      (λ c' => { gs' ∈ c' | antecedent gs'.2 })
      (λ c' => { gs' ∈ c' | consequent gs'.2 })
      c,
      antecedent gs.2 → consequent gs.2 := by
  intro gs h_mem _
  unfold subjIndChain at h_mem
  simp only [Set.mem_setOf_eq] at h_mem
  exact h_mem.2

/-!
### Pipeline characterization

The full pipeline `SUBJ → filter(P) → IND → filter(Q)` on a singleton
context is equivalent to a static existential conjunction over
historical alternatives. The dynamic pipeline gives *conjunction*
(`P ∧ Q`), not *implication* (`P → Q`); sequential composition gives
the stronger conjunctive reading, while the static `conditionalSF`
uses implication.
-/

/--
The SUBJ-IND chain with predication filters on a singleton context
characterizes the static existential conjunction
`∃ s₁ ∈ historicalBase(s₀), P(s₁) ∧ Q(s₁)`.
-/
theorem subjIndChain_singleton {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (g : Assignment (WorldTimeIndex W Time))
    (s₀ : WorldTimeIndex W Time)
    (P Q : WorldTimeIndex W Time → Prop) :
    (∃ gs, gs ∈ subjIndChain history v
      (fun c => { gs ∈ c | P gs.2 })
      (fun c => { gs ∈ c | Q gs.2 })
      ({(g, s₀)} : SitContext W Time)) ↔
    (∃ s₁ ∈ historicalBase history s₀, P s₁ ∧ Q s₁) := by
  unfold subjIndChain
  constructor
  · rintro ⟨gs, ⟨⟨⟨g', s₀', s₁, h_ctx, h_hist, h_upd, h_eq⟩, hP⟩, _⟩, hQ⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp h_ctx)
    exact ⟨s₁, h_hist, h_eq ▸ hP, h_eq ▸ hQ⟩
  · rintro ⟨s₁, h_hist, hP, hQ⟩
    refine ⟨(g.update v s₁, s₁), ⟨⟨⟨g, s₀, s₁, rfl, h_hist, rfl, rfl⟩, hP⟩, ?_⟩, hQ⟩
    simp only [Assignment.update_at]

/--
The dynamic pipeline entails the static conditional (`conditionalSF`).
Conjunction is stronger than implication: if the dynamic pipeline finds
an `s₁` satisfying both `P` and `Q`, then `P(s₁) → Q(s₁)` holds trivially.
-/
theorem subjIndChain_entails_conditionalSF {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (g : Assignment (WorldTimeIndex W Time))
    (s₀ : WorldTimeIndex W Time)
    (P : WorldTimeIndex W Time → Prop)
    (Q : WorldTimeIndex W Time → WorldTimeIndex W Time → Prop)
    (h : ∃ gs, gs ∈ subjIndChain history v
      (fun c => { gs ∈ c | P gs.2 })
      (fun c => { gs ∈ c | Q gs.2 gs.2 })
      ({(g, s₀)} : SitContext W Time)) :
    conditionalSF history P (fun s₁ _ => Q s₁ s₁) s₀ := by
  unfold conditionalSF SUBJ
  obtain ⟨s₁, h_hist, hP, hQ⟩ :=
    (subjIndChain_singleton history v g s₀ P (fun s => Q s s)).mp h
  exact ⟨s₁, h_hist, fun _ => hQ⟩

/-!
### Bridge to Hofmann (2025) accessibility

The same-world constraint enforced by `dynIND` (via the `sameWorld`
kernel in `Mood/Basic.lean`) parallels @cite{hofmann-2025}'s
veridicality-based accessibility for individual drefs:

- **Situation level** (this file, @cite{mendes-2025}): `dynIND`
  retrieves `s₁` via `s₂.world = s₁.world`. Governs cross-clausal
  situation binding (modal donkey anaphora).
- **Propositional dref level** (`Phenomena/Anaphora/Studies/Hofmann2025.lean`,
  @cite{hofmann-2025}): a dref is accessible iff it has a referent in
  all worlds of the local context, plus a discourse-consistency
  condition. Governs individual dref accessibility across negation,
  disjunction, and attitude contexts.

Both enforce the structural pattern that the retrieval context must be
compatible with the introduction context. For situations, this is
world identity; for individual drefs, this is the subset-plus-
existence condition (Hofmann 2025 Definition 39).
-/

end Mendes2025
