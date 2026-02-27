import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# Solstad & Bott (2024): Occasion Verbs — Experimental Data

@cite{solstad-bott-2024}

Theory-neutral experimental data from five experiments establishing that
**occasion verbs** (manage, dare, bother, hesitate) pattern with agent-experiencer
(AgExp) verbs for implicit causality (IC) bias, driven by verb presupposition
interacting with discourse coherence relations.

## Verb classes (p.8)

- **OccV** (Occasion Verbs): manage, dare, bother, hesitate
- **AgExp** (Agent-Experiencer): enjoy, like, love, hate, admire, envy, respect, value
- **StimExp** (Stimulus-Experiencer): frighten, amuse, fascinate, irritate,
  annoy, bore, charm, impress
- **AgPat** (Agent-Patient): kick, chase, hit, push, pull, carry, drag, call

## Key empirical findings

1. **Exp 1** (free continuation): OccV shows NP1 bias (like AgExp), contrasting
   with StimExp (NP2 bias) and AgPat (NP1 bias)
2. **Exp 2** (forced choice): Confirms OccV ≈ AgExp for NP1 bias
3. **Exp 3** (prompt manipulation): IC bias is modulated by explicit prompts
4. **Exp 4** (connective manipulation): "weil" (because) elicits IC bias;
   "obwohl" (although) and "und dann" (and then) reduce/eliminate it
5. **Exp 5** (replication of Exp 4 in different design)
-/

namespace Phenomena.ImplicitCausality.Studies.SolstadBott2024

-- ════════════════════════════════════════════════════
-- § 1. Verb Classes
-- ════════════════════════════════════════════════════

/-- The four verb classes in Solstad & Bott's experimental design. -/
inductive VerbClass where
  | occasionVerb   -- OccV: manage, dare, bother, hesitate
  | agentExp       -- AgExp: enjoy, like, love, hate, admire, envy, respect, value
  | stimExp        -- StimExp: frighten, amuse, fascinate, irritate, ...
  | agentPat       -- AgPat: kick, chase, hit, push, pull, carry, drag, call
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. IC Bias Direction
-- ════════════════════════════════════════════════════

/-- Implicit causality bias direction. -/
inductive ICBias where
  | np1   -- Subject-biased (cause attributed to subject)
  | np2   -- Object-biased (cause attributed to object)
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 3. Stimulus Verbs
-- ════════════════════════════════════════════════════

/-- A stimulus verb with its class annotation. -/
structure StimulusVerb where
  form : String
  verbClass : VerbClass
  deriving Repr, BEq

-- Occasion Verbs (4)
def manage_stim   : StimulusVerb := ⟨"manage", .occasionVerb⟩
def dare_stim     : StimulusVerb := ⟨"dare", .occasionVerb⟩
def bother_stim   : StimulusVerb := ⟨"bother", .occasionVerb⟩
def hesitate_stim : StimulusVerb := ⟨"hesitate", .occasionVerb⟩

-- Agent-Experiencer Verbs (8)
def enjoy_stim    : StimulusVerb := ⟨"enjoy", .agentExp⟩
def like_stim     : StimulusVerb := ⟨"like", .agentExp⟩
def love_stim     : StimulusVerb := ⟨"love", .agentExp⟩
def hate_stim     : StimulusVerb := ⟨"hate", .agentExp⟩
def admire_stim   : StimulusVerb := ⟨"admire", .agentExp⟩
def envy_stim     : StimulusVerb := ⟨"envy", .agentExp⟩
def respect_stim  : StimulusVerb := ⟨"respect", .agentExp⟩
def value_stim    : StimulusVerb := ⟨"value", .agentExp⟩

-- Stimulus-Experiencer Verbs (8)
def frighten_stim  : StimulusVerb := ⟨"frighten", .stimExp⟩
def amuse_stim     : StimulusVerb := ⟨"amuse", .stimExp⟩
def fascinate_stim : StimulusVerb := ⟨"fascinate", .stimExp⟩
def irritate_stim  : StimulusVerb := ⟨"irritate", .stimExp⟩
def annoy_stim     : StimulusVerb := ⟨"annoy", .stimExp⟩
def bore_stim      : StimulusVerb := ⟨"bore", .stimExp⟩
def charm_stim     : StimulusVerb := ⟨"charm", .stimExp⟩
def impress_stim   : StimulusVerb := ⟨"impress", .stimExp⟩

-- Agent-Patient Verbs (8)
def kick_stim   : StimulusVerb := ⟨"kick", .agentPat⟩
def chase_stim  : StimulusVerb := ⟨"chase", .agentPat⟩
def hit_stim    : StimulusVerb := ⟨"hit", .agentPat⟩
def push_stim   : StimulusVerb := ⟨"push", .agentPat⟩
def pull_stim   : StimulusVerb := ⟨"pull", .agentPat⟩
def carry_stim  : StimulusVerb := ⟨"carry", .agentPat⟩
def drag_stim   : StimulusVerb := ⟨"drag", .agentPat⟩
def call_stim   : StimulusVerb := ⟨"call", .agentPat⟩

/-- All 28 stimulus verbs. -/
def allStimuli : List StimulusVerb := [
  manage_stim, dare_stim, bother_stim, hesitate_stim,
  enjoy_stim, like_stim, love_stim, hate_stim,
  admire_stim, envy_stim, respect_stim, value_stim,
  frighten_stim, amuse_stim, fascinate_stim, irritate_stim,
  annoy_stim, bore_stim, charm_stim, impress_stim,
  kick_stim, chase_stim, hit_stim, push_stim,
  pull_stim, carry_stim, drag_stim, call_stim
]

-- ════════════════════════════════════════════════════
-- § 4. Predicted IC Bias by Class
-- ════════════════════════════════════════════════════

/-- Predicted IC bias direction for each verb class.

    This is the main empirical finding (Solstad & Bott 2024, Table 2):
    - OccV → NP1 (like AgExp, not like AgPat)
    - AgExp → NP1 (experiencer = subject is the locus of causation)
    - StimExp → NP2 (experiencer = object is the locus of causation)
    - AgPat → NP1 (agent = subject is the default cause) -/
def VerbClass.predictedBias : VerbClass → ICBias
  | .occasionVerb => .np1
  | .agentExp     => .np1
  | .stimExp      => .np2
  | .agentPat     => .np1

-- ════════════════════════════════════════════════════
-- § 5. Exp 1 & 2: Mean NP1 Proportions
-- ════════════════════════════════════════════════════

/-- Mean NP1 continuation proportions by verb class (Exp 1, free continuation).
    Values are approximate from Figure 2 (p.16). -/
structure ClassBiasData where
  verbClass : VerbClass
  np1Proportion : ℚ    -- Proportion of NP1 continuations
  deriving Repr

def exp1_occV   : ClassBiasData := ⟨.occasionVerb, 72/100⟩
def exp1_agExp  : ClassBiasData := ⟨.agentExp, 75/100⟩
def exp1_stimExp : ClassBiasData := ⟨.stimExp, 28/100⟩
def exp1_agPat  : ClassBiasData := ⟨.agentPat, 65/100⟩

-- ════════════════════════════════════════════════════
-- § 6. Exp 4: Connective Effects
-- ════════════════════════════════════════════════════

/-- Connective conditions in Experiment 4 (p.26).
    The German connectives are: weil (because), obwohl (although),
    und dann (and then). -/
inductive ExpConnective where
  | weil      -- "because" → Explanation relation
  | obwohl    -- "although" → Contrast relation
  | undDann   -- "and then" → Occasion relation
  deriving DecidableEq, Repr, BEq

/-- Key finding from Exp 4: IC bias magnitude varies by connective.
    "weil" (because) elicits the strongest IC effect; "obwohl" and
    "und dann" reduce it substantially (Figures 8–9, pp.28–30). -/
structure ConnectiveEffect where
  connective : ExpConnective
  verbClass : VerbClass
  np1Proportion : ℚ
  deriving Repr

-- Selected data points from Exp 4 (approximate from Figure 8)
def exp4_occV_weil    : ConnectiveEffect := ⟨.weil, .occasionVerb, 78/100⟩
def exp4_occV_obwohl  : ConnectiveEffect := ⟨.obwohl, .occasionVerb, 50/100⟩
def exp4_occV_undDann : ConnectiveEffect := ⟨.undDann, .occasionVerb, 48/100⟩

-- ════════════════════════════════════════════════════
-- § 7. Verification Theorems
-- ════════════════════════════════════════════════════

/-- OccV and AgExp share the same predicted IC bias (NP1). -/
theorem occV_matches_agExp :
    VerbClass.predictedBias .occasionVerb =
    VerbClass.predictedBias .agentExp := rfl

/-- StimExp differs from OccV in predicted IC bias. -/
theorem stimExp_differs_from_occV :
    VerbClass.predictedBias .stimExp ≠
    VerbClass.predictedBias .occasionVerb := by decide

/-- OccV IC bias is above chance (> 0.5) with "because" connective. -/
theorem occV_weil_above_chance :
    exp4_occV_weil.np1Proportion > 1/2 := by
  show 1/2 < (78 : ℚ)/100; norm_num

/-- OccV IC bias is at chance (~0.5) with "and then" connective. -/
theorem occV_undDann_near_chance :
    exp4_occV_undDann.np1Proportion ≤ 1/2 := by
  show (48 : ℚ)/100 ≤ 1/2; norm_num

/-- All 28 stimulus verbs are present. -/
theorem stimulus_count : allStimuli.length = 28 := rfl

/-- 4 occasion verbs in the stimulus set. -/
theorem occV_count :
    (allStimuli.filter (·.verbClass == .occasionVerb)).length = 4 := rfl

/-- 8 agent-experiencer verbs in the stimulus set. -/
theorem agExp_count :
    (allStimuli.filter (·.verbClass == .agentExp)).length = 8 := rfl

/-- 8 stimulus-experiencer verbs in the stimulus set. -/
theorem stimExp_count :
    (allStimuli.filter (·.verbClass == .stimExp)).length = 8 := rfl

/-- 8 agent-patient verbs in the stimulus set. -/
theorem agPat_count :
    (allStimuli.filter (·.verbClass == .agentPat)).length = 8 := rfl

end Phenomena.ImplicitCausality.Studies.SolstadBott2024
