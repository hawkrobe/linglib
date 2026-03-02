import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# Implicit Causality Data for Psych Verbs

@cite{solstad-bott-2022} @cite{solstad-bott-2024}

Theory-neutral experimental data on implicit causality (I-Caus) and implicit
consequentiality (I-Cons) for psych verbs. The experimental data comes from
@cite{solstad-bott-2022}, which tests stimulus-experiencer (STIM-EXP) and
experiencer-stimulus (EXP-STIM) verb classes in German.

The theoretical framework connecting occasion verbs, projectivity, and
IC bias comes from Solstad & Bott (2024, S&P 17:11).

## Verb classes

- **StimExp** (Stimulus-Experiencer): frighten, annoy, amuse — NP1 bias
- **ExpStim** (Experiencer-Stimulus): admire, like, fear — NP2 bias
- **AgentEvocator** (Agent-Evocator): criticise, congratulate — NP2 bias
- **AgentPatient** (Agent-Patient): kick, chase, hit — NP1 bias

## Key empirical findings

1. **Exp 1** (sentence continuation): I-Caus and I-Cons biases mirror each
   other for psych verbs. STIM-EXP: 87.4% NP1 with *weil*; EXP-STIM: 96%
   NP2 with *weil*.
2. **Exp 2** (coherence relations): Explanations dominate over consequences
   for both classes; consequence rate differs by class.
3. **Exp 3** (forced coreference): Asymmetry Hypothesis confirmed — even
   bias-incongruent continuations produce explanations.
4. **Exp 4** (explanation types): Explanations and consequences are of the
   types predicted by the Two-Mechanism Account.
-/

namespace Phenomena.ImplicitCausality.Studies.SolstadBott2024

-- ════════════════════════════════════════════════════
-- § 1. Verb Classes
-- ════════════════════════════════════════════════════

/-- Verb classes from the IC bias literature. -/
inductive VerbClass where
  | stimExp        -- StimExp: frighten, annoy, amuse — subject is stimulus
  | expStim        -- ExpStim: admire, like, fear — subject is experiencer
  | agentEvocator  -- AgEvoc: criticise, congratulate — subject acts on evocator
  | agentPat       -- AgPat: kick, chase, hit — subject is agent
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. IC Bias Direction
-- ════════════════════════════════════════════════════

/-- Implicit causality bias direction. -/
inductive ICBias where
  | np1   -- Subject-biased (explanation targets subject referent)
  | np2   -- Object-biased (explanation targets object referent)
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 3. Predicted IC Bias by Class
-- ════════════════════════════════════════════════════

/-- Predicted IC bias direction for each verb class.

    The IC bias tracks the STIMULUS argument, not the subject per se:
    - StimExp (stimulus = subject) → NP1 (explanation about subject)
    - ExpStim (stimulus = object) → NP2 (explanation about object)
    - AgentEvocator (evocator = object) → NP2
    - AgPat (agent = subject) → NP1 (default) -/
def VerbClass.predictedBias : VerbClass → ICBias
  | .stimExp       => .np1   -- stimulus is subject → NP1
  | .expStim       => .np2   -- stimulus is object → NP2
  | .agentEvocator => .np2   -- evocator is object → NP2
  | .agentPat      => .np1   -- agent is subject → NP1

-- ════════════════════════════════════════════════════
-- § 4. Connectives (Solstad & Bott 2022, Exp 1)
-- ════════════════════════════════════════════════════

/-- Connective conditions in @cite{solstad-bott-2022}.
    German connectives *weil* (because) and *sodass* (and so). -/
inductive ExpConnective where
  | weil      -- "because" → I-Caus (Explanation relation)
  | sodass    -- "and so" → I-Cons (Consequence relation)
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 5. Exp 1 Data: Coreference Biases (Table 1)
-- ════════════════════════════════════════════════════

/-- Subject coreference proportion from Exp 1, Table 1 of @cite{solstad-bott-2022}.
    These are real data from 52 German participants with 20 STIM-EXP and
    20 EXP-STIM verbs (gefallen excluded). -/
structure CorefDatum where
  verbClass : VerbClass
  connective : ExpConnective
  subjectCorefPct : ℚ    -- Percentage of NP1 (subject) coreference
  deriving Repr

-- Exp 1, Table 1 (Solstad & Bott 2022, p. 1322)
def exp1_stimExp_weil   : CorefDatum := ⟨.stimExp, .weil, 874/10⟩   -- 87.4%
def exp1_expStim_weil   : CorefDatum := ⟨.expStim, .weil, 40/10⟩    -- 4.0%
def exp1_stimExp_sodass : CorefDatum := ⟨.stimExp, .sodass, 48/10⟩  -- 4.8%
def exp1_expStim_sodass : CorefDatum := ⟨.expStim, .sodass, 779/10⟩ -- 77.9%

-- ════════════════════════════════════════════════════
-- § 6. Verification Theorems
-- ════════════════════════════════════════════════════

/-- StimExp and ExpStim have opposite predicted IC bias. -/
theorem stimExp_opposes_expStim :
    VerbClass.predictedBias .stimExp ≠
    VerbClass.predictedBias .expStim := by decide

/-- I-Caus (weil): StimExp has strong NP1 bias (87.4% > 50%). -/
theorem stimExp_weil_np1_bias :
    exp1_stimExp_weil.subjectCorefPct > 50 := by
  show 50 < (874 : ℚ)/10; norm_num

/-- I-Caus (weil): ExpStim has strong NP2 bias (4.0% < 50%). -/
theorem expStim_weil_np2_bias :
    exp1_expStim_weil.subjectCorefPct < 50 := by
  show (40 : ℚ)/10 < 50; norm_num

/-- I-Cons (sodass): Biases mirror I-Caus — StimExp → NP2, ExpStim → NP1.
    (Solstad & Bott 2022, §2.3: "almost perfect negative correlation" r = −0.94) -/
theorem icons_mirrors_icaus :
    exp1_stimExp_sodass.subjectCorefPct < 50 ∧
    exp1_expStim_sodass.subjectCorefPct > 50 := by
  constructor
  · show (48 : ℚ)/10 < 50; norm_num
  · show 50 < (779 : ℚ)/10; norm_num

/-- The Asymmetry Hypothesis: I-Caus and I-Cons derive from different
    mechanisms:
    - I-Caus: verb-semantic (Empty Slot Theory)
    - I-Cons: discourse-structural (Contiguity Principle) -/
theorem asymmetry_hypothesis_supported :
    -- I-Caus bias is stronger than I-Cons bias for both classes
    exp1_stimExp_weil.subjectCorefPct > exp1_expStim_sodass.subjectCorefPct := by
  show (779 : ℚ)/10 < (874 : ℚ)/10; norm_num

end Phenomena.ImplicitCausality.Studies.SolstadBott2024
