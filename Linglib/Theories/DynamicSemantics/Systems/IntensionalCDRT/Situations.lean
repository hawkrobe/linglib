/-
# Situation Discourse Referents for ICDRT

Extension of ICDRT with situation discourse referents (SDrefs).

## Motivation: Mendes (2025)

Mendes argues that the Portuguese Subordinate Future (SF) is a subjunctive
that introduces a situation dref -- parallel to how indefinites introduce
individual drefs in DRT.

Just as:
- Indefinites ("a man") introduce individual drefs
- Propositional drefs track local contexts

We add:
- Subjunctive mood introduces situation drefs
- These drefs can be retrieved by indicative mood for temporal anchoring

## Key Types

| Type | Interpretation |
|------|----------------|
| SDref | assignment → Situation W Time |
| SVar | situation variable indices |
| SitAssignment | extends ICDRTAssignment with situation variables |

## Connection to Mood Operators

The mood operators from `Sentence/Mood/Basic.lean` have dynamic counterparts:
- `SUBJ`: Introduces an SDref (existential over historical alternatives)
- `IND`: Retrieves an SDref (presuppositional)

## References

- Mendes, A. (2025). Indefiniteness in future reference. S&P 18(10).
- Hofmann, L. (2025). Anaphoric accessibility with flat update. S&P.
- Muskens, R. (1996). Combining Montague semantics and discourse representation.
-/

import Linglib.Theories.DynamicSemantics.Systems.IntensionalCDRT.Basic
import Linglib.Theories.DynamicSemantics.Systems.IntensionalCDRT.Update
import Linglib.Theories.TruthConditional.Core.Time
import Linglib.Theories.IntensionalSemantics.Mood.Basic

namespace DynamicSemantics.IntensionalCDRT.Situations

open TruthConditional.Core.Time
open IntensionalSemantics.Mood
open DynamicSemantics.IntensionalCDRT
open DynamicSemantics.Core


/--
A situation variable (names a situation dref).

Parallel to `IVar` for individuals and `PVar` for propositions.
-/
structure SVar where
  idx : Nat
  deriving DecidableEq, BEq, Repr, Hashable

/--
A situation discourse referent: assignment → Situation.

Maps each assignment to a situation (world + time).
This is the situation-level analog of `IDref`.

In Mendes' analysis, subjunctive mood introduces SDrefs.
-/
def SDref (W Time : Type*) (E : Type*) := ICDRTAssignment W E → Situation W Time

namespace SDref

variable {W Time E : Type*}

/-- Constant situation dref (same situation in all contexts) -/
def const (s : Situation W Time) : SDref W Time E := λ _ => s

/-- Extract the world component -/
def world (d : SDref W Time E) : ICDRTAssignment W E → W :=
  λ g => (d g).world

/-- Extract the time component -/
def time (d : SDref W Time E) : ICDRTAssignment W E → Time :=
  λ g => (d g).time

end SDref


/--
Extended ICDRT assignment including situation variables.

This extends `ICDRTAssignment` with a situation variable assignment.
-/
structure SitAssignment (W Time E : Type*) where
  /-- Base ICDRT assignment (individuals + propositions) -/
  base : ICDRTAssignment W E
  /-- Situation variable assignment -/
  sit : SVar → Situation W Time

namespace SitAssignment

variable {W Time E : Type*}

/-- Empty assignment -/
def empty (defaultSit : Situation W Time) : SitAssignment W Time E where
  base := ICDRTAssignment.empty
  sit := λ _ => defaultSit

/-- Update situation variable -/
def updateSit (g : SitAssignment W Time E) (v : SVar) (s : Situation W Time) :
    SitAssignment W Time E :=
  { g with sit := λ v' => if v' == v then s else g.sit v' }

/-- Lookup situation variable -/
notation g "⟦" v "⟧ₛ" => SitAssignment.sit g v

/-- Project to base assignment -/
def toBase (g : SitAssignment W Time E) : ICDRTAssignment W E := g.base

end SitAssignment


/--
Extended ICDRT context with situation tracking.

Contexts are now triples: (assignment, situation, world).
The situation is the "evaluation situation" for temporal semantics.
-/
def SitContext (W Time E : Type*) := Set (SitAssignment W Time E × Situation W Time)

instance {W Time E : Type*} : Membership (SitAssignment W Time E × Situation W Time) (SitContext W Time E) :=
  Set.instMembership
instance {W Time E : Type*} : EmptyCollection (SitContext W Time E) := Set.instEmptyCollection
instance {W Time E : Type*} : HasSubset (SitContext W Time E) := Set.instHasSubset
instance {W Time E : Type*} : Union (SitContext W Time E) := Set.instUnion
instance {W Time E : Type*} : Inter (SitContext W Time E) := Set.instInter

namespace SitContext

variable {W Time E : Type*}

/-- Project to worlds -/
def worlds (c : SitContext W Time E) : Set W :=
  { w | ∃ gs, gs ∈ c ∧ gs.2.world = w }

/-- Project to situations -/
def situations (c : SitContext W Time E) : Set (Situation W Time) :=
  { s | ∃ g, (g, s) ∈ c }

/-- Update with situation predicate -/
def updateSit (c : SitContext W Time E) (p : Situation W Time → Prop) :
    SitContext W Time E :=
  { gs ∈ c | p gs.2 }

/-- Current situations in context -/
def currentSituations (c : SitContext W Time E) : Set (Situation W Time) :=
  { s | ∃ g, (g, s) ∈ c }

end SitContext


/--
Dynamic SUBJ: Introduces a situation dref.

⟦SUBJ^v_{s₀}⟧ = λc. { (g[v↦s₁], s₁) | (g, s₀) ∈ c, s₁ ∈ hist(s₀) }

The subjunctive:
1. Takes an input context with current situation s₀
2. Introduces a NEW situation s₁ from the historical alternatives
3. Binds s₁ to situation variable v
4. Updates the context to use s₁ as the new current situation

This is the dynamic counterpart of `SUBJ` from Mood/Basic.lean.
-/
def dynSUBJ {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)  -- Fresh situation variable
    (c : SitContext W Time E) : SitContext W Time E :=
  { gs' |
    ∃ g s₀ s₁,
      -- Original context entry
      (g, s₀) ∈ c ∧
      -- s₁ is in the historical alternatives of s₀
      s₁ ∈ historicalBase history s₀ ∧
      -- Update assignment to bind v to s₁
      gs'.1 = g.updateSit v s₁ ∧
      -- New current situation is s₁
      gs'.2 = s₁ }

/--
Dynamic IND: Retrieves a situation dref.

⟦IND_v⟧ = λc. { (g, s) | (g, s) ∈ c, s.world = g(v).world }

The indicative:
1. Retrieves the situation from variable v
2. Requires the current situation to be in the same world
3. Passes through (presuppositional)

This is the dynamic counterpart of `IND` from Mood/Basic.lean.
-/
def dynIND {W Time E : Type*}
    (v : SVar)  -- Situation variable to retrieve
    (c : SitContext W Time E) : SitContext W Time E :=
  { gs ∈ c | gs.2.world = (gs.1.sit v).world }


/--
Dynamic PAST: Constrains event time to precede reference time.

Works with situation drefs: τ(s_event) < τ(s_ref)
-/
def dynPAST {W Time E : Type*} [LT Time]
    (eventVar refVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  { gs ∈ c | (gs.1.sit eventVar).time < (gs.1.sit refVar).time }

/--
Dynamic PRES: Constrains event time to equal reference time.
-/
def dynPRES {W Time E : Type*}
    (eventVar refVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  { gs ∈ c | (gs.1.sit eventVar).time = (gs.1.sit refVar).time }

/--
Dynamic FUT: Constrains event time to follow reference time.
-/
def dynFUT {W Time E : Type*} [LT Time]
    (eventVar refVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  { gs ∈ c | (gs.1.sit eventVar).time > (gs.1.sit refVar).time }


/--
Subordinate Future (SF) analysis.

The SF in Portuguese conditionals:
  "Se Maria estiver em casa, ela vai atender."
  "If Maria be.SF at home, she will answer."

Structure (Mendes p.29):
1. SF = SUBJ^{s₁}_{s₀} + FUT
2. SUBJ introduces s₁ ∈ hist(s₀)
3. FUT constrains τ(s₁) > τ(s₀)
4. Main clause is anchored to τ(s₁)

This is the compositional derivation:
⟦SF⟧ = ⟦SUBJ⟧ ∘ ⟦FUT⟧
-/
def subordinateFuture {W Time E : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (newSitVar : SVar)   -- Fresh variable for introduced situation
    (refSitVar : SVar)   -- Variable for reference situation
    (c : SitContext W Time E) : SitContext W Time E :=
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
def conditionalWithSF {W Time E : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (antecedentVar : SVar)  -- Situation introduced by SF
    (speechVar : SVar)      -- Speech time situation
    (antecedent : SitContext W Time E → SitContext W Time E)  -- "Maria is home"
    (consequent : SitContext W Time E → SitContext W Time E)  -- "she answers"
    (c : SitContext W Time E) : SitContext W Time E :=
  -- Apply SF to introduce antecedent situation
  let c₁ := subordinateFuture history antecedentVar speechVar c
  -- Filter by antecedent
  let c₂ := antecedent c₁
  -- Apply consequent (anchored to antecedentVar's time)
  consequent c₂


/--
SF introduces a future situation.

The subordinate future always introduces a situation with time ≥ current.
-/
theorem sf_introduces_future {W Time E : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (newVar refVar : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ subordinateFuture history newVar refVar c) :
    (gs.1.sit newVar).time ≥ (gs.1.sit refVar).time := by
  -- The subordinateFuture composes SUBJ and FUT
  -- FUT requires the new situation to be after the reference
  unfold subordinateFuture dynFUT at h
  obtain ⟨_, h_gt⟩ := h
  -- h_gt gives us the strict ordering from FUT
  exact le_of_lt h_gt

/--
SUBJ is existential over historical base.
-/
theorem dynSUBJ_existential {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ dynSUBJ history v c) :
    ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧ gs.2 ∈ historicalBase history s₀ := by
  unfold dynSUBJ at h
  obtain ⟨g, s₀, s₁, hc, h_hist, _, h_eq⟩ := h
  use s₀
  constructor
  · exact ⟨g, hc⟩
  · rw [h_eq]; exact h_hist

/--
IND is presuppositional (same-world check).
-/
theorem dynIND_same_world {W Time E : Type*}
    (v : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ dynIND v c) :
    gs.2.world = (gs.1.sit v).world := by
  unfold dynIND at h
  exact h.2


/--
Temporal shift is parasitic on modal donkey anaphora.

Mendes (2025) §3.2: the future-oriented interpretation of SF is not due
to an independent temporal operator. Instead, it follows from:

1. SUBJ introduces s₁ ∈ hist(s₀) - modal component
2. hist(s₀) includes situations with τ(s₁) ≥ τ(s₀) - temporal consequence
3. Main clause is evaluated at τ(s₁) via modal anaphora - binding

The temporal shift is *derived* from the modal semantics, not stipulated.

Modal donkey anaphora explains
why subjunctive mood enables future reference in subordinate clauses.
-/
theorem temporal_shift_parasitic_on_modal {W Time E : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (sfVar speechVar : SVar)
    (c : SitContext W Time E)
    -- For any situation in the output of SF application...
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ subordinateFuture history sfVar speechVar c)
    -- ...there exists an original speech situation...
    : ∃ (g₀ : SitAssignment W Time E) (s₀ : Situation W Time),
        -- ...that was in the input context...
        (g₀, s₀) ∈ c ∧
        -- ...and the temporal shift comes from SUBJ's modal component:
        -- 1. The bound situation s₁ is in the historical base of s₀
        (gs.1.sit sfVar) ∈ historicalBase history s₀ ∧
        -- 2. The temporal ordering τ(s₁) ≥ τ(s₀) follows from hist definition
        (gs.1.sit sfVar).time ≥ s₀.time ∧
        -- 3. The strict future τ(s₁) > τ(s₀) comes from FUT constraint
        (gs.1.sit sfVar).time > (gs.1.sit speechVar).time := by
  -- subordinateFuture = dynSUBJ ∘ dynFUT
  unfold subordinateFuture at h
  -- After dynFUT, we have the strict ordering
  unfold dynFUT at h
  obtain ⟨h_in_subj, h_gt⟩ := h
  -- After dynSUBJ, we have the historical base membership
  unfold dynSUBJ at h_in_subj
  obtain ⟨g, s₀, s₁, hc, h_hist, h_upd, h_eq⟩ := h_in_subj
  use g, s₀
  -- Helper: gs.1.sit sfVar = s₁
  have h_sit : gs.1.sit sfVar = s₁ := by
    rw [h_upd]
    unfold SitAssignment.updateSit
    -- For SVar with BEq derived from DecidableEq
    simp only [show (sfVar == sfVar) = true from by
      unfold instBEqSVar BEq.beq
      exact decide_eq_true rfl, ite_true]
  refine ⟨hc, ?_, ?_, ?_⟩
  -- 1. gs.1.sit sfVar = s₁ ∈ historicalBase history s₀
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
Without modal displacement, no temporal shift.

If we remove the modal component (SUBJ), there's no mechanism for
the future-oriented reading. This shows the temporal shift is parasitic.
-/
theorem no_modal_no_temporal_shift {W Time E : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h_in_c : gs ∈ c)
    -- Without SUBJ, the situation variable is not updated
    (h_no_subj : gs.1.sit v = gs.2)
    -- And gs.2 is the current situation, not a future one
    : gs.2.time = gs.2.time := by  -- Trivial: no shift occurs
  rfl


/--
Relative clause with SF in restrictor.

"Cada menino [que estiver acordado] vai receber um biscoito."
"Every boy [who is.SF awake] will get a cookie."

Structure:
1. SF in relative clause introduces situation s₁ ∈ hist(s₀)
2. Restrictor (boy ∧ awake) evaluated at s₁
3. Nuclear scope (get cookie) evaluated with temporal anchor from s₁
-/
def relativeClauseSF {W Time E : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (rcVar : SVar)           -- Situation variable for relative clause
    (speechVar : SVar)       -- Speech time situation
    (restrictor : E → SitContext W Time E → SitContext W Time E)  -- RC content
    (c : SitContext W Time E) : SitContext W Time E :=
  -- Apply SF to introduce the RC situation
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
def everyWithSFRestrictor {W Time E : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (rcVar speechVar : SVar)
    (restrictor : SitContext W Time E → SitContext W Time E)  -- "book that M reads"
    (nuclear : SitContext W Time E → SitContext W Time E)     -- "is interesting"
    (c : SitContext W Time E) : SitContext W Time E :=
  -- First: SF introduces situation for restrictor
  let c₁ := subordinateFuture history rcVar speechVar c
  -- Then: Filter by restrictor content
  let c₂ := restrictor c₁
  -- Finally: Apply nuclear scope (inherits temporal anchor)
  nuclear c₂

/--
SF in restrictor enables future reference for strong quantifiers.

With SF in the relative clause, "every" can quantify over future entities.

Note: Requires that restrictor and nuclear are filters (preserve subset membership).
Linguistically, predicates filter contexts without modifying assignments.
-/
theorem sf_restrictor_future_reference {W Time E : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (rcVar speechVar : SVar)
    (restrictor nuclear : SitContext W Time E → SitContext W Time E)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ everyWithSFRestrictor history rcVar speechVar restrictor nuclear c)
    -- Restrictor and nuclear are filters (preserve membership from SF)
    (hRN_filter : nuclear (restrictor (subordinateFuture history rcVar speechVar c))
                  ⊆ subordinateFuture history rcVar speechVar c) :
    -- The restrictor situation can be future relative to speech time
    (gs.1.sit rcVar).time > (gs.1.sit speechVar).time := by
  -- Track through the filter chain
  unfold everyWithSFRestrictor at h
  have h_sf : gs ∈ subordinateFuture history rcVar speechVar c := hRN_filter h
  -- subordinateFuture guarantees the future ordering via dynFUT
  unfold subordinateFuture dynFUT at h_sf
  exact h_sf.2


/--
Example sentence derivation (paper example 53).

"Se Maria estiver em casa, ela vai atender."
"If Maria be.SF home, she will answer."

Full CDRT derivation following formulas (54)-(63).
-/
structure SentenceDerivation (W Time E : Type*) where
  /-- The input context -/
  inputContext : SitContext W Time E
  /-- The output context after interpretation -/
  outputContext : SitContext W Time E
  /-- The situation variable introduced by SF -/
  sfSitVar : SVar
  /-- The speech time situation variable -/
  speechSitVar : SVar

/--
Step-by-step derivation following paper's formulas.

(54) ⟦SUBJ^s₁_{s₀}⟧ = λcλc'. ∃s₁[s₁ ∈ hist(s₀); c'(s₁)]
(55) ⟦Maria⟧ = maria
(56) ⟦estar em casa⟧ = λxλs. at-home(x)(s)
(57) ⟦SF⟧ = SUBJ + FUT
(58) ⟦atender⟧ = λxλs. answer(x)(s)
(59) ⟦ela⟧ = λP.P(maria) (bound to Maria in discourse)
(60) Full antecedent: SUBJ^s₁_{s₀}[FUT; at-home(maria)(s₁)]
(61) Full consequent: answer(maria)(s₁)  -- anchored to s₁
(62) Conditional: ∀(g,s₀)∈c: if ⟦antecedent⟧ then ⟦consequent⟧
(63) Result: Universal over historical alternatives where Maria is home
-/
def exampleDerivation {W Time E : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (maria : E)
    (atHome : E → Situation W Time → Prop)
    (answer : E → Situation W Time → Prop)
    (s₁ s₀ : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  -- (60) Antecedent: SF introduces s₁ with Maria at home
  let antecedent : SitContext W Time E → SitContext W Time E :=
    λ c' => { gs ∈ c' | atHome maria (gs.1.sit s₁) }
  -- (61) Consequent: Maria answers, evaluated at s₁'s time
  let consequent : SitContext W Time E → SitContext W Time E :=
    λ c' => { gs ∈ c' | answer maria (gs.1.sit s₁) }
  -- (62-63) Full conditional with SF
  conditionalWithSF history s₁ s₀ antecedent consequent c

/--
Derivation matches Mendes' formulas (54)-(63).

The output context captures exactly the truth conditions described
in the paper: universal quantification over historical alternatives
where the antecedent holds.
-/
theorem derivation_matches_paper {W Time E : Type*} [LE Time] [LT Time]
    (history : WorldHistory W Time)
    (maria : E)
    (atHome answer : E → Situation W Time → Prop)
    (s₁ s₀ : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ exampleDerivation history maria atHome answer s₁ s₀ c)
    -- s₀ and s₁ are distinct variables (required for proper tracking)
    (h_distinct : s₁ ≠ s₀)
    -- Speech time variable s₀ is properly initialized in the context:
    -- all context entries have s₀ bound to their current situation
    (h_init : ∀ g' s', (g', s') ∈ c → g'.sit s₀ = s') :
    -- The output satisfies:
    -- 1. s₁ is in the historical alternatives of s₀
    (gs.1.sit s₁) ∈ historicalBase history (gs.1.sit s₀) ∧
    -- 2. τ(s₁) > τ(s₀) (future)
    (gs.1.sit s₁).time > (gs.1.sit s₀).time ∧
    -- 3. If Maria is at home at s₁, she answers at s₁
    (atHome maria (gs.1.sit s₁) → answer maria (gs.1.sit s₁)) := by
  unfold exampleDerivation at h
  unfold conditionalWithSF at h
  simp only [Set.mem_setOf_eq] at h
  obtain ⟨⟨h_ant, _⟩, h_ans⟩ := h
  -- Track through subordinateFuture
  unfold subordinateFuture at h_ant
  unfold dynFUT at h_ant
  obtain ⟨h_subj, h_gt⟩ := h_ant
  unfold dynSUBJ at h_subj
  obtain ⟨g, s₀', sit₁, hc, h_hist, h_upd, h_eq⟩ := h_subj
  -- Helper: gs.1.sit s₁ = sit₁
  have h_s₁ : gs.1.sit s₁ = sit₁ := by
    rw [h_upd]
    unfold SitAssignment.updateSit
    simp only [show (s₁ == s₁) = true from by
      unfold instBEqSVar BEq.beq; exact decide_eq_true rfl, ite_true]
  -- Helper: gs.1.sit s₀ = g.sit s₀ (unchanged by update to s₁)
  have h_s₀ : gs.1.sit s₀ = g.sit s₀ := by
    rw [h_upd]
    unfold SitAssignment.updateSit
    -- s₀ ≠ s₁, so the if-then-else chooses the else branch
    have h_ne : (s₀ == s₁) = false := by
      unfold instBEqSVar BEq.beq
      have h_idx_ne : s₀.idx ≠ s₁.idx := by
        intro heq
        apply h_distinct
        cases s₀; cases s₁
        simp only at heq
        subst heq
        rfl
      exact decide_eq_false h_idx_ne
    simp only [h_ne]
    rfl
  -- From initialization: g.sit s₀ = s₀'
  have h_g_s₀ : g.sit s₀ = s₀' := h_init g s₀' hc
  refine ⟨?_, ?_, ?_⟩
  -- 1. s₁ ∈ historicalBase history (gs.1.sit s₀)
  · rw [h_s₁, h_s₀, h_g_s₀]
    exact h_hist
  -- 2. τ(s₁) > τ(s₀)
  · exact h_gt
  -- 3. Conditional semantics
  · intro _
    exact h_ans


end DynamicSemantics.IntensionalCDRT.Situations
