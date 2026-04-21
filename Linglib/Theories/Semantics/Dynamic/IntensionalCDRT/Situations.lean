/-
# Situation Discourse Referents for ICDRT

Extension of ICDRT with situation discourse referents (SDrefs).

## Motivation: @cite{mendes-2025}

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

Mood operators have dynamic counterparts here:
- `dynSUBJ`: Introduces an SDref (existential over historical alternatives)
- `dynIND`: Retrieves an SDref (presuppositional)
- Static counterparts live in `Theories/Semantics/Mood/Basic.lean`

-/

import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Basic
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Theories.Semantics.Mood.Basic

namespace Semantics.Dynamic.IntensionalCDRT.Situations

open _root_.Core (Situation)

open Core.Time
open Core.Modality.HistoricalAlternatives
open Semantics.Dynamic.IntensionalCDRT
open Semantics.Dynamic.Core
open Semantics.Mood


/--
A situation variable (names a situation dref).

Parallel to `IVar` for individuals and `PVar` for propositions.
-/
structure SVar where
  idx : Nat
  deriving DecidableEq, Repr, Hashable

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
instance {W Time E : Type*} :
    Singleton (SitAssignment W Time E × Situation W Time) (SitContext W Time E) :=
  Set.instSingletonSet

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

end SitContext


-- ════════════════════════════════════════════════════════════════
-- Context filters and general relation filters
-- ════════════════════════════════════════════════════════════════

/--
A context filter is an operation that only removes entries, never adds them.

Linguistic operations like predication, temporal constraints, and mood
retrieval (IND) are all filters. Updates like SUBJ are NOT filters —
they introduce new entries.
-/
def IsContextFilter {W Time E : Type*}
    (f : SitContext W Time E → SitContext W Time E) : Prop :=
  ∀ c, f c ⊆ c

namespace IsContextFilter

variable {W Time E : Type*}

theorem comp {f g : SitContext W Time E → SitContext W Time E}
    (hf : IsContextFilter f) (hg : IsContextFilter g) :
    IsContextFilter (fun c => g (f c)) :=
  fun c => Set.Subset.trans (hg (f c)) (hf c)

theorem id_filter : @IsContextFilter W Time E id :=
  fun _ _ h => h

end IsContextFilter

/--
Filter a context by a binary relation on situation variable lookups.

All temporal constraints (`dynPAST`, `dynPRES`, `dynFUT`) are instances
of `dynRelation` with the appropriate ordering on `.time`.
-/
def dynRelation {W Time E : Type*}
    (R : Situation W Time → Situation W Time → Prop)
    (v₁ v₂ : SVar) (c : SitContext W Time E) : SitContext W Time E :=
  { gs ∈ c | R (gs.1.sit v₁) (gs.1.sit v₂) }

theorem dynRelation_isFilter {W Time E : Type*}
    (R : Situation W Time → Situation W Time → Prop) (v₁ v₂ : SVar) :
    @IsContextFilter W Time E (dynRelation R v₁ v₂) :=
  fun _ _ h => h.1


/--
Dynamic SUBJ: Introduces a situation dref.

⟦SUBJ^v_{s₀}⟧ = λc. { (g[v↦s₁], s₁) | (g, s₀) ∈ c, s₁ ∈ hist(s₀) }

The subjunctive:
1. Takes an input context with current situation s₀
2. Introduces a NEW situation s₁ from the historical alternatives
3. Binds s₁ to situation variable v
4. Updates the context to use s₁ as the new current situation

See `Mood.SUBJ` in `Theories/Semantics/Mood/Basic.lean` for the static counterpart.
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

See `Mood.IND` in `Theories/Semantics/Mood/Basic.lean` for the static counterpart.
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

theorem dynIND_isFilter {W Time E : Type*} (v : SVar) :
    @IsContextFilter W Time E (dynIND v) :=
  fun _ _ h => h.1


-- ════════════════════════════════════════════════════════════════
-- Temporal operators as dynRelation instances
-- ════════════════════════════════════════════════════════════════

theorem dynPAST_eq_dynRelation {W Time E : Type*} [LT Time]
    (e r : SVar) (c : SitContext W Time E) :
    dynPAST e r c =
    dynRelation (fun s₁ s₂ : Situation W Time => s₁.time < s₂.time) e r c := rfl

theorem dynPRES_eq_dynRelation {W Time E : Type*}
    (e r : SVar) (c : SitContext W Time E) :
    dynPRES e r c =
    dynRelation (fun s₁ s₂ : Situation W Time => s₁.time = s₂.time) e r c := rfl

theorem dynFUT_eq_dynRelation {W Time E : Type*} [LT Time]
    (e r : SVar) (c : SitContext W Time E) :
    dynFUT e r c =
    dynRelation (fun s₁ s₂ : Situation W Time => s₁.time > s₂.time) e r c := rfl


-- ════════════════════════════════════════════════════════════════
-- dynRelation algebra
-- ════════════════════════════════════════════════════════════════

/-- Applying the same relation filter twice is the same as applying it once. -/
theorem dynRelation_idempotent {W Time E : Type*}
    (R : Situation W Time → Situation W Time → Prop)
    (v₁ v₂ : SVar) (c : SitContext W Time E) :
    dynRelation R v₁ v₂ (dynRelation R v₁ v₂ c) = dynRelation R v₁ v₂ c := by
  apply Set.ext; intro gs
  unfold dynRelation
  exact ⟨fun ⟨⟨hc, _⟩, hR⟩ => ⟨hc, hR⟩, fun ⟨hc, hR⟩ => ⟨⟨hc, hR⟩, hR⟩⟩

/-- Contradictory relation filters compose to the empty context. -/
theorem dynRelation_contradictory {W Time E : Type*}
    (R₁ R₂ : Situation W Time → Situation W Time → Prop)
    (h : ∀ s₁ s₂, R₁ s₁ s₂ → R₂ s₁ s₂ → False)
    (v₁ v₂ : SVar) (c : SitContext W Time E) :
    dynRelation R₁ v₁ v₂ (dynRelation R₂ v₁ v₂ c) = ∅ := by
  apply Set.ext; intro gs
  unfold dynRelation
  constructor
  · rintro ⟨⟨_, hR₂⟩, hR₁⟩
    exact absurd hR₁ (fun hR₁ => h _ _ hR₁ hR₂)
  · exact False.elim

/-- Transitive relations chain across three situation variables. -/
theorem dynRelation_transitive {W Time E : Type*}
    (R₁ R₂ R₃ : Situation W Time → Situation W Time → Prop)
    (hTrans : ∀ a b c, R₁ a b → R₂ b c → R₃ a c)
    (v₁ v₂ v₃ : SVar) (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ dynRelation R₂ v₂ v₃ (dynRelation R₁ v₁ v₂ c)) :
    R₃ (gs.1.sit v₁) (gs.1.sit v₃) :=
  hTrans _ _ _ h.1.2 h.2

/--
Trichotomy on any linearly ordered projection lifts to a context partition.

For any function `f : Situation → α` into a linear order, the three
comparison operators (<, =, >) form a complete partition of any context.
The temporal partition (`PAST ∪ PRES ∪ FUT = c`) is the special case
where `f = Situation.time`.
-/
theorem dynRelation_trichotomy {W Time E α : Type*} [LinearOrder α]
    (f : Situation W Time → α)
    (v₁ v₂ : SVar) (c : SitContext W Time E) :
    dynRelation (fun s₁ s₂ => f s₁ < f s₂) v₁ v₂ c ∪
    dynRelation (fun s₁ s₂ => f s₁ = f s₂) v₁ v₂ c ∪
    dynRelation (fun s₁ s₂ => f s₁ > f s₂) v₁ v₂ c = c := by
  apply Set.ext; intro gs
  unfold dynRelation
  constructor
  · rintro ((⟨hc, _⟩ | ⟨hc, _⟩) | ⟨hc, _⟩) <;> exact hc
  · intro hc
    rcases lt_trichotomy (f (gs.1.sit v₁)) (f (gs.1.sit v₂)) with h | h | h
    · exact Or.inl (Or.inl ⟨hc, h⟩)
    · exact Or.inl (Or.inr ⟨hc, h⟩)
    · exact Or.inr ⟨hc, h⟩


-- ════════════════════════════════════════════════════════════════
-- Temporal algebra (derived from dynRelation + order theory)
-- ════════════════════════════════════════════════════════════════

/-- PAST ∪ PRES ∪ FUT = identity. Derived from trichotomy on Time. -/
theorem temporal_partition {W Time E : Type*} [LinearOrder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time E) :
    dynPAST v₁ v₂ c ∪ dynPRES v₁ v₂ c ∪ dynFUT v₁ v₂ c = c := by
  rw [dynPAST_eq_dynRelation, dynPRES_eq_dynRelation, dynFUT_eq_dynRelation]
  exact dynRelation_trichotomy (fun s => s.time) v₁ v₂ c

/-- PAST and FUT are contradictory on the same variables. -/
theorem dynPAST_dynFUT_empty {W Time E : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time E) :
    dynPAST v₁ v₂ (dynFUT v₁ v₂ c) = ∅ := by
  rw [dynPAST_eq_dynRelation, dynFUT_eq_dynRelation]
  exact dynRelation_contradictory _ _
    (fun s₁ s₂ (h1 : s₁.time < s₂.time) (h2 : s₂.time < s₁.time) =>
      lt_asymm h1 h2) v₁ v₂ c

/-- PAST and PRES are contradictory on the same variables. -/
theorem dynPAST_dynPRES_empty {W Time E : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time E) :
    dynPAST v₁ v₂ (dynPRES v₁ v₂ c) = ∅ := by
  rw [dynPAST_eq_dynRelation, dynPRES_eq_dynRelation]
  exact dynRelation_contradictory _ _
    (fun s₁ s₂ (h1 : s₁.time < s₂.time) (h2 : s₁.time = s₂.time) =>
      absurd h1 (by rw [h2]; exact lt_irrefl _)) v₁ v₂ c

/-- PRES and FUT are contradictory on the same variables. -/
theorem dynPRES_dynFUT_empty {W Time E : Type*} [Preorder Time]
    (v₁ v₂ : SVar) (c : SitContext W Time E) :
    dynPRES v₁ v₂ (dynFUT v₁ v₂ c) = ∅ := by
  rw [dynPRES_eq_dynRelation, dynFUT_eq_dynRelation]
  exact dynRelation_contradictory _ _
    (fun s₁ s₂ (h1 : s₁.time = s₂.time) (h2 : s₂.time < s₁.time) =>
      absurd h2 (by rw [h1]; exact lt_irrefl _)) v₁ v₂ c

/-- Chained PAST constraints compose: e < r ∧ r < s → e < s. -/
theorem dynPAST_transitive {W Time E : Type*} [Preorder Time]
    (e r s : SVar) (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ dynPAST r s (dynPAST e r c)) :
    (gs.1.sit e).time < (gs.1.sit s).time := by
  rw [dynPAST_eq_dynRelation, dynPAST_eq_dynRelation] at h
  exact dynRelation_transitive _ _ _
    (fun s₁ s₂ s₃ (h1 : s₁.time < s₂.time) (h2 : s₂.time < s₃.time) =>
      lt_trans h1 h2) e r s c gs h


/--
Subordinate Future (SF) analysis.

The SF in Portuguese conditionals:
  "Se Maria estiver em casa, ela vai atender."
  "If Maria be.SF at home, she will answer."

Structure (@cite{mendes-2025}):
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

@cite{mendes-2025} §3.2: the future-oriented interpretation of SF is not due
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
    simp only [beq_self_eq_true, ite_true]
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
    (c : SitContext W Time E) : SitContext W Time E :=
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

Restrictor and nuclear must be context filters (`IsContextFilter`).
Linguistically, predicates filter contexts without modifying assignments.
-/
theorem sf_restrictor_future_reference {W Time E : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (rcVar speechVar : SVar)
    (restrictor nuclear : SitContext W Time E → SitContext W Time E)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ everyWithSFRestrictor history rcVar speechVar restrictor nuclear c)
    (hR : IsContextFilter restrictor) (hN : IsContextFilter nuclear) :
    -- The restrictor situation can be future relative to speech time
    (gs.1.sit rcVar).time > (gs.1.sit speechVar).time := by
  -- Track through the filter chain
  unfold everyWithSFRestrictor at h
  have h_sf : gs ∈ subordinateFuture history rcVar speechVar c :=
    Set.Subset.trans (hN _) (hR _) h
  -- subordinateFuture guarantees the future ordering via dynFUT
  unfold subordinateFuture dynFUT at h_sf
  exact h_sf.2


-- ════════════════════════════════════════════════════════════════
-- Bridge theorems: dynamic operators realize static operators
-- ════════════════════════════════════════════════════════════════

/-!
## Static↔Dynamic Bridge

The dynamic operators `dynSUBJ` and `dynIND` are the context-level lifts of
the static operators `Mood.SUBJ` and `Mood.IND` (defined in
`Theories/Semantics/Mood/Basic.lean`).

These bridge theorems prove the correspondence:
- `dynSUBJ` implements `SUBJ`'s existential quantification over historical
  alternatives, with additional bookkeeping (binding the result to a variable
  and updating the current situation).
- `dynIND` implements `IND`'s same-world presuppositional check as a
  context filter.
-/

/--
Full set characterization of dynSUBJ on singleton contexts.

Strictly stronger than `dynSUBJ_realizes_SUBJ`: gives the exact output set
rather than just an existential iff. The output of `dynSUBJ` on `{(g, s₀)}`
is precisely the set of `(g[v↦s₁], s₁)` for `s₁ ∈ historicalBase history s₀`.
-/
theorem dynSUBJ_singleton_eq {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (g : SitAssignment W Time E)
    (s₀ : Situation W Time) :
    dynSUBJ history v ({(g, s₀)} : SitContext W Time E) =
    { gs | ∃ s₁ ∈ historicalBase history s₀, gs = (g.updateSit v s₁, s₁) } := by
  apply Set.ext; intro gs
  unfold dynSUBJ
  constructor
  · rintro ⟨g', s₀', s₁, h_ctx, h_hist, h_upd, h_eq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp h_ctx)
    exact ⟨s₁, h_hist, Prod.ext h_upd h_eq⟩
  · rintro ⟨s₁, h_hist, h_eq⟩
    rw [h_eq]
    exact ⟨g, s₀, s₁, rfl, h_hist, rfl, rfl⟩

/--
Bridge: dynamic SUBJ realizes static SUBJ.

For a singleton context `{(g, s₀)}`, the set of situations reachable via
`dynSUBJ` at variable `v` that satisfy `P` is exactly the set that static
`SUBJ` existentially quantifies over.

This proves `dynSUBJ` is the context-level lift of `Mood.SUBJ`: the dynamic
operator implements the same existential quantification over historical
alternatives, with additional bookkeeping (binding the result to a variable
and updating the current situation).
-/
theorem dynSUBJ_realizes_SUBJ {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (g : SitAssignment W Time E)
    (s₀ : Situation W Time)
    (P : SitPred W Time) :
    (∃ gs ∈ dynSUBJ history v ({(g, s₀)} : SitContext W Time E),
      P (gs.1.sit v) s₀) ↔
    SUBJ history P s₀ := by
  unfold SUBJ dynSUBJ
  constructor
  · -- Forward: dynamic output → static existential
    rintro ⟨gs, ⟨g', s₀', s₁, h_ctx, h_hist, h_upd, h_eq⟩, h_P⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp h_ctx)
    have h_sit : gs.1.sit v = s₁ := by
      rw [h_upd]
      unfold SitAssignment.updateSit
      simp only [beq_self_eq_true, ite_true]
    exact ⟨s₁, h_hist, h_sit ▸ h_P⟩
  · -- Backward: static existential → dynamic witness
    rintro ⟨s₁, h_hist, h_P⟩
    refine ⟨(g.updateSit v s₁, s₁), ?_, ?_⟩
    · exact ⟨g, s₀, s₁, rfl, h_hist, rfl, rfl⟩
    · have h_sit : (g.updateSit v s₁).sit v = s₁ := by
        unfold SitAssignment.updateSit
        simp only [beq_self_eq_true, ite_true]
      rw [h_sit]
      exact h_P

/--
dynSUBJ invariant: variable v always equals the current situation.

After `dynSUBJ` binds `v`, looking up `v` in the assignment always
returns the current situation. This is the structural property that
makes `dynIND` vacuous on the same variable (see `dynIND_after_dynSUBJ_same_var`).
-/
theorem dynSUBJ_binds_current {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ dynSUBJ history v c) :
    gs.1.sit v = gs.2 := by
  unfold dynSUBJ at h
  obtain ⟨g, s₀, s₁, _, _, h_upd, h_eq⟩ := h
  rw [h_upd, h_eq]
  unfold SitAssignment.updateSit
  simp only [beq_self_eq_true, ite_true]

/--
Bridge: dynamic IND realizes static IND.

The filter condition imposed by `dynIND` is exactly the same-world
constraint of static `Mood.IND`: membership in the filtered context
plus a predicate on the situations is equivalent to membership in the
original context plus the static IND applied to those situations.
-/
theorem dynIND_realizes_IND {W Time E : Type*}
    (v : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (P : SitPred W Time) :
    (gs ∈ dynIND v c ∧ P gs.2 (gs.1.sit v)) ↔
    (gs ∈ c ∧ IND P (gs.1.sit v) gs.2) := by
  unfold dynIND IND
  constructor
  · rintro ⟨⟨hc, hw⟩, hP⟩
    exact ⟨hc, hw, hP⟩
  · rintro ⟨hc, hw, hP⟩
    exact ⟨⟨hc, hw⟩, hP⟩

/--
IND is identity after SUBJ on the same variable.

When SUBJ introduces s₁ and binds it to v, IND's same-world check
on v is trivially satisfied (`gs.2 = s₁ = gs.1.sit v` by construction).
This explains why `crossClausalBinding` with shared variables
preserves the full SUBJ output.
-/
theorem dynIND_after_dynSUBJ_same_var {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time E) :
    dynIND v (dynSUBJ history v c) = dynSUBJ history v c := by
  apply Set.ext; intro gs
  unfold dynIND
  constructor
  · exact fun ⟨h_mem, _⟩ => h_mem
  · intro h_mem
    exact ⟨h_mem, by rw [dynSUBJ_binds_current history v c gs h_mem]⟩

end Semantics.Dynamic.IntensionalCDRT.Situations
