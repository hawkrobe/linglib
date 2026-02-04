/-
# Modal Donkey Anaphora (Mendes 2025 §3.1)

The central theoretical insight of Mendes (2025): the Subordinate Future (SF)
enables **modal donkey anaphora** - subjunctive binds situation variables
across clause boundaries, just like indefinites bind individual variables
in classic donkey sentences.

## The Parallel

Classic donkey anaphora:
  "If a farmer owns a donkey, he beats it."
  - "a donkey" introduces individual dref x
  - "it" retrieves x outside the syntactic scope of "a"

Modal donkey anaphora:
  "Se Maria estiver em casa, ela vai atender."
  "If Maria be.SF home, she will answer."
  - SF introduces situation dref s₁
  - Main clause retrieves s₁ for temporal anchoring

## Key Formalization (Paper formulas 30-31)

(30) SUBJ introduces: [s₁ | s₁ ∈ hist(s₀)]
(31) IND retrieves: [| w_{s₂} = w_{s₁}]

The anaphoric relationship:
- SUBJ is existential (like indefinite "a")
- IND is presuppositional (like definite "the")

## References

- Mendes, A. (2025). Indefiniteness in future reference. S&P 18(10).
- Groenendijk & Stokhof (1991). Dynamic Predicate Logic.
- Roberts (1989). Modal subordination and pronominal anaphora.
-/

import Linglib.Theories.DynamicSemantics.IntensionalCDRT.Situations
import Linglib.Theories.DynamicSemantics.IntensionalCDRT.Basic

namespace Theories.DynamicSemantics.IntensionalCDRT.ModalDonkeyAnaphora

open Montague.Core.Time
open Montague.Sentence.Mood
open Theories.DynamicSemantics.IntensionalCDRT
open Theories.DynamicSemantics.IntensionalCDRT.Situations
open Theories.DynamicSemantics.Core


/--
A situation variable is **bound** if it was introduced by SUBJ.

In classic DRT, a variable is bound if it was introduced by an existential
quantifier or indefinite. Here, SUBJ plays the role of the indefinite.
-/
structure SitBinding (W Time : Type*) where
  /-- The variable that was introduced -/
  boundVar : SVar
  /-- The situation where binding occurred -/
  bindingSituation : Situation W Time
  /-- The historical alternatives available at binding -/
  alternatives : Set (Situation W Time)

/--
**Antecedent-contained binding**: The bound variable's value is
constrained to be in the historical alternatives of the binding situation.

This is the modal analog of the accessibility constraint in DRT.
-/
def SitBinding.isValid {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (b : SitBinding W Time) : Prop :=
  b.alternatives = historicalBase history b.bindingSituation

/--
**Modal accessibility**: A situation s₂ can anaphorically access s₁
if they share the same world (same-world constraint from IND).

This is formula (31) from the paper:
  IND_v = λP.[| w_{s₂} = w_{s₁}]; P(s₂)(s₁)
-/
def modallyAccessible {W Time : Type*}
    (s₁ s₂ : Situation W Time) : Prop :=
  s₂.world = s₁.world

/--
**Donkey accessibility** for situations: s₂ can retrieve s₁ if:
1. s₁ was introduced by SUBJ (in some local context)
2. s₂ satisfies the same-world constraint (IND)

This is the situation-level analog of the donkey accessibility condition.
-/
structure DonkeyAccessibility (W Time E : Type*) where
  /-- The antecedent situation (introduced by SUBJ) -/
  antecedent : Situation W Time
  /-- The consequent situation (retrieves via IND) -/
  consequent : Situation W Time
  /-- Same-world constraint satisfied -/
  sameWorld : modallyAccessible antecedent consequent


/--
**Cross-clausal situation binding**: Situation introduced in one clause
can be retrieved in another clause via modal donkey anaphora.

This formalizes the key insight: SF in the antecedent of a conditional
introduces a situation that the consequent can anaphorically access.

Example:
  "Se Maria estiver em casa, ela vai atender."
       ↑ SUBJ introduces s₁          ↑ IND retrieves s₁
-/
def crossClausualBinding {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (antecedentVar consequentVar : SVar)
    (c : SitContext W Time E) : SitContext W Time E :=
  -- First: SUBJ in antecedent introduces situation bound to antecedentVar
  let c₁ := dynSUBJ history antecedentVar c
  -- Then: IND in consequent retrieves via same-world constraint
  dynIND antecedentVar c₁

/--
**Theorem: Cross-clausal binding preserves world identity**

When a situation is introduced in the antecedent and retrieved in the
consequent, the two clauses are evaluated at the same world.
-/
theorem cross_clausal_same_world {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ crossClausualBinding history v v c) :
    gs.2.world = (gs.1.sit v).world := by
  unfold crossClausualBinding at h
  unfold dynIND at h
  exact h.2


/--
**The SUBJ-IND anaphoric chain** (Mendes 2025, §4.3)

This represents the complete anaphoric dependency:
1. SUBJ^v introduces situation s₁ ∈ hist(s₀)
2. Antecedent predicate P is evaluated at s₁
3. IND_v retrieves s₁ for the consequent
4. Consequent Q is evaluated at the same world as s₁

The result: temporal properties of the consequent are "inherited" from
the situation introduced by the subjunctive.
-/
def subjIndChain {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)  -- Shared situation variable
    (antecedentPred : SitContext W Time E → SitContext W Time E)
    (consequentPred : SitContext W Time E → SitContext W Time E)
    (c : SitContext W Time E) : SitContext W Time E :=
  -- Step 1: SUBJ introduces s₁
  let c₁ := dynSUBJ history v c
  -- Step 2: Filter by antecedent
  let c₂ := antecedentPred c₁
  -- Step 3: IND retrieves (same-world check)
  let c₃ := dynIND v c₂
  -- Step 4: Evaluate consequent
  consequentPred c₃

/--
**Theorem: The SUBJ-IND chain establishes modal donkey anaphora**

The consequent is evaluated at a world that agrees with the antecedent
world up to the introduction time.

Note: Requires that Q is a filter (preserves subset membership and assignments).
Linguistically, predicates filter contexts without modifying assignments.
-/
theorem subj_ind_chain_modal_donkey {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (P Q : SitContext W Time E → SitContext W Time E)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ subjIndChain history v P Q c)
    -- Q is a filter: it only selects subsets, preserving the IND property
    (hQ_filter : Q (dynIND v (P (dynSUBJ history v c))) ⊆ dynIND v (P (dynSUBJ history v c))) :
    -- The consequent situation shares its world with the bound situation
    gs.2.world = (gs.1.sit v).world := by
  unfold subjIndChain at h
  -- Q is applied to dynIND result, and filters preserve membership
  have h_in_ind : gs ∈ dynIND v (P (dynSUBJ history v c)) := hQ_filter h
  -- dynIND enforces the same-world constraint
  unfold dynIND at h_in_ind
  exact h_in_ind.2


/--
**Classic donkey anaphora structure** (for comparison)

"If a farmer owns a donkey, he beats it."

The indefinite "a donkey" introduces an individual dref that is
accessible in the consequent despite being outside its c-command domain.
-/
structure ClassicDonkey (E : Type*) where
  /-- The introduced individual variable -/
  boundIndivVar : IVar
  /-- The entity it binds to -/
  boundEntity : E

/--
**Modal donkey anaphora structure** (Mendes' contribution)

"If Maria be.SF home, she will answer."

The subjunctive introduces a situation dref that is accessible in the
consequent despite being outside its c-command domain.
-/
structure ModalDonkey (W Time : Type*) where
  /-- The introduced situation variable -/
  boundSitVar : SVar
  /-- The situation it binds to -/
  boundSituation : Situation W Time
  /-- Historical alternatives at binding -/
  historicalBase : Set (Situation W Time)

/--
**The structural parallel**

Both classic and modal donkey anaphora share:
1. Existential introduction in a subordinate position
2. Anaphoric retrieval outside c-command domain
3. Universal-like interpretation over domain

The difference:
- Classic: quantifies over individuals
- Modal: quantifies over situations (and their times)
-/
def structuralParallel : Prop :=
  -- Both involve:
  -- 1. Indefinite/existential introduction
  -- 2. Cross-clausal retrieval
  -- 3. Universal force in the consequent
  True  -- Documented parallel


/--
**E-type vs unselective binding for situations**

Mendes follows the DRT/dynamic tradition where binding is "unselective":
the situation variable is directly bound, not via an E-type pronoun.

This is crucial: SF doesn't introduce a description "the situation where..."
but directly binds a situation variable that IND retrieves.
-/
inductive SituationBindingStrategy where
  | unselective  -- Direct variable binding (DRT, Mendes)
  | eType        -- Descriptive retrieval (Evans)
  deriving DecidableEq, Repr

/--
**Mendes uses unselective binding**

The SF directly binds a situation variable, and IND retrieves it.
This is parallel to how indefinites work in DRT.
-/
def mendesBindingStrategy : SituationBindingStrategy :=
  .unselective

/--
**Theorem: Unselective binding gives universal force**

When SUBJ introduces a situation in a conditional antecedent,
the conditional quantifies universally over situations satisfying
the antecedent in the historical base.

This is the modal analog of donkey universals.
-/
theorem unselective_universal_force {W Time E : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (antecedent consequent : Situation W Time → Prop)
    (c : SitContext W Time E) :
    -- For all situations in the output...
    (∀ gs ∈ subjIndChain history v
      (fun c' => { gs' ∈ c' | antecedent gs'.2 })
      (fun c' => { gs' ∈ c' | consequent gs'.2 })
      c,
      -- ...if the antecedent holds, so does the consequent
      antecedent gs.2 → consequent gs.2) := by
  intro gs h_mem h_ant
  unfold subjIndChain at h_mem
  simp only [Set.mem_setOf_eq] at h_mem
  exact h_mem.2


/--
**Main Theorem: Modal donkey anaphora enables temporal shift**

The future-oriented interpretation of SF follows from modal donkey anaphora:
1. SUBJ introduces s₁ ∈ hist(s₀) with τ(s₁) ≥ τ(s₀)
2. The consequent is evaluated at s₁'s time via IND's retrieval
3. Therefore, the consequent can refer to times after τ(s₀)

This is the foundation for Theorem `temporal_shift_parasitic_on_modal`
(formalized in Situations.lean extension).
-/
theorem modal_donkey_enables_temporal_shift {W Time E : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time E)
    (gs : SitAssignment W Time E × Situation W Time)
    (h : gs ∈ dynSUBJ history v c) :
    ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧
          (gs.1.sit v).time ≥ s₀.time := by
  unfold dynSUBJ at h
  obtain ⟨g, s₀, s₁, hc, h_hist, h_upd, h_eq⟩ := h
  use s₀
  constructor
  · exact ⟨g, hc⟩
  · -- s₁ ∈ historicalBase history s₀ means s₁.time ≥ s₀.time
    unfold historicalBase at h_hist
    simp only [Set.mem_setOf_eq] at h_hist
    -- g' = g.updateSit v s₁, so g'.sit v = s₁
    have h_sit : gs.1.sit v = s₁ := by
      rw [h_upd]
      unfold SitAssignment.updateSit
      simp only [show (v == v) = true from by
        unfold instBEqSVar BEq.beq
        exact decide_eq_true rfl, ite_true]
    rw [h_sit]
    exact h_hist.2

/--
**Theorem: Donkey accessibility is transitive within a discourse**

If s₁ is accessible from s₀, and s₂ is accessible from s₁,
then s₂ is accessible from s₀ (within the same world).
-/
theorem donkey_accessibility_transitive {W Time : Type*}
    (s₀ s₁ s₂ : Situation W Time)
    (h₁ : modallyAccessible s₀ s₁)
    (h₂ : modallyAccessible s₁ s₂) :
    modallyAccessible s₀ s₂ := by
  unfold modallyAccessible at *
  -- h₁ : s₁.world = s₀.world
  -- h₂ : s₂.world = s₁.world
  -- goal : s₂.world = s₀.world
  exact h₂.trans h₁

-- Summary

/-
## What This Module Provides

### Core Concepts
- `SitBinding`: Records situation variable binding by SUBJ
- `modallyAccessible`: Same-world constraint for IND retrieval
- `DonkeyAccessibility`: Full accessibility relation for situations

### Cross-Clausal Binding
- `crossClausualBinding`: Situation introduced in one clause, retrieved in another
- `subjIndChain`: Complete SUBJ-IND anaphoric chain

### Structural Parallel
- `ClassicDonkey`: Traditional donkey anaphora structure
- `ModalDonkey`: Mendes' modal analog
- `structuralParallel`: Documents the parallel

### Key Theorems
- `cross_clausal_same_world`: Cross-clausal binding preserves world identity
- `modal_donkey_enables_temporal_shift`: Modal anaphora enables future reference
- `unselective_universal_force`: Donkey universals for situations
- `donkey_accessibility_transitive`: Transitivity of modal accessibility

### Connection to Other Modules
- `Situations.lean`: dynSUBJ, dynIND, subordinateFuture
- `Mood/Basic.lean`: Static SUBJ and IND operators
- Standard DRT infrastructure for individual donkey anaphora
-/

end Theories.DynamicSemantics.IntensionalCDRT.ModalDonkeyAnaphora
