import Linglib.Theories.Semantics.Tense.Dynamic
import Linglib.Theories.Semantics.Mood.Dynamic
import Linglib.Core.Modality.HistoricalAlternatives

/-!
# Modal Donkey Anaphora (@cite{mendes-2025} §3.1)

The central theoretical insight of @cite{mendes-2025}: the Subordinate Future (SF)
enables modal donkey anaphora -- subjunctive binds situation variables
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

## Key Formalization

SUBJ introduces: [s₁ | s₁ ∈ hist(s₀)]
IND retrieves: [| w_{s₂} = w_{s₁}]

The anaphoric relationship:
- SUBJ is existential (like indefinite "a")
- IND is presuppositional (like definite "the")
-/

namespace Semantics.Dynamic.IntensionalCDRT.ModalDonkeyAnaphora

open _root_.Core (Assignment WorldTimeIndex)
open Core.Modality.HistoricalAlternatives
open Semantics.Dynamic.Core
open Semantics.Mood


/--
Modal accessibility: a situation s₂ can anaphorically access s₁
if they share the same world (same-world constraint from IND).

From @cite{mendes-2025}'s IND operator:
  IND_v = λP.[| w_{s₂} = w_{s₁}]; P(s₂)(s₁)
-/
def modallyAccessible {W Time : Type*}
    (s₁ s₂ : WorldTimeIndex W Time) : Prop :=
  s₂.world = s₁.world

/--
Cross-clausal situation binding: situation introduced in one clause
can be retrieved in another clause via modal donkey anaphora.

SF in the antecedent of a conditional
introduces a situation that the consequent can anaphorically access.

Example:
  "Se Maria estiver em casa, ela vai atender."
       ↑ SUBJ introduces s₁ ↑ IND retrieves s₁
-/
def crossClausalBinding {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (antecedentVar _consequentVar : SVar)
    (c : SitContext W Time) : SitContext W Time :=
  -- First: SUBJ in antecedent introduces situation bound to antecedentVar
  let c₁ := dynSUBJ history antecedentVar c
  -- Then: IND in consequent retrieves via same-world constraint
  dynIND antecedentVar c₁

/--
Cross-clausal binding preserves world identity.

When a situation is introduced in the antecedent and retrieved in the
consequent, the two clauses are evaluated at the same world.
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
The SUBJ-IND anaphoric chain.

This represents the complete anaphoric dependency:
1. SUBJ^v introduces situation s₁ ∈ hist(s₀)
2. Antecedent predicate P is evaluated at s₁
3. IND_v retrieves s₁ for the consequent
4. Consequent Q is evaluated at the same world as s₁

The result: temporal properties of the consequent are "inherited" from
the situation introduced by the subjunctive.
-/
def subjIndChain {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)  -- Shared situation variable
    (antecedentPred : SitContext W Time → SitContext W Time)
    (consequentPred : SitContext W Time → SitContext W Time)
    (c : SitContext W Time) : SitContext W Time :=
  -- Step 1: SUBJ introduces s₁
  let c₁ := dynSUBJ history v c
  -- Step 2: Filter by antecedent
  let c₂ := antecedentPred c₁
  -- Step 3: IND retrieves (same-world check)
  let c₃ := dynIND v c₂
  -- Step 4: Evaluate consequent
  consequentPred c₃

/--
The SUBJ-IND chain establishes modal donkey anaphora.

The consequent is evaluated at a world that agrees with the antecedent
world up to the introduction time.

Q must be a context filter (`IsContextFilter`).
Linguistically, predicates filter contexts without modifying assignments.
-/
theorem subj_ind_chain_modal_donkey {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (P Q : SitContext W Time → SitContext W Time)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ subjIndChain history v P Q c)
    (hQ : IsContextFilter Q) :
    -- The consequent situation shares its world with the bound situation
    gs.2.world = (gs.1 v).world := by
  unfold subjIndChain at h
  -- Q is a filter, so membership in Q(...) implies membership in dynIND(...)
  have h_in_ind : gs ∈ dynIND v (P (dynSUBJ history v c)) := hQ _ h
  -- dynIND enforces the same-world constraint
  unfold dynIND at h_in_ind
  exact h_in_ind.2


/-!
### Structural parallel

Both classic and modal donkey anaphora share the same shape:
1. Existential introduction in a subordinate position
2. Anaphoric retrieval outside c-command domain
3. Universal-like interpretation over domain

Classic donkey anaphora quantifies over individuals;
modal donkey anaphora quantifies over situations (and their times).
-/

/--
Unselective binding gives universal force.

When SUBJ introduces a situation in a conditional antecedent,
the conditional quantifies universally over situations satisfying
the antecedent in the historical base.

This is the modal analog of donkey universals.
-/
theorem unselective_universal_force {W Time : Type*} [LE Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (antecedent consequent : WorldTimeIndex W Time → Prop)
    (c : SitContext W Time) :
    -- For all situations in the output...
    (∀ gs ∈ subjIndChain history v
      (λ c' => { gs' ∈ c' | antecedent gs'.2 })
      (λ c' => { gs' ∈ c' | consequent gs'.2 })
      c,
      -- ...if the antecedent holds, so does the consequent
      antecedent gs.2 → consequent gs.2) := by
  intro gs h_mem h_ant
  unfold subjIndChain at h_mem
  simp only [Set.mem_setOf_eq] at h_mem
  exact h_mem.2


/--
Modal donkey anaphora enables temporal shift.

The future-oriented interpretation of SF follows from modal donkey anaphora:
1. SUBJ introduces s₁ ∈ hist(s₀) with τ(s₁) ≥ τ(s₀)
2. The consequent is evaluated at s₁'s time via IND's retrieval
3. Therefore, the consequent can refer to times after τ(s₀)
-/
theorem modal_donkey_enables_temporal_shift {W Time : Type*} [Preorder Time]
    (history : WorldHistory W Time)
    (v : SVar)
    (c : SitContext W Time)
    (gs : Assignment (WorldTimeIndex W Time) × WorldTimeIndex W Time)
    (h : gs ∈ dynSUBJ history v c) :
    ∃ s₀, (∃ g₀, (g₀, s₀) ∈ c) ∧
          (gs.1 v).time ≥ s₀.time := by
  unfold dynSUBJ at h
  obtain ⟨g, s₀, s₁, hc, h_hist, h_upd, h_eq⟩ := h
  use s₀
  constructor
  · exact ⟨g, hc⟩
  · -- s₁ ∈ historicalBase history s₀ means s₁.time ≥ s₀.time
    unfold historicalBase at h_hist
    simp only [Set.mem_setOf_eq] at h_hist
    -- g' = g.update v s₁, so g' v = s₁
    have h_sit : gs.1 v = s₁ := by
      rw [h_upd]; simp only [Assignment.update_at]
    rw [h_sit]
    exact h_hist.2

/--
Donkey accessibility is transitive within a discourse.

If s₁ is accessible from s₀, and s₂ is accessible from s₁,
then s₂ is accessible from s₀ (within the same world).
-/
theorem donkey_accessibility_transitive {W Time : Type*}
    (s₀ s₁ s₂ : WorldTimeIndex W Time)
    (h₁ : modallyAccessible s₀ s₁)
    (h₂ : modallyAccessible s₁ s₂) :
    modallyAccessible s₀ s₂ := by
  unfold modallyAccessible at *
  -- h₁ : s₁.world = s₀.world
  -- h₂ : s₂.world = s₁.world
  -- goal : s₂.world = s₀.world
  exact h₂.trans h₁


-- ════════════════════════════════════════════════════════════════
-- Bridge to ICDRT accessibility (Operators.lean)
-- ════════════════════════════════════════════════════════════════

/-!
## Connection to ICDRT propositional accessibility

`modallyAccessible` (this file, @cite{mendes-2025}) and
`accessible` (`Operators.lean`, @cite{hofmann-2025}) formalize
anaphoric accessibility at two different levels:

- **Situation level** (`modallyAccessible`): s₂ retrieves s₁ via
  same-world constraint. Governs cross-clausal situation binding
  (modal donkey anaphora).
- **Propositional dref level** (`accessible`): v is accessible in
  context φ at state i iff v has a referent in all φ-worlds (local
  entailment) and discourse is consistent. Governs individual dref
  accessibility across negation, disjunction, and attitude contexts.

Both enforce the same structural pattern: the retrieval context must
be compatible with the introduction context. For situations, this is
world identity (`s₂.world = s₁.world`). For individual drefs, this
is the subset requirement (`φ_anaphor ⊆ φ_antecedent`, Definition 39)
combined with local entailment (v exists throughout φ_anaphor).

The unifying principle is @cite{hofmann-2025}'s veridicality: both
individual drefs and situation drefs are accessible when the anaphor's
local context is contained within the antecedent's local context.
-/

/-- Accessibility at the situation level entails accessibility at the
    world level: if s₂ can anaphorically retrieve s₁, then any
    world-level property holding at s₁'s world also holds at s₂'s. -/
theorem donkey_accessible_preserves_world_property {W Time : Type*}
    (s₁ s₂ : WorldTimeIndex W Time)
    (h : modallyAccessible s₁ s₂)
    (P : W → Prop) (hp : P s₁.world) :
    P s₂.world := by
  rwa [h]

-- ════════════════════════════════════════════════════════════════
-- Compositional bridge: dynamic pipeline ↔ static existential
-- ════════════════════════════════════════════════════════════════

/-!
## Pipeline characterization

The full dynamic pipeline `SUBJ → filter(P) → IND → filter(Q)` on a
singleton context is equivalent to a static existential conjunction
over historical alternatives.

Note: the dynamic pipeline gives *conjunction* (`P ∧ Q`), not
*implication* (`P → Q`). The static `conditionalSF` uses implication;
sequential composition gives the stronger conjunctive reading.
This matches the analysis where `seqUpdate` is sequential composition,
not the paper's DRS conditional test.
-/

/--
The SUBJ-IND chain with predication filters on a singleton context
characterizes the static existential conjunction:
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
  obtain ⟨s₁, h_hist, hP, hQ⟩ := (subjIndChain_singleton history v g s₀ P (fun s => Q s s)).mp h
  exact ⟨s₁, h_hist, fun _ => hQ⟩

end Semantics.Dynamic.IntensionalCDRT.ModalDonkeyAnaphora
