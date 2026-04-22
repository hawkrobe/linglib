import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Core.Causal.SEM.Monotonicity

/-!
# Causal Sufficiency
@cite{nadathur-lauer-2020} @cite{schulz-2011}

Causal sufficiency semantics for the verb "make" based on
@cite{nadathur-lauer-2020} Definition 23.

## Insight

"X made Y happen" asserts that X was **sufficient** for Y:
- Given the background situation, adding X guarantees Y
- The effect is inevitable once the cause is in place

## Formal Definition (Def 23)

C is **causally sufficient** for E in situation s iff:
  normalDevelopment(s ⊕ {C = true}) includes E = true
-/

namespace Semantics.Causation.Sufficiency

open Core.Causal
export Core.Causal (causallySufficient)

/-- Semantics of "make": X was causally sufficient for Y (@cite{nadathur-lauer-2020}).
    Definitionally identical to `causallySufficient` — exposed under the
    `make`-flavored name for use in lexical semantics. -/
abbrev makeSem (dyn : CausalDynamics) (background : Situation)
    (causeEvent effectEvent : Variable) : Prop :=
  causallySufficient dyn background causeEvent effectEvent

/-- Hub bridge: `makeSem ↔ causallySufficient` (true by construction). -/
theorem makeSem_iff_causallySufficient (dyn : CausalDynamics) (background : Situation)
    (causeEvent effectEvent : Variable) :
    makeSem dyn background causeEvent effectEvent ↔
      causallySufficient dyn background causeEvent effectEvent :=
  Iff.rfl

/-- Sufficiency implies effect occurrence (after cause). -/
theorem sufficient_implies_effect (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable)
    (h : causallySufficient dyn s cause effect) :
    developsToTrue dyn (s.extend cause true) effect := h

-- ════════════════════════════════════════════════════
-- § Helper: closed-form for `simple c e` law application
-- ════════════════════════════════════════════════════

/-- Helper for reasoning about `simple` law application: if cause is true
    and effect is undetermined, the law sets effect to true. -/
private theorem simple_applies_when_ready {a b : Variable} {s : Situation}
    (hMet : s.hasValue a true) (hNone : s.get b = none) :
    (CausalLaw.simple a b).apply s = s.extend b true :=
  CausalLaw.apply_of_met_undetermined
    (fun p hp => by
      simp only [CausalLaw.simple, List.mem_singleton] at hp
      rw [hp]; exact hMet)
    hNone

/-- Helper: if the precondition variable is undetermined, the simple law
    doesn't fire. -/
private theorem simple_doesnt_fire {a b : Variable} {s : Situation}
    (hNone : s.get a = none) :
    (CausalLaw.simple a b).apply s = s := by
  apply CausalLaw.apply_of_not_met
  intro hMet
  have := hMet (a, true) (by simp [CausalLaw.simple])
  -- `this : s.hasValue a true` but `hNone : s.get a = none` — contradiction
  unfold Situation.hasValue at this
  rw [show s.valuation a = s.get a from rfl, hNone] at this
  cases this

-- ════════════════════════════════════════════════════
-- § Disjunctive / Conjunctive Sufficiency
-- ════════════════════════════════════════════════════

/-- In disjunctive causation (A ∨ B → C), each disjunct is sufficient
    when the other is undetermined and effect is undetermined. -/
theorem disjunctive_each_sufficient (a b c : Variable)
    (ha : a ≠ b) (hac : a ≠ c) (_hbc : b ≠ c) :
    causallySufficient (CausalDynamics.disjunctiveCausation a b c)
      Situation.empty a c := by
  -- Setup: s = empty.extend a true
  set s := Situation.empty.extend a true with hs
  -- Compute: applyLawsOnce on disjunctive
  have hMet_a : s.hasValue a true := by
    show s.valuation a = some true
    simp [hs, Situation.extend, Situation.empty]
  have hNone_c : s.get c = none := by
    show (Situation.empty.extend a true).get c = none
    rw [Situation.extend_get_ne (Ne.symm hac)]; rfl
  have hNone_b : s.get b = none := by
    show (Situation.empty.extend a true).get b = none
    rw [Situation.extend_get_ne (Ne.symm ha)]; rfl
  -- After the first foldl step
  have hStep1 : (CausalLaw.simple a c).apply s = s.extend c true :=
    simple_applies_when_ready hMet_a hNone_c
  -- After both foldl steps: second law doesn't fire (b stays none after extending c)
  have hNone_b' : (s.extend c true).get b = none := by
    rw [Situation.extend_get_ne _hbc]; exact hNone_b
  have hStep2 : (CausalLaw.simple b c).apply (s.extend c true) = s.extend c true :=
    simple_doesnt_fire hNone_b'
  have hApp : applyLawsOnce (CausalDynamics.disjunctiveCausation a b c) s
              = s.extend c true := by
    show ([CausalLaw.simple a c, CausalLaw.simple b c].foldl _ s) = _
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hStep1, hStep2]
  -- Verify fixpoint after one round
  have hFix : isFixpoint (CausalDynamics.disjunctiveCausation a b c) (s.extend c true) := by
    intro law hLaw _ hNone
    -- Both laws have effect = c, and (s.extend c true).get c = some true ≠ none
    have hEffectC : law.effect = c := by
      simp only [CausalDynamics.disjunctiveCausation, List.mem_cons,
                 List.not_mem_nil, or_false] at hLaw
      rcases hLaw with hL | hL <;> (subst hL; rfl)
    rw [hEffectC, Situation.extend_get_same] at hNone
    cases hNone
  -- Conclude
  unfold causallySufficient
  rw [normalDevelopment_eq_applyLawsOnce_of_fixpoint _ _ (hApp ▸ hFix), hApp]
  show (s.extend c true).hasValue c true
  rw [Situation.extend_hasValue_same]

/-- In conjunctive causation (A ∧ B → C), neither alone is sufficient. -/
theorem conjunctive_neither_sufficient_alone (a b c : Variable)
    (_ha : a ≠ b) (hac : a ≠ c) (_hbc : b ≠ c) :
    ¬ (causallySufficient (CausalDynamics.conjunctiveCausation a b c)
        Situation.empty a c) := by
  set s := Situation.empty.extend a true with hs
  have hNone_b : s.get b = none := by
    show (Situation.empty.extend a true).get b = none
    rw [Situation.extend_get_ne (Ne.symm _ha)]; rfl
  -- Conjunctive law: precondition needs (a, true) AND (b, true). b is none → not met.
  have hNotMet : ¬ (CausalLaw.conjunctive a b c).preconditionsMet s := by
    intro hMet
    have := hMet (b, true) (by simp [CausalLaw.conjunctive])
    unfold Situation.hasValue at this
    rw [show s.valuation b = s.get b from rfl, hNone_b] at this
    cases this
  have hStep : (CausalLaw.conjunctive a b c).apply s = s :=
    CausalLaw.apply_of_not_met hNotMet
  have hApp : applyLawsOnce (CausalDynamics.conjunctiveCausation a b c) s = s := by
    show ([CausalLaw.conjunctive a b c].foldl _ s) = _
    simp only [List.foldl_cons, List.foldl_nil]; exact hStep
  -- s is a fixpoint (the law's preconditions can never be met without b)
  have hFix : isFixpoint (CausalDynamics.conjunctiveCausation a b c) s := by
    intro law hLaw hMet _
    have hL : law = CausalLaw.conjunctive a b c := by
      simp only [CausalDynamics.conjunctiveCausation, List.mem_cons,
                 List.not_mem_nil, or_false] at hLaw
      exact hLaw
    subst hL; exact hNotMet hMet
  -- Final: c is none in s, so causallySufficient fails
  unfold causallySufficient
  rw [normalDevelopment_of_fixpoint hFix]
  intro hHas
  unfold Situation.hasValue at hHas
  have hNone_c : s.get c = none := by
    show (Situation.empty.extend a true).get c = none
    rw [Situation.extend_get_ne (Ne.symm hac)]; rfl
  rw [show s.valuation c = s.get c from rfl, hNone_c] at hHas
  cases hHas

/-- In conjunctive causation, A is sufficient when B is in the background. -/
theorem conjunctive_sufficient_with_other (a b c : Variable)
    (ha : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    causallySufficient (CausalDynamics.conjunctiveCausation a b c)
      (Situation.empty.extend b true) a c := by
  set s := (Situation.empty.extend b true).extend a true with hs
  have hMet_a : s.hasValue a true := by
    show s.valuation a = some true; simp [hs, Situation.extend]
  have hMet_b : s.hasValue b true := by
    show s.valuation b = some true
    simp only [hs, Situation.extend]
    rw [show (b == a) = false from beq_false_of_ne (Ne.symm ha)]
    show (Situation.empty.extend b true).valuation b = some true
    simp [Situation.extend]
  have hNone_c : s.get c = none := by
    show ((Situation.empty.extend b true).extend a true).get c = none
    rw [Situation.extend_get_ne (Ne.symm hac), Situation.extend_get_ne (Ne.symm hbc)]
    rfl
  have hMetConj : (CausalLaw.conjunctive a b c).preconditionsMet s := by
    intro p hp
    simp only [CausalLaw.conjunctive, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp
    · rw [hp]; exact hMet_a
    · rw [hp]; exact hMet_b
  have hStep : (CausalLaw.conjunctive a b c).apply s = s.extend c true :=
    CausalLaw.apply_of_met_undetermined hMetConj hNone_c
  have hApp : applyLawsOnce (CausalDynamics.conjunctiveCausation a b c) s
              = s.extend c true := by
    show ([CausalLaw.conjunctive a b c].foldl _ s) = _
    simp only [List.foldl_cons, List.foldl_nil]; exact hStep
  -- Fixpoint after one round
  have hFix : isFixpoint (CausalDynamics.conjunctiveCausation a b c) (s.extend c true) := by
    intro law hLaw _ hNone
    have hL : law = CausalLaw.conjunctive a b c := by
      simp only [CausalDynamics.conjunctiveCausation, List.mem_cons,
                 List.not_mem_nil, or_false] at hLaw
      exact hLaw
    rw [hL, show (CausalLaw.conjunctive a b c).effect = c from rfl,
        Situation.extend_get_same] at hNone
    cases hNone
  unfold causallySufficient
  rw [normalDevelopment_eq_applyLawsOnce_of_fixpoint _ _ (hApp ▸ hFix), hApp]
  show (s.extend c true).hasValue c true
  rw [Situation.extend_hasValue_same]

end Semantics.Causation.Sufficiency
