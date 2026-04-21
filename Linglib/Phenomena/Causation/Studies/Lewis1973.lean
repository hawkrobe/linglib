import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Core.WorldTimeIndex
import Linglib.Theories.Semantics.Causation.CCSelection
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Phenomena.Causation.Studies.BarAsherSiegal2026

/-!
# @cite{lewis-1973-causation}: Causation

@cite{lewis-1973-causation}

Formalization of Lewis's counterfactual analysis of causation.

## Three Key Concepts

1. **Causal dependence** (p. 563): e depends causally on c iff the
   counterfactual "if c had not occurred, e would not have occurred"
   holds — the but-for test.

2. **Causation** (p. 563): the transitive closure of causal dependence.
   c causes e iff there exists a causal chain from c to e where each
   consecutive pair is a causal dependence.

3. **Epiphenomena asymmetry** (p. 565): intervention-based counterfactuals
   correctly distinguish genuine causes from mere correlates. The
   barometer does not cause the storm, even though they are correlated
   via atmospheric pressure.

## Bridge to Linglib Infrastructure

Lewis's causal dependence corresponds to the simple but-for test in our
SEM framework. For exogenous causes (no incoming causal laws), Lewis's
`lewisButFor` is equivalent to the but-for component of `completesForEffect`
(CCSelection.lean).

The key difference from @cite{nadathur-2024} Def 10b (`causallyNecessary`):
Lewis's but-for operates on the actual world via minimal intervention,
while Def 10b quantifies over consistent supersituations. For simple models
they agree; for complex models with alternative pathways, Def 10b is
strictly stronger.

## Limitations

@cite{lewis-1973-causation} acknowledges two limitations:

- **Overdetermination** (fn. 12): symmetric overdetermination cases are
  excluded — neither overdetermining cause passes the but-for test.
- **Late preemption**: the transitive closure mechanism handles early
  preemption but struggles with late preemption, where a backup cause
  operates at the same level as the actual cause. This motivated Lewis's
  later revision to "causation as influence."
-/

namespace Lewis1973

open Core (WorldTimeIndex)

open Core.Causal
open Semantics.Causation.CCSelection
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity

-- ════════════════════════════════════════════════════
-- § 1. Lewis's Counterfactual Via Intervention
-- ════════════════════════════════════════════════════

/-- Lewis's but-for counterfactual via Pearl's intervention.

    "If c had not occurred, e would not have occurred."

    Given background `bg` (exogenous variable settings + cause):
    1. Intervene: set cause=false, cut cause's incoming laws
    2. Develop normally from the modified situation
    3. Check that effect does NOT hold

    This implements the key counterfactual from @cite{lewis-1973-causation}
    p. 563: "if c had not been, e never had existed." In Pearl's framework,
    the intervention do(c=false) determines the closest ¬c-world for
    deterministic causal models. -/
def lewisButFor (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Bool :=
  let (dyn', bg') := intervene dyn bg cause false
  !(normalDevelopment dyn' bg').hasValue effect true

-- ════════════════════════════════════════════════════
-- § 2. Causal Dependence (Lewis p. 563)
-- ════════════════════════════════════════════════════

/-- Lewis's causal dependence among events (@cite{lewis-1973-causation} p. 563).

    "e depends causally on c iff the family O(e), ∼O(e) depends
    counterfactually on the family O(c), ∼O(c)."

    When both c and e actually occur, this reduces to the but-for test:
    O(c) □→ O(e) is automatic (both actually obtain), so the
    substantive condition is ∼O(c) □→ ∼O(e).

    The `bg` parameter should include the cause (and any other exogenous
    values). The "actual world" is `normalDevelopment dyn bg`. -/
def lewisDependence (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Bool :=
  let actual := normalDevelopment dyn bg
  -- Both c and e actually occur
  actual.hasValue cause true &&
  actual.hasValue effect true &&
  -- But-for: e would not have occurred without c
  lewisButFor dyn bg cause effect

-- ════════════════════════════════════════════════════
-- § 3. Causation as Transitive Closure (Lewis p. 563)
-- ════════════════════════════════════════════════════

/-- Search for a Lewis causal chain from `current` to `target`.

    Uses bounded DFS over the variable set to find a path where
    each consecutive pair is a Lewis causal dependence. -/
private def hasChainAux (dyn : CausalDynamics) (bg : Situation)
    (current target : Variable) (visited : List Variable)
    (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if current == target then true
    else
      let candidates := (allVariables dyn).filter fun v =>
        !(visited.contains v) && lewisDependence dyn bg current v
      candidates.any fun v =>
        hasChainAux dyn bg v target (current :: visited) fuel

/-- Lewis's causation: the transitive closure of causal dependence.

    @cite{lewis-1973-causation} p. 563: "Causal dependence among actual
    events implies causation. ... But I reject the converse: causal
    dependence may not be; so there can be causation without causal
    dependence. ... one event is a cause of another iff there exists
    a causal chain leading from the first to the second."

    c causes e iff there exists a finite sequence c, d₁, d₂, ..., e
    where each consecutive pair is a Lewis causal dependence. -/
def lewisCausation (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Bool :=
  hasChainAux dyn bg cause effect [] ((allVariables dyn).length + 1)

/-- `hasChainAux` returns true when current equals target with nonzero fuel. -/
private lemma hasChainAux_self (dyn : CausalDynamics) (bg : Situation)
    (v : Variable) (visited : List Variable) :
    ∀ (fuel : Nat), 0 < fuel → hasChainAux dyn bg v v visited fuel = true := by
  intro fuel hfuel
  cases fuel with
  | zero => omega
  | succ n => unfold hasChainAux; simp

/-- Causal dependence implies causation (one-step chain).

    @cite{lewis-1973-causation}: "Causal dependence among actual
    events implies causation." -/
theorem dependence_implies_causation (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable)
    (h : lewisDependence dyn bg cause effect = true)
    (hVar : (allVariables dyn).contains effect = true) :
    lewisCausation dyn bg cause effect = true := by
  simp only [lewisCausation]
  have h_mem : effect ∈ allVariables dyn := List.mem_of_elem_eq_true hVar
  by_cases h_eq : cause = effect
  · subst h_eq
    exact hasChainAux_self dyn bg cause [] _ (Nat.succ_pos _)
  · -- One-step chain: cause → effect is a direct dependence
    unfold hasChainAux
    simp only [beq_false_of_ne h_eq, Bool.false_eq_true, ite_false]
    rw [List.any_eq_true]
    refine ⟨effect, List.mem_filter.mpr ⟨h_mem, ?_⟩, ?_⟩
    · -- effect passes the filter: not visited ∧ dependence holds
      simp [h]
    · -- hasChainAux effect effect (cause :: []) n = true
      exact hasChainAux_self dyn bg effect (cause :: []) _
        (List.length_pos_of_mem h_mem)

-- ════════════════════════════════════════════════════
-- § 4. Simple Cause: A → B
-- ════════════════════════════════════════════════════

private abbrev va := mkVar "a"
private abbrev vb := mkVar "b"
private abbrev vc := mkVar "c"
private abbrev ve := mkVar "e"

private def simpleDyn : CausalDynamics := ⟨[CausalLaw.simple va vb]⟩
private def simpleBg : Situation := Situation.empty.extend va true

/-- Lewis's but-for holds for a simple cause.
    Without a, b does not develop. -/
theorem simple_butfor :
    lewisButFor simpleDyn simpleBg va vb = true := by native_decide

/-- Lewis's causal dependence holds for a simple cause.
    a and b both actually occur, and the but-for holds. -/
theorem simple_dependence :
    lewisDependence simpleDyn simpleBg va vb = true := by native_decide

/-- Lewis's causation holds (trivially, one-step chain). -/
theorem simple_causation :
    lewisCausation simpleDyn simpleBg va vb = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Causal Chain: A → B → C
-- ════════════════════════════════════════════════════

private def chainDyn : CausalDynamics := CausalDynamics.causalChain va vb vc
private def chainBg : Situation := Situation.empty.extend va true

/-- In the chain A→B→C, removing A prevents C.
    Lewis's but-for holds directly (no need for TC). -/
theorem chain_direct_butfor :
    lewisButFor chainDyn chainBg va vc = true := by native_decide

/-- Each step of the chain is a Lewis causal dependence.
    B depends on A, and C depends on B. -/
theorem chain_step_AB :
    lewisDependence chainDyn chainBg va vb = true := by native_decide

theorem chain_step_BC :
    lewisDependence chainDyn chainBg vb vc = true := by native_decide

/-- Lewis's causation via the full chain A→B→C. -/
theorem chain_causation :
    lewisCausation chainDyn chainBg va vc = true := by native_decide

/-- Direct dependence also holds for simple chains (without backup
    causes, the but-for test succeeds transitively). -/
theorem chain_direct_dependence :
    lewisDependence chainDyn chainBg va vc = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 6. Epiphenomena: Barometer and Storm
-- ════════════════════════════════════════════════════

/-! @cite{lewis-1973-causation} p. 565: the barometer reading (B) and
the storm (S) are both effects of atmospheric pressure (P). The
counterfactual analysis correctly identifies P as the common cause and
rejects the spurious "barometer causes storm" inference.

The key mechanism is intervention asymmetry: intervening on the barometer
(do(B=false)) cuts B's incoming law (P→B) but leaves P→S intact. Pressure
still causes the storm regardless of the barometer reading. -/

private def pressure := mkVar "pressure"
private def barometer := mkVar "barometer"
private def storm := mkVar "storm"

private def epiphDyn : CausalDynamics :=
  ⟨[CausalLaw.simple pressure barometer,
    CausalLaw.simple pressure storm]⟩

private def epiphBg : Situation := Situation.empty.extend pressure true

/-- Pressure causes the barometer reading. -/
theorem pressure_causes_barometer :
    lewisDependence epiphDyn epiphBg pressure barometer = true := by
  native_decide

/-- Pressure causes the storm. -/
theorem pressure_causes_storm :
    lewisDependence epiphDyn epiphBg pressure storm = true := by
  native_decide

/-- The barometer does NOT cause the storm.

    @cite{lewis-1973-causation} p. 565: intervention on the barometer
    (do(B=false)) cuts B's incoming law (P→B) but leaves P→S intact.
    P still causes S regardless of B. -/
theorem barometer_not_causes_storm :
    lewisDependence epiphDyn epiphBg barometer storm = false := by
  native_decide

/-- The storm does NOT cause the barometer. -/
theorem storm_not_causes_barometer :
    lewisDependence epiphDyn epiphBg storm barometer = false := by
  native_decide

/-- Full causal asymmetry: pressure is the genuine cause; neither
    effect causes the other; and no effect causes the common cause.

    @cite{lewis-1973-causation} p. 564: "Counterfactual dependence
    is NOT reversible." The barometer reading depends on the pressure,
    but the pressure does not depend on the reading. -/
theorem full_causal_asymmetry :
    -- P → B and P → S (genuine causation)
    lewisDependence epiphDyn epiphBg pressure barometer = true ∧
    lewisDependence epiphDyn epiphBg pressure storm = true ∧
    -- B ↛ S and S ↛ B (no spurious causation)
    lewisDependence epiphDyn epiphBg barometer storm = false ∧
    lewisDependence epiphDyn epiphBg storm barometer = false ∧
    -- B ↛ P and S ↛ P (no reverse causation)
    lewisDependence epiphDyn epiphBg barometer pressure = false ∧
    lewisDependence epiphDyn epiphBg storm pressure = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════
-- § 7. Overdetermination
-- ════════════════════════════════════════════════════

/-! @cite{lewis-1973-causation} fn. 12: "I shall not discuss symmetrical
cases of overdetermination, in which two overdetermining factors have
equal claim to count as causes."

Model: A ∨ B → E (disjunctive overdetermination). With both present,
neither is necessary — the but-for test fails for both. -/

private def overdetDyn : CausalDynamics :=
  CausalDynamics.disjunctiveCausation va vb ve

private def overdetBg : Situation :=
  Situation.empty.extend va true |>.extend vb true

/-- Neither overdetermining cause passes the but-for test.
    Without A, B still causes E. Without B, A still causes E. -/
theorem overdetermination_no_butfor :
    lewisButFor overdetDyn overdetBg va ve = false ∧
    lewisButFor overdetDyn overdetBg vb ve = false := by
  constructor <;> native_decide

/-- Neither overdetermining cause is a Lewis causal dependent. -/
theorem overdetermination_no_dependence :
    lewisDependence overdetDyn overdetBg va ve = false ∧
    lewisDependence overdetDyn overdetBg vb ve = false := by
  constructor <;> native_decide

/-- With only one cause present, dependence holds.
    Overdetermination is the problem, not sufficiency. -/
theorem single_cause_dependence :
    lewisDependence overdetDyn (Situation.empty.extend va true) va ve = true ∧
    lewisDependence overdetDyn (Situation.empty.extend vb true) vb ve = true := by
  constructor <;> native_decide

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Bar-Asher Siegal 2026 Door Model
-- ════════════════════════════════════════════════════

/-! The door model from @cite{bar-asher-siegal-2026} provides a concrete
test case for Lewis's analysis. The manual and automatic pathways
create overdetermination-like structure when both are available. -/

open BarAsherSiegal2026

/-- Lewis's but-for for the door model: handle is necessary in the
    single-pathway model. -/
theorem door_manual_butfor :
    lewisButFor manualOnlyDynamics
      (unlocked.extend handle true) handle doorOpens = true := by
  native_decide

/-- Lewis's causal dependence for the manual-only door. -/
theorem door_manual_dependence :
    lewisDependence manualOnlyDynamics
      (unlocked.extend handle true) handle doorOpens = true := by
  native_decide

/-- In the full model (both pathways active), the handle does NOT pass
    Lewis's but-for — the automatic pathway provides a backup.

    This matches @cite{bar-asher-siegal-2026}'s prediction: the verb
    *cause* (which requires necessity / member CC-selection) is
    infelicitous when alternative pathways exist. -/
theorem door_full_no_butfor :
    lewisButFor doorDynamics
      (unlocked.extend handle true |>.extend button true
        |>.extend electricity true)
      handle doorOpens = false := by
  native_decide

/-- Lewis's analysis agrees with CC-selection on the single-pathway
    model: the handle is both a Lewis causal dependent and satisfies
    both CC-selection modes. -/
theorem door_lewis_agrees_ccselection :
    lewisDependence manualOnlyDynamics
      (unlocked.extend handle true) handle doorOpens = true ∧
    ccConstraintSatisfied .completionOfSufficientSet
      manualOnlyDynamics unlocked handle doorOpens = true ∧
    ccConstraintSatisfied .memberOfSufficientSet
      manualOnlyDynamics unlocked handle doorOpens = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════
-- § 9. Bridge Theorems
-- ════════════════════════════════════════════════════

/-! Lewis's framework and linglib's infrastructure formalize the same
intuition via different mechanisms:

| Lewis 1973 | Linglib | Mechanism |
|---|---|---|
| `lewisButFor` | but-for in `completesForEffect` | intervention vs extend |
| `lewisDependence` | `completesForEffect` | + occurrence check |
| `lewisCausation` | `ccConstraintSatisfied` | TC vs CC-selection |

For exogenous causes (no incoming laws), `lewisButFor` and the but-for
component of `completesForEffect` agree: both check whether removing the
cause prevents the effect. The difference: `lewisButFor` uses Pearl's
`intervene` (cuts incoming laws + sets value), while `completesForEffect`
uses `bg.extend cause false` (sets value only). When cause has no
incoming laws, the law-cutting is vacuous. -/

/-- For simple dynamics (A→B), Lewis's causal dependence agrees
    with `completesForEffect` from CC-selection theory. -/
theorem lewis_agrees_completes_simple :
    lewisDependence simpleDyn simpleBg va vb = true ∧
    completesForEffect simpleDyn Situation.empty va vb = true := by
  constructor <;> native_decide

/-- For chain dynamics (A→B→C), Lewis's causal dependence agrees
    with `completesForEffect`. -/
theorem lewis_agrees_completes_chain :
    lewisDependence chainDyn chainBg va vc = true ∧
    completesForEffect chainDyn Situation.empty va vc = true := by
  constructor <;> native_decide

/-- For overdetermination, both Lewis and `completesForEffect` agree:
    neither overdetermining cause is individually necessary. -/
theorem lewis_agrees_completes_overdet :
    lewisDependence overdetDyn overdetBg va ve = false ∧
    completesForEffect overdetDyn (Situation.empty.extend vb true) va ve = false := by
  constructor <;> native_decide

/-- Lewis's but-for agrees with `causallyNecessary` (Def 10b) for
    simple dynamics — both identify the single cause as necessary. -/
theorem lewis_agrees_necessity_simple :
    lewisButFor simpleDyn simpleBg va vb = true ∧
    causallyNecessary simpleDyn Situation.empty va vb = true := by
  constructor <;> native_decide

/-- For overdetermination, both Lewis and Def 10b agree: neither
    overdetermining cause is necessary. -/
theorem lewis_agrees_necessity_overdet :
    lewisButFor overdetDyn overdetBg va ve = false ∧
    causallyNecessary overdetDyn Situation.empty va ve = false := by
  constructor <;> native_decide

-- ════════════════════════════════════════════════════
-- § 10. Preemption: Where TC Matters
-- ════════════════════════════════════════════════════

/-! @cite{lewis-1973-causation} p. 567: preemption is the main test case
for the transitive closure. c₁ actually causes e (via intermediate d),
while c₂ is a preempted backup that would have caused e if c₁ had been
absent.

In our SEM: c1→d, d→e, c2→e. With both c1 and c2 present, c1 fires
through d. Removing c1 still allows c2→e, so the DIRECT but-for fails
for c1. But the chain c1→d→e holds: d depends on c1, and e depends on d.

The complication: e's dependence on d requires that removing d prevents e.
But if c2→e is unconditional, removing d still allows c2 to cause e. In
this model, the chain breaks — this is Lewis's "late preemption" problem.

For the chain to work, the backup must be neutralized at the intermediate
step. We model early preemption where c2's route goes through d': c2→d',
d'→e, but d blocks d' via a negative precondition. Since our SEM doesn't
support negative effects, we model blocking via a conditional law:
c2 fires through e only if d is absent. -/

private def c1 := mkVar "c1"
private def c2 := mkVar "c2"
private def d := mkVar "d"

/-- Preemption model: c1 acts through intermediate d.
    c2 is a backup that causes e directly.
    Laws: c1→d, d→e, c2→e. -/
private def preemptDyn : CausalDynamics :=
  ⟨[CausalLaw.simple c1 d,
    CausalLaw.simple d ve,
    CausalLaw.simple c2 ve]⟩

private def preemptBg : Situation :=
  Situation.empty.extend c1 true |>.extend c2 true

/-- The direct but-for fails for c1: removing c1 still allows c2→e.
    This is the challenge of preemption. -/
theorem preemption_direct_butfor_fails :
    lewisButFor preemptDyn preemptBg c1 ve = false := by native_decide

/-- The intermediate step holds: d depends on c1. -/
theorem preemption_d_depends_c1 :
    lewisDependence preemptDyn preemptBg c1 d = true := by native_decide

/-- But e does NOT depend on d: removing d (via intervention) still
    allows c2→e. This is Lewis's late preemption problem — the backup
    cause operates at the same level as the actual effect. -/
theorem preemption_e_not_depends_d :
    lewisDependence preemptDyn preemptBg d ve = false := by native_decide

/-- Consequence: Lewis's TC-based causation also fails for c1→e in
    late preemption. The chain c1→d→e breaks at d→e because c2
    provides an unblocked backup for e.

    @cite{lewis-1973-causation} p. 567 handles only EARLY preemption
    where the backup is blocked before reaching the effect. Late
    preemption motivated Lewis's 2000 revision. -/
theorem preemption_tc_fails :
    lewisCausation preemptDyn preemptBg c1 ve = false := by native_decide

/-- The backup cause c2 also fails the direct but-for (c1→d→e is the
    actual pathway and d→e fires even without c2). -/
theorem preemption_c2_butfor_fails :
    lewisButFor preemptDyn preemptBg c2 ve = false := by native_decide

/-- With only c1 (no backup c2), dependence holds directly. -/
theorem preemption_no_backup :
    lewisDependence preemptDyn (Situation.empty.extend c1 true)
      c1 ve = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 11. Lewis's Causal Profiles
-- ════════════════════════════════════════════════════

/-- For simple dynamics, Lewis's analysis and the SEM profile agree
    completely: a is sufficient, necessary, and direct. -/
theorem lewis_profile_simple :
    lewisDependence simpleDyn simpleBg va vb = true ∧
    extractProfile simpleDyn Situation.empty va vb =
      { sufficient := true, necessary := true, direct := true } := by
  constructor <;> native_decide

/-- **Lewis vs Def 10b on chains**: this is where they DIVERGE.

    Lewis's but-for says A IS necessary for C (removing A prevents C).
    Def 10b says A is NOT necessary for C (a consistent supersituation
    could set B directly, bypassing A).

    This captures the key architectural difference:
    - Lewis: "would C have happened without A?" → No (simple intervention)
    - Def 10b: "could C happen without A?" → Yes (set B exogenously)

    Both are defensible; they formalize different notions of necessity.
    Lewis's is closer to everyday causal judgment ("A caused C").
    Def 10b is closer to the linguistic test for *cause* ("A was a
    prerequisite for C" — but was it the ONLY possible prerequisite?). -/
theorem lewis_vs_def10b_chain :
    -- Lewis: A is necessary for C (simple but-for)
    lewisButFor chainDyn chainBg va vc = true ∧
    -- Def 10b: A is NOT necessary for C (supersituation bypass)
    causallyNecessary chainDyn Situation.empty va vc = false ∧
    -- But both agree A is sufficient
    causallySufficient chainDyn Situation.empty va vc = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end Lewis1973
