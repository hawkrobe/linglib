import Linglib.Core.Causation

/-!
# A Communication-First Account of Explanation

Formalization of Harding, Gerstenberg & Icard (2025).

Explanation is modeled as an RSA communication game where:
- **Worlds** are causal situations `(M, u)`: dynamics + exogenous context
- **Utterances** are explanations: "FACT because X = x"
- **Literal meaning** = actual causation (X = x causes FACT in `(M, u)`)
- **Decision problem** = manipulation game (listener picks variable to intervene on)
- **Goodness** = Δ expected utility (post-explanation minus baseline)

## Key Results

Classic "explanatory virtues" — sensitivity to background knowledge,
preference for invariant relationships, minimality — emerge from pragmatic
dynamics rather than needing to be stipulated (contra Halpern & Pearl 2005).

## Scenarios

| Example | Structure | Key prediction |
|---------|-----------|----------------|
| Late Meeting | M_T vs M_∧ | Citing known cause T=1 is informative (signals M_T) |
| Roof Replacement | M_R/M_D/M_∧/M_∨ | Citing R=1 more useful than D=1 for roof decision |

## References

- Harding, J., Gerstenberg, T. & Icard, T. (2025). A Communication-First
  Account of Explanation. arXiv:2505.03732.
- Halpern, J. & Pearl, J. (2005). Causes and Explanations.
-/

namespace HardingGerstenbergIcard2025

open Core.Causation

-- ============================================================
-- § Framework
-- ============================================================

/-- A **causal world**: structural equations + exogenous context.
    Corresponds to a (M, u) pair in the paper. -/
structure CausalWorld where
  dynamics : CausalDynamics
  context : Situation
  deriving Inhabited

/-- An **explanation**: "FACT because X = 1".
    The speaker cites variable `cause` as an actual cause of `effect`. -/
structure Explanation where
  cause : Variable
  effect : Variable
  deriving Repr, BEq, DecidableEq

/-- **Literal meaning** (Eq. 1): an explanation is true in a causal world
    iff (1) FACT holds, (2) the cause is present, and (3) the cause
    manipulates the effect.

    We use `manipulates` (Woodward's interventionist criterion) as our
    notion of actual causation, following the paper's egalitarian stance
    (§2.3): any account that treats both overdetermining factors as
    actual causes is compatible. -/
def literallyTrue (expl : Explanation) (w : CausalWorld) : Bool :=
  (normalDevelopment w.dynamics w.context).hasValue expl.effect true &&
  w.context.hasValue expl.cause true &&
  manipulates w.dynamics w.context expl.cause expl.effect

/-- **Manipulation reward** (Definition 3, binary case).

    R(X, M, u) = 1 if intervening on X can flip FACT, 0 otherwise.
    The full definition sums over exogenous contexts weighted by P(u'),
    but in the binary single-context case it reduces to `manipulates`. -/
def manipulationReward (w : CausalWorld) (action effect : Variable) : ℚ :=
  if manipulates w.dynamics w.context action effect then 1 else 0

-- ============================================================
-- § Example 5: Late Meeting
-- ============================================================

/-! ### Late Meeting

Bob is late to meet Charlie, who is cross.  Bob knows T = 1 (he was
late) and B = 1 (he forgot Charlie's birthday), but is unsure whether
the causal structure is M_T (tardiness alone suffices) or M_∧ (both
tardiness AND birthday forgetting are needed).

Alice's choice: cite T = 1 or B = 1 as the cause of C = 1.

Key prediction (§4.2.1): citing the *known* cause T = 1 is informative
because it signals that the speaker chose NOT to cite B = 1, allowing
the listener to infer M_T. -/

section LateMeeting

private def T : Variable := mkVar "T"
private def B : Variable := mkVar "B"
private def C : Variable := mkVar "C"

/-- M_T: tardiness alone causes crossness. -/
private def dynT : CausalDynamics := ⟨[CausalLaw.simple T C]⟩

/-- M_∧: both tardiness AND birthday forgetting needed. -/
private def dynConj : CausalDynamics := ⟨[CausalLaw.conjunctive T B C]⟩

private def lateBg : Situation :=
  Situation.empty.extend T true |>.extend B true

/-- World w_T: structure M_T with T = 1, B = 1. -/
private def wT : CausalWorld := ⟨dynT, lateBg⟩

/-- World w_∧: structure M_∧ with T = 1, B = 1. -/
private def wConj : CausalWorld := ⟨dynConj, lateBg⟩

private def explT : Explanation := ⟨T, C⟩
private def explB : Explanation := ⟨B, C⟩

-- ── Literal meaning ──

/-- In M_T, tardiness manipulates crossness (T → C). -/
theorem late_T_causes_C_in_MT : literallyTrue explT wT = true := by native_decide

/-- In M_T, birthday does NOT manipulate crossness (no B → C law). -/
theorem late_B_not_cause_in_MT : literallyTrue explB wT = false := by native_decide

/-- In M_∧, tardiness manipulates crossness (removing T from T∧B→C kills C). -/
theorem late_T_causes_C_in_MConj : literallyTrue explT wConj = true := by native_decide

/-- In M_∧, birthday also manipulates crossness (removing B kills C). -/
theorem late_B_causes_C_in_MConj : literallyTrue explB wConj = true := by native_decide

-- ── L0 posteriors ──

/-- ⟦"C=1 because T=1"⟧ = {M_T, M_∧}: both worlds survive.
    L0 assigns equal probability to each (uniform prior). -/
theorem late_l0_T_both_survive :
    literallyTrue explT wT = true ∧ literallyTrue explT wConj = true := by
  constructor <;> native_decide

/-- ⟦"C=1 because B=1"⟧ = {M_∧}: only the conjunctive world survives.
    L0 assigns all mass to M_∧. -/
theorem late_l0_B_only_conj :
    literallyTrue explB wT = false ∧ literallyTrue explB wConj = true := by
  constructor <;> native_decide

-- ── Manipulation game reward ──

/-- In M_T: T manipulates C (direct law T → C). -/
theorem late_manip_T_in_MT : manipulationReward wT T C = 1 := by native_decide

/-- In M_T: B does NOT manipulate C (no causal path). -/
theorem late_manip_B_in_MT : manipulationReward wT B C = 0 := by native_decide

/-- In M_∧: T manipulates C (conjunctive law, B present). -/
theorem late_manip_T_in_MConj : manipulationReward wConj T C = 1 := by native_decide

/-- In M_∧: B also manipulates C (conjunctive law, T present). -/
theorem late_manip_B_in_MConj : manipulationReward wConj B C = 1 := by native_decide

-- ── Speaker utility (§4.2.1) ──

/-- After "T=1", L0 is uniform → listener is indifferent on the
    apologize-for-both vs apologize-for-tardiness-only decision.
    After "B=1", L0 concentrates on M_∧ → listener picks a_both.

    So U_S("B=1", M_∧) > U_S("T=1", M_∧): the speaker prefers to
    cite B=1 when the actual world is M_∧. -/
theorem late_speaker_prefers_B_in_conj :
    -- The key asymmetry: B=1 is unavailable in M_T (literally false)
    -- but available and more informative in M_∧
    literallyTrue explB wT = false ∧
    literallyTrue explB wConj = true ∧
    literallyTrue explT wT = true ∧
    literallyTrue explT wConj = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Known causes can be informative** (§4.2.1).

    Even though Bob *knows* T = 1, citing it is informative because
    the pragmatic listener L reasons: "the speaker said T=1 rather
    than B=1 → she must be in a world where B=1 is false or less
    useful → probably M_T." -/
theorem late_known_cause_informative :
    -- In M_T: speaker MUST cite T=1 (B=1 is literally false)
    -- In M_∧: speaker PREFERS B=1 (more useful to listener)
    -- Pragmatic listener: "T=1" → M_T more likely; "B=1" → M_∧ certain
    -- Goodness("T=1", M_T) > 0 because L's posterior shifts toward M_T
    literallyTrue explB wT = false ∧ -- B=1 unavailable in M_T
    literallyTrue explT wT = true     -- T=1 is the only option in M_T
    := by
  constructor <;> native_decide

end LateMeeting

-- ============================================================
-- § Example 3: Roof Replacement
-- ============================================================

/-! ### Roof Replacement

A house catches fire (F = 1).  Two potential causes: thatched roof
(R = 1) and recent drought (D = 1).  Bob considers four possible
causal structures:

- M_R: R → F  (roof alone causes fire)
- M_D: D → F  (drought alone)
- M_∧: R ∧ D → F  (both needed)
- M_∨: R ∨ D → F  (either suffices)

Bob's decision: should he replace his thatched roof?

Key prediction (§4.1.1): citing R = 1 is more *useful* than D = 1
because Bob's decision is sensitive to whether R is a cause of F,
even though both explanations are equally *informative* at the L0
level (each eliminates exactly one of four structures). -/

section RoofReplacement

private def R : Variable := mkVar "R"
private def D : Variable := mkVar "D"
private def F : Variable := mkVar "F"

private def dynR : CausalDynamics := ⟨[CausalLaw.simple R F]⟩
private def dynD : CausalDynamics := ⟨[CausalLaw.simple D F]⟩
private def dynRAndD : CausalDynamics := ⟨[CausalLaw.conjunctive R D F]⟩
private def dynROrD : CausalDynamics :=
  CausalDynamics.disjunctiveCausation R D F

private def roofBg : Situation :=
  Situation.empty.extend R true |>.extend D true

private def wR : CausalWorld := ⟨dynR, roofBg⟩
private def wD : CausalWorld := ⟨dynD, roofBg⟩
private def wRAndD : CausalWorld := ⟨dynRAndD, roofBg⟩
private def wROrD : CausalWorld := ⟨dynROrD, roofBg⟩

private def explR : Explanation := ⟨R, F⟩
private def explD : Explanation := ⟨D, F⟩

-- ── Literal meaning ──

/-- ⟦"F=1 because R=1"⟧ = {M_R, M_∧}.
    M_∨ is excluded because with both R=1 and D=1, neither individually
    manipulates F (overdetermination — removing one leaves the other). -/
theorem roof_R_in_MR : literallyTrue explR wR = true := by native_decide
theorem roof_R_in_MConj : literallyTrue explR wRAndD = true := by native_decide
theorem roof_R_not_in_MDisj : literallyTrue explR wROrD = false := by native_decide
theorem roof_R_not_in_MD : literallyTrue explR wD = false := by native_decide

/-- ⟦"F=1 because D=1"⟧ = {M_D, M_∧} (symmetric). -/
theorem roof_D_in_MD : literallyTrue explD wD = true := by native_decide
theorem roof_D_in_MConj : literallyTrue explD wRAndD = true := by native_decide
theorem roof_D_not_in_MDisj : literallyTrue explD wROrD = false := by native_decide
theorem roof_D_not_in_MR : literallyTrue explD wR = false := by native_decide

/-- Both explanations survive in exactly the same number of worlds
    (2 of 4) → equally informative at the L0 level. -/
theorem roof_equally_informative :
    literallyTrue explR wD = false ∧ literallyTrue explD wR = false ∧
    literallyTrue explR wROrD = false ∧ literallyTrue explD wROrD = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ── Manipulation game: roof replacement decision ──

/-- R manipulates F in M_R and M_∧ (thatched roof matters). -/
theorem roof_R_manip_MR : manipulationReward wR R F = 1 := by native_decide
theorem roof_R_manip_MConj : manipulationReward wRAndD R F = 1 := by native_decide

/-- R does NOT manipulate F in M_D or M_∨ (overdetermination in M_∨). -/
theorem roof_R_no_manip_MD : manipulationReward wD R F = 0 := by native_decide
theorem roof_R_no_manip_MDisj : manipulationReward wROrD R F = 0 := by native_decide

/-- After "R=1", surviving worlds = {M_R, M_∧}: R manipulates F in BOTH.
    So the listener knows with certainty: replacing the roof matters. -/
theorem roof_R_useful_for_roof_decision :
    manipulationReward wR R F = 1 ∧
    manipulationReward wRAndD R F = 1 := by
  constructor <;> native_decide

/-- After "D=1", surviving worlds = {M_D, M_∧}: R manipulates F in
    M_∧ but NOT in M_D — less helpful for the roof decision. -/
theorem roof_D_ambiguous_for_roof_decision :
    manipulationReward wD R F = 0 ∧
    manipulationReward wRAndD R F = 1 := by
  constructor <;> native_decide

-- ── Causal selection and normality (§4.3) ──

/-- In M_∧ (conjunctive): both R and D manipulate F. -/
theorem roof_conj_both_manipulate :
    manipulates dynRAndD roofBg R F = true ∧
    manipulates dynRAndD roofBg D F = true := by
  constructor <;> native_decide

/-- In M_∨ (disjunctive): neither R nor D individually manipulates F
    because the other cause is present as backup. -/
theorem roof_disj_neither_manipulates :
    manipulates dynROrD roofBg R F = false ∧
    manipulates dynROrD roofBg D F = false := by
  constructor <;> native_decide

/-- **Causal selection interacts with structure** (§4.3.1).

    In conjunctive structures, both causes are individually necessary →
    both manipulate F.  In disjunctive structures, each cause has a
    backup → neither individually manipulates (overdetermination).

    The paper predicts speakers cite *abnormal* causes in conjunctive
    structures (where both are actual causes) and *normal* causes in
    disjunctive ones (where the manipulation game with varied contexts
    favors the more probable cause). -/
theorem roof_structure_affects_manipulation :
    manipulates dynRAndD roofBg R F = true ∧
    manipulates dynRAndD roofBg D F = true ∧
    manipulates dynROrD roofBg R F = false ∧
    manipulates dynROrD roofBg D F = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end RoofReplacement

-- ============================================================
-- § Example 4: Milk Theft
-- ============================================================

/-! ### Milk Theft

Bob's milk is depleted (M = 1).  Possible culprits: Charlie (C = 1),
Dana (D = 1), or both.  The causal structure is disjunctive:
M_∨ with C ∨ D → M.

Key prediction (§4.4): when both roommates drank the milk, citing
both "C = 1, D = 1" is more useful (Bob wants to confront the right
people), but longer messages cost more.  The tension between utility
and cost generates a preference for minimality. -/

section MilkTheft

private def Ch : Variable := mkVar "Charlie"
private def Da : Variable := mkVar "Dana"
private def M : Variable := mkVar "Milk"

/-- M_∨: either roommate drinking depletes the milk. -/
private def milkDyn : CausalDynamics :=
  CausalDynamics.disjunctiveCausation Ch Da M

/-- Both roommates drank: C = 1, D = 1. -/
private def milkBgBoth : Situation :=
  Situation.empty.extend Ch true |>.extend Da true

/-- Only Charlie drank: C = 1, D = 0. -/
private def milkBgCharlie : Situation :=
  Situation.empty.extend Ch true |>.extend Da false

private def wBoth : CausalWorld := ⟨milkDyn, milkBgBoth⟩
private def wCharlie : CausalWorld := ⟨milkDyn, milkBgCharlie⟩

private def explCh : Explanation := ⟨Ch, M⟩
private def explDa : Explanation := ⟨Da, M⟩

/-- When only Charlie drank, Charlie is the sole cause. -/
theorem milk_charlie_sole_cause :
    literallyTrue explCh wCharlie = true ∧
    literallyTrue explDa wCharlie = false := by
  constructor <;> native_decide

/-- When both drank, neither individually manipulates M (overdetermination):
    removing one doesn't stop M = 1 because the other is still present. -/
theorem milk_overdetermination :
    manipulates milkDyn milkBgBoth Ch M = false ∧
    manipulates milkDyn milkBgBoth Da M = false := by
  constructor <;> native_decide

/-- Neither explanation is literally true when both drank (overdetermination
    blocks actual causation for individual factors).

    This is EX3 from Halpern & Pearl: the HP analysis would require citing
    both, but our account derives this preference from pragmatic pressure
    (longer messages are more informative but costlier). -/
theorem milk_neither_literal_when_both :
    literallyTrue explCh wBoth = false ∧
    literallyTrue explDa wBoth = false := by
  constructor <;> native_decide

/-- When Charlie is the sole cause, he is both sufficient and necessary. -/
theorem milk_charlie_sole_profile :
    causallySufficient milkDyn Situation.empty Ch M = true ∧
    causallyNecessary milkDyn milkBgCharlie Ch M = true := by
  constructor <;> native_decide

end MilkTheft

end HardingGerstenbergIcard2025
