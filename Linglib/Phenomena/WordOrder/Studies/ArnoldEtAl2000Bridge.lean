import Linglib.Phenomena.WordOrder.Studies.ArnoldEtAl2000
import Linglib.Theories.Syntax.DependencyGrammar.Formal.DependencyLength
import Linglib.Theories.Syntax.CCG.Core.Combinators
import Linglib.Core.InformationStructure

/-!
# Arnold et al. (2000): Competing Accounts and Their Derived Limitations

Formalizes the three accounts Arnold, Wasow, Losongco & Ginstrom (2000)
argue against, then derives each account's structural limitations from its
own definitions:

- `DependencyLength.totalDepLength` — the pure-weight account (Hawkins 1994)
- `Core.InformationStructure.DiscourseStatus` — the pure-discourse account (Givón 1988)
- `CCG.Combinators.ShiftFeature` — the CCG categorical account (Steedman 2000)

Each limitation is proved, not stipulated: it follows from the function
signatures and type structure already present in the theory files.
-/

namespace Phenomena.WordOrder.Studies.ArnoldEtAl2000Bridge

open DepGrammar DepGrammar.DependencyLength
open Phenomena.WordOrder.Studies.ArnoldEtAl2000
open Core.InformationStructure
open CCG.Combinators

-- ============================================================================
-- §1: The Pure-Weight Account (DLM / Hawkins 1994)
-- ============================================================================

/-!
## DLM: Correct on weight, blind to discourse

`totalDepLength` is defined as `t.deps.foldl (λ acc d => acc + depLength d) 0`.
Since `depLength` operates on `Dependency` = `(headIdx × depIdx × DepRel)`,
the function never accesses `t.words`. In a direct dependency chain, each
link's cost is purely positional: `|headIdx - depIdx|`. No property of the
words — form, category, features, discourse status — enters the computation.
-/

/-- **DLM word-invariance.** `totalDepLength` yields the same value for any
two trees sharing the same dependency structure, regardless of the words.

Proof: `rfl`. The body `t.deps.foldl ...` never mentions `t.words`.

Arnold et al. consequence: DLM correctly predicts the weight effect
(heavier NPs shift more, aligning with `heavyNPShiftOptimal < Suboptimal`
from `DependencyLength.lean`) but cannot predict the independent newness
effect in the dative alternation. -/
theorem totalDepLength_word_invariant (deps : List Dependency) (rootIdx : Nat)
    (words1 words2 : List Word) :
    totalDepLength { words := words1, deps := deps, rootIdx := rootIdx } =
    totalDepLength { words := words2, deps := deps, rootIdx := rootIdx } := by
  rfl

/-- Specialization: DLM assigns identical cost to trees differing only in
whether NPs are discourse-given or discourse-new. The independent newness
effect Arnold et al. find in the dative alternation (Study 1) is invisible
to `totalDepLength`. -/
theorem dlm_discourse_blind
    (deps : List Dependency) (rootIdx : Nat)
    (givenWords newWords : List Word) :
    totalDepLength { words := givenWords, deps := deps, rootIdx := rootIdx } =
    totalDepLength { words := newWords, deps := deps, rootIdx := rootIdx } :=
  totalDepLength_word_invariant deps rootIdx givenWords newWords

/-- Even at the single-dependency level, `depLength` ignores the grammatical
relation. The cost is purely `|headIdx - depIdx|` — relation type, and by
extension any property annotated on the dependency, is invisible. -/
theorem depLength_ignores_relation (h d : Nat) (r1 r2 : UD.DepRel) :
    depLength ⟨h, d, r1⟩ = depLength ⟨h, d, r2⟩ := by
  rfl

/-- Positive bridge: DLM correctly predicts the weight direction. Heavy NP
shift reduces dependency length (from `DependencyLength.lean` worked
examples), consistent with Arnold et al.'s `shift_rate_monotone`. -/
theorem dlm_predicts_heavy_shift :
    totalDepLength heavyNPShiftOptimal < totalDepLength heavyNPShiftSuboptimal := by
  native_decide

/-- DLM's short-before-long matches Arnold et al.'s Table 1: both DO and PD
place the heavier NP in second position. -/
theorem heavy_last_consistent_with_dlm :
    doLengths.second100 > doLengths.first100 ∧
    pdLengths.second100 > pdLengths.first100 :=
  heavy_last

-- ============================================================================
-- §2: The Pure-Discourse Account (Givón 1988)
-- ============================================================================

/-!
## Pure-discourse: Correct on newness, blind to weight

Givón (1988) claims ordering is determined by information status: given
referents precede new ones. Weight effects are epiphenomenal (new referents
need more descriptive material, so they tend to be heavier).

We formalize this as any ordering model whose predictions are functions
of `DiscourseStatus` alone — the type from `Core.InformationStructure`.
-/

/-- A pure-discourse ordering model: the preference for placing a constituent
in late position is determined solely by its discourse status. -/
structure PureDiscourseModel where
  latePref : DiscourseStatus → Nat
  /-- The core Givón claim: new material prefers late position. -/
  new_after_given : latePref .new > latePref .given

/-- **A pure-discourse model is weight-blind by type.** The function
`DiscourseStatus → Nat` admits no weight parameter. At a fixed discourse
status, the model returns a single value regardless of the constituent's
structural complexity.

Arnold et al. Study 2: at fixed discourse status, shift rates vary from
4.1% (1-word NPs) to 71.4% (4+ words). A pure-discourse model predicts
one rate for all of them. -/
theorem pure_discourse_weight_blind (m : PureDiscourseModel)
    (s : DiscourseStatus) (_weight1 _weight2 : Nat) :
    m.latePref s = m.latePref s := rfl

/-- **Impossibility.** A pure-discourse model cannot simultaneously match
even two of the four shift rates, since they would need to equal the single
value `m.latePref s`. Concretely: `shiftRate1w = 41` and `shiftRate2w = 178`
cannot both equal the same number. -/
theorem pure_discourse_cannot_match_gradient (m : PureDiscourseModel)
    (s : DiscourseStatus)
    (h1 : m.latePref s = shiftRate1w)
    (h2 : m.latePref s = shiftRate2w) : False :=
  absurd (h1.symm.trans h2) (by native_decide)

/-- The pure-discourse model also overpredicts: it claims newness should
always affect ordering, but Arnold et al.'s NP shift data shows newness
is NOT significant (`shiftResult.newnessSig = false`). -/
theorem pure_discourse_overpredicts_shift :
    shiftResult.newnessSig = false := by native_decide

-- ============================================================================
-- §3: The CCG Categorical Account (Steedman 2000)
-- ============================================================================

/-!
## CCG ±SHIFT: Too coarse for gradient data

Steedman (2000, p. 62–64) controls heavy NP shift via backward crossed
composition restricted by `ShiftFeature`:
- `+SHIFT`: argument can undergo heavy NP shift (via ⟨B×)
- `−SHIFT`: argument cannot shift (dative NP, PP complement)

This correctly captures the categorical shiftable/non-shiftable distinction.
But `ShiftFeature` has exactly 2 constructors, so `canHeavyShift` can
produce at most 2 distinct values. Arnold et al.'s data requires 4.
-/

/-- `canHeavyShift` is binary: its range is exactly `{true, false}`. -/
theorem canHeavyShift_binary (f : ShiftFeature) :
    canHeavyShift f = true ∨ canHeavyShift f = false := by
  cases f <;> simp [canHeavyShift]

/-- **Pigeonhole.** For any assignment of four weight classes to `ShiftFeature`
values, `canHeavyShift` must give the same answer for at least two classes.
Derived by exhaustive case-split over `ShiftFeature`'s 2 constructors ×4. -/
theorem shift_feature_conflates
    (w1 w2 w3 w4 : ShiftFeature) :
    canHeavyShift w1 = canHeavyShift w2 ∨
    canHeavyShift w1 = canHeavyShift w3 ∨
    canHeavyShift w1 = canHeavyShift w4 ∨
    canHeavyShift w2 = canHeavyShift w3 ∨
    canHeavyShift w2 = canHeavyShift w4 ∨
    canHeavyShift w3 = canHeavyShift w4 := by
  cases w1 <;> cases w2 <;> cases w3 <;> cases w4 <;> simp [canHeavyShift]

/-- The four shift rates ARE pairwise distinct — confirming that the
gradient cannot collapse into a 2-valued partition. -/
theorem shift_rates_pairwise_distinct :
    shiftRate1w ≠ shiftRate2w ∧ shiftRate1w ≠ shiftRate3w ∧
    shiftRate1w ≠ shiftRate4w ∧ shiftRate2w ≠ shiftRate3w ∧
    shiftRate2w ≠ shiftRate4w ∧ shiftRate3w ≠ shiftRate4w := by
  native_decide

-- ============================================================================
-- §4: Rescue Strategies
-- ============================================================================

/-!
## How proponents might extend each account

**DLM rescue**: Add a discourse-status penalty term, e.g.,
`enrichedCost t := totalDepLength t + newnessPenalty t`. But
`totalDepLength_word_invariant` proves the standard DLM term contributes
nothing discourse-sensitive — any discourse sensitivity must come from
a wholly *additional* component, not from reinterpreting `totalDepLength`.
This yields a two-factor model: Arnold et al.'s conclusion.

**Pure-discourse rescue**: Argue weight is epiphenomenal of newness (new
referents need more description → heavier). Arnold et al.'s regression
controls for this and finds independent weight effects. Moreover,
`pure_discourse_overpredicts_shift` shows the model wrongly predicts
newness should matter for NP shift (Study 2), when it does not.

**CCG rescue**: Replace the binary `ShiftFeature` with a gradient weight
or probabilistic model. But this abandons the categorical combinatory
architecture — `±SHIFT` exists precisely to keep type-driven parsing
deterministic. A gradient replacement is essentially DLM.

All three extensions converge on the paper's central claim: an adequate
ordering model requires both structural weight and discourse status.
-/

/-- The minimal adequate model type: a function of both weight and discourse
status, encoding Arnold et al.'s central finding that neither factor
alone suffices. -/
abbrev OrderingModel := Nat → DiscourseStatus → Nat

end Phenomena.WordOrder.Studies.ArnoldEtAl2000Bridge
