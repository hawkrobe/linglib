import Linglib.Core.Logic.Modal.BSML.Scenarios
import Linglib.Studies.Aloni2022.FreeChoice

/-!
# [aloni-2022]: BSML applied to permission disjunction

[aloni-2022]

Computational instantiation of NS FC, WS FC, Dual Prohibition, Double Negation
FC, and Modal Disjunction (Facts 3, 4, 5, 11, 12) in BSML+ on a 4-world deontic
model. Each result is a named theorem invoking the universal substrate theorem
in `Studies/Aloni2022/FreeChoice.lean`, applied to the concrete model
constructed below.

## Out of scope

- Negative FC (Fact 14)
- Universal FC, ALL-OTHERS-FC, ALL-OTHERS-DUAL-PROHIBITION (Aloni §6.2 first-order)
- BSML* (Fact 13–14, §6.3.1) and BSML◇ / BSML∅ (§7) interpretation strategies
- §6.1 epistemic vs deontic contrast (this file is purely deontic)

The universal results live in `Studies/Aloni2022/FreeChoice.lean`:
`narrowScopeFC`, `wideScopeFC`, `modalDisjunction`, `dualProhibition`,
`doubleNegationFC`, `negativeFC_poss_fails_bsmlPlus`. The Negative FC failure
(Fact 14) on a single Unit world is proved there.

## Atoms and worlds

This file uses **typed atoms** `FCAtom.{a, b}` (from `Core.Logic.Modal.BSML.Atoms`)
rather than String identifiers. The valuation routes directly through
`PowerSet2World.holds`, eliminating the silent typo trap of the earlier
String-based pattern (`match p with | "coffee" => ... | _ => false`).

Worlds are `PowerSet2World` (`nothing`/`onlyA`/`onlyB`/`both`), matching
Aloni 2022 Figure 1's `w_∅`/`w_a`/`w_b`/`w_ab`. We label `FCAtom.a` as
"coffee" and `FCAtom.b` as "tea" in prose only — the formal types are
the typed atoms throughout.
-/

namespace Aloni2022

open Core.Logic.Modal.BSML
open Core.Logic.Modal.BSML (FCAtom PowerSet2World)

-- ============================================================================
-- §1 Teams
-- ============================================================================

/-- The free-choice team: {`both`, `onlyA`, `onlyB`} = {w_ab, w_a, w_b}.
    Excludes `nothing` (= w_∅), the world that would supply a zero-witness
    substate for the disjunction enrichment. -/
def freeChoiceTeam : Finset PowerSet2World :=
  {.both, .onlyA, .onlyB}

/-- The prohibition team: just `nothing` (= w_∅). With `restrictiveModel`,
    R[nothing] = {nothing} so the prohibition `¬◇(a ∨ b)` is supported. -/
def prohibitionTeam : Finset PowerSet2World :=
  {.nothing}

-- ============================================================================
-- §2 Models
-- ============================================================================

/-- Deontic model: universal accessibility from every world. Indisputable on
    every non-empty team (R[w] = R[v] = univ trivially), but **not** state-based
    on `freeChoiceTeam` since R[w] = univ ⊋ freeChoiceTeam.

    Valuation: `val a w = w.holds a` — direct routing through the typed
    atom. No String fallthrough, no silent typos. -/
def deonticModel : BSMLModel PowerSet2World FCAtom where
  access := λ _ => Finset.univ
  val := λ p w => w.holds p

/-- Restrictive deontic model: from `nothing`, only `nothing` is accessible;
    from any other world, all worlds. Used for Dual Prohibition on the
    prohibition team `{nothing}`. -/
def restrictiveModel : BSMLModel PowerSet2World FCAtom where
  access := λ w =>
    match w with
    | .nothing => {.nothing}
    | _        => Finset.univ
  val := λ p w => w.holds p

/-- State-based deontic model: R[w] = freeChoiceTeam for every world. Strictly
    stronger than indisputability; required for Modal Disjunction (Fact 3). -/
def stateBasedModel : BSMLModel PowerSet2World FCAtom where
  access := λ _ => freeChoiceTeam
  val := λ p w => w.holds p

/-- A deontic model where indisputability **fails** on `freeChoiceTeam` —
    `onlyA` and `onlyB` see different accessible sets. Demonstrates that the
    indisputable-R precondition of `wideScopeFC` (Fact 5) is necessary, not
    incidental: WS FC's conclusion may fail on this model even when its
    enriched premise is supported. (Aloni 2022 Figure 5(b) shape — non-indisputable R.
    Figure 5(a) shows the dual case where R is indisputable but enrichment fails.) -/
def looseDeonticModel : BSMLModel PowerSet2World FCAtom where
  access := λ w =>
    match w with
    | .both    => {.both, .onlyA}
    | .onlyA   => {.both, .onlyA}
    | .onlyB   => {.onlyB}
    | .nothing => Finset.univ
  val := λ p w => w.holds p

-- ============================================================================
-- §3 Formulas (over typed FCAtom)
-- ============================================================================

/-- ◇(a ∨ b) — narrow-scope premise (Fact 4). -/
def mayHaveCoffeeOrTea : BSMLFormula FCAtom :=
  .poss (.disj (.atom .a) (.atom .b))

def mayCoffee : BSMLFormula FCAtom := .poss (.atom .a)
def mayTea    : BSMLFormula FCAtom := .poss (.atom .b)

/-- ¬◇(a ∨ b) — Dual Prohibition premise (Fact 11). -/
def prohibition : BSMLFormula FCAtom :=
  .neg (.poss (.disj (.atom .a) (.atom .b)))

def notMayCoffee : BSMLFormula FCAtom := .neg (.poss (.atom .a))
def notMayTea    : BSMLFormula FCAtom := .neg (.poss (.atom .b))

/-- ◇a ∨ ◇b — wide-scope disjunction premise (Fact 5). -/
def wideScopeDisj : BSMLFormula FCAtom :=
  .disj (.poss (.atom .a)) (.poss (.atom .b))

/-- ¬¬◇(a ∨ b) — double-negation premise (Fact 12). -/
def doubleNegMayHaveCoffeeOrTea : BSMLFormula FCAtom :=
  .neg (.neg (.poss (.disj (.atom .a) (.atom .b))))

/-- a ∨ b — plain disjunction (Modal Disjunction premise, Fact 3). -/
def plainDisj : BSMLFormula FCAtom :=
  .disj (.atom .a) (.atom .b)

-- ============================================================================
-- §4 Frame conditions on the chosen models
-- ============================================================================

theorem deonticModel_indisputable_on_team :
    deonticModel.IsIndisputable freeChoiceTeam := by decide

theorem stateBasedModel_state_based_on_team :
    stateBasedModel.IsStateBased freeChoiceTeam := by decide

theorem deonticModel_not_state_based_on_team :
    ¬ deonticModel.IsStateBased freeChoiceTeam := by decide

theorem looseDeonticModel_not_indisputable_on_team :
    ¬ looseDeonticModel.IsIndisputable freeChoiceTeam := by decide

-- ============================================================================
-- §5 Fact 4 (Narrow Scope FC) at `deonticModel`
-- ============================================================================

/-- Fact 4 instantiated at the deontic model + free-choice team:
    enriched ◇(a ∨ b) entails ◇a ∧ ◇b.
    Proved by invoking the universal substrate theorem `narrowScopeFC`. -/
theorem aloni2022_fact4_NS_FC
    (h : support deonticModel (enrich mayHaveCoffeeOrTea) freeChoiceTeam) :
    support deonticModel mayCoffee freeChoiceTeam ∧
    support deonticModel mayTea    freeChoiceTeam :=
  narrowScopeFC deonticModel (.atom .a) (.atom .b) freeChoiceTeam
    rfl rfl h

/-- The premise of Fact 4 holds on this model + team. -/
theorem aloni2022_fact4_premise_supported :
    support deonticModel (enrich mayHaveCoffeeOrTea) freeChoiceTeam := by decide

-- ============================================================================
-- §6 Fact 11 (Dual Prohibition) at `restrictiveModel`
-- ============================================================================

/-- Fact 11 instantiated at the restrictive model + prohibition team:
    enriched ¬◇(a ∨ b) entails ¬◇a ∧ ¬◇b. -/
theorem aloni2022_fact11_dual_prohibition
    (h : support restrictiveModel (enrich prohibition) prohibitionTeam) :
    support restrictiveModel notMayCoffee prohibitionTeam ∧
    support restrictiveModel notMayTea    prohibitionTeam :=
  dualProhibition restrictiveModel (.atom .a) (.atom .b) prohibitionTeam
    rfl rfl h

theorem aloni2022_fact11_premise_supported :
    support restrictiveModel (enrich prohibition) prohibitionTeam := by decide

-- ============================================================================
-- §7 Fact 5 (Wide Scope FC) at `deonticModel` and failure on `looseDeonticModel`
-- ============================================================================

/-- Fact 5 instantiated at the deontic model + free-choice team:
    enriched (◇a ∨ ◇b) entails ◇a ∧ ◇b, given indisputability.
    Indisputability holds trivially on this model (universal access), so this
    is a consequence-direction test — see `aloni2022_fact5_WS_FC_fails_loose`
    for the discriminating failure direction. -/
theorem aloni2022_fact5_WS_FC
    (h : support deonticModel (enrich wideScopeDisj) freeChoiceTeam) :
    support deonticModel mayCoffee freeChoiceTeam ∧
    support deonticModel mayTea    freeChoiceTeam :=
  wideScopeFC deonticModel (.atom .a) (.atom .b) freeChoiceTeam
    rfl rfl deonticModel_indisputable_on_team h

theorem aloni2022_fact5_premise_supported :
    support deonticModel (enrich wideScopeDisj) freeChoiceTeam := by decide

/-- The WS FC enriched premise IS supported on `looseDeonticModel` for
    `freeChoiceTeam` — even though indisputability fails. This pairs with
    `aloni2022_fact5_WS_FC_fails_loose` to demonstrate that the *implication*
    of WS FC genuinely fails (premise holds, conclusion does not) on this
    model — not a vacuous failure. -/
theorem aloni2022_fact5_premise_supported_loose :
    support looseDeonticModel (enrich wideScopeDisj) freeChoiceTeam := by decide

/-- Necessity of indisputability: on `looseDeonticModel` (where indisputability
    fails on `freeChoiceTeam`), the WS FC conclusion `mayCoffee` is **not**
    supported on the team — even though the enriched premise IS supported
    (`aloni2022_fact5_premise_supported_loose`). The substrate's `wideScopeFC`
    cannot apply (its indisputability hypothesis fails), and the implication
    genuinely breaks: premise holds, conclusion does not. -/
theorem aloni2022_fact5_WS_FC_fails_loose :
    ¬ support looseDeonticModel mayCoffee freeChoiceTeam := by decide

-- ============================================================================
-- §8 Fact 12 (Double Negation FC) at `deonticModel`
-- ============================================================================

/-- Fact 12 instantiated at the deontic model + free-choice team:
    enriched ¬¬◇(a ∨ b) entails ◇a ∧ ◇b (FC re-emerges
    under double negation). The earlier instantiation of this file
    (lines 117–118 in the pre-refactor version) duplicated the NS FC test
    rather than exhibiting the entailment from the double-negation premise;
    this is the correct form. -/
theorem aloni2022_fact12_double_negation
    (h : support deonticModel (enrich doubleNegMayHaveCoffeeOrTea) freeChoiceTeam) :
    support deonticModel mayCoffee freeChoiceTeam ∧
    support deonticModel mayTea    freeChoiceTeam :=
  doubleNegationFC deonticModel (.atom .a) (.atom .b) freeChoiceTeam
    rfl rfl h

theorem aloni2022_fact12_premise_supported :
    support deonticModel (enrich doubleNegMayHaveCoffeeOrTea) freeChoiceTeam := by
  decide

-- ============================================================================
-- §9 Fact 3 (Modal Disjunction) at `stateBasedModel`; failure on `deonticModel`
-- ============================================================================

/-- Fact 3 instantiated at the state-based model + free-choice team:
    enriched (a ∨ b) entails ◇a ∧ ◇b — without ◇ in the
    premise, by virtue of state-basedness. -/
theorem aloni2022_fact3_modal_disjunction
    (h : support stateBasedModel (enrich plainDisj) freeChoiceTeam) :
    support stateBasedModel mayCoffee freeChoiceTeam ∧
    support stateBasedModel mayTea    freeChoiceTeam :=
  modalDisjunction stateBasedModel (.atom .a) (.atom .b) freeChoiceTeam
    rfl rfl stateBasedModel_state_based_on_team h

theorem aloni2022_fact3_premise_supported :
    support stateBasedModel (enrich plainDisj) freeChoiceTeam := by decide

end Aloni2022
