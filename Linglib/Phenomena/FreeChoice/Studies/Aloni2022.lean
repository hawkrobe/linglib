import Linglib.Phenomena.FreeChoice.Atoms
import Linglib.Phenomena.FreeChoice.Worlds
import Linglib.Theories.Semantics.BSML.FreeChoice

/-!
# @cite{aloni-2022}: BSML applied to permission disjunction

@cite{aloni-2022}

Computational instantiation of NS FC, WS FC, Dual Prohibition, Double Negation
FC, and Modal Disjunction (Facts 3, 4, 5, 11, 12) in BSML+ on a 4-world deontic
model. Each result is a named theorem invoking the universal substrate theorem
in `Theories/Semantics/BSML/FreeChoice.lean`, applied to the concrete model
constructed below.

## Out of scope

- Negative FC (Fact 14)
- Universal FC, ALL-OTHERS-FC, ALL-OTHERS-DUAL-PROHIBITION (Aloni §6.2 first-order)
- BSML* (Fact 13–14, §6.3.1) and BSML◇ / BSML∅ (§7) interpretation strategies
- §6.1 epistemic vs deontic contrast (this file is purely deontic)

The universal results live in `Theories/Semantics/BSML/FreeChoice.lean`:
`narrowScopeFC`, `wideScopeFC`, `modalDisjunction`, `dualProhibition`,
`doubleNegationFC`, `negativeFC_poss_fails_bsmlPlus`. The Negative FC failure
(Fact 14) on a single Unit world is proved there.

## Worlds and atoms

Worlds are `Phenomena.FreeChoice.PowerSet2World` (`nothing`/`onlyA`/`onlyB`/`both`),
matching Aloni 2022 Figure 1's `w_∅`/`w_a`/`w_b`/`w_ab`. Atoms `"coffee"`/`"tea"`
route through typed `FCAtom.a`/`FCAtom.b` via `coffeeTeaVal`.
-/

namespace Phenomena.FreeChoice.Studies.Aloni2022

open Semantics.BSML
open Phenomena.FreeChoice (FCAtom PowerSet2World)

-- ============================================================================
-- §1 Valuation
-- ============================================================================

/-- Single shared valuation routing the String atoms `"coffee"` and `"tea"`
    through the typed `FCAtom.a` / `FCAtom.b` via `PowerSet2World.holds`. The
    `_ => false` fallthrough is forced by `BSMLModel.val : String → α → Bool`
    in the substrate; full elimination would require atom-polymorphic BSML. -/
def coffeeTeaVal : String → PowerSet2World → Bool
  | "coffee", w => w.holds .a
  | "tea",    w => w.holds .b
  | _,        _ => false

-- ============================================================================
-- §2 Teams
-- ============================================================================

/-- The free-choice team: {`both`, `onlyA`, `onlyB`} = {w_ab, w_a, w_b}.
    Excludes `nothing` (= w_∅), the world that would supply a zero-witness
    substate for the disjunction enrichment. -/
def freeChoiceTeam : Finset PowerSet2World :=
  {.both, .onlyA, .onlyB}

/-- The prohibition team: just `nothing` (= w_∅). With `restrictiveModel`,
    R[nothing] = {nothing} so the prohibition `¬◇(coffee ∨ tea)` is supported. -/
def prohibitionTeam : Finset PowerSet2World :=
  {.nothing}

-- ============================================================================
-- §3 Models
-- ============================================================================

/-- Deontic model: universal accessibility from every world. Indisputable on
    every non-empty team (R[w] = R[v] = univ trivially), but **not** state-based
    on `freeChoiceTeam` since R[w] = univ ⊋ freeChoiceTeam. -/
def deonticModel : BSMLModel PowerSet2World where
  access := λ _ => Finset.univ
  val := coffeeTeaVal

/-- Restrictive deontic model: from `nothing`, only `nothing` is accessible;
    from any other world, all worlds. Used for Dual Prohibition on the
    prohibition team `{nothing}`. -/
def restrictiveModel : BSMLModel PowerSet2World where
  access := λ w =>
    match w with
    | .nothing => {.nothing}
    | _        => Finset.univ
  val := coffeeTeaVal

/-- State-based deontic model: R[w] = freeChoiceTeam for every world. Strictly
    stronger than indisputability; required for Modal Disjunction (Fact 3). -/
def stateBasedModel : BSMLModel PowerSet2World where
  access := λ _ => freeChoiceTeam
  val := coffeeTeaVal

/-- A deontic model where indisputability **fails** on `freeChoiceTeam` —
    `onlyA` and `onlyB` see different accessible sets. Demonstrates that the
    indisputable-R precondition of `wideScopeFC` (Fact 5) is necessary, not
    incidental: WS FC's conclusion may fail on this model even when its
    enriched premise is supported. (Aloni 2022 Figure 5(b) shape — non-indisputable R.
    Figure 5(a) shows the dual case where R is indisputable but enrichment fails.) -/
def looseDeonticModel : BSMLModel PowerSet2World where
  access := λ w =>
    match w with
    | .both    => {.both, .onlyA}
    | .onlyA   => {.both, .onlyA}
    | .onlyB   => {.onlyB}
    | .nothing => Finset.univ
  val := coffeeTeaVal

-- ============================================================================
-- §4 Formulas
-- ============================================================================

/-- ◇(coffee ∨ tea) — narrow-scope premise (Fact 4). -/
def mayHaveCoffeeOrTea : BSMLFormula :=
  .poss (.disj (.atom "coffee") (.atom "tea"))

def mayCoffee : BSMLFormula := .poss (.atom "coffee")
def mayTea    : BSMLFormula := .poss (.atom "tea")

/-- ¬◇(coffee ∨ tea) — Dual Prohibition premise (Fact 11). -/
def prohibition : BSMLFormula :=
  .neg (.poss (.disj (.atom "coffee") (.atom "tea")))

def notMayCoffee : BSMLFormula := .neg (.poss (.atom "coffee"))
def notMayTea    : BSMLFormula := .neg (.poss (.atom "tea"))

/-- ◇coffee ∨ ◇tea — wide-scope disjunction premise (Fact 5). -/
def wideScopeDisj : BSMLFormula :=
  .disj (.poss (.atom "coffee")) (.poss (.atom "tea"))

/-- ¬¬◇(coffee ∨ tea) — double-negation premise (Fact 12). -/
def doubleNegMayHaveCoffeeOrTea : BSMLFormula :=
  .neg (.neg (.poss (.disj (.atom "coffee") (.atom "tea"))))

/-- coffee ∨ tea — plain disjunction (Modal Disjunction premise, Fact 3). -/
def plainDisj : BSMLFormula :=
  .disj (.atom "coffee") (.atom "tea")

-- ============================================================================
-- §5 Frame conditions on the chosen models
-- ============================================================================

theorem deonticModel_indisputable_on_team :
    deonticModel.isIndisputable freeChoiceTeam := by decide

theorem stateBasedModel_state_based_on_team :
    stateBasedModel.isStateBased freeChoiceTeam := by decide

theorem deonticModel_not_state_based_on_team :
    ¬ deonticModel.isStateBased freeChoiceTeam := by decide

theorem looseDeonticModel_not_indisputable_on_team :
    ¬ looseDeonticModel.isIndisputable freeChoiceTeam := by decide

-- ============================================================================
-- §6 Fact 4 (Narrow Scope FC) at `deonticModel`
-- ============================================================================

/-- Fact 4 instantiated at the deontic model + free-choice team:
    enriched ◇(coffee ∨ tea) entails ◇coffee ∧ ◇tea.
    Proved by invoking the universal substrate theorem `narrowScopeFC`. -/
theorem aloni2022_fact4_NS_FC
    (h : support deonticModel (enrich mayHaveCoffeeOrTea) freeChoiceTeam) :
    support deonticModel mayCoffee freeChoiceTeam ∧
    support deonticModel mayTea    freeChoiceTeam :=
  narrowScopeFC deonticModel (.atom "coffee") (.atom "tea") freeChoiceTeam
    rfl rfl h

/-- The premise of Fact 4 holds on this model + team. -/
theorem aloni2022_fact4_premise_supported :
    support deonticModel (enrich mayHaveCoffeeOrTea) freeChoiceTeam := by decide

-- ============================================================================
-- §7 Fact 11 (Dual Prohibition) at `restrictiveModel`
-- ============================================================================

/-- Fact 11 instantiated at the restrictive model + prohibition team:
    enriched ¬◇(coffee ∨ tea) entails ¬◇coffee ∧ ¬◇tea. -/
theorem aloni2022_fact11_dual_prohibition
    (h : support restrictiveModel (enrich prohibition) prohibitionTeam) :
    support restrictiveModel notMayCoffee prohibitionTeam ∧
    support restrictiveModel notMayTea    prohibitionTeam :=
  dualProhibition restrictiveModel (.atom "coffee") (.atom "tea") prohibitionTeam
    rfl rfl h

theorem aloni2022_fact11_premise_supported :
    support restrictiveModel (enrich prohibition) prohibitionTeam := by decide

-- ============================================================================
-- §8 Fact 5 (Wide Scope FC) at `deonticModel` and failure on `looseDeonticModel`
-- ============================================================================

/-- Fact 5 instantiated at the deontic model + free-choice team:
    enriched (◇coffee ∨ ◇tea) entails ◇coffee ∧ ◇tea, given indisputability.
    Indisputability holds trivially on this model (universal access), so this
    is a consequence-direction test — see `aloni2022_fact5_WS_FC_fails_loose`
    for the discriminating failure direction. -/
theorem aloni2022_fact5_WS_FC
    (h : support deonticModel (enrich wideScopeDisj) freeChoiceTeam) :
    support deonticModel mayCoffee freeChoiceTeam ∧
    support deonticModel mayTea    freeChoiceTeam :=
  wideScopeFC deonticModel (.atom "coffee") (.atom "tea") freeChoiceTeam
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
-- §9 Fact 12 (Double Negation FC) at `deonticModel`
-- ============================================================================

/-- Fact 12 instantiated at the deontic model + free-choice team:
    enriched ¬¬◇(coffee ∨ tea) entails ◇coffee ∧ ◇tea (FC re-emerges
    under double negation). The earlier instantiation of this file
    (lines 117–118 in the pre-refactor version) duplicated the NS FC test
    rather than exhibiting the entailment from the double-negation premise;
    this is the correct form. -/
theorem aloni2022_fact12_double_negation
    (h : support deonticModel (enrich doubleNegMayHaveCoffeeOrTea) freeChoiceTeam) :
    support deonticModel mayCoffee freeChoiceTeam ∧
    support deonticModel mayTea    freeChoiceTeam :=
  doubleNegationFC deonticModel (.atom "coffee") (.atom "tea") freeChoiceTeam
    rfl rfl h

theorem aloni2022_fact12_premise_supported :
    support deonticModel (enrich doubleNegMayHaveCoffeeOrTea) freeChoiceTeam := by
  decide

-- ============================================================================
-- §10 Fact 3 (Modal Disjunction) at `stateBasedModel`; failure on `deonticModel`
-- ============================================================================

/-- Fact 3 instantiated at the state-based model + free-choice team:
    enriched (coffee ∨ tea) entails ◇coffee ∧ ◇tea — without ◇ in the
    premise, by virtue of state-basedness. -/
theorem aloni2022_fact3_modal_disjunction
    (h : support stateBasedModel (enrich plainDisj) freeChoiceTeam) :
    support stateBasedModel mayCoffee freeChoiceTeam ∧
    support stateBasedModel mayTea    freeChoiceTeam :=
  modalDisjunction stateBasedModel (.atom "coffee") (.atom "tea") freeChoiceTeam
    rfl rfl stateBasedModel_state_based_on_team h

theorem aloni2022_fact3_premise_supported :
    support stateBasedModel (enrich plainDisj) freeChoiceTeam := by decide

end Phenomena.FreeChoice.Studies.Aloni2022
