import Linglib.Phenomena.AuxiliaryVerbs.Selection
import Linglib.Phenomena.AuxiliaryVerbs.Studies.Olivier2026
import Linglib.Theories.Syntax.Minimalism.NestedAgree

/-!
# @cite{amato-2025} mechanism applied to Italian restructuring AS

**Scope clarification.** This file does *not* model @cite{amato-2025}'s
§3 (monoclausal Italian auxiliary selection in non-restructuring
contexts). It models the @cite{amato-2025}/@cite{amato-2024}
*mechanism* (cyclic-Agree person feature on Perf, with Nested Agree
restricting the second probe) *applied to* the Romance restructuring
problem set up by @cite{olivier-2026}. The clause structure
(`RestructuringClauseAmato extends Olivier2026.RestructuringClause`)
inherits matrix-modal / compound-tense / clitic-position fields from
the Olivier restructuring framework — not from Amato §3, which is
monoclausal throughout.

Concrete consequence: the reflexive-case predicate
`VIsPhiActive c.base.embeddedClass = .reflexive →
c.base.refCliticPos ≠ .climbed` uses **clitic climbing as a
diagnostic** for whether the chain reaches v. Climbing is a
restructuring-domain criterion (Olivier 2026, Amato 2024), *not* an
Amato 2025 §3 criterion (which doesn't deal with restructuring or
clitic climbing). The Amato §3 reflexive analysis (φ-defective
reflexive + SCC counter-feeding, §3.4.3) is *not* what this file
models.

What this file *does* model faithfully:
- The Nested-Agree-on-Perf configuration (`toNestedConfig`)
- The DM vocabulary insertion rule HAVE = `Perf[π:α]`, BE elsewhere
  (@cite{amato-2025} rule 14)
- The Amato-2024 complement-size lever (vP vs TP) for restructuring
  optionality
- The Olivier 2026 / Amato 2024 prediction divergence on the
  TP-complement reflexive case

What this file *does not* model (out of scope, requires further
work):
- Indirect reflexive (Amato §3.4.3 example 5b: `Teresa si è lavata
  il vestito`)
- Impersonal `si` (Amato §3.4.4 example 5d)
- §3.5 Ariellese-style feature-ordering parametrization
- The φ-defective-reflexive + SCC counter-feeding mechanism (the
  alternative to clitic-climbing-as-diagnostic for the reflexive
  case)

The cross-domain Amato 2025 case studies for non-restructuring
phenomena live in `Phenomena/Agreement/Studies/Amato2025.lean`
(§4.1.2 Icelandic DAT-NOM, §4.2.1 Lak perfective) and
`Phenomena/FillerGap/Studies/Amato2025.lean` (§4.2.3 Bulgarian wh).

## DM elsewhere inversion (vs @cite{olivier-2026})

@cite{amato-2025}: HAVE = `Perf[π:α]`, BE = elsewhere.
@cite{olivier-2026} inverts: HAVE = elsewhere, BE = `T[ID:α] =
vAux[ID:α]`. This file follows the Amato convention — load-bearing
for the cross-theory divergence theorem at the bottom.

The cyclic-Agree person-feature analysis adopted here originates in
@cite{amato-2023}'s monograph and is refined by @cite{amato-2025}.
-/

namespace Phenomena.AuxiliaryVerbs.Studies.Amato2025

open Phenomena.AuxiliaryVerbs.Selection
open Phenomena.AuxiliaryVerbs.Studies.Olivier2026
open Minimalism
open Minimalism.NestedAgree

/-! ## Probe stack (Nested Agree on Perf) -/

/-- The two features Perf probes for, in order. `inflPerf` is valued
    from below by the participle morphology on the lower v;
    `personUPers` is the open person slot resolved by π-Agree under
    Nested Agree. @cite{amato-2025}. -/
inductive Probe where
  | inflPerf      -- [*Infl:perf*]
  | personUPers   -- [*π:_*]
  deriving DecidableEq, Repr

/-- The ordered probe stack on Perf in the argument-structure-driven
    Italian system: `inflPerf` first, then `personUPers`, the second
    constrained by Maximized Matching to the goal already found by
    Infl-Agree (@cite{amato-2025}). -/
def vAuxProbes : List Probe := [.inflPerf, .personUPers]

/-! ## Complement size — restructuring optionality lever -/

/-- Size of the complement of the restructuring head. The
    complement-size analysis of restructuring optionality originates in
    @cite{amato-2024}: a vP complement licenses the Nested-Agree chain
    that can yield AS; a TP complement closes the chain (the EA is the
    closest goal for the matrix π-probe), forcing HAVE. The 2025 NLLT
    paper retains this lever within the broader Nested Agree framework. -/
inductive ComplementSize where
  | vP   -- thin complement; π-Agree threads through to v
  | tp   -- larger complement; embedded T closes the chain
  deriving DecidableEq, Repr

/-! ## Restructuring clauses (Amato variant) -/

/-- A `[Modal + Infinitive]` restructuring clause as @cite{amato-2025}
    models it. Wraps Olivier's `RestructuringClause` (the four shared
    structural diagnostics) with the distinctive `complementSize` field.
    Keeping the base structure intact lets the two theories be compared
    directly: every Olivier clause projects to an Amato clause by
    choosing a complement size, and vice versa. -/
structure RestructuringClauseAmato where
  /-- The Olivier-shape four-field core. -/
  base : RestructuringClause
  /-- Complement-size lever for restructuring optionality. -/
  complementSize : ComplementSize
  deriving DecidableEq, Repr

/-! ## The structural primitive: φ-activity of the lower v

    The whole Italian aux selection chain — `PersonAgreeSucceeds`,
    `daughters`, `predictedMatrixAuxAmato` — derives from a single
    structural primitive: whether the lower v carries active φ-features
    in a given clause configuration. By making `VIsPhiActive` the shared
    underlying definition rather than encoding the answer (`PersonAgreeSucceeds`)
    into the abstract `daughters` field of `toNestedConfig`, the
    Nested-Agree bridge theorem `personAgree_iff_runStack_hits` becomes
    a derivation through a common primitive instead of an unfolding
    tautology. -/

/-- Does the lower v carry active φ-features in this clause? @cite{amato-2025}:

    - TP complement: embedded T closes the chain at T; v is *effectively*
      the embedded T (φ-active).
    - vP complement, transitive/unergative: v has its own person features.
    - vP complement, unaccusative: v is φ-defective (Amato §3.4.2).
    - vP complement, reflexive: v's φ comes from EA when the clitic stays
      low; when the clitic climbs, the chain bottoms out on the φ-defective
      cliticized reflexive (Amato §3.4.3).

    *Structural primitive*: this predicate reads only the clause's
    structural fields (complement size, embedded verb class, clitic
    position). Other definitions in this file (`PersonAgreeSucceeds`,
    `toNestedConfig.daughters`) are derived from `VIsPhiActive`, not
    independently re-encoded. -/
def VIsPhiActive (c : RestructuringClauseAmato) : Prop :=
  match c.complementSize with
  | .tp => True
  | .vP =>
    match c.base.embeddedClass with
    | .transitive   => True
    | .unergative   => True
    | .unaccusative => False
    | .reflexive    => c.base.refCliticPos ≠ .climbed

instance : DecidablePred VIsPhiActive := fun c => by
  unfold VIsPhiActive
  cases c.complementSize <;> first | infer_instance |
    (cases c.base.embeddedClass <;> infer_instance)

/-! ## Person-valuation outcome under Nested Agree -/

/-- π-Agree on Perf succeeds iff the lower v is φ-active. By definition
    of `VIsPhiActive`. Stated as a `Prop` (mathlib pattern: predicates
    are `Prop` with `[DecidablePred]`). -/
def PersonAgreeSucceeds (c : RestructuringClauseAmato) : Prop := VIsPhiActive c

instance : DecidablePred PersonAgreeSucceeds := fun c => by
  unfold PersonAgreeSucceeds; infer_instance

/-! ## Vocabulary insertion (@cite{amato-2025}, rule 14a/b) -/

/-- Spell out Perf per the @cite{amato-2025} vocabulary items: HAVE iff
    π-Agree succeeded; BE elsewhere. NOTE: this is the *opposite*
    convention from @cite{olivier-2026} (rule 55), which treats BE as the
    result of an ID-match check and HAVE as elsewhere. The two surface
    predictions agree on the canonical AS configurations but diverge on
    the TP-complement reflexive (see
    `amato2025_olivier_diverge_on_tp_complement`). -/
def predictedMatrixAuxAmato (c : RestructuringClauseAmato) : PerfectAux :=
  if PersonAgreeSucceeds c then .have else .be

/-! ## Auxiliary Switch predicate (Amato variant) -/

/-- Does this clause exhibit Auxiliary Switch under Amato 2025's
    Nested-Agree analysis? AS = the matrix surfaces as BE in a
    configuration where its own argument structure would otherwise
    select HAVE. As in Olivier, AS requires the matrix to be modal and
    in a compound tense; the embedded clause must be BE-selecting in the
    canonical sense. The Amato-specific filter is then the Nested-Agree
    outcome: AS surfaces precisely when π-Agree on Perf *fails*. -/
def AuxiliarySwitchOccursAmato (c : RestructuringClauseAmato) : Prop :=
  c.base.matrixModal = true ∧ c.base.compoundTense = true ∧
  SelectsBe c.base.embeddedClass ∧
  ¬ PersonAgreeSucceeds c

instance : DecidablePred AuxiliarySwitchOccursAmato := fun c => by
  unfold AuxiliarySwitchOccursAmato
  cases c.base.embeddedClass <;> infer_instance

/-! ## Examples -/

/-- Canonical AS case under Amato: modal + compound + reflexive,
    clitic climbed, vP complement. Predicts BE. -/
def beModalReflexiveClimbedVP : RestructuringClauseAmato :=
  { base := beWantReflexiveClimbed, complementSize := .vP }

/-- The wedge case: same modal + compound + reflexive + climbing
    configuration, but with a TP complement. Amato predicts HAVE
    (the embedded T closes the Nested-Agree chain). -/
def haveModalReflexiveClimbedTP : RestructuringClauseAmato :=
  { base := beWantReflexiveClimbed, complementSize := .tp }

/-- Modal + compound + unaccusative, vP complement. Predicts BE
    (φ-defective lower v, π-Agree fails). -/
def beModalUnaccusativeVP : RestructuringClauseAmato :=
  { base := beWantCome, complementSize := .vP }

/-- Modal + compound + unaccusative, TP complement. The distinctive
    optionality prediction: with a TP-sized complement the chain bottoms
    out at T, π-Agree succeeds, HAVE surfaces. -/
def haveModalUnaccusativeTP : RestructuringClauseAmato :=
  { base := beWantCome, complementSize := .tp }

/-- Modal + compound + transitive, vP complement. Predicts HAVE
    (transitive v has person features). -/
def haveModalTransitiveVP : RestructuringClauseAmato :=
  { base := haveWantTransitive, complementSize := .vP }

/-! ## Theorems -/

/-- A non-modal matrix never triggers Auxiliary Switch under
    @cite{amato-2025}. -/
theorem amato_as_requires_modal (c : RestructuringClauseAmato)
    (h : c.base.matrixModal = false) :
    ¬ AuxiliarySwitchOccursAmato c := by
  intro ⟨hM, _⟩
  exact Bool.false_ne_true (h ▸ hM)

/-- A non-compound matrix tense never triggers Auxiliary Switch. -/
theorem amato_as_requires_compound (c : RestructuringClauseAmato)
    (h : c.base.compoundTense = false) :
    ¬ AuxiliarySwitchOccursAmato c := by
  intro ⟨_, hC, _⟩
  exact Bool.false_ne_true (h ▸ hC)

/-- A transitive embedded verb never triggers Auxiliary Switch under
    Amato (same `SelectsBe` filter as in Olivier). -/
theorem amato_as_requires_be_selecting (c : RestructuringClauseAmato)
    (h : c.base.embeddedClass = .transitive) :
    ¬ AuxiliarySwitchOccursAmato c := by
  intro ⟨_, _, hsel, _⟩
  rw [h] at hsel
  exact PerfectAux.noConfusion hsel

/-! ### Per-example smoke tests

    Single-witness predictions on the example clauses above. These
    document expected outputs but are not reusable lemmas — the
    universally-quantified versions `amato_vp_unaccusative_predicts_be`,
    `amato_tp_complement_predicts_have`, etc. below are the load-bearing
    statements. -/

example : predictedMatrixAuxAmato beModalUnaccusativeVP = .be := by decide
example : predictedMatrixAuxAmato haveModalUnaccusativeTP = .have := by decide
example : predictedMatrixAuxAmato haveModalTransitiveVP = .have := by decide
example : predictedMatrixAuxAmato beModalReflexiveClimbedVP = .be := by decide

/-! ### Universally-quantified predictions

    These are the genuine theorems: they generalize over *any* clause
    matching a structural shape, not over a single hand-built witness. -/

/-- For *any* vP-complement unaccusative clause, Amato predicts BE:
    φ-defective v leaves `Perf[π:_]` unvalued, BE surfaces as elsewhere. -/
theorem amato_vp_unaccusative_predicts_be (c : RestructuringClauseAmato)
    (hSize : c.complementSize = .vP)
    (hClass : c.base.embeddedClass = .unaccusative) :
    predictedMatrixAuxAmato c = .be := by
  simp [predictedMatrixAuxAmato, PersonAgreeSucceeds, VIsPhiActive, hSize, hClass]

/-- For *any* TP-complement clause, Amato predicts HAVE: the embedded T
    closes the Nested-Agree chain regardless of embedded verb class. The
    distinctive optionality prediction (originating in @cite{amato-2024}'s
    complement-size analysis). -/
theorem amato_tp_complement_predicts_have (c : RestructuringClauseAmato)
    (hSize : c.complementSize = .tp) :
    predictedMatrixAuxAmato c = .have := by
  simp [predictedMatrixAuxAmato, PersonAgreeSucceeds, VIsPhiActive, hSize]

/-- For *any* vP-complement transitive clause, Amato predicts HAVE:
    transitive v has person features, π-Agree succeeds. -/
theorem amato_vp_transitive_predicts_have (c : RestructuringClauseAmato)
    (hSize : c.complementSize = .vP)
    (hClass : c.base.embeddedClass = .transitive) :
    predictedMatrixAuxAmato c = .have := by
  simp [predictedMatrixAuxAmato, PersonAgreeSucceeds, VIsPhiActive, hSize, hClass]

/-- For *any* vP-complement reflexive clause with clitic climbing,
    Amato predicts BE: the φ-defective cliticized reflexive blocks
    π-Agree from valuing `Perf[π:_]`. -/
theorem amato_vp_reflexive_climbed_predicts_be (c : RestructuringClauseAmato)
    (hSize : c.complementSize = .vP)
    (hClass : c.base.embeddedClass = .reflexive)
    (hClimb : c.base.refCliticPos = .climbed) :
    predictedMatrixAuxAmato c = .be := by
  simp [predictedMatrixAuxAmato, PersonAgreeSucceeds, VIsPhiActive,
    hSize, hClass, hClimb]

/-! ## Bridge to the NestedAgree theory

    The translation builds an abstract `SyntacticObject` standing in
    for the Italian Perf+vP structure (Perf with vP complement; vP =
    DPsubj + v' = v + DPobj) and uses `validGoal` to mark v as
    φ-active iff `VIsPhiActive c` — the structural primitive both
    `PersonAgreeSucceeds` and the abstract NestedAgree machinery
    consume. The bridge theorem `personAgree_iff_runStack_hits` then
    proves that the abstract `runStack` outcome tracks the linguistic
    predicate by chasing through the shared primitive on a fixed
    `SyntacticObject` substrate (`cCommandsIn`, `containsOrEq`). -/

private def aT : LIToken := ⟨LexicalItem.simple .T [], 0⟩
private def aV : LIToken := ⟨LexicalItem.simple .V [], 1⟩
private def aDPsubj : LIToken := ⟨LexicalItem.simple .D [], 2⟩
private def aDPobj : LIToken := ⟨LexicalItem.simple .D [], 3⟩

private def perfProbe : ProbeProfile := ⟨.T, some .C⟩

/-- Translate an Amato clause to an abstract `NestedAgreeConfig` over
    a Minimalist `SyntacticObject`, using `NestedAgree.standardConfig`.
    Tree: `Perf [DPsubj [v DPobj]]`, goal = v. `validGoal` flags v as
    φ-active iff `VIsPhiActive c`; all other heads are phi-active. -/
def toNestedConfig (c : RestructuringClauseAmato) : NestedAgreeConfig :=
  standardConfig perfProbe aT aDPsubj aV aDPobj aV
    (fun y => if y = SyntacticObject.leaf aV then decide (VIsPhiActive c) else true)

/-- Every Amato clause whose v is φ-active yields a well-formed Nested
    Agree configuration. The precondition is structurally meaningful
    — `IsNestedAgreeConfig` requires `goalHead` (= v) to be in
    `initialDomain` (= Perf's c-command, filtered by `validGoal`); a
    φ-defective v has `validGoal (.leaf aV) = false` and is correctly
    excluded. This is the formal expression of @cite{amato-2025}'s
    "the chain breaks down at π-Agree" for unaccusative and
    vP-reflexive-with-climbing cases. -/
theorem amato_clause_is_nested (c : RestructuringClauseAmato)
    (h : PersonAgreeSucceeds c) :
    IsNestedAgreeConfig (toNestedConfig c) := by
  unfold IsNestedAgreeConfig NestedAgreeConfig.initialDomain
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · -- .leaf aV ∈ standardLinearTree _.subtrees: purely structural after unfold.
    show SyntacticObject.leaf aV ∈
      (standardLinearTree aT aDPsubj aV aDPobj).subtrees
    decide
  · -- (decide (cCommandsIn _ perf v) && validGoal v) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · -- Perf c-commands v in the standardLinearTree: purely structural.
      show decide (cCommandsIn (standardLinearTree aT aDPsubj aV aDPobj)
        (SyntacticObject.leaf aT) (SyntacticObject.leaf aV)) = true
      decide
    · -- validGoal (.leaf aV) = decide (VIsPhiActive c) = true (from h).
      show (decide (VIsPhiActive c)) = true
      exact decide_eq_true h

/-- Bridge: π-Agree succeeds iff `runStack` finds the goal at probe 1.
    Both sides reduce through the shared `VIsPhiActive` primitive on
    the same `SyntacticObject` substrate — the abstract Nested-Agree
    machinery faithfully models the linguistic predicate. The proof
    chases through `cCommandsIn`/`containsOrEq` on the
    `standardLinearTree` instance, not through a stipulated
    `daughters` field. -/
theorem personAgree_iff_runStack_hits (c : RestructuringClauseAmato) :
    PersonAgreeSucceeds c ↔ (runStack (toNestedConfig c) 1).isSome = true := by
  rw [runStack_some_iff]
  unfold PersonAgreeSucceeds
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- length = stack.length = 2 > 1: structural after unfold.
      show 1 < ([⟨.T, some .C⟩, ⟨.T, some .C⟩] : List ProbeProfile).length
      decide
    · -- goalHead ∈ searchDomain 1 = daughters; reflexively in its
      -- own daughters when phi-active.
      show SyntacticObject.leaf aV ∈ (toNestedConfig c).searchDomain 1
      rw [searchDomain_succ]
      exact goalHead_mem_daughters _ (amato_clause_is_nested c h)
  · rintro ⟨_, hMem⟩
    -- hMem : goalHead ∈ daughters; the filter requires validGoal,
    -- which reduces to `decide (VIsPhiActive c)`.
    rw [searchDomain_succ] at hMem
    show VIsPhiActive c
    have hMemFilter := (List.mem_filter.mp hMem).2
    rw [Bool.and_eq_true] at hMemFilter
    -- hMemFilter.2 : validGoal (.leaf aV) = true
    --             ≡ decide (VIsPhiActive c) = true
    exact of_decide_eq_true hMemFilter.2

/-! ## Bridge to @cite{olivier-2026}: agreement and divergence -/

/-- On the canonical AS configuration — modal + compound + reflexive
    + climbed clitic + vP complement — both theories predict BE. The
    interconnection-density payoff: where the empirical generalization
    is robust, the two theories converge by construction at the surface,
    regardless of disagreement about mechanism. -/
theorem amato2025_olivier_agree_on_canonical :
    predictedMatrixAuxAmato beModalReflexiveClimbedVP =
    predictedMatrixAux beWantReflexiveClimbed := by decide

/-- On the same modal + compound + reflexive + climbed clitic
    configuration but with a TP-sized complement, Amato predicts HAVE
    (the embedded T closes the chain) while Olivier predicts BE (the
    climbed reflexive equates ID across matrix and embedded domains; the
    complement size is invisible to ID-matching). This is the empirical
    wedge between the two theories. -/
theorem amato2025_olivier_diverge_on_tp_complement :
    predictedMatrixAuxAmato haveModalReflexiveClimbedTP ≠
    predictedMatrixAux beWantReflexiveClimbed := by decide

end Phenomena.AuxiliaryVerbs.Studies.Amato2025
