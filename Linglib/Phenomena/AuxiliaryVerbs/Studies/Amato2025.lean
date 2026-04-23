import Linglib.Phenomena.AuxiliaryVerbs.Selection
import Linglib.Phenomena.AuxiliaryVerbs.Studies.Olivier2026
import Linglib.Theories.Syntax.Minimalism.NestedAgree

/-!
# @cite{amato-2025} — Italian auxiliary selection via Nested Agree
@cite{amato-2023}

@cite{amato-2025} (NLLT) advances *Nested Agree* — the configuration of
ordered probes plus maximized matching, formalized at
`Theories/Syntax/Minimalism/NestedAgree.lean` — as a unifying account
across at least six syntactic phenomena:

- Italian auxiliary selection (this file).
- Case + agreement alignments in ditransitives.
- Dative intervention in Icelandic biclausal sentences.
- φ-agreement on the perfective in Lak.
- Subject φ-agreement in Spanish VOS clauses.
- Multiple wh-fronting in Bulgarian, via Merge features.

The paper is also explicit about what is *not* a Nested-Agree
configuration: Italian past participle agreement requires Edge Features,
not Nested Agree. This file consumes only the §3 Italian auxiliary slot;
the other applications are deferred.

## Italian auxiliary selection (§3)

In Standard Italian, the perfect head Perf bears two ordered probes:
`[*Infl:perf*] ≻ [*π:_*]`. Infl-Agree fires first (Perf agrees with the
v head for [Infl]); π-Agree fires second, restricted by Nested Agree to
the daughters of v. Under this restriction the higher subject is
*outside* π-Agree's search domain — there is no minimality violation,
even though the lower argument controls the auxiliary form.

When the lower v is φ-defective (unaccusatives) or φ-defective-via-
clitic (reflexives), π-Agree on Perf fails to value `[*π:_*]`. The DM
elsewhere allomorph BE then surfaces; HAVE is the more specific
allomorph inserted whenever π is valued.

## Complement size (precursor: @cite{amato-2024})

The complement-size argument — vP vs TP — is the key contribution of
@cite{amato-2024} and is preserved here as the structural lever for
restructuring optionality. With a TP complement, the embedded T is the
closest goal for π-Agree; the chain bottoms out at T (HAVE). With a vP
complement, the chain reaches v (BE under defectiveness conditions).

## Relation to @cite{olivier-2026}

Both theories agree on the canonical AS configuration (modal + compound
+ reflexive + climbed). They diverge on the TP-complement reflexive:
Amato predicts HAVE (T closes the chain), Olivier predicts BE (climbed
reflexive equates ID across domains regardless of complement size). The
divergence is preserved at the bottom of this file, with the prediction
inverted to track the new framework.

## DM elsewhere inversion (vs @cite{olivier-2026})

@cite{amato-2025}: HAVE = `Perf[π:α]`, BE = elsewhere. @cite{olivier-2026}
inverts: HAVE = elsewhere, BE = `T[ID:α] = vAux[ID:α]`. This file follows
the Amato convention.
-/

namespace Phenomena.AuxiliaryVerbs.Studies.Amato2025

open Phenomena.AuxiliaryVerbs.Selection
open Phenomena.AuxiliaryVerbs.Studies.Olivier2026
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

/-! ## Bridge to the NestedAgree theory -/

/-- Translate an Amato clause to an abstract `NestedAgreeConfig`.

    Token alphabet: `0` = DPsubj, `1` = the lower v (the shared goal),
    `2` = DPobj (or the cliticized reflexive). Probe 0 = Infl-Agree;
    probe 1 = π-Agree.

    The `daughters` function — v's reachable subtree — is derived from
    the structural primitive `VIsPhiActive`: a φ-defective v is *not*
    reachable as a goal, so it does not appear in its own daughters.
    This is *not* "encode the answer (PersonAgreeSucceeds) into the
    config"; both `daughters` and `PersonAgreeSucceeds` derive from the
    common structural primitive `VIsPhiActive`, which reads independent
    clause data (complement size, verb class, clitic position).

    `searchDomain` is now derived (`Theories/Syntax/Minimalism/NestedAgree.lean`),
    not stipulated as a field. The matryoshka follows by `rfl`. -/
def toNestedConfig (c : RestructuringClauseAmato) : NestedAgreeConfig where
  stack := [⟨.T, some .C⟩, ⟨.T, some .C⟩]
  goalLabel := 1
  daughters
    | 1 => if VIsPhiActive c then [1, 2] else [2]
    | _ => []
  initialDomain := [0, 1, 2]

/-- Every Amato clause yields a well-formed Nested Agree configuration
    *under the precondition that v is φ-active*. The precondition is
    structurally meaningful — it is exactly conjunct (B) of
    `IsNestedAgreeConfig` (the goal lies in its own daughters): a
    φ-defective v is not in `daughters 1`, so the configuration is
    correctly excluded from `IsNestedAgreeConfig`. That is the formal
    expression of @cite{amato-2025}'s "the chain breaks down at π-Agree"
    for unaccusative and vP-reflexive-with-climbing cases. -/
theorem amato_clause_is_nested (c : RestructuringClauseAmato)
    (h : PersonAgreeSucceeds c) :
    IsNestedAgreeConfig (toNestedConfig c) := by
  refine ⟨?_, ?_⟩
  · -- (A) goalLabel = 1 ∈ initialDomain = [0, 1, 2]
    show (1 : Token) ∈ ([0, 1, 2] : List Token); decide
  · -- (B) goalLabel = 1 ∈ daughters 1 = if VIsPhiActive c then [1,2] else [2]
    show (1 : Token) ∈ (if VIsPhiActive c then ([1, 2] : List Token) else [2])
    have h' : VIsPhiActive c := h
    rw [if_pos h']
    decide

/-- Bridge: π-Agree succeeds iff `runStack` finds the goal at probe 1.
    Both sides reduce through the shared `VIsPhiActive` primitive — the
    abstract Nested-Agree machinery faithfully tracks the linguistic
    predicate. *Not* a stipulation: `PersonAgreeSucceeds` and the
    `daughters` field of `toNestedConfig` derive from `VIsPhiActive`
    independently; this theorem documents that the abstraction is a
    faithful model. -/
theorem personAgree_iff_runStack_hits (c : RestructuringClauseAmato) :
    PersonAgreeSucceeds c ↔ (runStack (toNestedConfig c) 1).isSome = true := by
  rw [runStack_some_iff]
  unfold PersonAgreeSucceeds
  -- (toNestedConfig c).length = stack.length = 2; goalLabel = 1
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · show 1 < 2; decide
    · -- searchDomain 1 = daughters goalLabel = daughters 1
      --              = if VIsPhiActive c then [1,2] else [2]
      show (1 : Token) ∈ (if VIsPhiActive c then ([1, 2] : List Token) else [2])
      rw [if_pos h]; decide
  · rintro ⟨_, hMem⟩
    by_contra hne
    -- hMem : 1 ∈ (toNestedConfig c).searchDomain 1
    --      = (toNestedConfig c).daughters 1
    --      = if VIsPhiActive c then [1,2] else [2]
    -- ¬ VIsPhiActive c ⇒ branch is [2] ⇒ 1 ∉ [2]
    have hMem' : (1 : Token) ∈ (if VIsPhiActive c then ([1, 2] : List Token) else [2]) :=
      hMem
    rw [if_neg hne] at hMem'
    exact absurd hMem' (by decide)

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
