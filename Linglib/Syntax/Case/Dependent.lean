import Linglib.Features.Case.Basic
import Linglib.Features.Case.Capabilities
import Linglib.Features.Case.Source

/-!
# Dependent case

This file defines the configurational case algorithm of [marantz-1991], in
the form [baker-2015] gives it. Case is read off the arrangement of NPs in
a Spell-Out domain under a disjunctive priority hierarchy: lexical case
assigned by a particular head outranks dependent case, assigned to an NP
standing in a c-command relation with another caseless NP, which in turn
outranks the unmarked default. Which case the dependent rule assigns is the
alignment parameter — accusative on the lower NP, ergative on the higher, or
both at once in a tripartite system.

`assignCases` runs the hierarchy over a flat Spell-Out domain, list position
encoding c-command. `assignCasesPhased` runs the two-cycle variant of
[baker-vinokurova-2010], in which the configurational rules apply once per
phase and Agree with a functional head values whatever they leave unmarked.
`CaseSystemConfig` selects a mechanism per case, so a purely configurational
grammar, a purely Agree-based one ([chomsky-2000]), and the mixed grammars
in between are parameterizations of a single algorithm rather than rival
formalisations.

## Main definitions

* `CaseSource`: how a case was assigned; `CaseSource.toNeutral` projects it
  onto the account-neutral `Case.Source`.
* `CaseLanguageType`: the alignment parameter fixing the dependent and
  unmarked cases.
* `NPInDomain`, `CasedNP`: an NP before and after case assignment.
* `assignCases`: the one-pass algorithm over a Spell-Out domain.
* `structuralCasesFor`: the cases the algorithm can assign to a caseless NP.
* `CaseSystemConfig`: per-case choice of assignment mechanism.
* `PhasedNP`, `assignCasesPhased`: the two-cycle algorithm.

## Main results

* `lexical_bleeds_dependent`: lexical case pre-empts the dependent rule.
* `nonlexical_case_mem_structuralCasesFor`: the algorithm assigns a caseless
  NP only cases its alignment type admits.
* `assignCases_length`, `assignCasesPhased_length`: both algorithms are
  total — one `CasedNP` per input NP.
* `dat_persists_through_assignCasesPhased`: the Elsewhere ordering of the
  dative rule over the accusative rule is structural, not a stipulated rule
  ordering.

## Implementation notes

List position encodes structural height: earlier is higher, and c-commands
everything later. NP identity is carried by a `String` label, which
`getCaseOf` and `getSourceOf` look up; the labels are inert for the
algorithm, which reads only the lexical-case field and list position.

## References

* [marantz-1991]
* [baker-2015]
* [baker-vinokurova-2010]
-/

namespace Syntax.Case

/-! ### Case sources -/

/-- The mechanism that assigned a case, ordered by priority: `lexical`
    (a specific head, e.g. P or inherent V case) outranks `dependent`
    (structural configuration), which outranks `unmarked` (the default).
    `agree` is the Chomskyan alternative to `dependent`, valuation by a
    functional head. -/
inductive CaseSource where
  | lexical
  | dependent
  | unmarked
  | agree
  deriving DecidableEq, Repr

/-- The account-neutral provenance of a dependent-case source: configural
    and Agree-valued cases are `structural`, lexical is `inherent`, and
    unmarked is `default`. -/
def CaseSource.toNeutral : CaseSource → _root_.Case.Source
  | .lexical => .inherent
  | .dependent => .structural
  | .unmarked => .default
  | .agree => .structural

/-- Dependent case is total: no source it produces is the crash `uncased`,
    unlike the hybrid licensing of `Licensing.LicensingOutcome`. -/
theorem CaseSource.toNeutral_ne_uncased (s : CaseSource) :
    s.toNeutral ≠ _root_.Case.Source.uncased := by
  cases s <;> decide

/-! ### Alignment types -/

/-- The alignment parameter, fixing which case the dependent rule assigns
    and which case is the default: accusative (dependent ACC on the lower
    NP, unmarked NOM), ergative (dependent ERG on the higher NP, unmarked
    ABS), or tripartite (both dependent rules active, unmarked ABS). -/
inductive CaseLanguageType where
  | accusative
  | ergative
  | tripartite
  deriving DecidableEq, Repr

/-! ### Spell-Out domains -/

/-- An NP in a Spell-Out domain, before case assignment. `lexicalCase` is
    `some c` when a P or V head has pre-assigned case `c`. -/
structure NPInDomain where
  /-- Label identifying this NP. -/
  label : String
  /-- Case pre-assigned by a P or V head, e.g. ablative from Japanese *kara*. -/
  lexicalCase : Option Case
  deriving DecidableEq, Repr

/-- An NP after case assignment, carrying its case and the source that
    assigned it. -/
structure CasedNP where
  /-- Label identifying this NP, inherited from its `NPInDomain`. -/
  label : String
  /-- The assigned case. -/
  case : Case
  /-- The mechanism that assigned it. -/
  source : CaseSource
  deriving DecidableEq, Repr

instance : HasCase CasedNP := ⟨fun np => some np.case⟩

/-- The case assigned to the NP labelled `label`, if any. -/
def getCaseOf (label : String) (results : List CasedNP) : Option Case :=
  (results.find? (·.label == label)).bind HasCase.caseOf

/-- The source of the case assigned to the NP labelled `label`, if any. -/
def getSourceOf (label : String) (results : List CasedNP) : Option CaseSource :=
  (results.find? (·.label == label)).map (·.source)

/-! ### The dependent case rules -/

/-- Some NP in the list has no lexical case, and so can serve as the
    caseless competitor a dependent rule needs. -/
def anyLacksCaseIn (nps : List NPInDomain) : Bool :=
  nps.any (·.lexicalCase.isNone)

/-- Dependent accusative: a caseless NP c-commanded by a caseless NP gets
    ACC. `higherNPs` are the NPs c-commanding `np`. -/
def dependentAccusative (higherNPs : List NPInDomain) (np : NPInDomain) : Option Case :=
  if np.lexicalCase.isNone && anyLacksCaseIn higherNPs then some .acc else none

/-- Dependent ergative: a caseless NP c-commanding a caseless NP gets ERG.
    `lowerNPs` are the NPs `np` c-commands. -/
def dependentErgative (np : NPInDomain) (lowerNPs : List NPInDomain) : Option Case :=
  if np.lexicalCase.isNone && anyLacksCaseIn lowerNPs then some .erg else none

/-- The default case an alignment type assigns to an NP no other rule
    reached: NOM in an accusative language, ABS otherwise. -/
def unmarkedCaseFor : CaseLanguageType → Case
  | .accusative => .nom
  | .ergative => .abs
  | .tripartite => .abs

/-! ### One-pass case assignment -/

/-- Case for one NP, given the NPs above and below it: lexical case if it
    has any, else the dependent case its alignment type licenses, else the
    unmarked default. A tripartite language tries ergative before
    accusative, so an NP with a caseless competitor on both sides — the
    middle NP of a caseless triple — surfaces as ERG. -/
def assignOneCase (lang : CaseLanguageType) (higherNPs lowerNPs : List NPInDomain)
    (np : NPInDomain) : CasedNP :=
  let cased c src : CasedNP := { label := np.label, case := c, source := src }
  let unmarked := cased (unmarkedCaseFor lang) .unmarked
  match np.lexicalCase with
  | some c => cased c .lexical
  | none =>
    match lang with
    | .accusative => ((dependentAccusative higherNPs np).map (cased · .dependent)).getD unmarked
    | .ergative => ((dependentErgative np lowerNPs).map (cased · .dependent)).getD unmarked
    | .tripartite =>
      (((dependentErgative np lowerNPs).orElse fun _ => dependentAccusative higherNPs np).map
        (cased · .dependent)).getD unmarked

/-- `assignCases`, with the already-processed NPs accumulated in `higher`. -/
private def assignCasesGo (lang : CaseLanguageType) (higher : List NPInDomain) :
    List NPInDomain → List CasedNP
  | [] => []
  | np :: rest => assignOneCase lang higher rest np :: assignCasesGo lang (higher ++ [np]) rest

/-- Case for every NP in a Spell-Out domain. List order encodes structural
    height: the first NP is highest and c-commands all the others. -/
def assignCases (lang : CaseLanguageType) (nps : List NPInDomain) : List CasedNP :=
  assignCasesGo lang [] nps

private theorem assignCasesGo_length (lang : CaseLanguageType)
    (higher nps : List NPInDomain) : (assignCasesGo lang higher nps).length = nps.length := by
  induction nps generalizing higher with
  | nil => rfl
  | cons _ _ ih => simp [assignCasesGo, ih]

/-- The one-pass algorithm is total: exactly one `CasedNP` per input NP. -/
@[simp] theorem assignCases_length (lang : CaseLanguageType) (nps : List NPInDomain) :
    (assignCases lang nps).length = nps.length :=
  assignCasesGo_length lang [] nps

/-! ### Priority and alignment -/

/-- An NP with lexical case keeps it, whatever the configuration. -/
theorem lexical_bleeds_dependent (lang : CaseLanguageType) (c : Case) (label : String)
    (higherNPs lowerNPs : List NPInDomain) :
    (assignOneCase lang higherNPs lowerNPs
      { label := label, lexicalCase := some c }).source = .lexical := by
  cases lang <;> rfl

/-- Dependent accusative needs only two caseless NPs in one domain, not an
    agentive Voice head; cf. `Scott2023.dependent_case_ignores_voice`. -/
theorem no_voice_needed_for_acc :
    let nps : List NPInDomain :=
      [ { label := "subj", lexicalCase := none },
        { label := "obj", lexicalCase := none } ]
    getCaseOf "obj" (assignCases .accusative nps) = some .acc ∧
    getSourceOf "obj" (assignCases .accusative nps) = some .dependent := by decide

/-- Two caseless NPs in an ergative language: the higher gets dependent ERG
    and the lower unmarked ABS, mirroring the accusative pattern. -/
theorem ergative_mirror :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .ergative nps) = some .erg ∧
    getCaseOf "lower" (assignCases .ergative nps) = some .abs := by decide

/-- A lone caseless NP in an accusative language gets unmarked NOM: with no
    competitor, no dependent case arises. -/
theorem single_np_nom :
    let nps : List NPInDomain := [ { label := "sole", lexicalCase := none } ]
    getCaseOf "sole" (assignCases .accusative nps) = some .nom ∧
    getSourceOf "sole" (assignCases .accusative nps) = some .unmarked := by decide

/-- A tripartite transitive marks the higher NP ERG and the lower ACC, and
    a tripartite intransitive marks its sole NP ABS. -/
theorem tripartite_transitive_and_intransitive :
    let tr : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    let intr : List NPInDomain := [ { label := "sole", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .tripartite tr) = some .erg ∧
    getCaseOf "lower" (assignCases .tripartite tr) = some .acc ∧
    getCaseOf "sole" (assignCases .tripartite intr) = some .abs := by decide

/-- Tripartite alignment subsumes both others: its higher NP gets the case
    an ergative language would assign, its lower NP the case an accusative
    language would. -/
theorem tripartite_subsumes_both :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .tripartite nps) =
      getCaseOf "higher" (assignCases .ergative nps) ∧
    getCaseOf "lower" (assignCases .tripartite nps) =
      getCaseOf "lower" (assignCases .accusative nps) := by decide

/-! ### The structural case inventory -/

/-- The cases the algorithm can assign to an NP without lexical case. -/
def structuralCasesFor : CaseLanguageType → List Case
  | .accusative => [.nom, .acc]
  | .ergative => [.abs, .erg]
  | .tripartite => [.abs, .erg, .acc]

/-- A caseless NP receives one of the cases its alignment type admits. -/
theorem nonlexical_case_mem_structuralCasesFor (lang : CaseLanguageType)
    (higherNPs lowerNPs : List NPInDomain) (np : NPInDomain) (h : np.lexicalCase = none) :
    (assignOneCase lang higherNPs lowerNPs np).case ∈ structuralCasesFor lang := by
  cases lang <;>
    by_cases hh : anyLacksCaseIn higherNPs <;> by_cases hl : anyLacksCaseIn lowerNPs <;>
    simp [assignOneCase, dependentAccusative, dependentErgative, structuralCasesFor,
      unmarkedCaseFor, h, hh, hl]

/-! ### Per-case assignment mechanisms -/

/-- How nominative is assigned: by Agree with finite T, or as the elsewhere
    default. [baker-vinokurova-2010] argue for the former in Sakha, and
    [gong-2022] for Mongolian. -/
inductive NomAssignment where
  | agreeT
  | unmarkedDefault
  deriving DecidableEq, Repr

/-- How dative is assigned: as dependent case, or nonstructurally, in which
    case it neither competes for dependent case nor is available at
    intermediate positions ([gong-2022] on Mongolian). -/
inductive DatAssignment where
  | nonstructural
  | dependent
  deriving DecidableEq, Repr

/-- How accusative is assigned: as dependent case ([marantz-1991]), or by
    Agree with v ([chomsky-2000]). -/
inductive AccAssignment where
  | dependent
  | agreeV
  deriving DecidableEq, Repr

/-- How genitive is assigned: by Agree with D, the DP-internal counterpart
    of T-Agree ([baker-vinokurova-2010]), or nonstructurally, as in the
    Russian numeric and partitive genitives. -/
inductive GenAssignment where
  | agreeD
  | nonstructural
  deriving DecidableEq, Repr

/-- A grammar's choice of mechanism for each structural case, alongside its
    alignment type. A purely configurational grammar takes `unmarkedDefault`
    nominative with `dependent` accusative and dative; a purely Agree-based
    one takes `agreeT`, `agreeD`, `agreeV` and nonstructural dative; the
    Sakha grammar of [baker-vinokurova-2010] mixes the two, valuing
    nominative and genitive by Agree but accusative and dative
    configurationally. -/
structure CaseSystemConfig where
  /-- The alignment type, fixing the dependent and unmarked cases. -/
  langType : CaseLanguageType
  /-- How nominative is assigned. -/
  nomMode : NomAssignment
  /-- How dative is assigned. -/
  datMode : DatAssignment
  /-- How accusative is assigned. -/
  accMode : AccAssignment := .dependent
  /-- How genitive is assigned. -/
  genMode : GenAssignment := .agreeD
  deriving DecidableEq, Repr

/-! ### Phased case assignment -/

/-- The cycle a case rule applies on, in the two-phase model: the VP phase
    or the CP phase. Coarser than `Minimalist.Phase`, which the case
    algorithm does not need. -/
inductive CasePhase where
  | vp
  | cp
  deriving DecidableEq, Repr

/-- An NP carrying the phase information the cyclic algorithm reads:
    where it was merged, whether it moved to a higher phase before case was
    evaluated, whether it is a case competitor at all, and whether it is
    DP-internal. -/
structure PhasedNP extends NPInDomain where
  /-- The phase the NP was merged in. -/
  basePhase : CasePhase
  /-- The NP moved to a higher phase before case was evaluated. -/
  shifted : Bool := false
  /-- The NP bears a θ-role with respect to some case assigner. Bare-NP
      adverbs do not, and so are not competitors for the dependent rules. -/
  isArgumental : Bool := true
  /-- The NP is a DP-internal possessor, invisible to the clausal passes and
      valued instead by D-Agree. -/
  inDP : Bool := false
  deriving DecidableEq, Repr

/-- Every VP-merged NP is visible on the VP cycle: shift happens at the
    boundary between cycles. -/
def PhasedNP.visibleOnVP (p : PhasedNP) : Bool := p.basePhase == .vp

/-- An NP is visible on the CP cycle when it was merged there or shifted out
    of VP; an unshifted VP-internal NP has been transferred. -/
def PhasedNP.visibleOnCP (p : PhasedNP) : Bool :=
  p.basePhase == .cp || p.shifted

/-- An NP part-way through the derivation. `case = none` means not yet
    valued; lexical case is valued from the start. -/
structure PhasedState where
  /-- The NP being valued. -/
  np : PhasedNP
  /-- Its case and the source that valued it, once some pass has. -/
  case : Option (Case × CaseSource)
  deriving DecidableEq, Repr

/-- The NP has been valued, by any mechanism. The dependent rules apply
    only to unmarked NPs, which is what makes their ordering an Elsewhere
    ordering rather than a stipulation. -/
def PhasedState.marked (s : PhasedState) : Bool := s.case.isSome

/-- Value lexical case from each NP, leaving everything else unmarked. -/
def initStates (nps : List PhasedNP) : List PhasedState :=
  nps.map fun p => { np := p, case := p.lexicalCase.map (fun c => (c, .lexical)) }

/-- Value the NP at index `i` as `c` from source `src`. -/
def setCaseAt (i : Nat) (c : Case) (src : CaseSource)
    (states : List PhasedState) : List PhasedState :=
  states.modify i fun s => { s with case := some (c, src) }

/-- The state is a candidate for a case rule on this cycle: visible,
    argumental, clause-level, and not yet valued. -/
def unmarkedEligible (cycle : CasePhase) (s : PhasedState) : Bool :=
  let visible := match cycle with
    | .vp => s.np.visibleOnVP
    | .cp => s.np.visibleOnCP
  visible && s.np.isArgumental && !s.np.inDP && !s.marked

/-- The indices of the states eligible on a cycle, highest first. -/
def unmarkedVisible (cycle : CasePhase) (states : List PhasedState) : List Nat :=
  states.zipIdx.filterMap fun p => if unmarkedEligible cycle p.1 then some p.2 else none

/-- The dative rule: on the VP cycle, an NP c-commanding another unmarked NP
    is valued dative. Its context is the more restrictive one, so it bleeds
    the accusative rule on that cycle. -/
def applyDatRule (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  if cfg.datMode != .dependent then states
  else match unmarkedVisible .vp states with
    | i :: _ :: _ => setCaseAt i .dat .dependent states
    | _ => states

/-- The accusative rule: on either cycle, an NP c-commanded by another
    unmarked NP is valued accusative. -/
def applyAccRule (cfg : CaseSystemConfig) (cycle : CasePhase)
    (states : List PhasedState) : List PhasedState :=
  if cfg.accMode != .dependent then states
  else match (unmarkedVisible cycle states).reverse with
    | last :: _ :: _ => setCaseAt last .acc .dependent states
    | _ => states

/-- v-Agree: v probes into its complement and values the closest unmarked
    goal accusative. The Chomskyan alternative to `applyAccRule`; `accMode`
    makes the two mutually exclusive. -/
def applyAccAgree (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  match cfg.accMode with
  | .agreeV =>
    match (unmarkedVisible .cp states).reverse with
    | last :: _ => setCaseAt last .acc .agree states
    | [] => states
  | .dependent => states

/-- T-Agree: T values the highest unmarked NP visible at CP nominative. -/
def applyNomAgree (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  match cfg.nomMode with
  | .agreeT =>
    match unmarkedVisible .cp states with
    | first :: _ => setCaseAt first .nom .agree states
    | [] => states
  | .unmarkedDefault => states

/-- D-Agree: each D values its unmarked possessor genitive. The clausal
    passes see a DP as opaque, so this is the only pass that reaches inside
    one. -/
def applyGenAgree (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  match cfg.genMode with
  | .agreeD =>
    states.map fun s =>
      if s.np.inDP && !s.marked then { s with case := some (.gen, .agree) } else s
  | .nonstructural => states

/-- The last-resort sweep: every still-unmarked NP takes the unmarked case
    of its alignment type. -/
def applyDefault (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  states.map fun s =>
    if s.marked then s else { s with case := some (unmarkedCaseFor cfg.langType, .unmarked) }

/-- The valued NP, or `none` if no pass reached it. -/
def PhasedState.toCased (s : PhasedState) : Option CasedNP :=
  s.case.map fun (c, src) => { label := s.np.label, case := c, source := src }

/-- The two-cycle algorithm: the dative then accusative rule on the VP
    cycle, the accusative rule again on the CP cycle, then the Agree probes,
    then the default sweep. The dependent rules and their Agree counterparts
    are gated on disjoint `CaseSystemConfig` settings, so their relative
    order matters only where neither fires. -/
def assignCasesPhased (cfg : CaseSystemConfig) (nps : List PhasedNP) : List CasedNP :=
  let s0 := initStates nps
  let s1 := applyDatRule cfg s0
  let s2 := applyAccRule cfg .vp s1
  let s3 := applyAccRule cfg .cp s2
  let s4 := applyAccAgree cfg s3
  let s5 := applyNomAgree cfg s4
  let s6 := applyGenAgree cfg s5
  let s7 := applyDefault cfg s6
  s7.filterMap PhasedState.toCased

/-! ### Totality of the phased algorithm -/

@[simp] theorem initStates_length (nps : List PhasedNP) :
    (initStates nps).length = nps.length := List.length_map ..

@[simp] theorem setCaseAt_length (i : Nat) (c : Case) (src : CaseSource)
    (states : List PhasedState) :
    (setCaseAt i c src states).length = states.length := List.length_modify ..

@[simp] theorem applyDatRule_length (cfg : CaseSystemConfig) (states : List PhasedState) :
    (applyDatRule cfg states).length = states.length := by
  unfold applyDatRule; split <;> [rfl; (split <;> simp)]

@[simp] theorem applyAccRule_length (cfg : CaseSystemConfig) (cycle : CasePhase)
    (states : List PhasedState) :
    (applyAccRule cfg cycle states).length = states.length := by
  unfold applyAccRule; split <;> [rfl; (split <;> simp)]

@[simp] theorem applyAccAgree_length (cfg : CaseSystemConfig) (states : List PhasedState) :
    (applyAccAgree cfg states).length = states.length := by
  unfold applyAccAgree; split <;> [(split <;> simp); rfl]

@[simp] theorem applyNomAgree_length (cfg : CaseSystemConfig) (states : List PhasedState) :
    (applyNomAgree cfg states).length = states.length := by
  unfold applyNomAgree; split <;> [(split <;> simp); rfl]

@[simp] theorem applyGenAgree_length (cfg : CaseSystemConfig) (states : List PhasedState) :
    (applyGenAgree cfg states).length = states.length := by
  unfold applyGenAgree; split <;> simp

@[simp] theorem applyDefault_length (cfg : CaseSystemConfig) (states : List PhasedState) :
    (applyDefault cfg states).length = states.length := List.length_map ..

/-- The default sweep leaves nothing unvalued. -/
theorem applyDefault_all_some (cfg : CaseSystemConfig) (states : List PhasedState) :
    ∀ s ∈ applyDefault cfg states, s.case.isSome := by
  intro s hs
  simp only [applyDefault, List.mem_map] at hs
  obtain ⟨t, _, rfl⟩ := hs
  unfold PhasedState.marked
  split <;> simp_all

@[simp] private theorem toCased_isSome (s : PhasedState) :
    s.toCased.isSome = s.case.isSome := by
  unfold PhasedState.toCased; cases s.case <;> rfl

/-- The phased algorithm is total: exactly one `CasedNP` per input NP, none
    dropped and none duplicated. -/
theorem assignCasesPhased_length (cfg : CaseSystemConfig) (nps : List PhasedNP) :
    (assignCasesPhased cfg nps).length = nps.length := by
  rw [assignCasesPhased, List.filterMap_length_eq_length.mpr
    (fun s hs => by simpa using applyDefault_all_some _ _ s hs)]
  simp

/-! ### Valued NPs are never overwritten -/

/-- Every index a cycle offers a case rule points at an unvalued state. -/
private theorem unmarkedVisible_unmarked {cycle : CasePhase} {states : List PhasedState}
    {i : Nat} (h : i ∈ unmarkedVisible cycle states) :
    ∃ s, states[i]? = some s ∧ s.marked = false := by
  rw [unmarkedVisible, List.mem_filterMap] at h
  obtain ⟨⟨s, k⟩, hmem, hcond⟩ := h
  rw [List.mem_zipIdx_iff_getElem?] at hmem
  by_cases hg : unmarkedEligible cycle s
  · obtain rfl := Option.some.inj (if_pos hg ▸ hcond)
    exact ⟨s, hmem, by simp_all [unmarkedEligible]⟩
  · rw [if_neg hg] at hcond; cases hcond

/-- A pass that either leaves the states alone or rewrites a single index
    drawn from `unmarkedVisible` cannot overwrite a valued NP. This is the
    structural content of the Elsewhere ordering: `unmarkedVisible` filters
    valued states out, so no later rule can reach one. -/
private theorem getElem?_of_spec {cycle : CasePhase} {states out : List PhasedState}
    {i : Nat} {s : PhasedState} (h_get : states[i]? = some s) (h_marked : s.marked)
    (hspec : out = states ∨
      ∃ j ∈ unmarkedVisible cycle states, ∃ f, out = states.modify j f) :
    out[i]? = some s := by
  obtain rfl | ⟨j, hj, f, rfl⟩ := hspec
  · exact h_get
  · obtain ⟨s', hs', hs'_unmarked⟩ := unmarkedVisible_unmarked hj
    have hne : j ≠ i := by rintro rfl; rw [h_get] at hs'; cases hs'; simp_all
    rw [List.getElem?_modify_ne _ _ hne]; exact h_get

private theorem applyAccRule_spec (cfg : CaseSystemConfig) (cycle : CasePhase)
    (states : List PhasedState) :
    applyAccRule cfg cycle states = states ∨
      ∃ j ∈ unmarkedVisible cycle states, ∃ f,
        applyAccRule cfg cycle states = states.modify j f := by
  unfold applyAccRule
  split
  · exact .inl rfl
  · split
    case h_1 last _ _ heq =>
      have : last ∈ (unmarkedVisible cycle states).reverse := by
        rw [heq]; exact List.mem_cons_self ..
      exact .inr ⟨last, by simpa using this, _, rfl⟩
    case h_2 => exact .inl rfl

private theorem applyAccAgree_spec (cfg : CaseSystemConfig) (states : List PhasedState) :
    applyAccAgree cfg states = states ∨
      ∃ j ∈ unmarkedVisible .cp states, ∃ f, applyAccAgree cfg states = states.modify j f := by
  unfold applyAccAgree
  split
  · split
    case h_1 last _ heq =>
      have : last ∈ (unmarkedVisible .cp states).reverse := by rw [heq]; exact List.mem_cons_self ..
      exact .inr ⟨last, by simpa using this, _, rfl⟩
    case h_2 => exact .inl rfl
  · exact .inl rfl

private theorem applyNomAgree_spec (cfg : CaseSystemConfig) (states : List PhasedState) :
    applyNomAgree cfg states = states ∨
      ∃ j ∈ unmarkedVisible .cp states, ∃ f, applyNomAgree cfg states = states.modify j f := by
  unfold applyNomAgree
  split
  · split
    case h_1 first _ heq => exact .inr ⟨first, heq ▸ List.mem_cons_self .., _, rfl⟩
    case h_2 => exact .inl rfl
  · exact .inl rfl

/-- The accusative rule never overwrites a valued NP. -/
theorem applyAccRule_preserves_marked_at (cfg : CaseSystemConfig)
    (cycle : CasePhase) (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyAccRule cfg cycle states)[i]? = some s :=
  getElem?_of_spec h_get h_marked (applyAccRule_spec cfg cycle states)

/-- v-Agree never overwrites a valued NP. -/
theorem applyAccAgree_preserves_marked_at (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyAccAgree cfg states)[i]? = some s :=
  getElem?_of_spec h_get h_marked (applyAccAgree_spec cfg states)

/-- T-Agree never overwrites a valued NP. -/
theorem applyNomAgree_preserves_marked_at (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyNomAgree cfg states)[i]? = some s :=
  getElem?_of_spec h_get h_marked (applyNomAgree_spec cfg states)

/-- D-Agree never overwrites a valued NP. -/
theorem applyGenAgree_preserves_marked_at (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyGenAgree cfg states)[i]? = some s := by
  unfold applyGenAgree
  split
  · rw [List.getElem?_map, h_get]; simp [h_marked]
  · exact h_get

/-- The default sweep never overwrites a valued NP. -/
theorem applyDefault_preserves_marked_at (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyDefault cfg states)[i]? = some s := by
  rw [applyDefault, List.getElem?_map, h_get]; simp [h_marked]

/-- A dative valued by the dative rule survives every later pass, so the
    Elsewhere ordering of the dative rule over the accusative rule is a
    consequence of how the passes read `unmarkedVisible`, not a stipulated
    rule ordering. -/
theorem dat_persists_through_assignCasesPhased (cfg : CaseSystemConfig)
    (nps : List PhasedNP) (i : Nat) (s : PhasedState)
    (h_get : (applyDatRule cfg (initStates nps))[i]? = some s)
    (h_dat : s.case = some (.dat, .dependent)) :
    let s0 := initStates nps
    let s1 := applyDatRule cfg s0
    let s2 := applyAccRule cfg .vp s1
    let s3 := applyAccRule cfg .cp s2
    let s4 := applyAccAgree cfg s3
    let s5 := applyNomAgree cfg s4
    let s6 := applyGenAgree cfg s5
    let s7 := applyDefault cfg s6
    s7[i]? = some s := by
  have h_marked : s.marked = true := by rw [PhasedState.marked, h_dat]; rfl
  exact applyDefault_preserves_marked_at cfg _ i s
    (applyGenAgree_preserves_marked_at cfg _ i s
      (applyNomAgree_preserves_marked_at cfg _ i s
        (applyAccAgree_preserves_marked_at cfg _ i s
          (applyAccRule_preserves_marked_at cfg .cp _ i s
            (applyAccRule_preserves_marked_at cfg .vp _ i s h_get h_marked)
            h_marked) h_marked) h_marked) h_marked) h_marked

end Syntax.Case
