import Linglib.Theories.Syntax.Minimalism.Core.Agree

/-!
# Dependent Case Theory
@cite{marantz-1991} @cite{baker-2015} @cite{deal-2010} @cite{ozaki-2026} @cite{scott-2023}

Originally proposed by @cite{marantz-1991} as an alternative to Agree-based
case assignment; developed into a cross-linguistic algorithm by
@cite{baker-2015}. Case is determined by the structural configuration of
NPs within a Spell-Out domain:

1. **Lexical case**: Assigned by a particular head (P, V) — highest priority
2. **Dependent case**: Assigned to an NP that stands in a c-command
   relation with another caseless NP in the same domain
   - Accusative languages: lower NP gets ACC
   - Ergative languages: higher NP gets ERG
   - Tripartite languages: higher NP gets ERG *and* lower gets ACC
3. **Unmarked case**: Default for any NP still without case
   - Accusative languages: NOM
   - Ergative languages: ABS
   - Tripartite languages: ABS

## Tripartite Alignment

In tripartite systems (e.g., Nez Perce; @cite{deal-2010}), intransitive subjects
(S), transitive agents (A), and transitive patients (P) each receive
distinct case. Under dependent case, this follows from applying *both*
dependent ergative (to the higher NP) and dependent accusative (to the
lower NP) in the same domain, with ABS as the unmarked default (surfacing
only when no case competitor exists — i.e., intransitives).

**Note**: Not all tripartite systems use dependent case. SJA Mam
achieves tripartite alignment via inherent case from Voice (ERG for agents,
ACC for objects) plus structural case from Infl (ABS for intransitive S).
See `Fragments.Mayan.Mam.Agreement` for the Agree-based analysis.

## Key Application: @cite{ozaki-2026}

Japanese departure verbs (*hanareru* 'leave', *deru* 'exit') are dyadic
unaccusatives with two internal arguments and no thematic Voice. Accusative
*-o* on the source arises from dependent case (not from v/Voice), while
ablative *kara* is lexical case from an optional P head that bleeds
dependent accusative.

-/

namespace Minimalism

-- ============================================================================
-- § 1: Case Sources
-- ============================================================================

/-- The source of case assignment, ordered by priority.
    Lexical case (assigned by P, V) takes priority over dependent case,
    which takes priority over unmarked (default) case. -/
inductive CaseSource where
  | lexical    -- Assigned by a specific head (P, inherent V case)
  | dependent  -- Assigned by structural configuration (@cite{baker-2015})
  | unmarked   -- Default when no other case applies
  | agree      -- Assigned by Agree with a functional head T or D
               -- (@cite{chomsky-2000}; NOM/GEN in @cite{baker-vinokurova-2010})
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Language Typology
-- ============================================================================

/-- Language type determines which dependent and unmarked cases are used.
    - Accusative: dependent = ACC (on lower NP), unmarked = NOM
    - Ergative: dependent = ERG (on higher NP), unmarked = ABS
    - Tripartite: dependent = ERG (on higher) + ACC (on lower), unmarked = ABS
      (@cite{scott-2023}: SJA Mam; cf. Nez Perce) -/
inductive CaseLanguageType where
  | accusative  -- Japanese, English, Romance, ...
  | ergative    -- Basque, Hindi (split), ...
  | tripartite  -- Nez Perce (@cite{deal-2010}), Warlpiri, ...
  deriving DecidableEq, Repr

-- ============================================================================
-- § 3: NP in a Spell-Out Domain
-- ============================================================================

/-- An NP within a Spell-Out domain, before case assignment.
    List position encodes structural height: earlier = higher = c-commands later.

    If a P head (e.g., Japanese *kara*) assigns lexical case to the NP,
    `lexicalCase` is `some c`; otherwise it is `none`. -/
structure NPInDomain where
  /-- Label identifying this NP -/
  label : String
  /-- Lexical case pre-assigned by a P or V head (e.g., ABL from *kara*) -/
  lexicalCase : Option CaseVal
  deriving DecidableEq, Repr

-- ============================================================================
-- § 4: Case Assignment Result
-- ============================================================================

/-- Result of case assignment: an NP with its case value and source. -/
structure CasedNP where
  label : String
  case : CaseVal
  source : CaseSource
  deriving DecidableEq, Repr

/-- Look up the assigned case for an NP by label. -/
def getCaseOf (label : String) (results : List CasedNP) : Option CaseVal :=
  (results.find? (·.label == label)).map (·.case)

/-- Look up the case source for an NP by label. -/
def getSourceOf (label : String) (results : List CasedNP) : Option CaseSource :=
  (results.find? (·.label == label)).map (·.source)

-- ============================================================================
-- § 5: Dependent Case Rules
-- ============================================================================

/-- Does any NP in the list lack lexical case?
    Used to check whether a dependent case competitor exists. -/
def anyLacksCaseIn (nps : List NPInDomain) : Bool :=
  nps.any (·.lexicalCase.isNone)

/-- Dependent accusative: assigned to an NP that is c-commanded by
    another caseless NP in the same domain.

    In our list representation, NP at index i is c-commanded by all NPs
    at index j < i. So NP_i gets ACC if it has no lexical case and
    some NP before it also has no lexical case. -/
def dependentAccusative (higherNPs : List NPInDomain) (np : NPInDomain) : Option CaseVal :=
  if np.lexicalCase.isNone && anyLacksCaseIn higherNPs then
    some .acc
  else
    none

/-- Dependent ergative: assigned to an NP that c-commands another caseless NP.
    NP_i gets ERG if it has no lexical case and some NP after it also
    has no lexical case. -/
def dependentErgative (np : NPInDomain) (lowerNPs : List NPInDomain) : Option CaseVal :=
  if np.lexicalCase.isNone && anyLacksCaseIn lowerNPs then
    some .erg
  else
    none

-- ============================================================================
-- § 6: Unmarked Case
-- ============================================================================

/-- Unmarked (default) case for a given language type.
    - Accusative languages: NOM
    - Ergative languages: ABS
    - Tripartite languages: ABS (only intransitive S gets unmarked case) -/
def unmarkedCaseFor (lang : CaseLanguageType) : CaseVal :=
  match lang with
  | .accusative => .nom
  | .ergative => .abs
  | .tripartite => .abs

-- ============================================================================
-- § 7: Full Algorithm
-- ============================================================================

/-- Assign case to a single NP given the NPs structurally above and below it.
    Applies the three-step priority: lexical → dependent → unmarked. -/
def assignOneCase (lang : CaseLanguageType) (higherNPs lowerNPs : List NPInDomain)
    (np : NPInDomain) : CasedNP :=
  match np.lexicalCase with
  | some c => { label := np.label, case := c, source := .lexical }
  | none =>
    match lang with
    | .accusative =>
      match dependentAccusative higherNPs np with
      | some c => { label := np.label, case := c, source := .dependent }
      | none => { label := np.label, case := unmarkedCaseFor lang, source := .unmarked }
    | .ergative =>
      match dependentErgative np lowerNPs with
      | some c => { label := np.label, case := c, source := .dependent }
      | none => { label := np.label, case := unmarkedCaseFor lang, source := .unmarked }
    | .tripartite =>
      -- Tripartite: both dependent ERG and ACC are active. An NP that
      -- c-commands a caseless NP gets ERG; an NP c-commanded by a caseless
      -- NP gets ACC. An NP with neither competitor gets unmarked ABS.
      match dependentErgative np lowerNPs with
      | some c => { label := np.label, case := c, source := .dependent }
      | none =>
        match dependentAccusative higherNPs np with
        | some c => { label := np.label, case := c, source := .dependent }
        | none => { label := np.label, case := unmarkedCaseFor lang, source := .unmarked }

/-- Assign case to all NPs in a Spell-Out domain.
    Processes the list left-to-right, maintaining context of higher NPs
    and remaining lower NPs for each position. -/
def assignCasesAux (lang : CaseLanguageType) (higher : List NPInDomain)
    (remaining : List NPInDomain) : List CasedNP :=
  match remaining with
  | [] => []
  | np :: rest =>
    let result := assignOneCase lang higher rest np
    result :: assignCasesAux lang (higher ++ [np]) rest

/-- Top-level case assignment for a list of NPs in a Spell-Out domain.
    List order encodes structural height:
    first = highest = c-commands all others. -/
def assignCases (lang : CaseLanguageType) (nps : List NPInDomain) : List CasedNP :=
  assignCasesAux lang [] nps

-- ============================================================================
-- § 8: Ozaki's Alternation — Worked Derivations
-- ============================================================================

/-! ## ACC Variant

"Taro-ga mura-o hanare-ta" (Taro-NOM village-ACC leave-PAST)

Two bare NPs in the TP Spell-Out domain:
- Leaver NP (higher, raised to Spec-TP)
- Source NP (lower, complement of V)
- Source gets dependent ACC; Leaver gets unmarked NOM -/

def accVariantNPs : List NPInDomain :=
  [ { label := "leaver", lexicalCase := none },
    { label := "source", lexicalCase := none } ]

def accVariantResult : List CasedNP :=
  assignCases .accusative accVariantNPs

/-! ## ABL Variant

"Taro-ga mura-kara hanare-ta" (Taro-NOM village-from leave-PAST)

One bare NP + one PP (lexical ABL from *kara*):
- Leaver NP (higher, raised to Spec-TP)
- Source PP (lower, *kara* assigns lexical ABL)
- Source has lexical ABL (bleeds dependent case); Leaver gets unmarked NOM -/

def ablVariantNPs : List NPInDomain :=
  [ { label := "leaver", lexicalCase := none },
    { label := "source", lexicalCase := some .abl } ]

def ablVariantResult : List CasedNP :=
  assignCases .accusative ablVariantNPs

-- ============================================================================
-- § 9: Verification Theorems
-- ============================================================================

/-- Lexical case bleeds dependent case: an NP with lexical case is never
    assigned dependent case, regardless of structural configuration. -/
theorem lexical_bleeds_dependent (lang : CaseLanguageType) (c : CaseVal)
    (higherNPs lowerNPs : List NPInDomain) :
    (assignOneCase lang higherNPs lowerNPs
      { label := "x", lexicalCase := some c }).source = .lexical := by
  cases lang <;> simp [assignOneCase]

/-- ACC variant: source (lower NP) gets dependent accusative. -/
theorem acc_variant_source_gets_acc :
    getCaseOf "source" accVariantResult = some .acc := by native_decide

/-- ACC variant: source case is dependent (not lexical or unmarked). -/
theorem acc_variant_source_is_dependent :
    getSourceOf "source" accVariantResult = some .dependent := by native_decide

/-- ACC variant: leaver (higher NP) gets unmarked nominative. -/
theorem acc_variant_leaver_gets_nom :
    getCaseOf "leaver" accVariantResult = some .nom := by native_decide

/-- ACC variant: leaver case is unmarked. -/
theorem acc_variant_leaver_is_unmarked :
    getSourceOf "leaver" accVariantResult = some .unmarked := by native_decide

/-- ABL variant: source gets lexical ablative (from *kara*). -/
theorem abl_variant_source_gets_abl :
    getCaseOf "source" ablVariantResult = some .abl := by native_decide

/-- ABL variant: source case is lexical (from P head *kara*). -/
theorem abl_variant_source_is_lexical :
    getSourceOf "source" ablVariantResult = some .lexical := by native_decide

/-- ABL variant: leaver gets unmarked nominative. -/
theorem abl_variant_leaver_gets_nom :
    getCaseOf "leaver" ablVariantResult = some .nom := by native_decide

/-- Dependent ACC does not require agentive Voice — it only requires
    two caseless NPs in the same Spell-Out domain. The Voice head's
    flavor is irrelevant to the case algorithm. -/
theorem no_voice_needed_for_acc :
    let nps : List NPInDomain :=
      [ { label := "subj", lexicalCase := none },
        { label := "obj", lexicalCase := none } ]
    getCaseOf "obj" (assignCases .accusative nps) = some .acc ∧
    getSourceOf "obj" (assignCases .accusative nps) = some .dependent := by
  native_decide

/-- All NPs receive case in the ACC variant. -/
theorem acc_variant_all_cased :
    accVariantResult.length = 2 := by native_decide

/-- All NPs receive case in the ABL variant. -/
theorem abl_variant_all_cased :
    ablVariantResult.length = 2 := by native_decide

-- ============================================================================
-- § 9b: Tripartite Alignment Properties
-- ============================================================================

/-! ## Tripartite: Theory-Level Properties

In a tripartite system, both dependent ergative and dependent accusative
are active simultaneously: the higher NP gets ERG, the lower gets ACC,
and an NP with no case competitor gets unmarked ABS. These are properties
of the algorithm, not of any particular language. Language-specific
derivations (e.g., SJA Mam) belong in `Phenomena/Case/Bridge/`. -/

/-- Tripartite transitive: higher NP gets dependent ERG. -/
theorem tripartite_higher_gets_erg :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .tripartite nps) = some .erg := by native_decide

/-- Tripartite transitive: lower NP gets dependent ACC. -/
theorem tripartite_lower_gets_acc :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "lower" (assignCases .tripartite nps) = some .acc := by native_decide

/-- Tripartite intransitive: sole NP gets unmarked ABS. -/
theorem tripartite_sole_gets_abs :
    let nps : List NPInDomain :=
      [ { label := "sole", lexicalCase := none } ]
    getCaseOf "sole" (assignCases .tripartite nps) = some .abs := by native_decide

/-- All three cases are distinct — the defining property of tripartite.
    ERG ≠ ACC ≠ ABS, derived purely from the algorithm. -/
theorem tripartite_three_distinct :
    let tr := assignCases .tripartite
          [ { label := "higher", lexicalCase := none },
            { label := "lower", lexicalCase := none } ]
    let intr := assignCases .tripartite
          [ { label := "sole", lexicalCase := none } ]
    getCaseOf "higher" tr ≠ getCaseOf "lower" tr ∧
    getCaseOf "higher" tr ≠ getCaseOf "sole" intr ∧
    getCaseOf "lower" tr ≠ getCaseOf "sole" intr := by native_decide

/-- Tripartite subsumes both ergative and accusative dependent case:
    ERG on the higher NP matches pure ergative; ACC on the lower NP
    matches pure accusative. -/
theorem tripartite_subsumes_both :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .tripartite nps) =
    getCaseOf "higher" (assignCases .ergative nps) ∧
    getCaseOf "lower" (assignCases .tripartite nps) =
    getCaseOf "lower" (assignCases .accusative nps) := by native_decide

-- ============================================================================
-- § 10: Deeper Properties
-- ============================================================================

/-- ACC and ABL are mutually exclusive on the source: the same structural
    position receives exactly one of ACC (dependent) or ABL (lexical),
    never both. This follows from the priority ordering — lexical case
    preempts dependent case entirely. -/
theorem acc_abl_mutually_exclusive :
    getCaseOf "source" accVariantResult = some .acc ∧
    getCaseOf "source" ablVariantResult = some .abl := by native_decide

/-- The leaver gets NOM in both variants. The alternation affects only the
    source argument; the subject case is invariant. -/
theorem leaver_nom_invariant :
    getCaseOf "leaver" accVariantResult = some .nom ∧
    getCaseOf "leaver" ablVariantResult = some .nom := by native_decide

/-- Ergative mirror: in an ergative language with two caseless NPs, the
    *higher* NP gets dependent ERG and the lower gets unmarked ABS.
    This is the typological inverse of the accusative pattern. -/
theorem ergative_mirror :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .ergative nps) = some .erg ∧
    getCaseOf "lower" (assignCases .ergative nps) = some .abs := by
  native_decide

/-- A single caseless NP in an accusative language gets NOM — the
    standard intransitive case. No dependent case arises because
    there is no case competitor. -/
theorem single_np_nom :
    let nps : List NPInDomain :=
      [ { label := "sole", lexicalCase := none } ]
    getCaseOf "sole" (assignCases .accusative nps) = some .nom ∧
    getSourceOf "sole" (assignCases .accusative nps) = some .unmarked := by
  native_decide

/-- Case is purely configural: two NPs with identical labels but different
    lexical case inputs produce different outputs. The algorithm is
    sensitive only to the NP inventory, not to verb type or Voice flavor. -/
theorem case_is_configural :
    getCaseOf "source" accVariantResult ≠ getCaseOf "source" ablVariantResult := by
  native_decide

-- ============================================================================
-- § 11: Structural Case Inventory
-- ============================================================================

/-- The structural (non-lexical) cases that the dependent case algorithm
    can assign for each language type. These are exactly the cases that
    appear in the `none` (no lexical case) branch of `assignOneCase`. -/
def structuralCasesFor : CaseLanguageType → List CaseVal
  | .accusative => [.nom, .acc]
  | .ergative   => [.abs, .erg]
  | .tripartite => [.abs, .erg, .acc]

/-- In an accusative language, any NP without lexical case receives
    either NOM (unmarked) or ACC (dependent). -/
theorem accusative_nonlexical_cases
    (higherNPs lowerNPs : List NPInDomain) (np : NPInDomain)
    (h : np.lexicalCase = none) :
    let result := assignOneCase .accusative higherNPs lowerNPs np
    result.case = .nom ∨ result.case = .acc := by
  simp only [assignOneCase, dependentAccusative, h, Option.isNone, Bool.true_and,
             unmarkedCaseFor]
  cases anyLacksCaseIn higherNPs
  · left; rfl
  · right; rfl

/-- In an ergative language, any NP without lexical case receives
    either ABS (unmarked) or ERG (dependent). -/
theorem ergative_nonlexical_cases
    (higherNPs lowerNPs : List NPInDomain) (np : NPInDomain)
    (h : np.lexicalCase = none) :
    let result := assignOneCase .ergative higherNPs lowerNPs np
    result.case = .abs ∨ result.case = .erg := by
  simp only [assignOneCase, dependentErgative, h, Option.isNone, Bool.true_and,
             unmarkedCaseFor]
  cases anyLacksCaseIn lowerNPs
  · left; rfl
  · right; rfl

/-- In a tripartite language, any NP without lexical case receives
    ABS (unmarked), ERG (dependent on a lower NP), or ACC (dependent
    on a higher NP). -/
theorem tripartite_nonlexical_cases
    (higherNPs lowerNPs : List NPInDomain) (np : NPInDomain)
    (h : np.lexicalCase = none) :
    let result := assignOneCase .tripartite higherNPs lowerNPs np
    result.case = .abs ∨ result.case = .erg ∨ result.case = .acc := by
  simp only [assignOneCase, dependentErgative, dependentAccusative, h,
             Option.isNone, Bool.true_and, unmarkedCaseFor]
  cases anyLacksCaseIn lowerNPs
  · cases anyLacksCaseIn higherNPs
    · left; rfl
    · right; right; rfl
  · right; left; rfl

-- ============================================================================
-- S 12: Language-Specific Case System Configuration
-- ============================================================================

/-- How nominative case is assigned in a language.
    @cite{baker-vinokurova-2010}: in Sakha (and Mongolian, per
    @cite{gong-2022}), NOM is assigned by finite T via Agree, not
    as an unmarked default. This distinction matters for Wholesale
    Late Merger: Agree-based NOM is tied to a specific functional
    head, while unmarked NOM is a last-resort default. -/
inductive NomAssignment where
  | agreeT           -- NOM assigned by finite T via Agree
  | unmarkedDefault  -- NOM is the elsewhere/default case
  deriving DecidableEq, Repr

/-- How dative case is assigned.
    @cite{gong-2022}: DAT is nonstructural in Mongolian — it does not
    participate in dependent case competition and is not available at
    intermediate scrambling positions for WLM. -/
inductive DatAssignment where
  | nonstructural  -- Inherent/lexical (Mongolian, Japanese)
  | dependent      -- Dependent case (structurally assigned)
  deriving DecidableEq, Repr

/-- How accusative case is assigned.
    @cite{baker-vinokurova-2010}: in Sakha (and Mongolian, per
    @cite{gong-2022}), ACC is dependent case (Marantz-style); the
    standard Chomskyan alternative is that ACC is assigned by v/Voice
    via Agree (often paired with Burzio's Generalization). -/
inductive AccAssignment where
  | dependent  -- ACC is dependent case (Marantz; B&V Sakha)
  | agreeV     -- ACC assigned by v via Agree (standard Chomsky 2000/2001)
  deriving DecidableEq, Repr

/-- How genitive case is assigned.
    @cite{baker-vinokurova-2010}: in Sakha, GEN is assigned by D via
    Agree to the possessor (parallel to T-Agree NOM at the clausal
    level). Russian numeric and partitive GEN is nonstructural. -/
inductive GenAssignment where
  | agreeD         -- GEN assigned by D via Agree (Sakha; @cite{baker-vinokurova-2010})
  | nonstructural  -- GEN as inherent/lexical (Russian numeric)
  deriving DecidableEq, Repr

/-- A language-specific case system configuration.
    Bundles the alignment type with the per-case mechanism choices.

    Each of the four structural cases (NOM, GEN, ACC, DAT) gets an
    independent mechanism plug-in. Marantz's purely-configurational
    picture, Chomsky's purely-Agree picture, and B&V's two-modality
    Sakha grammar all fall out as parameterizations of this single
    structure:

    | Theory          | nom              | gen      | acc       | dat            |
    |-----------------|------------------|----------|-----------|----------------|
    | Marantz pure    | unmarkedDefault  | (—)      | dependent | dependent      |
    | Chomsky pure    | agreeT           | agreeD   | agreeV    | nonstructural  |
    | Sakha (B&V)     | agreeT           | agreeD   | dependent | dependent      |
    | Mongolian       | agreeT           | agreeD   | dependent | nonstructural  |

    `accMode` and `genMode` default to the most common values across the
    library so that existing instances need not specify them. -/
structure CaseSystemConfig where
  langType : CaseLanguageType
  nomMode : NomAssignment
  datMode : DatAssignment
  accMode : AccAssignment := .dependent
  genMode : GenAssignment := .agreeD
  deriving DecidableEq, Repr

-- ============================================================================
-- § 13: Phased Case Assignment (@cite{baker-vinokurova-2010})
-- ============================================================================

/-! ## Phased case assignment

@cite{baker-vinokurova-2010} formalize Sakha case as cycling over
two phases: VP (the smaller phase) and CP. Two configurational
rules apply (paper (4a)/(4b), restated as (85)):

- (4a) DAT rule: if NP1 c-commands NP2 in the same VP-phase,
  value NP1 as DAT unless NP2 is already marked.
- (4b) ACC rule: if NP1 c-commands NP2 in the same phase,
  value NP2 as ACC unless NP1 is already marked.

(4a) bleeds (4b) on the VP cycle by Elsewhere ordering — its
context (one specific phase) is more restrictive than (4b)'s
(any phase).

After dependent case has applied, Agree (paper (5)/(86)) values
remaining unvalued NPs:

- T agrees with the highest unvalued NP visible at CP, valuing NOM.
- D agrees with its dependent NP inside a DP, valuing GEN.

Each NP carries a `basePhase` (where it was merged) and a
`shifted` flag (did it move to a higher phase before evaluation).
PIC: NPs that stayed inside VP are not visible on the CP cycle. -/

/-- Cycle in the @cite{baker-vinokurova-2010} two-phase model.
    Distinct from the more articulated `Minimalism.Phase` structure
    in `Phase.lean`; this is just the binary VP-vs-CP distinction
    that the case algorithm cycles over. -/
inductive CasePhase where
  | vp  -- inside VP (the smaller phase in B&V)
  | cp  -- in SpecvP or higher (visible on the CP cycle)
  deriving DecidableEq, Repr

/-- An NP equipped with phase information.
    `basePhase` records where the NP was merged; `shifted` marks
    NPs that have moved to a higher phase before case evaluation. -/
structure PhasedNP extends NPInDomain where
  basePhase : CasePhase
  shifted : Bool := false
  deriving DecidableEq, Repr

/-- Visible on the VP cycle: NPs whose basePhase is `vp`.
    Even shifted NPs are visible at this point — shift happens at
    the boundary between cycles. -/
def PhasedNP.visibleOnVP (p : PhasedNP) : Bool := p.basePhase == .vp

/-- Visible on the CP cycle: NPs in `cp`, plus VP-base NPs that
    shifted out of VP. Unshifted VP NPs were transferred (PIC). -/
def PhasedNP.visibleOnCP (p : PhasedNP) : Bool :=
  p.basePhase == .cp || p.shifted

/-- Mutable state during phased case assignment. `case = none`
    means "not yet valued"; lexical case starts with the value
    pre-set. -/
structure PhasedState where
  np : PhasedNP
  case : Option (CaseVal × CaseSource)
  deriving Repr

/-- An NP is "marked" iff its case has been valued (lexically,
    by dependent rule, or by agreement). The "unless...marked"
    clauses of (4a)/(4b) check this. -/
def PhasedState.marked (s : PhasedState) : Bool := s.case.isSome

/-- Initialize: pre-fill lexical case from the NP's `lexicalCase`
    field; everything else starts unvalued. -/
def initStates (nps : List PhasedNP) : List PhasedState :=
  nps.map fun p => { np := p,
                     case := p.lexicalCase.map (fun c => (c, .lexical)) }

/-- Replace the case of the NP at index `i` with `(c, src)`. -/
def setCaseAt (i : Nat) (c : CaseVal) (src : CaseSource)
    (states : List PhasedState) : List PhasedState :=
  states.zipIdx.map fun (s, j) =>
    if j == i then { s with case := some (c, src) } else s

/-- Indices of unmarked NPs visible on a given cycle, in c-command
    order (highest first, since list-position encodes height). -/
def unmarkedVisible (cycle : CasePhase) (states : List PhasedState) : List Nat :=
  states.zipIdx.filterMap fun (s, i) =>
    let visible := match cycle with
                   | .vp => s.np.visibleOnVP
                   | .cp => s.np.visibleOnCP
    if visible && !s.marked then some i else none

/-- Apply the DAT rule (4a) on the VP cycle: if there are at least
    two unmarked NPs visible at vP, mark the highest as DAT. -/
def applyDatRule (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  if cfg.datMode != .dependent then states
  else match unmarkedVisible .vp states with
       | i :: _ :: _ => setCaseAt i .dat .dependent states
       | _ => states

/-- Apply the ACC rule (4b) on a given cycle: if there are at least
    two unmarked NPs visible, mark the lowest as ACC. -/
def applyAccRule (cfg : CaseSystemConfig) (cycle : CasePhase)
    (states : List PhasedState) : List PhasedState :=
  if cfg.accMode != .dependent then states
  else
    let idxs := unmarkedVisible cycle states
    match idxs.reverse with
    | last :: _ :: _ => setCaseAt last .acc .dependent states
    | _ => states

/-- Apply T-Agree (paper (5)/(86)): the highest unmarked NP visible
    on the CP cycle gets NOM via Agree. -/
def applyNomAgree (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  match cfg.nomMode with
  | .agreeT =>
    match (unmarkedVisible .cp states).head? with
    | some i => setCaseAt i .nom .agree states
    | none => states
  | .unmarkedDefault => states

/-- Default case for any NP still unmarked at the end of the
    derivation. Uses `unmarkedCaseFor` from § 6. -/
def applyDefault (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  states.map fun s =>
    if s.marked then s
    else { s with case := some (unmarkedCaseFor cfg.langType, .unmarked) }

/-- Materialize a `PhasedState` as a `CasedNP` (or omit if no case
    was ever assigned — caller should ensure `applyDefault` ran). -/
def PhasedState.toCased (s : PhasedState) : Option CasedNP :=
  s.case.map fun (c, src) => { label := s.np.label, case := c, source := src }

/-- The B&V phased algorithm: VP cycle (DAT then ACC), CP cycle (ACC),
    NOM via T-Agree, then a default sweep. -/
def assignCasesPhased (cfg : CaseSystemConfig) (nps : List PhasedNP) :
    List CasedNP :=
  let s0 := initStates nps
  let s1 := applyDatRule cfg s0           -- VP cycle: (4a)
  let s2 := applyAccRule cfg .vp s1       -- VP cycle: (4b), bled if (4a) fired
  let s3 := applyAccRule cfg .cp s2       -- CP cycle: (4b)
  let s4 := applyNomAgree cfg s3          -- T-Agree → NOM
  let s5 := applyDefault cfg s4           -- last resort
  s5.filterMap PhasedState.toCased

end Minimalism
