import Linglib.Core.Case.Basic
/-!
# Dependent Case Theory
@cite{marantz-1991} @cite{baker-2015}

The dependent case algorithm: case is determined by the structural
configuration of NPs within a Spell-Out domain, applied via a
disjunctive priority hierarchy:

1. **Lexical case**: assigned by a particular head (P, V) — highest priority
2. **Dependent case**: assigned to an NP that stands in a c-command
   relation with another caseless NP in the same domain
   - Accusative languages: lower NP gets ACC
   - Ergative languages: higher NP gets ERG
   - Tripartite languages: higher NP gets ERG *and* lower gets ACC
3. **Unmarked case**: default for any NP still without case
   - Accusative languages: NOM
   - Ergative languages: ABS
   - Tripartite languages: ABS

This file is the *theory* — the language-typology enum, the configural
rules, and the case-assignment algorithm. Empirical applications,
cross-linguistic validation, and competing analyses live in
`Phenomena/Case/Studies/`.

## Where to Find What

- `Studies/Marantz1991.lean` — the original proposal: abstract vs.
  morphological case, Georgian split-ergative spellout, the case
  realization hierarchy as the parallel to the agreement accessibility
  hierarchy
- `Studies/Baker2015.lean` — the typological survey: cross-linguistic
  derivations across accusative (German, Turkish), ergative (Basque),
  and split-ergative (Hindi, Georgian) columns
- `Studies/BakerVinokurova2010.lean` — the Sakha case study, including
  the dependent-case-with-Agree hybrid
- `Studies/Woolford1997.lean` — four-way case systems (Nez Perce):
  ERG-as-inherent challenges the dependent-case derivation of ergative
- `Studies/Scott2023.lean` — voice-based case in Mam: a sibling theory
  in which Voice and Infl assign case directly by argument position,
  with `dependent_case_ignores_voice` staging the contrast
- `Studies/Ozaki2026.lean` — Japanese departure verbs: dependent ACC on
  the source of dyadic unaccusatives, with lexical ABL from *kara*
  bleeding dependent case
- `Studies/Caha2009.lean` — typological prediction at the inventory level,
  using the `PartialOrder Core.Case` instance from
  `Theories/Interfaces/Morphosyntax/CaseContainment.lean`. The dependent
  case algorithm produces values in `Core.Case`; their relative ranking
  is the canonical containment order, which Caha's *ABA constraint
  applies to.

## Companion Infrastructure

- `Theories/Syntax/Minimalism/Voice.lean` — Voice flavors and
  phase-hood, used by the Agree-based competitor and by Voice-based
  case (Scott 2023)
- `Theories/Syntax/Minimalism/CaseFilter.lean` — the Agree-based
  licensing requirement that every DP must receive Case
- `Theories/Syntax/Case/Licensing.lean` — Kalin's hybrid licensing
  framework: one obligatory primary licenser per clause + secondary
  licensers as a last-resort response to convergence failure, deriving
  DOM patterns as the surface signature of secondary-licenser activation
- `Theories/Interfaces/Morphosyntax/CaseContainment.lean` — the
  containment hierarchy (`PartialOrder Core.Case`) and
  `respectsCahaContainment` predicate that consume `Core.Case` values

-/

namespace Syntax.Case

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
  lexicalCase : Option Core.Case
  deriving DecidableEq, Repr

-- ============================================================================
-- § 4: Case Assignment Result
-- ============================================================================

/-- Result of case assignment: an NP with its case value and source. -/
structure CasedNP where
  label : String
  case : Core.Case
  source : CaseSource
  deriving DecidableEq, Repr

/-- Look up the assigned case for an NP by label. -/
def getCaseOf (label : String) (results : List CasedNP) : Option Core.Case :=
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
def dependentAccusative (higherNPs : List NPInDomain) (np : NPInDomain) : Option Core.Case :=
  if np.lexicalCase.isNone && anyLacksCaseIn higherNPs then
    some .acc
  else
    none

/-- Dependent ergative: assigned to an NP that c-commands another caseless NP.
    NP_i gets ERG if it has no lexical case and some NP after it also
    has no lexical case. -/
def dependentErgative (np : NPInDomain) (lowerNPs : List NPInDomain) : Option Core.Case :=
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
def unmarkedCaseFor (lang : CaseLanguageType) : Core.Case :=
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
theorem lexical_bleeds_dependent (lang : CaseLanguageType) (c : Core.Case)
    (higherNPs lowerNPs : List NPInDomain) :
    (assignOneCase lang higherNPs lowerNPs
      { label := "x", lexicalCase := some c }).source = .lexical := by
  cases lang <;> simp [assignOneCase]

/-- ACC variant: source (lower NP) gets dependent accusative. -/
theorem acc_variant_source_gets_acc :
    getCaseOf "source" accVariantResult = some .acc := by decide

/-- ACC variant: source case is dependent (not lexical or unmarked). -/
theorem acc_variant_source_is_dependent :
    getSourceOf "source" accVariantResult = some .dependent := by decide

/-- ACC variant: leaver (higher NP) gets unmarked nominative. -/
theorem acc_variant_leaver_gets_nom :
    getCaseOf "leaver" accVariantResult = some .nom := by decide

/-- ACC variant: leaver case is unmarked. -/
theorem acc_variant_leaver_is_unmarked :
    getSourceOf "leaver" accVariantResult = some .unmarked := by decide

/-- ABL variant: source gets lexical ablative (from *kara*). -/
theorem abl_variant_source_gets_abl :
    getCaseOf "source" ablVariantResult = some .abl := by decide

/-- ABL variant: source case is lexical (from P head *kara*). -/
theorem abl_variant_source_is_lexical :
    getSourceOf "source" ablVariantResult = some .lexical := by decide

/-- ABL variant: leaver gets unmarked nominative. -/
theorem abl_variant_leaver_gets_nom :
    getCaseOf "leaver" ablVariantResult = some .nom := by decide

/-- Dependent ACC does not require agentive Voice — it only requires
    two caseless NPs in the same Spell-Out domain. The Voice head's
    flavor is irrelevant to the case algorithm. -/
theorem no_voice_needed_for_acc :
    let nps : List NPInDomain :=
      [ { label := "subj", lexicalCase := none },
        { label := "obj", lexicalCase := none } ]
    getCaseOf "obj" (assignCases .accusative nps) = some .acc ∧
    getSourceOf "obj" (assignCases .accusative nps) = some .dependent := by
  decide

/-- All NPs receive case in the ACC variant. -/
theorem acc_variant_all_cased :
    accVariantResult.length = 2 := by decide

/-- All NPs receive case in the ABL variant. -/
theorem abl_variant_all_cased :
    ablVariantResult.length = 2 := by decide

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
    getCaseOf "higher" (assignCases .tripartite nps) = some .erg := by decide

/-- Tripartite transitive: lower NP gets dependent ACC. -/
theorem tripartite_lower_gets_acc :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "lower" (assignCases .tripartite nps) = some .acc := by decide

/-- Tripartite intransitive: sole NP gets unmarked ABS. -/
theorem tripartite_sole_gets_abs :
    let nps : List NPInDomain :=
      [ { label := "sole", lexicalCase := none } ]
    getCaseOf "sole" (assignCases .tripartite nps) = some .abs := by decide

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
    getCaseOf "lower" tr ≠ getCaseOf "sole" intr := by decide

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
    getCaseOf "lower" (assignCases .accusative nps) := by decide

-- ============================================================================
-- § 10: Deeper Properties
-- ============================================================================

/-- ACC and ABL are mutually exclusive on the source: the same structural
    position receives exactly one of ACC (dependent) or ABL (lexical),
    never both. This follows from the priority ordering — lexical case
    preempts dependent case entirely. -/
theorem acc_abl_mutually_exclusive :
    getCaseOf "source" accVariantResult = some .acc ∧
    getCaseOf "source" ablVariantResult = some .abl := by decide

/-- The leaver gets NOM in both variants. The alternation affects only the
    source argument; the subject case is invariant. -/
theorem leaver_nom_invariant :
    getCaseOf "leaver" accVariantResult = some .nom ∧
    getCaseOf "leaver" ablVariantResult = some .nom := by decide

/-- Ergative mirror: in an ergative language with two caseless NPs, the
    *higher* NP gets dependent ERG and the lower gets unmarked ABS.
    This is the typological inverse of the accusative pattern. -/
theorem ergative_mirror :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .ergative nps) = some .erg ∧
    getCaseOf "lower" (assignCases .ergative nps) = some .abs := by
  decide

/-- A single caseless NP in an accusative language gets NOM — the
    standard intransitive case. No dependent case arises because
    there is no case competitor. -/
theorem single_np_nom :
    let nps : List NPInDomain :=
      [ { label := "sole", lexicalCase := none } ]
    getCaseOf "sole" (assignCases .accusative nps) = some .nom ∧
    getSourceOf "sole" (assignCases .accusative nps) = some .unmarked := by
  decide

/-- Case is purely configural: two NPs with identical labels but different
    lexical case inputs produce different outputs. The algorithm is
    sensitive only to the NP inventory, not to verb type or Voice flavor. -/
theorem case_is_configural :
    getCaseOf "source" accVariantResult ≠ getCaseOf "source" ablVariantResult := by
  decide

-- ============================================================================
-- § 11: Structural Case Inventory
-- ============================================================================

/-- The structural (non-lexical) cases that the dependent case algorithm
    can assign for each language type. These are exactly the cases that
    appear in the `none` (no lexical case) branch of `assignOneCase`. -/
def structuralCasesFor : CaseLanguageType → List Core.Case
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
    NPs that have moved to a higher phase before case evaluation.
    `isArgumental` flags whether the NP bears a θ-role w.r.t. some
    case-assigning head — only argumental NPs are case competitors
    for rules (4a)/(4b). Bare-NP adverbs (e.g., 'yesterday', 'two
    kilometers') are non-argumental. @cite{baker-vinokurova-2010}
    (8)–(9) and footnote 5.

    `inDP` flags NPs that participate only in DP-internal case
    assignment (possessors): these are skipped by every clausal pass
    and are valued by `applyGenAgree` when `genMode := .agreeD`. -/
structure PhasedNP extends NPInDomain where
  basePhase : CasePhase
  shifted : Bool := false
  isArgumental : Bool := true
  inDP : Bool := false
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
  case : Option (Core.Case × CaseSource)
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
def setCaseAt (i : Nat) (c : Core.Case) (src : CaseSource)
    (states : List PhasedState) : List PhasedState :=
  states.zipIdx.map fun (s, j) =>
    if j == i then { s with case := some (c, src) } else s

/-- The eligibility predicate used by `unmarkedVisible`: a state is
    eligible iff it is visible on the cycle, argumental, not DP-
    internal, and not yet marked. Factored out so structural proofs
    (e.g. `applyAccRule_preserves_marked_at`) can manipulate the
    condition without unfolding pattern lambdas. -/
def unmarkedEligible (cycle : CasePhase) (s : PhasedState) : Bool :=
  let visible := match cycle with
                 | .vp => s.np.visibleOnVP
                 | .cp => s.np.visibleOnCP
  visible && s.np.isArgumental && !s.np.inDP && !s.marked

/-- Indices of unmarked, *argumental*, clause-level NPs visible on a
    given cycle, in c-command order (highest first, since list-position
    encodes height). Non-argumental NPs (bare-NP adverbs) and DP-
    internal NPs (possessors) are filtered out: per
    @cite{baker-vinokurova-2010} (8)–(9), rules (4a)/(4b) apply only
    between argumental NPs at the clausal level. -/
def unmarkedVisible (cycle : CasePhase) (states : List PhasedState) : List Nat :=
  states.zipIdx.filterMap fun p =>
    if unmarkedEligible cycle p.1 then some p.2 else none

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
    match (unmarkedVisible cycle states).reverse with
    | last :: _ :: _ => setCaseAt last .acc .dependent states
    | _ => states

/-- Apply v-Agree: the lowest CP-visible unmarked argumental NP gets
    ACC via Agree. This is the standard Chomskyan picture
    (@cite{chomsky-2000}; @cite{chomsky-2001}): v probes downward into
    its complement and Agrees with the closest goal. The dependent-
    accusative algorithm (`applyAccRule`) is the alternative to this
    pass; the two are mutually exclusive on a given grammar via the
    `accMode` parameter. -/
def applyAccAgree (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  match cfg.accMode with
  | .agreeV =>
    match (unmarkedVisible .cp states).reverse with
    | last :: _ => setCaseAt last .acc .agree states
    | [] => states
  | .dependent => states

/-- Apply T-Agree (paper (5)/(86)): the highest unmarked NP visible
    on the CP cycle gets NOM via Agree. -/
def applyNomAgree (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  match cfg.nomMode with
  | .agreeT =>
    match unmarkedVisible .cp states with
    | first :: _ => setCaseAt first .nom .agree states
    | [] => states
  | .unmarkedDefault => states

/-- Apply D-Agree (paper (5)/(86)): every unmarked DP-internal NP
    (possessor) is valued GEN by its dominating D head. The clausal
    algorithm sees DP-internals as opaque (filtered from
    `unmarkedVisible`); this pass is the DP-internal counterpart to
    `applyNomAgree`. The Russian numeric/partitive GEN, by contrast,
    is `.nonstructural` and lives in `lexicalCase`. -/
def applyGenAgree (cfg : CaseSystemConfig) (states : List PhasedState) :
    List PhasedState :=
  match cfg.genMode with
  | .agreeD =>
    states.map fun s =>
      if s.np.inDP && !s.marked then
        { s with case := some (.gen, .agree) }
      else s
  | .nonstructural => states

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
    v-Agree → ACC (only when `accMode := .agreeV`), T-Agree → NOM,
    D-Agree → GEN, then a default sweep.

    `applyAccRule` and `applyAccAgree` are mutually exclusive on the
    cases they touch (gated by `accMode`), so their relative order
    only matters when neither fires. The order chosen — dependent
    rules first, then Agree — mirrors the standard Chomskyan picture
    where v probes after VP-internal structure has been built. -/
def assignCasesPhased (cfg : CaseSystemConfig) (nps : List PhasedNP) :
    List CasedNP :=
  let s0 := initStates nps
  let s1 := applyDatRule cfg s0           -- VP cycle: (4a)
  let s2 := applyAccRule cfg .vp s1       -- VP cycle: (4b), bled if (4a) fired
  let s3 := applyAccRule cfg .cp s2       -- CP cycle: (4b)
  let s4 := applyAccAgree cfg s3          -- v-Agree → ACC (Chomsky)
  let s5 := applyNomAgree cfg s4          -- T-Agree → NOM
  let s6 := applyGenAgree cfg s5          -- D-Agree → GEN (DP-internal)
  let s7 := applyDefault cfg s6           -- last resort
  s7.filterMap PhasedState.toCased

-- ============================================================================
-- § 14: Soundness of the Phased Algorithm
-- ============================================================================

/-! Length preservation (one CasedNP per input PhasedNP) and totality
(every input NP receives exactly one case) are the key well-formedness
properties of `assignCasesPhased`. They fall out structurally:
each per-pass operation preserves list length, and `applyDefault`
guarantees no state escapes uncased. -/

theorem initStates_length (nps : List PhasedNP) :
    (initStates nps).length = nps.length := by
  unfold initStates; rw [List.length_map]

theorem setCaseAt_length (i : Nat) (c : Core.Case) (src : CaseSource)
    (states : List PhasedState) :
    (setCaseAt i c src states).length = states.length := by
  unfold setCaseAt
  rw [List.length_map, List.length_zipIdx]

theorem applyDatRule_length (cfg : CaseSystemConfig)
    (states : List PhasedState) :
    (applyDatRule cfg states).length = states.length := by
  unfold applyDatRule
  split
  · rfl
  · split <;> first | rfl | exact setCaseAt_length _ _ _ _

theorem applyAccRule_length (cfg : CaseSystemConfig) (cycle : CasePhase)
    (states : List PhasedState) :
    (applyAccRule cfg cycle states).length = states.length := by
  unfold applyAccRule
  split
  · rfl
  · split <;> first | rfl | exact setCaseAt_length _ _ _ _

theorem applyAccAgree_length (cfg : CaseSystemConfig)
    (states : List PhasedState) :
    (applyAccAgree cfg states).length = states.length := by
  unfold applyAccAgree
  split
  · split <;> first | rfl | exact setCaseAt_length _ _ _ _
  · rfl

theorem applyNomAgree_length (cfg : CaseSystemConfig)
    (states : List PhasedState) :
    (applyNomAgree cfg states).length = states.length := by
  unfold applyNomAgree
  split
  · split <;> first | rfl | exact setCaseAt_length _ _ _ _
  · rfl

theorem applyGenAgree_length (cfg : CaseSystemConfig)
    (states : List PhasedState) :
    (applyGenAgree cfg states).length = states.length := by
  unfold applyGenAgree
  split
  · rw [List.length_map]
  · rfl

theorem applyDefault_length (cfg : CaseSystemConfig)
    (states : List PhasedState) :
    (applyDefault cfg states).length = states.length := by
  unfold applyDefault; rw [List.length_map]

/-- After the final default sweep, every state's case is valued. -/
theorem applyDefault_all_some (cfg : CaseSystemConfig)
    (states : List PhasedState) :
    ∀ s ∈ applyDefault cfg states, s.case.isSome := by
  intro s hs
  simp only [applyDefault, List.mem_map] at hs
  obtain ⟨t, _, rfl⟩ := hs
  unfold PhasedState.marked
  split <;> simp_all

private theorem filterMap_length_of_all_some {α β}
    (f : α → Option β) (l : List α)
    (h : ∀ x ∈ l, (f x).isSome) :
    (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : (f x).isSome := h x (by simp)
    have hxs : ∀ y ∈ xs, (f y).isSome := fun y hy => h y (by simp [hy])
    rw [List.filterMap_cons]
    cases hf : f x with
    | none => rw [hf] at hx; cases hx
    | some _ =>
      simp only [List.length_cons]
      exact congrArg (· + 1) (ih hxs)

private theorem toCased_isSome_iff (s : PhasedState) :
    s.toCased.isSome ↔ s.case.isSome := by
  unfold PhasedState.toCased
  cases s.case <;> simp

/-- **Soundness (length preservation).** The phased algorithm produces
    exactly one `CasedNP` per input `PhasedNP`. No NP is dropped or
    duplicated; the algorithm is total. -/
theorem assignCasesPhased_length (cfg : CaseSystemConfig) (nps : List PhasedNP) :
    (assignCasesPhased cfg nps).length = nps.length := by
  unfold assignCasesPhased
  simp only []
  rw [filterMap_length_of_all_some _ _ (fun s hs => by
        rw [toCased_isSome_iff]; exact applyDefault_all_some _ _ s hs)]
  rw [applyDefault_length, applyGenAgree_length, applyNomAgree_length,
      applyAccAgree_length, applyAccRule_length, applyAccRule_length,
      applyDatRule_length, initStates_length]

-- ============================================================================
-- § 15: Bleeding by Marking — (4a) DAT Bleeds (4b) ACC, Structurally
-- ============================================================================

/-! The Elsewhere ordering of (4a) over (4b) on the VP cycle is not a
stipulated rule-ordering preference: it falls out from the fact that
`unmarkedVisible` filters out marked NPs, so any pass that only
modifies indices in `unmarkedVisible` cannot overwrite a previously-
valued NP. We prove this once for `applyAccRule` (it never overwrites
a marked state) and use it to derive the bleeding theorem for
arbitrary inputs. -/

/-- `setCaseAt` at index `i` leaves every other index untouched. -/
private theorem setCaseAt_get?_ne (i j : Nat) (c : Core.Case) (src : CaseSource)
    (states : List PhasedState) (h : i ≠ j) :
    (setCaseAt i c src states)[j]? = states[j]? := by
  unfold setCaseAt
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases hj : states[j]? with
  | none => rfl
  | some s =>
    simp only [Option.map_some, Nat.zero_add]
    have : (j == i) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun heq => h heq.symm
    rw [this]
    rfl

/-- Every index in `unmarkedVisible cycle states` corresponds to an
    unmarked state. -/
private theorem unmarkedVisible_unmarked (cycle : CasePhase)
    (states : List PhasedState) (i : Nat)
    (h : i ∈ unmarkedVisible cycle states) :
    ∃ s, states[i]? = some s ∧ s.marked = false := by
  unfold unmarkedVisible at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨s, k⟩, hmem, hcond⟩ := h
  -- hcond : (if unmarkedEligible cycle s then some k else none) = some i
  by_cases hg : unmarkedEligible cycle s = true
  · rw [if_pos hg] at hcond
    have hki : k = i := Option.some.inj hcond
    subst hki
    rw [List.mem_iff_getElem?] at hmem
    obtain ⟨n, hn⟩ := hmem
    rw [List.getElem?_zipIdx] at hn
    cases hsn : states[n]? with
    | none => rw [hsn] at hn; cases hn
    | some s' =>
      rw [hsn] at hn
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Nat.zero_add] at hn
      obtain ⟨hs_eq, hk_eq⟩ := hn
      subst hs_eq; subst hk_eq
      refine ⟨s', hsn, ?_⟩
      unfold unmarkedEligible at hg
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
      exact hg.2
  · rw [if_neg hg] at hcond; cases hcond

/-- Spec for `applyAccRule`: it either leaves states unchanged, or it
    sets one specific unmarked-visible index to ACC. -/
private theorem applyAccRule_spec (cfg : CaseSystemConfig) (cycle : CasePhase)
    (states : List PhasedState) :
    applyAccRule cfg cycle states = states ∨
    ∃ last, last ∈ unmarkedVisible cycle states ∧
      applyAccRule cfg cycle states = setCaseAt last .acc .dependent states := by
  unfold applyAccRule
  split
  · exact Or.inl rfl
  · split
    case h_1 last _ _ heq =>
      refine Or.inr ⟨last, ?_, rfl⟩
      have : last ∈ (unmarkedVisible cycle states).reverse := by rw [heq]; simp
      simpa using this
    case h_2 => exact Or.inl rfl

/-- **(4b) ACC never overwrites a marked NP.** This is the structural
    content of the Elsewhere ordering: once a state has been valued
    (lexically, by (4a) DAT, or by Agree), `unmarkedVisible` no
    longer includes its index, so `applyAccRule` cannot touch it. -/
theorem applyAccRule_preserves_marked_at (cfg : CaseSystemConfig)
    (cycle : CasePhase) (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyAccRule cfg cycle states)[i]? = some s := by
  rcases applyAccRule_spec cfg cycle states with heq | ⟨last, hlast, heq⟩
  · rw [heq]; exact h_get
  · rw [heq]
    obtain ⟨s', hs', hs'_unmarked⟩ := unmarkedVisible_unmarked cycle states last hlast
    have hne : last ≠ i := by
      intro hidx
      rw [hidx, h_get] at hs'
      have : s = s' := (Option.some.injEq _ _).mp hs'
      rw [this] at h_marked
      rw [hs'_unmarked] at h_marked
      cases h_marked
    rw [setCaseAt_get?_ne _ _ _ _ _ hne]
    exact h_get

/-- v-Agree, like (4b), only touches `unmarkedVisible` indices and so
    cannot overwrite a marked NP. -/
theorem applyAccAgree_preserves_marked_at (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyAccAgree cfg states)[i]? = some s := by
  unfold applyAccAgree
  split
  · split
    case h_1 last _ heq =>
      have hlast_mem : last ∈ unmarkedVisible .cp states := by
        have : last ∈ (unmarkedVisible .cp states).reverse := by
          rw [heq]; exact List.mem_cons_self
        simpa using this
      obtain ⟨s', hs', hs'_unmarked⟩ :=
        unmarkedVisible_unmarked .cp states last hlast_mem
      have hne : last ≠ i := by
        intro hidx
        rw [hidx, h_get] at hs'
        have : s = s' := (Option.some.injEq _ _).mp hs'
        rw [this, hs'_unmarked] at h_marked
        cases h_marked
      rw [setCaseAt_get?_ne _ _ _ _ _ hne]; exact h_get
    case h_2 => exact h_get
  · exact h_get

/-- T-Agree only touches `unmarkedVisible .cp` indices. -/
theorem applyNomAgree_preserves_marked_at (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyNomAgree cfg states)[i]? = some s := by
  unfold applyNomAgree
  split
  · split
    case h_1 first _ heq =>
      have hfirst_mem : first ∈ unmarkedVisible .cp states := by
        rw [heq]; exact List.mem_cons_self
      obtain ⟨s', hs', hs'_unmarked⟩ :=
        unmarkedVisible_unmarked .cp states first hfirst_mem
      have hne : first ≠ i := by
        intro hidx
        rw [hidx, h_get] at hs'
        have : s = s' := (Option.some.injEq _ _).mp hs'
        rw [this, hs'_unmarked] at h_marked
        cases h_marked
      rw [setCaseAt_get?_ne _ _ _ _ _ hne]; exact h_get
    case h_2 => exact h_get
  · exact h_get

/-- D-Agree only modifies unmarked DP-internal states. -/
theorem applyGenAgree_preserves_marked_at (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyGenAgree cfg states)[i]? = some s := by
  unfold applyGenAgree
  split
  · rw [List.getElem?_map, h_get]
    simp only [Option.map_some]
    have : (s.np.inDP && !s.marked) = false := by
      rw [h_marked]; simp
    rw [this]; rfl
  · exact h_get

/-- The default sweep only modifies unmarked states. -/
theorem applyDefault_preserves_marked_at (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : states[i]? = some s) (h_marked : s.marked = true) :
    (applyDefault cfg states)[i]? = some s := by
  unfold applyDefault
  rw [List.getElem?_map, h_get]
  simp only [Option.map_some]
  rw [h_marked]; rfl

/-- **DAT bleeds ACC on the VP cycle, structurally.** For every input
    state list, the NP marked DAT by `applyDatRule` keeps its DAT case
    through the subsequent VP-cycle `applyAccRule` call. -/
theorem dat_persists_through_vp_acc (cfg : CaseSystemConfig)
    (states : List PhasedState) (i : Nat) (s : PhasedState)
    (h_get : (applyDatRule cfg states)[i]? = some s)
    (h_dat  : s.case = some (.dat, .dependent)) :
    (applyAccRule cfg .vp (applyDatRule cfg states))[i]? = some s := by
  apply applyAccRule_preserves_marked_at
  · exact h_get
  · unfold PhasedState.marked; rw [h_dat]; rfl

/-- **DAT marking persists all the way through `assignCasesPhased`.**
    Whatever NP `applyDatRule` values DAT survives every subsequent
    pass — both ACC cycles, both Agree probes, and the default sweep —
    because each pass only modifies states it sees as unmarked. The
    Sakha-specific empirical theorem `ditrans_goal_dat` follows from
    this structural fact applied to the ditransitive input. -/
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
  have h_marked : s.marked = true := by
    unfold PhasedState.marked; rw [h_dat]; rfl
  have h2 := applyAccRule_preserves_marked_at cfg .vp _ i s h_get h_marked
  have h3 := applyAccRule_preserves_marked_at cfg .cp _ i s h2 h_marked
  have h4 := applyAccAgree_preserves_marked_at cfg _ i s h3 h_marked
  have h5 := applyNomAgree_preserves_marked_at cfg _ i s h4 h_marked
  have h6 := applyGenAgree_preserves_marked_at cfg _ i s h5 h_marked
  exact applyDefault_preserves_marked_at cfg _ i s h6 h_marked

end Syntax.Case
