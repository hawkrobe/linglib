import Linglib.Theories.Syntax.Minimalism.Core.Agree

/-!
# Dependent Case Theory
@cite{baker-2015} @cite{deal-2010} @cite{marantz-1991} @cite{ozaki-2025} @cite{scott-2023}

An alternative to Agree-based case assignment. Case is determined by
the structural configuration of NPs within a Spell-Out domain:

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

In tripartite systems (e.g., Nez Perce; Deal 2010), intransitive subjects
(S), transitive agents (A), and transitive patients (P) each receive
distinct case. Under dependent case, this follows from applying *both*
dependent ergative (to the higher NP) and dependent accusative (to the
lower NP) in the same domain, with ABS as the unmarked default (surfacing
only when no case competitor exists — i.e., intransitives).

**Note**: Not all tripartite systems use dependent case. SJA Mam
achieves tripartite alignment via inherent case from Voice (ERG for agents,
ACC for objects) plus structural case from Infl (ABS for intransitive S).
See `Fragments.Mam.Agreement` for the Agree-based analysis.

## Key Application: @cite{ozaki-2025}

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
  | dependent  -- Assigned by structural configuration (Baker 2015)
  | unmarked   -- Default when no other case applies
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Language Typology
-- ============================================================================

/-- Language type determines which dependent and unmarked cases are used.
    - Accusative: dependent = ACC (on lower NP), unmarked = NOM
    - Ergative: dependent = ERG (on higher NP), unmarked = ABS
    - Tripartite: dependent = ERG (on higher) + ACC (on lower), unmarked = ABS
      (Scott 2023: SJA Mam; cf. Nez Perce) -/
inductive CaseLanguageType where
  | accusative  -- Japanese, English, Romance, ...
  | ergative    -- Basque, Hindi (split), ...
  | tripartite  -- Nez Perce (Deal 2010), Warlpiri, ...
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 4: Case Assignment Result
-- ============================================================================

/-- Result of case assignment: an NP with its case value and source. -/
structure CasedNP where
  label : String
  case : CaseVal
  source : CaseSource
  deriving DecidableEq, BEq, Repr

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

end Minimalism
