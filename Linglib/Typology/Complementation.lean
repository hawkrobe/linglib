import Linglib.Data.WALS.Aggregation
import Linglib.Data.WALS.Features.F94A
import Linglib.Data.WALS.Features.F95A
import Linglib.Data.WALS.Features.F124A
import Linglib.Data.WALS.Features.F125A
import Linglib.Data.WALS.Features.F126A
import Linglib.Data.WALS.Features.F127A
import Linglib.Data.WALS.Features.F128A

/-!
# Typology.Complementation
[noonan-2007] [dryer-2013-wals] [dryer-haspelmath-2013]

Per-language typological substrate for complementation, subordination, and
complement-taking predicates (CTPs), covering [noonan-2007]'s typology
plus seven WALS chapters:

- **Ch 94** ([dryer-2013-wals]): Order of adverbial subordinator and clause.
- **Ch 95** ([dryer-2013-wals]): OV order × adposition type.
- **Ch 124--128** (Cristofaro): 'Want' complement subjects, purpose clauses,
  'when' clauses, reason clauses, utterance complement clauses.

Mirrors the `Linglib/Typology/{Possession,Negation,Comparison,Coordination,
Modality,Gender,Alignment,ArgumentStructure,Copulas,Morphology}` substrate-
extension pattern. Fragment-importable.

## What lives here

- §1. Noonan complement typology: `NoonanCompType`, `CTPClass`,
  `RealityStatus`, `ctpRealityStatus`, `CTPDatum`, `NoonanCompType.isReduced`.
- §2. Subordination typology (Ch 94--95): `SubordinatorOrder`,
  `OVAdpositionType`, `ComplementizerPosition`, `RelativeClausePosition`,
  `PurposeClauseStrategy`, `SubordinationProfile` + helpers.
- §3. WALSCount row struct + totalOf.
- §4. Cristofaro complementation typology (Ch 124--128):
  `BalancedDeranked`, `WantCompStrategy`, `ComplementationProfile`.
- §5. WALS converters `fromWALS{124A,125A,126A,127A,128A}`.
- §6. WALS aggregate sample-size theorems.
- §7. Corpus-only generalisations: initial subordinator dominance,
  harmonic-pattern dominance, OV-postpositions strength,
  utterance-complements-mostly-balanced, purpose-deranked-more-than-utterance.

## Theory-laden caveats

- `RealityStatus` is Noonan's binary realis/irrealis split; finer
  modal/evidential distinctions live elsewhere.
- `BalancedDeranked` is Cristofaro's coarse classification; it conflates the
  Noonan-style finer typology (indicative/subjunctive/infinitive/...) into
  three buckets. The Noonan ↔ Cristofaro mapping is non-trivial:
  balanced ≈ indicative/subjunctive, deranked ≈ infinitive/nominalized/
  participle, balancedDeranked = both.
- `ctpRealityStatus`'s default for `phasal` is realis (start/stop/continue
  presuppose the event has happened), but specific lexical items can override.

## Out of scope

- The CTP per-verb data (Sections E-G of the original file: `english_say`,
  `latin_dicere`, etc.) and Noonan's verified generalizations
  (G1--G4: realis/irrealis split, equi-deletion restriction, negative
  raising, indicative hierarchy) live in `Studies/
  Noonan2007.lean`.
- The 20-language `SubordinationProfile` sample, the Q1--Q12 typological
  generalizations, and areal pattern theorems live in
  `Studies/Dryer2013.lean`.
- The 19-language `ComplementationProfile` sample and W/X cross-chapter
  generalizations live in `Studies/Cristofaro2013.lean`.
-/

set_option autoImplicit false

namespace Typology.Complementation

private abbrev ch94  := Data.WALS.F94A.allData
private abbrev ch95  := Data.WALS.F95A.allData
private abbrev ch124 := Data.WALS.F124A.allData
private abbrev ch125 := Data.WALS.F125A.allData
private abbrev ch126 := Data.WALS.F126A.allData
private abbrev ch127 := Data.WALS.F127A.allData
private abbrev ch128 := Data.WALS.F128A.allData

-- ============================================================================
-- §1. Noonan Complement Typology
-- ============================================================================

/-- The six major complement types attested cross-linguistically.
    Ordered roughly from most to least "finite" (Noonan's "balanced" to
    "deranked"). -/
inductive NoonanCompType where
  | indicative     -- Finite clause with indicative mood marking
  | subjunctive    -- Finite clause with subjunctive/irrealis marking
  | paratactic     -- Juxtaposed clause, no subordinator
  | infinitive     -- Non-finite with "to" or equivalent
  | nominalized    -- Gerund / action nominal
  | participle     -- Participial complement
  deriving DecidableEq, Repr

/-- Is this complement type "reduced" (non-finite)? -/
def NoonanCompType.isReduced : NoonanCompType → Bool
  | .infinitive  => true
  | .nominalized => true
  | .participle  => true
  | _            => false

/-- Noonan's twelve CTP classes, organized by semantic contribution.

    The ordering follows [noonan-2007] Table 2.1 from most to least
    "assertive":
    - Utterance/propAttitude/pretence: report/judge propositional content
    - Commentative/knowledge: evaluate/know propositional content
    - Perception: direct experience
    - Desiderative/manipulative/modal: irrealis orientation
    - Achievement/phasal: aspectual
    - Negative: negation as CTP -/
inductive CTPClass where
  | utterance       -- say, tell, report
  | propAttitude    -- believe, think, suppose
  | pretence        -- pretend, act as if
  | commentative    -- regret, be sorry
  | knowledge       -- know, realize, discover
  | perception      -- see, hear, feel
  | desiderative    -- want, wish, hope
  | manipulative    -- make, cause, persuade, order
  | modal           -- can, must, should
  | achievement     -- positive: manage, dare; negative: try, forget to, avoid (§3.2.10)
  | phasal          -- start, stop, continue
  /-- A CTP whose sole semantic content is sentential negation
      ([noonan-2007] §3.2.13). Typologically rare; canonical examples
      are Fijian *sega* and Shuswap negative predicates. English `avoid`,
      `refrain`, `prevent` are NOT in this class — they are *negative
      achievement* predicates (§3.2.10). -/
  | negative
  deriving DecidableEq, Repr

/-- The fundamental realis/irrealis split that predicts complement type
    selection. Realis CTPs tend toward indicative; irrealis toward
    subjunctive/infinitive ([noonan-2007] §2.3). -/
inductive RealityStatus where
  | realis    -- CTP asserts or presupposes complement truth
  | irrealis  -- CTP does not commit to complement truth
  deriving DecidableEq, Repr

/-- Default reality status of each CTP class ([noonan-2007] Table 2.3). -/
def ctpRealityStatus : CTPClass → RealityStatus
  | .utterance    => .realis
  | .propAttitude => .realis
  | .pretence     => .irrealis
  | .commentative => .realis
  | .knowledge    => .realis
  | .perception   => .realis
  | .desiderative => .irrealis
  | .manipulative => .irrealis
  | .modal        => .irrealis
  | .achievement  => .irrealis
  | .phasal       => .realis
  | .negative     => .irrealis

/-- A cross-linguistic datum about a complement-taking predicate.

    Each datum records:
    - Language and verb identification
    - CTP class (Noonan Table 2.1)
    - Which complement types this verb allows in this language
    - Reality status (defaults to `ctpRealityStatus ctpClass`, but
      overridable for exceptions)
    - Control/raising properties ([noonan-2007] §2.1--2.2)
    - Negative raising -/
structure CTPDatum where
  language : String
  verb : String
  ctpClass : CTPClass
  allowedCompTypes : List NoonanCompType
  realityStatus : RealityStatus
  hasEquiDeletion : Bool
  hasRaising : Bool
  hasNegativeRaising : Bool
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. Subordination Typology (Ch 94--95)
-- ============================================================================

/-- WALS Ch 94: How adverbial subordinators are positioned relative to
    their clause. -/
inductive SubordinatorOrder where
  /-- Subordinator is a free word preceding the clause.
      E.g., English "because he left", Arabic "li'anna-hu ghaadara". -/
  | initialWord
  /-- Subordinator is a free word following the clause.
      E.g., Japanese "kare-ga kaetta kara". -/
  | finalWord
  /-- Subordinator is a suffix on the verb at the end of the clause.
      E.g., Turkish "-dIgI icin". -/
  | finalSuffix
  /-- Mixed or no dominant subordination pattern. -/
  | mixed
  deriving DecidableEq, Repr

/-- WALS Ch 95: Four-way classification combining verb-object order with
    adposition type. The two "harmonic" patterns dominate; the two
    "disharmonic" patterns are rare. -/
inductive OVAdpositionType where
  /-- VO order with prepositions (head-initial harmony). -/
  | voPrep
  /-- OV order with postpositions (head-final harmony). -/
  | ovPostp
  /-- VO order with postpositions (disharmonic; rare). -/
  | voPostp
  /-- OV order with prepositions (disharmonic; rare). -/
  | ovPrep
  deriving DecidableEq, Repr

/-- Position of the complementizer (the subordinating morpheme introducing
    a complement clause, e.g., English "that"). Strongly mirrors the
    subordinator order from WALS Ch 94. -/
inductive ComplementizerPosition where
  | initial   -- E.g., English "that he left"
  | final     -- E.g., Japanese "kare-ga kaetta to"
  | none      -- No overt complementizer (Mandarin serial verbs etc.)
  deriving DecidableEq, Repr

/-- Position of the relative clause with respect to the head noun.
    WALS Ch 90 documents the cross-linguistic distribution. -/
inductive RelativeClausePosition where
  | postNominal       -- E.g., English "the man [who left]"
  | preNominal        -- E.g., Japanese "[kaetta] hito" -- correlates with OV
  | internallyHeaded  -- Bambara, Navajo
  | correlative       -- Hindi-style "jo... vo..."
  deriving DecidableEq, Repr

/-- Strategy for expressing purpose clauses ("in order to V"). -/
inductive PurposeClauseStrategy where
  | subjunctive     -- Greek "gia na fiji"
  | infinitive      -- English "to leave", German "um zu gehen"
  | nominalization  -- Turkish "git-mek icin"
  | serialVerb      -- Yoruba and West African / Oceanic
  deriving DecidableEq, Repr

/-- A language's subordination profile combining all five dimensions. -/
structure SubordinationProfile where
  language : String
  iso : String := ""
  /-- Ch 94: order of adverbial subordinator and clause. -/
  subordinatorOrder : SubordinatorOrder
  /-- Ch 95: OV order × adposition type. -/
  ovAdposition : OVAdpositionType
  /-- Complementizer position (initial, final, or none). -/
  compPosition : ComplementizerPosition
  /-- Relative clause position. -/
  rcPosition : RelativeClausePosition
  /-- Purpose clause strategy. -/
  purposeStrategy : PurposeClauseStrategy
  /-- Basic word order label for cross-referencing. -/
  basicOrder : String := ""
  /-- Notes on the subordination system. -/
  notes : String := ""
  deriving Repr

/-- Does this profile have an initial subordinator? -/
def SubordinationProfile.hasInitialSubordinator (p : SubordinationProfile) : Bool :=
  p.subordinatorOrder == .initialWord

/-- Does this profile have a final subordinator (word or suffix)? -/
def SubordinationProfile.hasFinalSubordinator (p : SubordinationProfile) : Bool :=
  p.subordinatorOrder == .finalWord || p.subordinatorOrder == .finalSuffix

/-- Does this profile have VO order? -/
def SubordinationProfile.isVO (p : SubordinationProfile) : Bool :=
  p.ovAdposition == .voPrep || p.ovAdposition == .voPostp

/-- Does this profile have OV order? -/
def SubordinationProfile.isOV (p : SubordinationProfile) : Bool :=
  p.ovAdposition == .ovPostp || p.ovAdposition == .ovPrep

/-- Does this profile have pre-nominal RCs? -/
def SubordinationProfile.hasPreNominalRC (p : SubordinationProfile) : Bool :=
  p.rcPosition == .preNominal

/-- Does this profile have post-nominal RCs? -/
def SubordinationProfile.hasPostNominalRC (p : SubordinationProfile) : Bool :=
  p.rcPosition == .postNominal

/-! `WALSCount` + `WALSCount.totalOf` are imported from
    `Linglib/Data/WALS/Aggregation.lean` (shared with the other
    Typology files that consume WALS distributions). -/

open Data.WALS (WALSCount)

-- ============================================================================
-- §3. Cristofaro Complementation Typology (Ch 124--128)
-- ============================================================================

/-- Cristofaro's balanced/deranked typology for complement clauses
    (shared across WALS Chapters 125A--128A). "Balanced" means the
    complement retains main-clause morphology; "deranked" means it uses
    reduced/non-finite forms; "balancedDeranked" means both strategies exist. -/
inductive BalancedDeranked where
  | balanced
  | balancedDeranked
  | deranked
  deriving DecidableEq, Repr

/-- Cristofaro's 'want' complement subject typology (WALS Ch 124A).
    Captures whether desiderative CTPs leave the complement subject
    implicit or express it overtly -- plus the desiderative affix/particle
    alternative where 'want' is not a separate verb. -/
inductive WantCompStrategy where
  | subjectImplicit   -- Complement subject left implicit (equi-like)
  | subjectOvert      -- Complement subject expressed overtly
  | both              -- Both construction types exist
  | desidAffix        -- Desiderative verbal affix (no separate verb)
  | desidParticle     -- Desiderative particle (no separate verb)
  deriving DecidableEq, Repr

/-- A language's complementation profile across WALS Chapters 124A--128A.
    Fields are optional because not every language appears in every WALS
    chapter's sample. -/
structure ComplementationProfile where
  language : String
  walsCode : String
  /-- Ch 124A: 'want' complement subject strategy. -/
  wantComp : Option WantCompStrategy := none
  /-- Ch 125A: purpose clause type. -/
  purposeClause : Option BalancedDeranked := none
  /-- Ch 126A: 'when' clause type. -/
  whenClause : Option BalancedDeranked := none
  /-- Ch 127A: reason clause type. -/
  reasonClause : Option BalancedDeranked := none
  /-- Ch 128A: utterance complement clause type. -/
  utteranceComp : Option BalancedDeranked := none
  /-- Notes on the complementation system. -/
  notes : String := ""
  deriving Repr, DecidableEq

-- ============================================================================
-- §5. WALS converters
-- ============================================================================

/-- Map WALS F124A to `WantCompStrategy`. -/
def fromWALS124A : Data.WALS.F124A.WantComplementSubject → WantCompStrategy
  | .subjectIsLeftImplicit     => .subjectImplicit
  | .subjectIsExpressedOvertly => .subjectOvert
  | .bothConstructionTypesExist => .both
  | .desiderativeVerbalAffix   => .desidAffix
  | .desiderativeParticle      => .desidParticle

/-- Map WALS F125A to `BalancedDeranked`. -/
def fromWALS125A : Data.WALS.F125A.PurposeClauseType → BalancedDeranked
  | .balanced         => .balanced
  | .balancedDeranked => .balancedDeranked
  | .deranked         => .deranked

/-- Map WALS F126A to `BalancedDeranked`. -/
def fromWALS126A : Data.WALS.F126A.WhenClauseType → BalancedDeranked
  | .balanced         => .balanced
  | .balancedDeranked => .balancedDeranked
  | .deranked         => .deranked

/-- Map WALS F127A to `BalancedDeranked`. -/
def fromWALS127A : Data.WALS.F127A.ReasonClauseType → BalancedDeranked
  | .balanced         => .balanced
  | .balancedDeranked => .balancedDeranked
  | .deranked         => .deranked

/-- Map WALS F128A to `BalancedDeranked`. -/
def fromWALS128A : Data.WALS.F128A.UtteranceComplementType → BalancedDeranked
  | .balanced         => .balanced
  | .balancedDeranked => .balancedDeranked
  | .deranked         => .deranked

-- ============================================================================
-- §6. Theory-neutral WALS distribution facts
-- ============================================================================

/-- Ch 94: initial subordinator words are by far the most common type. -/
theorem ch94_initial_word_most_common :
    let init := (ch94.filter (·.value == .initialSubordinatorWord)).length
    init > (ch94.filter (·.value == .finalSubordinatorWord)).length ∧
    init > (ch94.filter (·.value == .internalSubordinatorWord)).length ∧
    init > (ch94.filter (·.value == .subordinatingSuffix)).length ∧
    init > (ch94.filter (·.value == .mixed)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Ch 94: initial subordinator words outnumber final words plus suffixes
    combined. -/
theorem ch94_initial_dominates_final :
    (ch94.filter (·.value == .initialSubordinatorWord)).length >
    (ch94.filter (·.value == .finalSubordinatorWord)).length +
    (ch94.filter (·.value == .subordinatingSuffix)).length := by native_decide

/-- Ch 94: initial subordinator words account for over 60% of the sample. -/
theorem ch94_initial_over_60_percent :
    (ch94.filter (·.value == .initialSubordinatorWord)).length * 100 >
    ch94.length * 60 := by native_decide

/-- Ch 95: harmonic patterns (VO+Prep, OV+Postp) account for over 80% of
    sampled languages. The OV-postposition correlation is one of the
    strongest in typology. -/
theorem ch95_harmonic_dominant :
    (ch95.filter (·.value == .voAndPrepositions)).length +
    (ch95.filter (·.value == .ovAndPostpositions)).length >
      ch95.length * 8 / 10 := by
  native_decide

/-- Ch 95: OV+Postpositions is the single most common pairing. -/
theorem ch95_ov_postp_most_common :
    (ch95.filter (·.value == .ovAndPostpositions)).length >
    (ch95.filter (·.value == .voAndPrepositions)).length := by native_decide

/-- Ch 95: disharmonic patterns are rare (under 6% of the sample). -/
theorem ch95_disharmonic_rare :
    ((ch95.filter (·.value == .voAndPostpositions)).length +
     (ch95.filter (·.value == .ovAndPrepositions)).length) * 100 <
      ch95.length * 6 := by native_decide

/-- Ch 128: utterance complements are overwhelmingly balanced; "say/tell"
    complements tend to retain main-clause morphology cross-linguistically. -/
theorem utterance_comps_mostly_balanced :
    (ch128.filter (·.value == .balanced)).length >
    (ch128.filter (·.value == .deranked)).length * 10 := by native_decide

/-- Cross-chapter: purpose clauses (Ch 125) favor deranking more than
    utterance complements (Ch 128). Reflects the irrealis orientation of
    purpose clauses. -/
theorem purpose_more_deranked_than_utterance :
    (ch125.filter (·.value == .deranked)).length >
    (ch128.filter (·.value == .deranked)).length := by native_decide

-- ============================================================================
-- §8. Notional-Complement Surface Structure ([deal-2026])
-- ============================================================================

/-! ### Theory-neutral surface enum

Following the cross-framework reconciler discipline, `ComplementClauseStructure`
describes the *surface pattern* a notional complement clause realises, without
committing to one framework's internal analysis. Each Theory projects its native
account into this enum: HPSG always projects `headExternalModifier` for true
RCs; Minimalist (with [deal-2026]) projects `abarInternalCP` for Nez Perce
relative-embeddings (REs) and `barePropositionalCP` for English `that`-clauses.
-/

/-- Surface-pattern enumeration of notional-complement-clause shapes attested
    cross-linguistically.

    [deal-2026]'s typology dissolves the Kayne/Arsenij\'evi\'c ([kayne-2008],
    [kayne-2014], [arsenijevic-2009]) universalist claim that all
    clausal complementation is relativization. The *surface* options are
    independent of any one framework's commitments about underlying structure.

    The Kayne/Arsenij\'evi\'c universalist hypothesis is now a single decidable
    statement: `∀ c : ComplementClauseStructure, c = .abarInternalCP`. Deal 2026
    refutes it by exhibiting `.barePropositionalCP` as an attested cell
    (Nez Perce simplex embeddings and English *think*-complementation). -/
inductive ComplementClauseStructure where
  /-- CP with internal Ā-dependency from a high functional projection above TP.
      Nez Perce REs ([deal-2026]), Adyghe REs ([caponigro-polinsky-2011]),
      Bulgarian REs ([krapova-2010]). -/
  | abarInternalCP
  /-- Bare CP with no internal Ā-dependency. Nez Perce simplex embeddings and
      English *think*-complementation ([deal-2026]). -/
  | barePropositionalCP
  /-- CP wrapped in a nominal projection (D, possibly with N). Washo factive
      complementation ([hanink-bochnak-2017], [bochnak-hanink-2021]),
      Ndebele ([pietraszko-2019], with additional P shell). -/
  | nominalization
  /-- True relative clause: an adjunct modifier of a head noun. The pattern
      that Kayne/Arsenij\'evi\'c claim subsumes all others. -/
  | headExternalModifier
  /-- Internally-headed relative clause (Bambara, Navajo). -/
  | headInternalRelative
  /-- High adjunct, not complementation at all. Amahuaca attitude reports
      ([deal-2026] §3, citing Clem 2022 — needs separate bib entry). -/
  | adjunct
  deriving DecidableEq, Repr

-- ============================================================================
-- §9. CP External Shell Inventory ([deal-2026] Table 79)
-- ============================================================================

/-! ### CP-external wrapping shells

Where `ComplementSize` and `ClauseSpine` (Syntax/Minimalist/) record
*internal* clause height (vP/TP/CP/NmlzP), `CPShell` records what wraps the CP
*externally*. Deal 2026's Table 79 cross-classifies the two axes; this file
houses the external axis as Fragment-importable substrate.

Anchored to [deal-2026] Table 79; placement of individual languages in
Table 79 cells consumes per-language Fragment data and lives in
`Studies/Deal2026.lean`. -/

/-- A wrapping head category that may appear above a CP in a notional complement.
    [deal-2026] Table 79 attests three: D (Washo, Adyghe), N (Adyghe),
    P (Bulgarian, Ndebele). C is included as the base case to give a uniform
    representation of `bareCP` as `[.C]`. -/
inductive CPShell where
  /-- The CP itself (always present). -/
  | c
  /-- D shell (determiner wrapping CP). -/
  | d
  /-- N shell (nominal head between D and CP). -/
  | n
  /-- P shell (preposition wrapping the CP-headed argument). -/
  | p
  deriving DecidableEq, Repr

/-- An ordered shell list, innermost first.

    Convention: head element is the C of the CP itself; subsequent elements
    are progressively more peripheral wrappers. So `[.c, .d]` = `dCP` (D wraps
    CP), `[.c, .n, .d]` = `dnCP` (D wraps N wraps CP), `[.c, .d, .p]` = `pdCP`
    (P wraps D wraps CP). -/
abbrev CPShellInventory := List CPShell

/-- Predicate: this shell inventory is attested in [deal-2026] Table 79.

    Six attested shapes (one per cell), four shell-shapes:
    - `[.c]`        = `bareCP` (V CP row)
    - `[.c, .d]`    = `dCP`    (V D CP — Washo per [bochnak-hanink-2021])
    - `[.c, .n, .d]` = `dnCP`  (V D N CP row — Adyghe)
    - `[.c, .d, .p]` = `pdCP`  (V P D CP row — Bulgarian, Ndebele) -/
def isAttestedShell : CPShellInventory → Bool
  | [.c] => true
  | [.c, .d] => true
  | [.c, .n, .d] => true
  | [.c, .d, .p] => true
  | _ => false

/-- The bare-CP cell (Nez Perce REs and simplex; English *think*). -/
def bareCP : CPShellInventory := [.c]

/-- The V D CP cell (Washo per [bochnak-hanink-2021]). -/
def dCP : CPShellInventory := [.c, .d]

/-- The V D N CP cell (Adyghe REs per [caponigro-polinsky-2011]). -/
def dnCP : CPShellInventory := [.c, .n, .d]

/-- The V P D CP cell (Bulgarian REs per [krapova-2010];
    Ndebele per [pietraszko-2019]). -/
def pdCP : CPShellInventory := [.c, .d, .p]

/-! ### Concrete facts on the named witnesses

The full implicational generalisations ("every attested inventory containing P
also contains D") are folklore from inspection of the four named cells. We
prove the consumed facts directly on the named shells; the universal claim is
tracked in [deal-2026] Table 79 commentary, not as a Lean theorem
(general `List.Mem` reasoning over `CPShellInventory` would be substantial
boilerplate without proportionate payoff). -/

/-- The four named witnesses are all attested (Deal 2026 Table 79). -/
theorem named_shells_attested :
    isAttestedShell bareCP = true ∧
    isAttestedShell dCP = true ∧
    isAttestedShell dnCP = true ∧
    isAttestedShell pdCP = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The pdCP cell contains both P and D — the empirical generalisation that
    P-shelling co-occurs with D-shelling. -/
theorem pdCP_contains_p_and_d : CPShell.p ∈ pdCP ∧ CPShell.d ∈ pdCP := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The dnCP cell contains both N and D — N appears only inside a D shell. -/
theorem dnCP_contains_n_and_d : CPShell.n ∈ dnCP ∧ CPShell.d ∈ dnCP := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Every named shell contains C (the CP itself). -/
theorem named_shells_contain_c :
    CPShell.c ∈ bareCP ∧ CPShell.c ∈ dCP ∧
    CPShell.c ∈ dnCP ∧ CPShell.c ∈ pdCP := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- An unattested example: `V P CP` (P with no D shell) — [deal-2026]
    Table 79 has no such cell. -/
theorem pCP_not_attested : isAttestedShell [.c, .p] = false := rfl

/-- Another unattested example: `V N CP` (N with no D shell). -/
theorem nCP_not_attested : isAttestedShell [.c, .n] = false := rfl

end Typology.Complementation
