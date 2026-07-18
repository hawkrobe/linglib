import Linglib.Features.Case.Basic
import Linglib.Data.UD.Basic
import Linglib.Features.Prominence
import Linglib.Syntax.Case.Alignment
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Morphology.Word

/-!
# Shared Mayan Fragment Infrastructure

Types and parameters shared across the Mayan language fragments
(Q'anjob'al, Chol, Kaqchikel, K'iche', Mam, etc.), following
[coon-mateo-pedro-preminger-2014], [imanishi-2020], [tada-1993], and
[coon-2013].

The **Mayan Absolutive Parameter** is the observable position of
absolutive agreement morphemes relative to the verb stem. HIGH-ABS
languages place absolutive immediately after the aspect marker (pre-stem;
template ASP-ABS-ERG-ROOT-SUFFIX; Highland Guatemala); LOW-ABS languages
place it after the stem (post-stem; template ASP-ERG-ROOT-SUFFIX-ABS;
Lowland Mexico). Extending [tada-1993],
[coon-mateo-pedro-preminger-2014] observe that this correlates with
extraction asymmetries: HIGH-ABS languages overwhelmingly exhibit
syntactic ergativity while LOW-ABS languages do not.

## Main declarations

* `Mayan.ABSPosition`, `Mayan.CaseLocus`, `Mayan.toCaseLocus`: the
  absolutive parameter and its case-locus interpretation.
* `Mayan.MarkerSet`: the Set A / Set B agreement paradigms.
* `Mayan.caseChol`, `Mayan.caseQanjobalan`, `Mayan.caseKaqchikel`,
  `Mayan.caseKiche`, `Mayan.caseMam`, `Mayan.caseTseltalan`: per-branch
  aspect-driven case assignment, with `erg…`/`acc…` aspect projections.
* `Mayan.VerbForm`: transitive vs Agent Focus, and its agreement slots.
* `Mayan.ExponentTable`, `Mayan.ExponentTable.IsThirdSgZero`: agreement
  paradigms over φ-cells and the null-3sg predicate.
* `Mayan.MarkerLinearity`: prefixal / suffixal / either marker linearity.
* `Mayan`, `Mayan.isStandard`, `Mayan.caseAt`: the language registry
  and the case-assignment dispatcher.

## Implementation notes

The observable `ABSPosition` receives a theoretical interpretation as
`CaseLocus`, the functional head assigning case to transitive objects:
ABS=NOM (HIGH-ABS) has Infl⁰ assign nominative, ABS=DEF (LOW-ABS) has v⁰
assign accusative, with "absolutive" a cover term either way
([legate-2008]). Both types assign ergative uniformly (via transitive
v⁰) and nominative to intransitive subjects (via Infl⁰).
-/

/-- The Mayan languages with consolidated Fragment files. -/
inductive Mayan where
  | Chol | Qanjobal | Kaqchikel | Tseltal | Tsotsil | Mam | Kiche | Yukatek
  deriving DecidableEq, Repr

namespace Mayan

open Agreement

/-! ### Mayan absolutive parameter -/

/-- The position of absolutive agreement morphemes relative to the verb
    stem. Observable from the linear order of morphemes in the verb-aspect
    complex — no theoretical commitment required. -/
inductive ABSPosition where
  | high  -- ABS on aspect marker (pre-stem)
  | low   -- ABS on verb stem (post-stem)
  deriving DecidableEq, Repr

/-! ### Case locus -/

/-- Abstract case assignment locus for transitive objects.

    - **absNom**: Infl⁰ assigns case to transitive object (HIGH-ABS).
      [legate-2008]'s ABS=NOM.
    - **absDef**: v⁰ assigns case to transitive object (LOW-ABS).
      [legate-2008]'s ABS=DEF. -/
inductive CaseLocus where
  | absNom  -- Infl⁰ assigns case to transitive object (HIGH-ABS)
  | absDef  -- v⁰ assigns case to transitive object (LOW-ABS)
  deriving DecidableEq, Repr

/-- Map the observable morphological parameter to the theoretical
    case-assignment locus. -/
def toCaseLocus : ABSPosition → CaseLocus
  | .high => .absNom
  | .low  => .absDef

/-! ### Agreement marker paradigms -/

/-- The two agreement marker paradigms found in Mayan languages.
    Set A and set B are the traditional Mayanist labels for the two
    cross-referencing paradigms on the verb.

    These are framework-agnostic descriptive labels — they do not commit
    to an analysis of the markers as ergative, accusative, nominative,
    or absolutive. -/
inductive MarkerSet where
  /-- Set A: cross-references ergative arguments (transitive agent) and
      genitives (possessors). Ergative and genitive are homophonous. -/
  | setA
  /-- Set B: cross-references absolutive arguments (intransitive subject
      and, in ergative alignment, transitive patient). -/
  | setB
  deriving DecidableEq, Repr

/-! ### Aspect-conditioned case: three branches, two split triggers

Per [aissen-england-zavala-2017] and [koizumi-2023] Ch. 2 (citing
Campbell & Kaufman 1985), these languages sit in three different major
branches: Chol in Greater Tseltalan (Western), Q'anjob'al in Greater
Q'anjob'alan (Western), Kaqchikel in K'ichean-Mamean (Eastern). The
"extended ergative" non-perfective pattern (Set A on non-perfective
subjects) arose independently in all three — convergent
grammaticalization of nominalized aspectual constructions, not common
inheritance — but the trigger for the split differs.

**Cholan (aspect category)**, per [vazquez-alvarez-2011] §1.9.4,
[imanishi-2020] §2.2, [zavala-maldonado-2017] §3: Chol, Chontal, and
other Cholan languages split by aspect — ergative in perfective,
accusative in all non-perfective aspects. Vázquez Álvarez 2011 §1.9.4:
"the ergative pattern is split in all non-perfective aspects."

**Q'anjob'alan (syntactic dependency)**, per [mateo-toledo-2008] §1.1.1,
[imanishi-2020] §2.2, [zavala-maldonado-2017] §3 (citing Francisco
Pascual 2007): Q'anjob'al, Akateko, Popti', Chuj split in dependent
clauses lacking aspect markers, not by aspect category. Mateo Toledo
2008 §1.1.1: "split ergativity occurs in any clause without an overt
preverbal aspect marker." Seven syntactic contexts trigger it (Francisco
Pascual 2007): aspectless complements, purpose clauses, coordinate
clauses, preverbal depictives, resultatives, manner adverbs, and
preverbal aspectual/modal auxiliaries (e.g. the progressive `lanan`).
The imperfective `chi-` IS an aspect marker, so IMP clauses keep
canonical ergative; only PROG (matrix `lanan`, not a preverbal aspect
marker) triggers the split. `caseQanjobalan` approximates the syntactic
trigger via `.Prog`; the other six contexts can't be encoded at this
granularity.

### Why `.gen` not `.nom`?

Both descriptive grammars ([vazquez-alvarez-2011] §1.9.4 for Chol,
[mateo-toledo-2008] §1.1.1 for Q'anjob'al) characterize the
non-perfective alignment as nominative-accusative (Set A as
nominative-like). `Alignment.extendedErgative.assignCase` returns `.gen`
on Coon's view (Set A on non-perfective subjects is genitive licensed by
D under nominalization); the morphological identity of Set A with
possessive markers makes `.gen` defensible, but it is a theoretical
choice — a descriptive-grammar implementation would return `.nom`.
[zavala-maldonado-2017] §3 (p. 235) calls Coon's no-split re-analysis
"unconvincing": the split-ergative pattern is the descriptive consensus. -/

/-- Cholan aspect-driven case assignment ([vazquez-alvarez-2011] §1.9.4;
    [zavala-maldonado-2017] §3): ergative in perfective, extended-ergative
    (accusative-like) in all non-perfective aspects. Used by Chol;
    presumably also Chontal, Ch'orti', Cholti per the Cholan-branch
    generalization ([aissen-england-zavala-2017]). -/
def caseChol : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | .Perf, r => Alignment.ergative.assignCase r
  | .Imp, r | .Prog, r | .Prosp, r | .Hab, r | .Iter, r =>
    Alignment.extendedErgative.assignCase r

/-- Q'anjob'alan aspect-driven case assignment ([mateo-toledo-2008]
    §1.1.1; [zavala-maldonado-2017] §3): the split is triggered by
    dependent clauses lacking aspect markers, not by aspect category. This
    function approximates that via `.Prog` (the `lanan` progressive is one
    of Francisco Pascual 2007's seven split contexts); other non-perfective
    aspects (e.g. `.Imp` with the `chi-` marker) keep canonical ergative.
    Contrast Cholan, where the IMP `mi-` marker does trigger the accusative
    split. -/
def caseQanjobalan : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | .Prog, r => Alignment.extendedErgative.assignCase r
  | .Perf, r | .Imp, r | .Prosp, r | .Hab, r | .Iter, r =>
    Alignment.ergative.assignCase r

/-- Perfective projection of `caseChol`. Equals
    `Alignment.ergative.assignCase` by definition. -/
abbrev ergCaseChol : Features.Prominence.ArgumentRole → Case := caseChol .Perf

/-- Non-perfective (imperfective-and-up) projection of `caseChol`. Equals
    `Alignment.extendedErgative.assignCase` by definition. Reflects
    Chol's pattern of split in all non-perfective aspects. -/
abbrev accCaseChol : Features.Prominence.ArgumentRole → Case := caseChol .Imp

/-- Perfective projection of `caseQanjobalan`. Equals
    `Alignment.ergative.assignCase` by definition. -/
abbrev ergCaseQanjobalan : Features.Prominence.ArgumentRole → Case :=
  caseQanjobalan .Perf

/-- Progressive projection of `caseQanjobalan`. Equals
    `Alignment.extendedErgative.assignCase` by definition. Reflects
    Q'anjob'al's `lanan`-construction trigger; other non-perfective
    aspects in Q'anjob'al keep canonical ergative. -/
abbrev accCaseQanjobalan : Features.Prominence.ArgumentRole → Case :=
  caseQanjobalan .Prog

/-- Kaqchikel (K'ichean-Mamean = Eastern Mayan) aspect-driven case
    assignment. Per [imanishi-2014] §3.3.1 ("Kaqchikel: ERG=OBJ", p. 122)
    and [imanishi-2020] §2.2, Kaqchikel shows a cross-linguistically rare
    INVERTED alignment in PROG sentences with the `ajin` matrix predicate:
    the OBJECT, not the subject, is cross-referenced by Set A (ERG/GEN) —
    the opposite of the Cholan/Q'anjob'alan extended-ergative pattern.
    Imanishi 2014 derives it from the Unaccusative Requirement on
    Nominalization plus phase-head ergative Case: the object is the only
    Case-less DP in the passivized nominalized clause and gets ERG/GEN from
    D, while the subject is base-generated in matrix Spec-PredP (headed by
    `ajin`) and gets ABS from Infl. The pattern is construction-specific
    (PROG `ajin` and certain embedding-verb constructions), not a
    Kaqchikel-non-perfective generalization; other aspects keep canonical
    ergative (Imanishi 2014 Table 3.1, p. 95). Per [imanishi-2014] fn. 26
    (p. 141), some varieties/consultants reject patterns in
    [garcia-matzar-rodriguez-guajan-1997]; the claim rests on Imanishi's
    fieldwork on a specific variety. -/
def caseKaqchikel : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | .Prog, r => Alignment.invertedErgative.assignCase r
  | .Perf, r | .Imp, r | .Prosp, r | .Hab, r | .Iter, r =>
    Alignment.ergative.assignCase r

/-- Perfective projection of `caseKaqchikel`. Equals
    `Alignment.ergative.assignCase` by definition. Kaqchikel perfective
    is canonical ergative (A → ERG, S/P → ABS). -/
abbrev ergCaseKaqchikel : Features.Prominence.ArgumentRole → Case :=
  caseKaqchikel .Perf

/-- Progressive projection of `caseKaqchikel`. Equals
    `Alignment.invertedErgative.assignCase` by definition. The
    construction-specific inverted pattern (S/A → ABS, P → ERG/GEN)
    documented by Imanishi 2014/2020 for Kaqchikel `ajin`-progressive
    sentences. -/
abbrev accCaseKaqchikel : Features.Prominence.ArgumentRole → Case :=
  caseKaqchikel .Prog

/-- K'iche' (K'ichean) case assignment. Per [mondloch-2017] (Lessons 9,
    15), K'iche' is uniformly ergative-absolutive with no aspect-conditioned
    split — Set A (ERG) cross-references A across all aspects, Set B (ABS)
    cross-references S and P. This contrasts with its sister Kaqchikel's
    construction-specific inverted PROG `ajin` pattern; per [imanishi-2014]
    fn. 26 p. 141 K'ichean dialectal variation is non-trivial, but Mondloch
    documents no analogous K'iche' split. The aspect parameter is retained
    for shape-uniformity with the other Mayan `case*` functions; all aspects
    map to canonical ergative. -/
def caseKiche : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | _, r => Alignment.ergative.assignCase r

/-- K'iche' ergative-absolutive case (uniform across aspects). Equals
    `Alignment.ergative.assignCase` by definition. -/
abbrev ergCaseKiche : Features.Prominence.ArgumentRole → Case :=
  caseKiche .Perf

/-- San Juan Atitán Mam (K'ichean-Mamean / Eastern Mayan) case assignment.
    Per [scott-2023] ch. 3, SJA Mam is morphologically tripartite — A → ERG
    (Set A on Voice), P → ACC (no agreement; overt pronoun required), S →
    ABS (Set B on Infl). Mam lacks independent DP case morphology, so the
    tripartite analysis is recoverable only from agreement; per Scott ch. 3
    §3.4 the underlying abstract Cases are nonetheless distinct: ERG
    (inherent from Voice), ACC (structural from Voice), ABS (structural from
    Infl). Other Mam dialects (notably Ixtahuacán Mam per England 1983b /
    [zavala-maldonado-2017] §4–5) have been characterized as ergative with
    neutral patterns in dependent clauses, not tripartite; this substrate
    encodes Scott's SJA Mam analysis. Mam shows no aspect-conditioned split
    (Scott ch. 3), so the aspect parameter is retained only for
    shape-uniformity; all aspects map to tripartite. -/
def caseMam : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | _, r => Alignment.tripartite.assignCase r

/-- SJA Mam tripartite case (uniform across aspects). Equals
    `Alignment.tripartite.assignCase` by definition. -/
abbrev ergCaseMam : Features.Prominence.ArgumentRole → Case :=
  caseMam .Perf

/-- Tseltalan (Tseltal, Tsotsil) case assignment.

    Per [polian-2013] and [aissen-polian-2025]: Tseltalan
    languages are uniformly **ergative-absolutive** with no aspect-
    conditioned split (in contrast with their Cholan cousins). The
    aspect parameter is retained for shape-uniformity with the other
    Mayan `case*` functions. -/
def caseTseltalan : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | _, r => Alignment.ergative.assignCase r

/-- Tseltalan ergative-absolutive case (uniform across aspects). Equals
    `Alignment.ergative.assignCase` by definition. -/
abbrev ergCaseTseltalan : Features.Prominence.ArgumentRole → Case :=
  caseTseltalan .Perf

/-- Yucatecan aspect/status-driven case assignment ([hofling-2017] p. 692:
    Set A marks transitive subjects and incompletive intransitive
    subjects; Set B marks transitive objects and completive intransitive
    subjects): ergative in the completive (perfective),
    extended-ergative in the incompletive aspects. -/
def caseYukatek : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | .Perf, r => Alignment.ergative.assignCase r
  | .Imp, r | .Prog, r | .Prosp, r | .Hab, r | .Iter, r =>
    Alignment.extendedErgative.assignCase r

/-- Yucatec completive ergative-absolutive case. -/
abbrev ergCaseYukatek : Features.Prominence.ArgumentRole → Case :=
  caseYukatek .Perf

/-- Yucatec incompletive extended-ergative case. -/
abbrev accCaseYukatek : Features.Prominence.ArgumentRole → Case :=
  caseYukatek .Imp

/-! ### Person-number paradigm

The pan-Mayan person/number agreement paradigm is keyed by the canonical
    φ-cell `Agreement.Cell` (the same φ a `Pronoun`/`Word` carries): the six
    cells covering the cross-Mayan consensus (Cholan, K'ichean, Q'anjob'alan,
    Tseltalan; [kaufman-norman-1984] Tables 7-8) are exactly
    `Agreement.Cell.pnCells`. Per-language Set A / Set B tables are
    `Agreement.Paradigm String` values constructed over those cells, so a
    controller's `Word.agrCell` indexes them directly ([corbett-1998]).
    Languages with a 1pl inclusive/exclusive split (Chol's `-on lojon` 1plExcl,
    [kaufman-norman-1984] p. 91) refine at the per-language level. -/

/-! ### Verb form (transitive vs Agent Focus) -/

/-- The two verb forms relevant to Mayan agreement morphology.
    Used by HIGH-ABS languages with an Agent Focus alternation
    (Q'anjob'al, Kaqchikel) and trivially by LOW-ABS languages
    (where `.agentFocus` is unattested). -/
inductive VerbForm where
  | transitive   -- canonical transitive
  | agentFocus   -- AF construction (HIGH-ABS A-extraction)
  deriving DecidableEq, Repr

/-- Whether the form bears Set A agreement (ergative cross-reference).
    Canonical transitive: yes; AF forms "are morphologically intransitive
    and bear only a Set B (absolutive) affix" ([polian-2017] p. 222). -/
def VerbForm.hasSetA : VerbForm → Bool
  | .transitive => true
  | .agentFocus => false

/-- Whether the form bears a dedicated AF suffix. The exponent is
    per-language (Kaqchikel *-ö* or *-n* [erlewine-2016], Q'anjob'al *-on*
    [coon-mateo-pedro-preminger-2014]); its presence tracks the form. -/
def VerbForm.hasAFSuffix : VerbForm → Bool
  | .transitive => false
  | .agentFocus => true

/-- Agreement slots on the verbal complex, derived from the paradigm
    inventory: Set B is always present; Set A only where the form bears it
    (transitive: 2, AF: 1). -/
def VerbForm.agreementSlots (f : VerbForm) : Nat :=
  1 + if f.hasSetA then 1 else 0

/-! ### Exponent tables -/

/-- An exponent table: a descriptive agreement paradigm over canonical φ-cells
    (`Agreement.Cell`), mapping each person/number cell to its surface string.
    Per-language `setAExponent`/`setBExponent` populate this; cross-Mayan
    typology theorems quantify over it. Discontinuous exponents (person
    marker plus a separate plural word) are notated with `…` between the
    parts, e.g. Q'anjob'al `"s-…heb'"`; null exponents use the `∅`
    notations documented at `ExponentTable.IsThirdSgZero`. -/
abbrev ExponentTable := Agreement.Paradigm String

/-- Decidable predicate: the third-person singular Set B slot is
    morphologically null. An invariant of the standard Mayan branches per
    [kaufman-norman-1984] Table 8 (reconstructing to proto-Cholan and
    proto-Mayan), but not strictly pan-Mayan — SJA Mam's default Set B
    `tz'=` surfaces in the 3sg slot per [scott-2023] §3.3.2, so
    `CoonMateoPedroPreminger2014.mayan_p3sg_abs_null` quantifies only
    over `isStandard = true`. The
    predicate is notation-agnostic: `"-∅"` (suffix-notated Set B: Cholan,
    Q'anjob'alan, Tseltal, and Tsotsil — whose system also has a prefixal
    subset, see `Tsotsil.setBLinearity`), `"∅"` (prefixal Set B: Kaqchikel
    and other K'ichean HIGH-ABS), and `"∅-"` all encode "no overt 3sg
    exponent". The disjunction form is kernel-decidable, unlike a
    `String.replace` normalization. -/
def ExponentTable.IsThirdSgZero (e : ExponentTable) : Prop :=
  e.realize (.pn .third .Sing) = some "-∅" ∨
  e.realize (.pn .third .Sing) = some "∅" ∨
  e.realize (.pn .third .Sing) = some "∅-"

instance (e : ExponentTable) : Decidable e.IsThirdSgZero := by
  unfold ExponentTable.IsThirdSgZero; exact inferInstance

/-! ### Marker linearity -/

/-- The morphological linearity of an agreement marker on the verb stem.

    Tseltalan languages contrast on this dimension: per
    [aissen-polian-2025] Table 1, Tseltal Set B is consistently
    suffixal, while Tsotsil Set B is prefixal-or-suffixal depending on
    dialect and morphosyntactic context. Cholan and Q'anjob'alan Set B
    are uniformly suffixal. Set A is uniformly prefixal across all
    formalised Mayan languages — a candidate cross-Mayan invariant. -/
inductive MarkerLinearity where
  | prefixal
  | suffixal
  | either   -- prefixal-or-suffixal (Tsotsil Set B)
  deriving DecidableEq, Repr

/-! ### Language registry and case dispatcher -/

/-- All registered Mayan languages, useful for cross-Mayan typology
    theorems quantified by `∀ lang ∈ Mayan.all`. -/
def all : List Mayan :=
  [.Chol, .Qanjobal, .Kaqchikel, .Tseltal, .Tsotsil, .Mam, .Kiche, .Yukatek]

/-- The Mayan languages with the standard ergative-absolutive base
    (perfective ergative; Set B 3sg null per K&N reconstruction). Mam is
    the exception: per [scott-2023], San Juan Atitán Mam is morphologically
    tripartite (S, A, P each distinct in case and agreement), with Set B
    3sg surfacing as the default `tz'=` rather than null — so
    `CoonMateoPedroPreminger2014.mayan_p3sg_abs_null` and
    `CoonMateoPedroPreminger2014.mayan_perfective_ergative` quantify only
    over `isStandard = true`. Whether Mam is "really" tripartite vs
    ergative-with-neutral-objects is contested (cf. England 1983b vs Scott
    2023; Zavala 2017 §4 calls Ch'orti' the only tripartite Mayan); the
    substrate adopts Scott's analysis, recorded in `Mam/Agreement.lean`. -/
def isStandard : Mayan → Bool
  | .Mam => false
  | _    => true

/-- Aspect-driven case assignment dispatched by language. Routes to the
    existing per-branch `case*` substrate functions; the dispatcher is
    the consolidation point that lets cross-Mayan theorems quantify
    over `Mayan` rather than enumerate per-language `rfl` facts. -/
def caseAt : Mayan → UD.Aspect → Features.Prominence.ArgumentRole → Case
  | .Chol,      asp, r => caseChol asp r
  | .Qanjobal,  asp, r => caseQanjobalan asp r
  | .Kaqchikel, asp, r => caseKaqchikel asp r
  | .Tseltal,   asp, r => caseTseltalan asp r
  | .Tsotsil,   asp, r => caseTseltalan asp r
  | .Mam,       asp, r => caseMam asp r
  | .Kiche,     asp, r => caseKiche asp r
  | .Yukatek,   asp, r => caseYukatek asp r

/-! ### Verb templates -/

/-- A position class in the Mayan verbal complex, in the traditional
    Mayanist categories (so Set A and Set B stay distinct — a cut
    `Morphology.MorphCategory` cannot draw). -/
inductive VerbSlot where
  | aspect
  | setB
  | setA
  | root
  | status
  deriving DecidableEq, Repr

/-- The verbal-complex template, stem-inclusive and left-to-right, in
    canonical transitive citation form. Per-language morpheme orders as
    documented in each fragment ([preminger-2014] (12) for the K'ichean
    shape, [vazquez-alvarez-2011] §3.4 for Chol, [polian-2017] for
    Tseltalan and the Mam status-suffix loss); Tsotsil's prefixal Set B
    subset is recorded at `Tsotsil.setBLinearity`. -/
def template : Mayan → List VerbSlot
  | .Kaqchikel | .Kiche | .Qanjobal => [.aspect, .setB, .setA, .root, .status]
  | .Mam => [.aspect, .setB, .setA, .root]
  | .Chol | .Yukatek => [.aspect, .setA, .root, .status, .setB]
  | .Tseltal | .Tsotsil => [.aspect, .setA, .root, .setB]

/-- The absolutive-position classifier derived from the template: HIGH
    iff Set B precedes the root. `absPosition_matches_template` in
    `Studies/CoonMateoPedroPreminger2014.lean` checks it against the
    fragments' analytical `absPosition` values. -/
def templateABSPosition (l : Mayan) : ABSPosition :=
  if .setB ∈ (template l).takeWhile (· ≠ .root) then .high else .low

end Mayan
