import Linglib.Features.Case.Basic
import Linglib.Data.UD.Basic
import Linglib.Features.Prominence
import Linglib.Syntax.Case.Alignment
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Morphology.Word

/-!
# Shared Mayan Fragment Infrastructure
[coon-mateo-pedro-preminger-2014] [imanishi-2020] [tada-1993] [coon-2013]

Types and parameters shared across Mayan language fragments (Q'anjob'al,
Chol, Kaqchikel, K'iche', Mam, etc.).

## The Mayan Absolutive Parameter

The position of absolutive agreement morphemes relative to the verb stem
is an observable morphological parameter:

- **HIGH-ABS**: absolutive immediately follows the aspect marker (pre-stem).
  Template: ASP-ABS-ERG-ROOT-SUFFIX. Highland Guatemala languages.
- **LOW-ABS**: absolutive follows the verb stem (post-stem).
  Template: ASP-ERG-ROOT-SUFFIX-ABS. Lowland Mexico languages.

[coon-mateo-pedro-preminger-2014] observe (extending [tada-1993])
that this correlates with extraction asymmetries: overwhelmingly, HIGH-ABS
languages exhibit syntactic ergativity while LOW-ABS languages do not.

## Case Locus (theoretical interpretation)

The observable `ABSPosition` receives a theoretical interpretation in
terms of which functional head assigns case to the transitive object:

- **ABS=NOM** (HIGH-ABS): Infl⁰ assigns case (= nominative) to transitive
  objects. "Absolutive" is a cover term for nominative.
- **ABS=DEF** (LOW-ABS): v⁰ assigns case (= accusative) to transitive
  objects. "Absolutive" is a cover term for accusative.

Both types assign ergative uniformly (via transitive v⁰) and nominative
to intransitive subjects (via Infl⁰).
-/

namespace Mayan

open Agreement

-- ============================================================================
-- § 1: Mayan Absolutive Parameter (observable)
-- ============================================================================

/-- The position of absolutive agreement morphemes relative to the verb
    stem. Observable from the linear order of morphemes in the verb-aspect
    complex — no theoretical commitment required. -/
inductive ABSPosition where
  | high  -- ABS on aspect marker (pre-stem)
  | low   -- ABS on verb stem (post-stem)
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Case Locus (theoretical interpretation)
-- ============================================================================

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

-- ============================================================================
-- § 3: Agreement Marker Paradigms
-- ============================================================================

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

-- ============================================================================
-- § 4: Aspect-Conditioned Case Assignment in Cholan vs Q'anjob'alan
-- ============================================================================

/-! ## Three different major Mayan branches; two different cut-off patterns

Per [aissen-england-zavala-2017] (Routledge handbook) and
[koizumi-2023] Ch. 2 (citing Campbell & Kaufman 1985), the
canonical Mayan family classification places these languages in
**three different major branches**:

- Chol → Cholan group → **Greater Tseltalan** (Western Mayan)
- Q'anjob'al → Q'anjob'al group → **Greater Q'anjob'alan** (Western Mayan)
- Kaqchikel → K'ichean group → **K'ichean-Mamean** (Eastern Mayan)

The "extended ergative" non-perfective pattern arose **independently**
in three different major branches — convergent grammaticalization of
nominalized aspectual constructions, not common inheritance.

But while the surface alignment is similar (Set A on subjects in
non-perfective contexts), the **trigger for the split differs**:

**Cholan trigger (aspect category)** — per
[vazquez-alvarez-2011] §1.9.4, [imanishi-2020] §2.2,
and [zavala-maldonado-2017] §3:

  Chol, Chontal, and other Cholan languages exhibit **aspect-based**
  split ergativity. The split is triggered by aspect category:
  ergative in **perfective**, accusative in **all non-perfective**
  aspects (imperfective, progressive, etc.). Per Vázquez Álvarez 2011
  §1.9.4: "the ergative pattern is split in all non-perfective aspects."

**Q'anjob'alan trigger (syntactic dependency)** — per
[mateo-toledo-2008] §1.1.1, [imanishi-2020] §2.2,
and [zavala-maldonado-2017] §3 (citing Francisco Pascual 2007):

  Q'anjob'al, Akateko, Popti', Chuj, etc. exhibit a **syntactic** split
  triggered by **dependent clauses lacking aspect markers** — NOT by
  aspect category. Mateo Toledo 2008 §1.1.1: "split ergativity occurs
  in any clause without an overt preverbal aspect marker." Seven
  syntactic constructions trigger the split (per Francisco Pascual
  2007), including: aspectless complements, purpose clauses,
  coordinate clauses, preverbal depictives, preverbal resultatives,
  preverbal manner adverbs, and **preverbal aspectual/modal auxiliaries
  (e.g., the progressive `lanan`)**. The Q'anjob'al imperfective
  marker `chi-` IS an aspect marker, so IMP clauses keep canonical
  ergative — only PROG (which uses `lanan` matrix predicate, not a
  preverbal aspect marker) triggers the split.

The Aspect-indexed function below approximates the syntactic trigger
via `.Prog` for Q'anjob'alan; the other 6 syntactic-dependency
contexts can't be encoded at this granularity.

## Why `.gen` not `.nom`?

Both descriptive grammars ([vazquez-alvarez-2011] §1.9.4 for Chol,
[mateo-toledo-2008] §1.1.1 for Q'anjob'al) characterize the
non-perfective alignment as **nominative-accusative** (Set A as
nominative-like). The substrate's `Alignment.extendedErgative.assignCase`
returns `.gen` (from Coon's analytical view: Set A on subjects in
non-perfective is genitive licensed by D under nominalization). The
morphological identity of Set A with possessive markers across Mayan
makes `.gen` analytically defensible, but it's a theoretical choice;
a descriptive-grammar implementation would return `.nom`.

[zavala-maldonado-2017] §3 (p. 235) calls Coon's no-split
re-analysis "unconvincing" — the split-ergative pattern is the
descriptive consensus, with Coon's nominalization analysis being one
analytical framing among several. -/

/-- Cholan aspect-driven case assignment.

    Per [vazquez-alvarez-2011] §1.9.4 + [zavala-maldonado-2017]
    §3: ergative in perfective; accusative-like (extended-ergative) in
    ALL non-perfective aspects (imperfective, progressive, prospective,
    habitual, iterative). Used by Chol; presumably also Chontal,
    Ch'orti', Cholti per the Cholan-branch generalization in
    [aissen-england-zavala-2017]. -/
def caseChol : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | .Perf, r => Alignment.ergative.assignCase r
  | .Imp, r | .Prog, r | .Prosp, r | .Hab, r | .Iter, r =>
    Alignment.extendedErgative.assignCase r

/-- Q'anjob'alan aspect-driven case assignment.

    Per [mateo-toledo-2008] §1.1.1 + [zavala-maldonado-2017]
    §3: split is triggered by **dependent clauses lacking aspect
    markers**, not by aspect category. The aspect-indexed function below
    approximates this with `.Prog` (since the progressive uses the
    `lanan` matrix predicate construction, which is one of the seven
    split-triggering syntactic contexts per Francisco Pascual 2007).
    Other non-perfective aspects (`.Imp` with `chi-` marker, etc.) keep
    the canonical ergative pattern — they ARE aspect-marked.

    DIFFERS FROM CHOLAN: Chol's IMP `mi-` marker triggers the
    accusative split (per Vázquez Álvarez 2011 §1.9.4); Q'anjob'al's
    IMP `chi-` does NOT (per Mateo Toledo 2008 §1.1.1). -/
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

/-- Kaqchikel (K'ichean / K'ichean-Mamean = Eastern Mayan) aspect-driven
    case assignment.

    Per [imanishi-2014] §3.3.1 ("Kaqchikel: ERG=OBJ", p. 122) and
    [imanishi-2020] §2.2: Kaqchikel exhibits a cross-linguistically
    rare INVERTED alignment in PROG sentences with the `ajin` matrix
    predicate — the OBJECT (not the subject) is cross-referenced by
    Set A (ergative/genitive). This is the OPPOSITE of the
    Cholan/Q'anjob'alan extended-ergative pattern.

    Imanishi 2014 derives this from the Unaccusative Requirement on
    Nominalization + phase head ergative Case: the object becomes the
    only Case-less DP in the passivized nominalized clause and receives
    ERG/GEN from D as phase head. The subject is base-generated outside
    (in matrix Spec-PredP headed by `ajin`) and gets ABS from Infl.

    The pattern is **construction-specific** (PROG `ajin` and certain
    embedding-verb constructions), not a broader Kaqchikel-non-perfective
    generalization. Other aspects in Kaqchikel (perfective, imperfective)
    keep canonical ergative alignment per Imanishi 2014 Table 3.1 (p. 95).

    Dialectal variation: per [imanishi-2014] fn. 26 (p. 141), some
    Kaqchikel varieties / consultants don't accept all the patterns
    documented in [garcia-matzar-rodriguez-guajan-1997]. The
    inverted-pattern claim is grounded in Imanishi's primary fieldwork
    on a specific Kaqchikel variety. -/
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

/-- K'iche' (K'ichean) case assignment.

    Per [mondloch-2017] (Lessons 9, 15): K'iche' is a uniformly
    **ergative-absolutive** language without an aspect-conditioned
    split — Set A (ergative) cross-references A across all aspects;
    Set B (absolutive) cross-references S and P. This contrasts with
    its sister Kaqchikel, which has the construction-specific
    inverted pattern in PROG `ajin`. Per [imanishi-2014] fn. 26
    p. 141, dialectal variation in K'ichean languages is non-trivial,
    but Mondloch documents no analogous K'iche' split. The aspect
    parameter is retained for shape-uniformity with the other Mayan
    `case*` functions; all aspects map to canonical ergative. -/
def caseKiche : UD.Aspect → Features.Prominence.ArgumentRole → Case
  | _, r => Alignment.ergative.assignCase r

/-- K'iche' ergative-absolutive case (uniform across aspects). Equals
    `Alignment.ergative.assignCase` by definition. -/
abbrev ergCaseKiche : Features.Prominence.ArgumentRole → Case :=
  caseKiche .Perf

/-- San Juan Atitán Mam (K'ichean-Mamean / Eastern Mayan) case assignment.

    Per [scott-2023] ch. 3: SJA Mam is **morphologically
    tripartite** — A → ERG (Set A on Voice), P → ACC (no agreement;
    overt pronoun required), S → ABS (Set B on Infl). Mam lacks
    independent DP case morphology; the tripartite analysis is
    recoverable only from agreement patterns. Per Scott's analysis
    (ch. 3 §3.4), the underlying abstract Cases are nonetheless
    distinct: ERG (inherent from Voice), ACC (structural from Voice),
    ABS (structural from Infl).

    Other Mam dialects (notably Ixtahuacán Mam per England 1983b /
    [zavala-maldonado-2017] §4–5) have been characterized as
    ergative with neutral patterns in dependent clauses, NOT
    tripartite. This substrate encodes Scott's SJA Mam analysis;
    alternative-dialect fragments would need a different
    parameterization.

    Mam shows no aspect-conditioned alignment split (per Scott
    ch. 3, the tripartite pattern is uniform). The aspect parameter
    is retained for shape-uniformity with the other Mayan `case*`
    functions; all aspects map to tripartite. -/
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

-- ============================================================================
-- § 5: Person-Number Paradigm
-- ============================================================================

/-! The pan-Mayan person/number agreement paradigm is keyed by the canonical
    φ-cell `Agreement.Cell` (the same φ a `Pronoun`/`Word` carries): the six
    cells covering the cross-Mayan consensus (Cholan, K'ichean, Q'anjob'alan,
    Tseltalan; [kaufman-norman-1984] Tables 7-8) are exactly
    `Agreement.Cell.pnCells`. Per-language Set A / Set B tables are
    `Agreement.Paradigm String` values constructed over those cells, so a
    controller's `Word.agrCell` indexes them directly ([corbett-1998]).
    Languages with a 1pl inclusive/exclusive split (Chol's `-on lojon` 1plExcl,
    [kaufman-norman-1984] p. 91) refine at the per-language level. -/

-- ============================================================================
-- § 6: Verb Form (transitive vs Agent Focus)
-- ============================================================================

/-- The two verb forms relevant to Mayan agreement morphology.
    Used by HIGH-ABS languages with an Agent Focus alternation
    (Q'anjob'al, Kaqchikel) and trivially by LOW-ABS languages
    (where `.agentFocus` is unattested). -/
inductive VerbForm where
  | transitive   -- canonical transitive
  | agentFocus   -- AF construction (HIGH-ABS A-extraction)
  deriving DecidableEq, Repr

/-- Whether the form bears Set A agreement (ergative cross-reference).
    Canonical transitive: yes. AF: no (the agent loses Set A under
    [coon-mateo-pedro-preminger-2014]'s analysis). -/
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

-- ============================================================================
-- § 7: Exponent Tables
-- ============================================================================

/-- An exponent table: a descriptive agreement paradigm over canonical φ-cells
    (`Agreement.Cell`), mapping each person/number cell to its surface string.
    Per-language `setAExponent`/`setBExponent` populate this; cross-Mayan
    typology theorems quantify over it. -/
abbrev ExponentTable := Agreement.Paradigm String

/-- Decidable predicate: the third-person singular slot is morphologically
    null. An invariant of the **standard** Mayan branches per
    [kaufman-norman-1984] Table 8 — Set B 3sg null reconstructs to
    proto-Cholan and proto-Mayan. **Not strictly pan-Mayan**: SJA Mam's
    default Set B `tz'=` surfaces in the 3sg slot per [scott-2023]
    §3.3.2; the cross-Mayan theorem `mayan_p3sg_abs_null` quantifies
    only over `MayanLang.isStandard = true`. The predicate is
    **notation-agnostic** — surface notation varies by linearity:
    `"-∅"` for suffixal Set B (Cholan, Q'anjob'alan, Tseltal, Tsotsil),
    `"∅"` for prefixal Set B (Kaqchikel and other K'ichean HIGH-ABS
    languages), `"∅-"` for prefixal-with-trailing-dash convention. All
    resolve to the same morphological claim: no overt 3sg exponent. The
    disjunction form is kernel-decidable (unlike a `String.replace`
    normalization, which is opaque to `decide`). -/
def ExponentTable.IsThirdSgZero (e : ExponentTable) : Prop :=
  e.realize (.pn .third .Sing) = some "-∅" ∨
  e.realize (.pn .third .Sing) = some "∅" ∨
  e.realize (.pn .third .Sing) = some "∅-"

instance (e : ExponentTable) : Decidable e.IsThirdSgZero := by
  unfold ExponentTable.IsThirdSgZero; exact inferInstance

-- ============================================================================
-- § 7b: Marker Linearity
-- ============================================================================

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

-- ============================================================================
-- § 8: Mayan Language Registry + caseAt Dispatcher
-- ============================================================================

/-- The Mayan languages with consolidated Fragment files. Yukatek has
    substrate work pending and is not yet in the registry; it'll be
    added once `caseYukatek` and the consolidated Agreement.lean shape
    are in place. -/
inductive MayanLang where
  | Chol | Qanjobal | Kaqchikel | Tseltal | Tsotsil | Mam | Kiche
  deriving DecidableEq, Repr

/-- All registered Mayan languages, useful for cross-Mayan typology
    theorems quantified by `∀ lang ∈ MayanLang.all`. -/
def MayanLang.all : List MayanLang :=
  [.Chol, .Qanjobal, .Kaqchikel, .Tseltal, .Tsotsil, .Mam, .Kiche]

/-- The Mayan languages with the **standard ergative-absolutive base**
    (perfective ergative; Set B 3sg null per K&N reconstruction).

    Mam is the **exception**: per [scott-2023], San Juan Atitán
    Mam is morphologically **tripartite** (S, A, P each receive
    distinct case and agreement), and its Set B 3sg surfaces as the
    default `tz'=` form rather than null. The substrate exposes this
    as a falsification of pan-Mayan invariants when Mam is in scope —
    `mayan_p3sg_abs_null` and `mayan_perfective_ergative` quantify
    only over `isStandard = true` languages.

    Whether Mam is "really" tripartite vs ergative-with-neutral-objects
    is a contested analytical question (cf. England 1983b vs Scott
    2023; Zavala 2017 §4 calls Ch'orti' the only tripartite Mayan).
    The substrate adopts Scott's analysis as recorded in
    `Mam/Agreement.lean`. -/
def MayanLang.isStandard : MayanLang → Bool
  | .Mam => false
  | _    => true

/-- Aspect-driven case assignment dispatched by language. Routes to the
    existing per-branch `case*` substrate functions; the dispatcher is
    the consolidation point that lets cross-Mayan theorems quantify
    over `MayanLang` rather than enumerate per-language `rfl` facts. -/
def caseAt : MayanLang → UD.Aspect → Features.Prominence.ArgumentRole → Case
  | .Chol,      asp, r => caseChol asp r
  | .Qanjobal,  asp, r => caseQanjobalan asp r
  | .Kaqchikel, asp, r => caseKaqchikel asp r
  | .Tseltal,   asp, r => caseTseltalan asp r
  | .Tsotsil,   asp, r => caseTseltalan asp r
  | .Mam,       asp, r => caseMam asp r
  | .Kiche,     asp, r => caseKiche asp r

end Mayan
