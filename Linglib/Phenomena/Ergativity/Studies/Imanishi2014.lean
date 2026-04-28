import Linglib.Theories.Syntax.Case.Alignment
import Linglib.Fragments.Mayan.Params
import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Fragments.Mayan.Chol.Agreement
import Linglib.Fragments.Mayan.Qanjobal.Agreement

/-!
# Imanishi 2014 — Default Ergative @cite{imanishi-2014}

@cite{imanishi-2014} (MIT PhD dissertation, advisor: David Pesetsky)
addresses an alignment puzzle in non-perfective Mayan: Chol and
Q'anjob'al show extended-ergative alignment (S/A → ERG, P → ABS),
but Kaqchikel shows an **inverted** pattern in PROG `ajin`
constructions (S/A → ABS, P → ERG/GEN). The published successor
@cite{imanishi-2020} parameterizes the same data through inherent vs
structural Case; the dissertation derives both sides from a single
mechanism: the **Unaccusative Requirement on Nominalization (URN)**.

This study file consumes the substrate primitives in
`Theories/Syntax/Case/Alignment.lean`
(`Alignment.invertedErgative.assignCase`,
`Alignment.ergative.assignCase`) and `Fragments/Mayan/Params.lean`
(`caseKaqchikel`, `ergCaseKaqchikel`, `accCaseKaqchikel`,
`caseChol`, `caseQanjobalan`) and verifies that the substrate
faithfully encodes Imanishi's analysis.

## The Alignment Puzzle (@cite{imanishi-2014} §3.3, eqs. (87)-(88))

|                | S    | O      |
|----------------|------|--------|
| **Kaqchikel-type intransitive** | ABS  | —      |
| **Kaqchikel-type transitive**   | ABS  | ERG    |
| **Chol/Q'anjob'al intransitive**| ERG  | —      |
| **Chol/Q'anjob'al transitive**  | ERG  | ABS    |

Both are non-perfective (involve embedded nominalization), but
Kaqchikel's ERG lands on OBJECT, not subject.

## The Mechanism: URN (@cite{imanishi-2014} §3.3.1, eq. (90), p. 123)

> **Unaccusative Requirement on Nominalization**: Nominalized verbs
> must lack an external argument.

In Kaqchikel, the URN holds. Two consequences:

1. **Subject base-generation outside** (§3.3.1, p. 124): the external
   argument cannot appear inside the nominalized clause; it is base-
   generated as the argument of the embedding predicate (e.g., `ajin`
   PROG, `chäp` 'begin') in the matrix. From there it receives ABS
   from matrix Infl.
2. **Object as highest Case-less DP** (§3.3.1, p. 124): the
   nominalized verb cannot assign Case to the object. The object
   becomes the highest Case-less DP inside the nominalized clause
   when a phase triggers Spell-Out, and receives ergative Case from
   the phase head D — the "phase head ergative Case" of Imanishi's
   central thesis.

In Chol and Q'anjob'al, URN does NOT obligatorily apply (§3.3.3),
so the external argument can stay inside the nominalized clause and
receives ergative Case there directly.

## Construction-specificity

Imanishi's Kaqchikel data is restricted to PROG `ajin` and certain
embedding-verb constructions (`chäp` 'begin'). Other aspects in
Kaqchikel keep canonical ergative alignment (Imanishi 2014 Table 3.1,
p. 95). The fragment substrate `caseKaqchikel` matches: only
`.Prog` triggers the inverted pattern; `.Perf`, `.Imp`, `.Prosp`,
`.Hab`, `.Iter` keep canonical ergative.

## Dialectal variation (@cite{imanishi-2014} fn. 26, p. 141)

Imanishi notes: "My Kaqchikel consultants do not accept nominalized
patterns as in (120). This is presumably because of dialectal
differences." Some Kaqchikel varieties documented by
@cite{garcia-matzar-rodriguez-guajan-1997} show patterns Imanishi's
consultants don't accept. The substrate's `caseKaqchikel` encodes
Imanishi's variety; alternative-variety Lean fragments would need
a different parameterization.

-/

namespace Phenomena.Ergativity.Studies.Imanishi2014

open Features.Prominence (ArgumentRole)

-- ============================================================================
-- § 1: URN (Unaccusative Requirement on Nominalization)
-- ============================================================================

/-- The URN parameter @cite{imanishi-2014} eq. (90) p. 123: does
    nominalization in this language require unaccusative structure
    (no external argument inside the nominalized clause)? -/
inductive URN where
  /-- URN holds: nominalized clauses must lack an external argument
      (Kaqchikel pattern). -/
  | required
  /-- URN does not obligatorily apply: external argument may stay
      inside (Chol, Q'anjob'al pattern). -/
  | optional
  deriving DecidableEq, Repr

/-- Per @cite{imanishi-2014} §3.3.1, Kaqchikel requires URN. -/
def kaqchikelURN : URN := .required

/-- Per @cite{imanishi-2014} §3.3.3, Chol does not obligatorily
    require URN. -/
def cholURN : URN := .optional

/-- Per @cite{imanishi-2014} §3.3.3, Q'anjob'al does not obligatorily
    require URN. -/
def qanjobalURN : URN := .optional

-- ============================================================================
-- § 2: Substrate Bridge — caseKaqchikel encodes Imanishi's analysis
-- ============================================================================

/-- @cite{imanishi-2014} §3.3.1 (the "Kaqchikel: ERG=OBJ" section):
    in PROG `ajin` constructions, the case pattern is S/A → ABS,
    P → ERG/GEN. The substrate's `caseKaqchikel .Prog` returns
    `Alignment.invertedErgative.assignCase` by definition (see
    `Fragments/Mayan/Params.lean:246`); this theorem verifies the
    derived case values match Imanishi's Kaqchikel-type table (87). -/
theorem kaqchikel_progressive_matches_imanishi :
    Fragments.Mayan.accCaseKaqchikel .A = .abs ∧
    Fragments.Mayan.accCaseKaqchikel .P = .gen ∧
    Fragments.Mayan.accCaseKaqchikel .S = .abs := ⟨rfl, rfl, rfl⟩

/-- The substrate's `accCaseKaqchikel` is exactly
    `invertedErgative.assignCase` — the Phase F load-bearing theorem.
    Holds by definitional equality (`accCaseKaqchikel := caseKaqchikel
    .Prog := invertedErgative.assignCase`). -/
theorem invertedErgative_matches_kaqchikel_progressive :
    Fragments.Mayan.accCaseKaqchikel .A = Alignment.invertedErgative.assignCase .A ∧
    Fragments.Mayan.accCaseKaqchikel .P = Alignment.invertedErgative.assignCase .P ∧
    Fragments.Mayan.accCaseKaqchikel .S = Alignment.invertedErgative.assignCase .S :=
  ⟨rfl, rfl, rfl⟩

/-- @cite{imanishi-2014} eq. (88) Chol/Q'anjob'al-type: in their
    non-perfective, S/A → ERG, P → ABS (extended ergative). The
    substrate's `accCaseChol` returns `extendedErgative.assignCase`. -/
theorem chol_nonperfective_matches_imanishi :
    Fragments.Mayan.accCaseChol .A = .gen ∧
    Fragments.Mayan.accCaseChol .P = .abs ∧
    Fragments.Mayan.accCaseChol .S = .gen := ⟨rfl, rfl, rfl⟩

/-- Q'anjob'alan non-perfective matches the same extended-ergative
    pattern as Chol. (Q'anjob'alan only triggers split in PROG, so
    `accCaseQanjobalan` is `caseQanjobalan .Prog`.) -/
theorem qanjobalan_progressive_matches_imanishi :
    Fragments.Mayan.accCaseQanjobalan .A = .gen ∧
    Fragments.Mayan.accCaseQanjobalan .P = .abs ∧
    Fragments.Mayan.accCaseQanjobalan .S = .gen := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Cross-Language Inversion — Kaqchikel inverts Chol on A/P axis
-- ============================================================================

/-- The deepest empirical claim of @cite{imanishi-2014} §3.3: Kaqchikel
    and Chol/Q'anjob'al show MIRROR-IMAGE non-perfective alignment on
    the A/P axis. Where Chol gives A → GEN and P → ABS, Kaqchikel gives
    A → ABS and P → GEN. The two-element diff between the substrate
    cases makes the inversion structurally visible. -/
theorem kaqchikel_inverts_chol_on_AP :
    Fragments.Mayan.accCaseKaqchikel .A = Fragments.Mayan.accCaseChol .P ∧
    Fragments.Mayan.accCaseKaqchikel .P = Fragments.Mayan.accCaseChol .A :=
  ⟨rfl, rfl⟩

/-- The S argument behaves identically in both language types: ABS in
    Kaqchikel (matrix-Infl-assigned to argument-of-`ajin`), GEN in
    Chol (D-assigned to nominalized-clause-internal subject). The
    inversion is on A and P; S is asymmetric. -/
theorem S_does_not_invert :
    Fragments.Mayan.accCaseKaqchikel .S ≠ Fragments.Mayan.accCaseChol .S := by
  decide

-- ============================================================================
-- § 4: Construction-Specificity
-- ============================================================================

/-- Per @cite{imanishi-2014} Table 3.1 (p. 95) and the substrate
    `caseKaqchikel`: only PROG triggers the inverted pattern. Other
    aspects retain canonical ergative alignment. -/
theorem kaqchikel_perfective_canonical_ergative :
    Fragments.Mayan.caseKaqchikel .Perf .A = Alignment.ergative.assignCase .A ∧
    Fragments.Mayan.caseKaqchikel .Imp .A = Alignment.ergative.assignCase .A ∧
    Fragments.Mayan.caseKaqchikel .Hab .A = Alignment.ergative.assignCase .A :=
  ⟨rfl, rfl, rfl⟩

/-- Only PROG triggers the inverted pattern — the construction-
    specificity claim made structural. -/
theorem only_prog_inverts :
    Fragments.Mayan.caseKaqchikel .Prog .A ≠ Fragments.Mayan.caseKaqchikel .Perf .A := by
  decide

-- ============================================================================
-- § 5: URN-Driven Predictions
-- ============================================================================

/-- The URN-driven prediction: in URN-required languages
    (Kaqchikel), the inverted pattern surfaces; in URN-optional
    languages (Chol, Q'anjob'al), the extended-ergative pattern
    surfaces. The substrate encodes this via `caseKaqchikel` vs
    `caseChol`/`caseQanjobalan`. -/
def imanishiPredictedAccA (lang : URN) : Core.Case :=
  match lang with
  | .required => .abs   -- Kaqchikel-type: A → ABS (matrix Infl)
  | .optional => .gen   -- Chol/Q'anjob'al-type: A → GEN (phase head D)

def imanishiPredictedAccP (lang : URN) : Core.Case :=
  match lang with
  | .required => .gen   -- Kaqchikel-type: P → GEN/ERG (phase head D)
  | .optional => .abs   -- Chol/Q'anjob'al-type: P → ABS

/-- The substrate values match Imanishi's URN-driven predictions. -/
theorem substrate_matches_URN_predictions :
    Fragments.Mayan.accCaseKaqchikel .A = imanishiPredictedAccA kaqchikelURN ∧
    Fragments.Mayan.accCaseKaqchikel .P = imanishiPredictedAccP kaqchikelURN ∧
    Fragments.Mayan.accCaseChol .A = imanishiPredictedAccA cholURN ∧
    Fragments.Mayan.accCaseChol .P = imanishiPredictedAccP cholURN ∧
    Fragments.Mayan.accCaseQanjobalan .A = imanishiPredictedAccA qanjobalURN ∧
    Fragments.Mayan.accCaseQanjobalan .P = imanishiPredictedAccP qanjobalURN :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.Ergativity.Studies.Imanishi2014
