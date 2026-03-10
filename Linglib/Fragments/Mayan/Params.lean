/-!
# Shared Mayan Fragment Infrastructure
@cite{coon-mateo-pedro-preminger-2014} @cite{imanishi-2020} @cite{tada-1993}

Types and parameters shared across Mayan language fragments (Q'anjob'al,
Chol, Kaqchikel, K'iche', Mam, etc.).

## The Mayan Absolutive Parameter

The position of absolutive agreement morphemes relative to the verb stem
is an observable morphological parameter:

- **HIGH-ABS**: absolutive immediately follows the aspect marker (pre-stem).
  Template: ASP-ABS-ERG-ROOT-SUFFIX. Highland Guatemala languages.
- **LOW-ABS**: absolutive follows the verb stem (post-stem).
  Template: ASP-ERG-ROOT-SUFFIX-ABS. Lowland Mexico languages.

@cite{coon-mateo-pedro-preminger-2014} observe (extending @cite{tada-1993})
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

namespace Fragments.Mayan

-- ============================================================================
-- § 1: Mayan Absolutive Parameter (observable)
-- ============================================================================

/-- The position of absolutive agreement morphemes relative to the verb
    stem. Observable from the linear order of morphemes in the verb-aspect
    complex — no theoretical commitment required. -/
inductive ABSPosition where
  | high  -- ABS on aspect marker (pre-stem)
  | low   -- ABS on verb stem (post-stem)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Case Locus (theoretical interpretation)
-- ============================================================================

/-- Abstract case assignment locus for transitive objects.

    - **absNom**: Infl⁰ assigns case to transitive object (HIGH-ABS).
      @cite{legate-2008}'s ABS=NOM.
    - **absDef**: v⁰ assigns case to transitive object (LOW-ABS).
      @cite{legate-2008}'s ABS=DEF. -/
inductive CaseLocus where
  | absNom  -- Infl⁰ assigns case to transitive object (HIGH-ABS)
  | absDef  -- v⁰ assigns case to transitive object (LOW-ABS)
  deriving DecidableEq, BEq, Repr

/-- Map the observable morphological parameter to the theoretical
    case-assignment locus. -/
def toCaseLocus : ABSPosition → CaseLocus
  | .high => .absNom
  | .low  => .absDef

end Fragments.Mayan
