import Linglib.Morphology.Reflex

/-!
# Extraction Morphology
[elkins-torrence-brown-2026] [erlewine-2018] [erlewine-2016]

Theory-neutral substrate for cross-linguistic extraction morphology — how
languages morphologically mark that a constituent has undergone A-bar-movement
(wh-movement, relativization, focus fronting, etc.). Bare-root `Extraction`
namespace in `Syntax/` (graduated from the dissolving `Typology/`). Per-language
data are bare `def`s in `Fragments/<Lang>/…`.

Languages vary dramatically in whether and how they track extraction:
- English: no overt marking (gap strategy)
- Austronesian (Tagalog, Malagasy): voice alternation marks which argument
  has been extracted
- Mayan (Mam, K'iche'): dedicated morphemes on verbal complex
  (Mam =(y)a', K'iche' *wi*)
- Celtic (Irish): complementizer changes form (*aL* vs. *aN*)
- Chamorro: agreement morphology tracks extracted position

-/

namespace Extraction

-- ============================================================================
-- § 1: Extraction Marking Strategy
-- ============================================================================

/-- How a language morphologically marks extraction (A-bar-movement).

    This is a descriptive typology of the *surface* strategy; different
    syntactic theories will derive these differently. -/
inductive ExtractionMarkingStrategy where
  /-- No overt morphology marks extraction. The extracted position is a
      silent gap. E.g., English "What did you buy __?". (Renamed from
      `none` to avoid shadowing `Option.none`.) -/
  | unmarked
  /-- Voice alternation: verbal voice morphology changes to mark which
      argument has been extracted. E.g., Tagalog Actor/Patient/Locative
      voice; Toba Batak Actor/Object voice. -/
  | voiceAlternation
  /-- A dedicated morpheme appears on the verbal complex when extraction
      occurs. E.g., Mam =(y)a' on Voice0/Dir0, K'iche' *wi*, Kaqchikel
      AF *-ö* or *-n*, Irish complementizer *aL*. -/
  | dedicatedMorpheme
  /-- Agreement morphology on the verb tracks the extracted position.
      E.g., Chamorro wh-agreement. -/
  | agreementTracking
  /-- The complementizer changes form depending on whether extraction has
      occurred through its clause. E.g., Irish *aL* (direct) vs. *aN*
      (indirect). -/
  | complementizerChange
  deriving DecidableEq, Repr

/-! The 5 cases above are descriptive surface-typology categories. The
*analytical* claims that competing accounts give for *why* a language
has the surface pattern it does — e.g., Erlewine `[erlewine-2016]`
`[erlewine-2018]` on Kaqchikel/Mayan AF as Spec-to-Spec
Anti-Locality repair; Erlewine 2018 on Toba Batak extraction as a
structural pivot restriction; Aldridge, Coon, Coon & Mateo Pedro &
Preminger, Coon & Keine, Henderson, etc. with rival analyses — live
in `Studies/` files anchored on the specific
paper. They are not enum cases here. -/

-- ============================================================================
-- § 2: Extraction Target
-- ============================================================================

/-- The grammatical position from which extraction occurs.

    This intersects with the [keenan-comrie-1977] Accessibility Hierarchy
    (see `Typology/RelativeClause/Basic.lean`), but is defined independently
    because extraction morphology may make finer distinctions than
    relativization. -/
inductive ExtractionTarget where
  /-- Subject (ergative/nominative) extraction -/
  | subject
  /-- Direct object (accusative/absolutive) extraction -/
  | directObject
  /-- Indirect object (dative/applicative) extraction -/
  | indirectObject
  /-- Oblique (instrumental, locative, etc.) extraction -/
  | oblique
  /-- Possessor extraction -/
  | possessor
  deriving DecidableEq, Repr

/-- The thematic category of an argument being extracted: agent
    (external argument), patient (internal argument), or oblique.

    Coarser than `ThetaRole` (which distinguishes agent/experiencer/
    causer, patient/theme, goal/source/instrument). Used when the
    relevant distinction is which macro-role is extracted, not fine-
    grained thematic relations or structural positions.

    Complements `ExtractionTarget` (structural position): ArgumentRole
    identifies *what* is extracted; ExtractionTarget identifies *where*
    it was extracted. The two coincide in simple active clauses
    (agent = subject, patient = object) but diverge under voice
    alternation (in OV, the patient becomes the subject). -/
inductive ArgumentRole where
  | agent    -- external argument (agent, experiencer, causer)
  | patient  -- internal argument (patient, theme)
  | oblique  -- oblique argument (instrument, goal, source, etc.)
  deriving DecidableEq, Repr

/-- Default structural position for a given argument role (active voice). -/
def ArgumentRole.defaultPosition : ArgumentRole → ExtractionTarget
  | .agent => .subject
  | .patient => .directObject
  | .oblique => .oblique

/-- What is being extracted: a DP argument (which has a thematic role
    and needs Case licensing) or a non-DP adjunct (which has no
    thematic role and is Case-exempt).

    This distinction drives the DP/non-DP extraction asymmetry: in
    predicate-fronting languages like Toba Batak, only DP extraction
    is restricted to the pivot; adjuncts extract freely. -/
inductive Extractee where
  | dpArg : ArgumentRole → Extractee
  | adjunct : Extractee
  deriving DecidableEq, Repr

/-! ### Extraction marking as morphological reflexes

A language's extraction marking is the overt morphosyntactic *response* to
extraction from each target position, as `Morphology.Reflex` lists — the
movement itself is not a reflex ([branan-erlewine-2023]). Per-language data
are a nested `Lang.Extraction` namespace with a host type `Site` and

    realize : ExtractionTarget → List (Morphology.Reflex Site)

(`Site := Empty` for languages that mark nothing). Languages with several
markers place them at their cells — K'iche' AF at `.subject` and *wi* at
`.oblique` are different cells of one function, not competing profiles.
Marker-specific claims are reflex-membership statements. A coarse
`strategy : ExtractionMarkingStrategy` label may accompany the data as
WALS-style typology. Per-language `Lang.Extraction` namespaces must not
redeclare root `Extraction` leaf names, so unqualified references keep
resolving. -/

/-- Does the language overtly mark extraction from a given target? The
shared overtness predicate of `Morphology/Reflex.lean`. -/
def Marked {C : Type*} (realize : ExtractionTarget → List (Morphology.Reflex C))
    (t : ExtractionTarget) : Prop :=
  Morphology.Reflex.Overt (realize t)

instance {C : Type*} (realize : ExtractionTarget → List (Morphology.Reflex C))
    (t : ExtractionTarget) : Decidable (Marked realize t) :=
  inferInstanceAs (Decidable (Morphology.Reflex.Overt _))

end Extraction
