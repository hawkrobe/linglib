import Linglib.Theories.Morphology.Nanosyntax.Core
import Linglib.Features.IndefiniteType
import Linglib.Fragments.Slavic.Russian.Indefinites
import Linglib.Fragments.English.Indefinites
import Linglib.Fragments.Latin.Indefinites
import Linglib.Fragments.Yakut.Indefinites
import Linglib.Fragments.Kannada.Indefinites

/-!
# Dekier (2021): Morphosyntax of specific and non-specific indefinite markers
@cite{dekier-2021}

*Glossa: a journal of general linguistics* 6(1), 1–33.

This paper proposes a nanosyntactic analysis of indefinite markers,
arguing that the non-specific, specific unknown, and specific known
functions correspond to three layers of a universal syntactic hierarchy
(the **indefinite fseq**):

    F₁P (non-specific) ⊂ F₂P (specific unknown) ⊂ F₃P (specific known)

Using data from 45 languages, @cite{dekier-2021} shows:

1. **Four attested syncretism patterns**: AAA (English), ABB (Yakut),
   AAB (Latin), ABC (Russian). The *ABA pattern is unattested.

2. **The *ABA generalization** (@cite{bobaljik-2012}) holds for
   indefinites: the Superset and Elsewhere Principles of Nanosyntax
   guarantee that a single lexical entry cannot match two non-contiguous
   phrasal nodes.

3. **Paradigm gaps** are monotonic: gaps always start from the TOP of
   the hierarchy (SK first, then SU). No language has a gap for NS
   while filling SU or SK.

4. **Prefix vs suffix**: spellout-driven movement produces suffixes
   (unary foot), subderivation produces prefixes (binary foot).
   Russian *-nibudEntry'* and *-to* are suffixes; *koeEntry-* is a prefix.

## Connection to linglib

This is the paper critiqued by @cite{bubnov-2026}. While Dekier
argues that nanosyntax explains the indefinite typology via structural
containment, Bubnov argues that the semantic account of
@cite{degano-aloni-2025} (based on team-semantic `variation` and
`constancy`) provides a better explanation — one that also predicts
which type is unattested (type vi) and accounts for bidirectional
diachronic change.

Both papers analyze the same cross-linguistic data. This file
formalizes Dekier's POSITIVE nanosyntactic analysis; `Bubnov2026.lean`
formalizes the critique.
-/

set_option autoImplicit false

namespace Dekier2021

open Morphology.Nanosyntax
open Features.IndefiniteType
open Fragments.Slavic.Russian.Indefinites
open Fragments.English.Indefinites
open Fragments.Latin.Indefinites
open Fragments.Yakut.Indefinites
open Fragments.Kannada.Indefinites

-- ============================================================================
-- §1. The Indefinite Hierarchy
-- ============================================================================

/-! Dekier's hierarchy:

        F₃P  ⇒  specific known marker
       / \
      F₃  F₂P  ⇒  specific unknown marker
         / \
        F₂  F₁P  ⇒  non-specific marker
            |
            F₁

    Features are ordered on a universal fseq. Each layer is characterized
    by its rank (depth). A lexical entry at rank r stores F₁...Fᵣ and
    matches any target of rank ≤ r via the Superset Principle. -/

/-- Fseq ranks for indefinite features. -/
def nsRank : Nat := 0   -- F₁P: non-specific
def suRank : Nat := 1   -- F₂P: specific unknown
def skRank : Nat := 2   -- F₃P: specific known

-- ============================================================================
-- §2. Cross-linguistic Data (Tables 7 & 8)
-- ============================================================================

/-- A cross-linguistic indefinite paradigm entry.
    `none` in a cell indicates a paradigm gap. -/
structure ParadigmEntry where
  language : String
  nsForm : Option String   -- non-specific marker
  suForm : Option String   -- specific unknown marker
  skForm : Option String   -- specific known marker
  deriving Repr, DecidableEq, BEq

-- AAA languages (Table 7)
def pEnglish   : ParadigmEntry := ⟨"English",        "some-",   "some-",   "some-"⟩
def pPolish    : ParadigmEntry := ⟨"Polish",          "-ś",      "-ś",      "-ś"⟩
def pJapanese  : ParadigmEntry := ⟨"Japanese",        "-ka",     "-ka",     "-ka"⟩
def pKorean    : ParadigmEntry := ⟨"Korean",          "-nka",    "-nka",    "-nka"⟩
def pLezgian   : ParadigmEntry := ⟨"Lezgian",         "-jat'ani","-jat'ani","-jat'ani"⟩
def pRomanian  : ParadigmEntry := ⟨"Romanian",        "-va",     "-va",     "-va"⟩
def pBulgarian : ParadigmEntry := ⟨"Bulgarian",       "nja-",    "nja-",    "nja-"⟩
def pSerboCro  : ParadigmEntry := ⟨"Serbo-Croatian",  "ne-",     "ne-",     "ne-"⟩
def pCzech     : ParadigmEntry := ⟨"Czech",           "ně-",     "ně-",     "ně-"⟩
def pSlovak    : ParadigmEntry := ⟨"Slovak",          "nie-",    "nie-",    "nie-"⟩
def pHungarian : ParadigmEntry := ⟨"Hungarian",       "vala-",   "vala-",   "vala-"⟩
def pHebrew    : ParadigmEntry := ⟨"Hebrew",          "-šehu",   "-šehu",   "-šehu"⟩
def pTurkish   : ParadigmEntry := ⟨"Turkish",         "bir-",    "bir-",    "bir-"⟩
def pLatvian   : ParadigmEntry := ⟨"Latvian",         "kaut-",   "kaut-",   "kaut-"⟩

-- ABB languages (Table 7)
def pYakut     : ParadigmEntry := ⟨"Yakut",           "-eme",    "-ere",    "-ere"⟩
def pGeorgian  : ParadigmEntry := ⟨"Georgian",        "-me",     "-γac",    "-γac"⟩
def pOssetic   : ParadigmEntry := ⟨"Ossetic",         "is-",     "-dær",    "-dær"⟩

-- AAB languages (Table 7)
def pLatin     : ParadigmEntry := ⟨"Latin",           "ali-",    "ali-",    "-dam"⟩

-- ABC languages (Table 7)
def pRussian   : ParadigmEntry := ⟨"Russian",         "-nibud'", "-to",     "koe-"⟩
def pLithuanian: ParadigmEntry := ⟨"Lithuanian",      "-nors",   "kaž-",    "kai-"⟩

-- Paradigm gaps (Table 8)
def pKannada   : ParadigmEntry := ⟨"Kannada",         "-aadaruu","-oo",     none⟩
def pQuechua   : ParadigmEntry := ⟨"Quechua",         "-pis",    "-chi",    none⟩
def pChinese   : ParadigmEntry := ⟨"Mandarin Chinese","wh-pron", none,      none⟩
def pSwahili   : ParadigmEntry := ⟨"Swahili",         none,      none,      none⟩
def pIrish     : ParadigmEntry := ⟨"Irish",           none,      none,      none⟩
def pFilipino  : ParadigmEntry := ⟨"Filipino",        none,      none,      none⟩

/-- The full paradigms from Table 7 (21 languages with complete data). -/
def fullParadigms : List ParadigmEntry :=
  [pEnglish, pPolish, pJapanese, pKorean, pLezgian, pRomanian,
   pBulgarian, pSerboCro, pCzech, pSlovak, pHungarian, pHebrew,
   pTurkish, pLatvian,
   pYakut, pGeorgian, pOssetic,
   pLatin,
   pRussian, pLithuanian]

theorem full_paradigm_count : fullParadigms.length = 20 := by decide

/-- The paradigm-gap languages from Table 8 (6 languages). -/
def gapParadigms : List ParadigmEntry :=
  [pKannada, pQuechua, pChinese, pSwahili, pIrish, pFilipino]

-- ============================================================================
-- §3. Nanosyntactic Lexicons and Spellout
-- ============================================================================

/-! Each syncretism pattern corresponds to a particular lexicon
    configuration. The spellout algorithm (Superset + Elsewhere
    Principles) derives the surface pattern from the lexicon. -/

/-- English AAA: a single entry at rank 2 covers all three layers.
    *some-* ⇔ F₃P. -/
def englishLex : List LexEntry := [⟨2, "some-"⟩]

theorem english_spellout :
    spellout englishLex nsRank = some "some-" ∧
    spellout englishLex suRank = some "some-" ∧
    spellout englishLex skRank = some "some-" := by decide

/-- Yakut ABB: *-emeEntry* at rank 0 (F₁P), *-ereEntry* at rank 2 (F₃P).
    Elsewhere gives *-emeEntry* for NS, *-ereEntry* covers SU and SK. -/
def yakutLex : List LexEntry := [⟨0, "-eme"⟩, ⟨2, "-ere"⟩]

theorem yakut_spellout :
    spellout yakutLex nsRank = some "-eme" ∧
    spellout yakutLex suRank = some "-ere" ∧
    spellout yakutLex skRank = some "-ere" := by decide

/-- Latin AAB: *aliEntry-* at rank 1 (F₂P), *-damEntry* at rank 2 (F₃P).
    *aliEntry-* covers NS and SU via Superset; *-damEntry* wins for SK
    via Elsewhere (closer match).

    Note: the nanosyntactic derivation is complex — *aliEntry-* is
    a prefix (subderivation), *-damEntry* is a suffix (constituent
    extraction). -/
def latinLex : List LexEntry := [⟨1, "ali-"⟩, ⟨2, "-dam"⟩]

theorem latin_spellout :
    spellout latinLex nsRank = some "ali-" ∧
    spellout latinLex suRank = some "ali-" ∧
    spellout latinLex skRank = some "-dam" := by decide

/-- Russian ABC: three entries, one per rank. Each layer gets its
    own exponent.
    *-nibudEntry'* ⇔ F₁P (suffix), *-to* ⇔ F₂P (suffix),
    *koeEntry-* ⇔ F₃P (prefix). -/
def russianLex : List LexEntry :=
  [⟨0, "-nibud'"⟩, ⟨1, "-to"⟩, ⟨2, "koe-"⟩]

theorem russian_spellout :
    spellout russianLex nsRank = some "-nibud'" ∧
    spellout russianLex suRank = some "-to" ∧
    spellout russianLex skRank = some "koe-" := by decide

/-- Lithuanian ABC: three entries at ranks 0, 1, 2.
    @cite{dekier-2021} Table 7. -/
def lithuanianLex : List LexEntry :=
  [⟨0, "-nors"⟩, ⟨1, "kaž-"⟩, ⟨2, "kai-"⟩]

theorem lithuanian_spellout :
    spellout lithuanianLex nsRank = some "-nors" ∧
    spellout lithuanianLex suRank = some "kaž-" ∧
    spellout lithuanianLex skRank = some "kai-" := by decide

-- ============================================================================
-- §4. Syncretism Patterns — Verified
-- ============================================================================

/-! Patterns are COMPUTED from spellout results, not stipulated. We
    derive the syncretism check from each Fragment file's canonical
    `.form` data rather than restating the form strings here. Note:
    Russian's Fragment form `"-нибудь (-nibud')"` differs from Dekier's
    Table 7 transliteration `"-nibud'"`; `classifyTriple` only inspects
    distinctness, so both classifications coincide as ABC. -/

theorem english_is_aaa :
    classifyTriple someEntry.form someEntry.form someEntry.form = .AAA := by decide

theorem yakut_is_abb :
    classifyTriple emeEntry.form ereEntry.form ereEntry.form = .ABB := by decide

theorem latin_is_aab :
    classifyTriple aliEntry.form aliEntry.form damEntry.form = .AAB := by decide

theorem russian_is_abc :
    classifyTriple nibudEntry.form toEntry.form koeEntry.form = .ABC := by decide

/-- Lithuanian forms have no Fragment file yet (no `Fragments.Lithuanian.Indefinites`),
    so the strings stay inline here. -/
theorem lithuanian_is_abc :
    classifyTriple "-nors" "kaž-" "kai-" = .ABC := by decide

-- ============================================================================
-- §5. *ABA Impossibility
-- ============================================================================

/-! The Elsewhere Principle (@cite{dekier-2021}): "If several
    lexical items match a syntactic node, insert the entry with the
    fewest features unspecified for that node."

    Combined with the Superset Principle: if entry β (rank rβ) beats
    entry α (rank rα > rβ) for case Y, then β also beats α for ALL
    cases X < Y. So α cannot resurface below β on the fseq.

    This is `smaller_entry_dominates_below` from `Nanosyntax.Core`. -/

/-- No lexicon analyzed by Dekier produces *ABA. -/
theorem no_aba_in_sample :
    abaViolation englishLex nsRank suRank skRank = false ∧
    abaViolation yakutLex nsRank suRank skRank = false ∧
    abaViolation latinLex nsRank suRank skRank = false ∧
    abaViolation russianLex nsRank suRank skRank = false ∧
    abaViolation lithuanianLex nsRank suRank skRank = false := by
  decide

/-- The ABA pattern itself is unattested cross-linguistically.
    This aligns with the *ABA generalization of @cite{bobaljik-2012}. -/
theorem aba_unattested_pattern :
    ¬ (classifyTriple "A" "B" "A").IsAttested := by decide

-- ============================================================================
-- §6. Paradigm Gaps
-- ============================================================================

/-! @cite{dekier-2021} Table 8: paradigm gaps follow a
    monotonic pattern. Gaps always start from the TOP of the hierarchy
    (SK first, then SU). No language has a gap for NS while having
    a form for SU or SK.

    This follows from the Superset Principle: any entry at rank r
    matches ALL targets of rank ≤ r. So if ANY entry exists in the
    lexicon, NS (rank 0) is always filled. -/

/-- Paradigm gap lexicons: the gap position corresponds to the
    ABSENCE of high-rank entries. -/

-- Kannada (AB-): entries at ranks 0 and 1, no rank-2 entry
def kannadaLex : List LexEntry := [⟨0, "-aadaruu"⟩, ⟨1, "-oo"⟩]

theorem kannada_gap :
    spellout kannadaLex nsRank = some "-aadaruu" ∧
    spellout kannadaLex suRank = some "-oo" ∧
    spellout kannadaLex skRank = none := by decide

-- Chinese (A--): single entry at rank 0
def chineseLex : List LexEntry := [⟨0, "wh-pron"⟩]

theorem chinese_gap :
    spellout chineseLex nsRank = some "wh-pron" ∧
    spellout chineseLex suRank = none ∧
    spellout chineseLex skRank = none := by decide

-- Empty lexicon (---): Swahili, Irish, Filipino
def emptyLex : List LexEntry := []

theorem empty_gap :
    spellout emptyLex nsRank = none ∧
    spellout emptyLex suRank = none ∧
    spellout emptyLex skRank = none := by decide

/-- Consequence: if NS (rank 0) has no form, nothing does. -/
theorem no_ns_implies_no_su_sk (lex : List LexEntry)
    (h : spellout lex nsRank = none) :
    spellout lex suRank = none ∧ spellout lex skRank = none := by
  exact ⟨gap_propagates_upward lex 0 1 h (by omega),
         gap_propagates_upward lex 0 2 h (by omega)⟩

/-- Consequence: if SU (rank 1) has no form, SK doesn't either. -/
theorem no_su_implies_no_sk (lex : List LexEntry)
    (h : spellout lex suRank = none) :
    spellout lex skRank = none :=
  gap_propagates_upward lex 1 2 h (by omega)

-- Verify against the actual data:
-- Kannada (AB-): SK absent, SU present ✓
-- Chinese (A--): SK absent, SU absent, NS present ✓
-- Swahili (---): all absent ✓
-- No attested pattern of form -A-, --A, or -AB (gap below a filled cell)

-- ============================================================================
-- §7. Prefix/Suffix Predictions
-- ============================================================================

/-! @cite{dekier-2021}: the nanosyntactic derivation
    predicts a structural difference between prefixes and suffixes:

    - **Suffix**: formed via spellout-driven movement (roll-up).
      The stem moves above the indefinite layer, leaving a remnant
      constituent with a unary foot. Result: stem + marker.

    - **Prefix**: formed via subderivation. The indefinite layers
      are built in a parallel derivation and integrated as a complex
      left branch. Result: marker + stem.

    In Russian:
    - *-nibudEntry'* (F₁P, rank 0): suffix — stem rolls up past F₁
    - *-to* (F₂P, rank 1): suffix — stem rolls up past F₂
    - *koeEntry-* (F₃P, rank 2): prefix — subderived [F₁, F₂, F₃]

    Prediction: in a language with both prefixes and suffixes,
    the morphological boundary (prefix/suffix break) correlates with
    the derivational mechanism switch (spellout movement → subderivation).
-/

/-- Russian indefinite markers with their morphological types.
    @cite{dekier-2021}. -/
structure MarkerMorphology where
  form : String
  rank : Nat
  morphType : MorphType
  deriving Repr

def russianMarkers : List MarkerMorphology :=
  [⟨"-nibud'", 0, .suffix⟩, ⟨"-to", 1, .suffix⟩, ⟨"koe-", 2, .prefix⟩]

/-- In Russian, suffixes occupy the lower ranks and the prefix occupies
    the highest rank. This matches the spellout-movement (low) vs
    subderivation (high) prediction. -/
theorem russian_suffix_prefix_split :
    russianMarkers.all (fun m =>
      match m.morphType with
      | .suffix => m.rank < 2
      | .prefix => m.rank ≥ 2) = true := by decide

-- ============================================================================
-- §8. The Hierarchy Direction
-- ============================================================================

/-! @cite{dekier-2021}: the ordering NS < SU < SK is preferred over
    SK < SU < NS based on **functional complexity**:

    - NS markers only introduce an indefinite entity (simplest)
    - SU markers add specificity of the referent
    - SK markers add speaker knowledge of the referent's identity

    Each higher layer adds a functional property, matching the
    nanosyntactic assumption that higher layers on the fseq encode
    more complex functional content.

    Both orderings are compatible with the syncretism data. The
    functional complexity argument selects NS < SU < SK. -/

/-- The hierarchy respects the rank ordering. -/
theorem hierarchy_ordering : nsRank < suRank ∧ suRank < skRank :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- §9. Bridge to Fragment Data
-- ============================================================================

/-! Connect the nanosyntactic spellout results to the typed indefinite
    entries in the fragment files. The fragment entries use the Degano
    & Aloni typology (`IndefiniteSpecType`), which is the semantic
    counterpart to Dekier's syntactic hierarchy. -/

/-- English *some-* fills all three functions — consistent with a
    single nanosyntactic entry at rank 2 (F₃P). -/
theorem english_bridge :
    someEntry.allowsNS = true ∧ someEntry.allowsSU = true ∧
    someEntry.allowsSK = true ∧
    spellout englishLex nsRank = some "some-" ∧
    spellout englishLex suRank = some "some-" ∧
    spellout englishLex skRank = some "some-" := ⟨rfl, rfl, rfl,
  by decide, by decide, by decide⟩

/-- Russian paradigm: three fragments match three spellout results. -/
theorem russian_bridge :
    nibudEntry.allowsNS = true ∧ toEntry.allowsSU = true ∧ koeEntry.allowsSK = true ∧
    spellout russianLex nsRank = some "-nibud'" ∧
    spellout russianLex suRank = some "-to" ∧
    spellout russianLex skRank = some "koe-" := ⟨rfl, rfl, rfl,
  by decide, by decide, by decide⟩

/-- Yakut paradigm: two fragments match two spellout results. -/
theorem yakut_bridge :
    emeEntry.allowsNS = true ∧ ereEntry.allowsSK = true ∧ ereEntry.allowsSU = true ∧
    spellout yakutLex nsRank = some "-eme" ∧
    spellout yakutLex suRank = some "-ere" ∧
    spellout yakutLex skRank = some "-ere" := ⟨rfl, rfl, rfl,
  by decide, by decide, by decide⟩

/-- Latin paradigm: two fragments match two spellout results. -/
theorem latin_bridge :
    aliEntry.allowsNS = true ∧ aliEntry.allowsSU = true ∧ damEntry.allowsSK = true ∧
    spellout latinLex nsRank = some "ali-" ∧
    spellout latinLex suRank = some "ali-" ∧
    spellout latinLex skRank = some "-dam" := ⟨rfl, rfl, rfl,
  by decide, by decide, by decide⟩

/-- Kannada: the SK gap in the nanosyntactic model aligns with the
    absence of a SK-covering form in the fragment data. -/
theorem kannada_bridge :
    aadaruuEntry.allowsNS = true ∧ ooEntry.allowsSU = true ∧
    spellout kannadaLex nsRank = some "-aadaruu" ∧
    spellout kannadaLex suRank = some "-oo" ∧
    spellout kannadaLex skRank = none := ⟨rfl, rfl,
  by decide, by decide, by decide⟩

-- ============================================================================
-- §10. ParadigmEntry ↔ Spellout Consistency
-- ============================================================================

/-! The `ParadigmEntry` records (Tables 7 & 8) and the nanosyntactic
    lexicons are two independent representations of the same data.
    These theorems verify they agree. -/

theorem pEnglish_matches_spellout :
    pEnglish.nsForm = spellout englishLex nsRank ∧
    pEnglish.suForm = spellout englishLex suRank ∧
    pEnglish.skForm = spellout englishLex skRank := by decide

theorem pYakut_matches_spellout :
    pYakut.nsForm = spellout yakutLex nsRank ∧
    pYakut.suForm = spellout yakutLex suRank ∧
    pYakut.skForm = spellout yakutLex skRank := by decide

theorem pLatin_matches_spellout :
    pLatin.nsForm = spellout latinLex nsRank ∧
    pLatin.suForm = spellout latinLex suRank ∧
    pLatin.skForm = spellout latinLex skRank := by decide

theorem pRussian_matches_spellout :
    pRussian.nsForm = spellout russianLex nsRank ∧
    pRussian.suForm = spellout russianLex suRank ∧
    pRussian.skForm = spellout russianLex skRank := by decide

theorem pLithuanian_matches_spellout :
    pLithuanian.nsForm = spellout lithuanianLex nsRank ∧
    pLithuanian.suForm = spellout lithuanianLex suRank ∧
    pLithuanian.skForm = spellout lithuanianLex skRank := by decide

theorem pKannada_matches_spellout :
    pKannada.nsForm = spellout kannadaLex nsRank ∧
    pKannada.suForm = spellout kannadaLex suRank ∧
    pKannada.skForm = spellout kannadaLex skRank := by decide

theorem pChinese_matches_spellout :
    pChinese.nsForm = spellout chineseLex nsRank ∧
    pChinese.suForm = spellout chineseLex suRank ∧
    pChinese.skForm = spellout chineseLex skRank := by decide

-- ============================================================================
-- §11. The 45-Language Sample
-- ============================================================================

/-! @cite{dekier-2021} analyzed 45 languages total: Basque,
    Bulgarian, Catalan, Czech, Dutch, English, Filipino, Finnish,
    French, Georgian, German, Greek, Hausa, Hebrew, Hindi, Hungarian,
    Icelandic, Irish, Italian, Japanese, Kannada, Kazakh, Korean,
    Latin, Latvian, Lithuanian, Lezgian, Maltese, Mandarin Chinese,
    Nanay, Ossetic, Persian, Polish, Portuguese, Quechua, Romanian,
    Russian, Serbian/Croatian, (Colombian) Spanish, Swahili, Swedish,
    Turkish, and Yakut.

    Of these, 20 have complete paradigms with explicit forms in
    Tables 7 (formalized above). 6 have paradigm gaps (Table 8).
    The remaining 19 are discussed in the appendices or show patterns
    consistent with the four attested types. -/

/-- No language in the sample violates *ABA. -/
theorem sample_no_aba :
    fullParadigms.all (fun p =>
      match p.nsForm, p.suForm, p.skForm with
      | some ns, some su, some sk => decide (classifyTriple ns su sk).IsAttested
      | _, _, _ => true) = true := by decide

/-- All paradigm-gap languages have gaps at the TOP of the hierarchy,
    consistent with the monotonicity prediction. -/
theorem gaps_at_top :
    gapParadigms.all (fun p =>
      -- if SK is present, SU must be present
      (p.skForm.isSome → p.suForm.isSome) ∧
      -- if SU is present, NS must be present
      (p.suForm.isSome → p.nsForm.isSome)) = true := by decide

end Dekier2021
