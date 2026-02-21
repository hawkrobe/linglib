import Linglib.Theories.Semantics.Tense.Basic
import Linglib.Theories.Semantics.Tense.TenseAspectComposition

/-!
# Kratzer (1998): More Structural Analogies Between Pronouns and Tenses
@cite{kratzer-1998}

Kratzer extends Partee's (1973) tense–pronoun analogy in three directions
beyond the shared indexical/anaphoric/bound classification:

## Core Contributions

1. **Aspect decomposition of English simple past** (§4): English "simple past"
   is morphologically fused but semantically = PRESENT tense + PERFECT aspect.
   This explains why English past can be used "out of the blue" (deictically):
   the tense head is PRESENT (indexical). German Preterit is a genuine PAST
   pronoun (anaphoric — requires a discourse antecedent).

2. **SOT deletion** (§5): the simultaneous reading under attitude embedding
   arises from morphological identity triggering optional deletion of the
   embedded tense, leaving the embedded clause tenseless (hence simultaneous).
   Past is NEVER ambiguous — it always encodes temporal precedence.

3. **Zero forms and locality** (§3): zero (phonologically empty) pronouns and
   tenses are licensed when a referential expression is locally bound by an
   agreeing head. This unifies zero tense under SOT, Japanese pro-drop, and
   reflexive reduction, and explains why Persian has zero pronouns but NOT
   zero tense (tense is in C, outside the local agreement domain of Agr/Infl).

4. **Reflexive ↔ simultaneous parallel** (§3): reflexive pronouns = locally
   bound zero pronouns; simultaneous tense = locally bound zero tense.
   Same locality condition, different referential domains.

## Key Distinction from Ogihara

Kratzer and Ogihara make the same SOT predictions (both derive shifted
and simultaneous readings) but differ on what "past" means:
- Kratzer: past is NEVER ambiguous; simultaneous = deletion of past
- Ogihara: past IS ambiguous; simultaneous = zero-tense reading of past

## References

- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
  *SALT VIII*, 92-110.
- Partee, B. (1973). Some structural analogies between tenses and pronouns.
- Klein, W. (1994). Time in Language.
-/

namespace Semantics.Tense.Kratzer

open Core.Tense
open Core.Reichenbach
open Semantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § SOT Deletion
-- ════════════════════════════════════════════════════════════════

/-- Kratzer's SOT deletion: when embedded tense morphology is identical
    to matrix tense morphology, the embedded tense can be optionally
    deleted, making the embedded clause temporally dependent on the
    matrix event time.

    `matrixTense`: the tense of the matrix clause
    `embeddedTense`: the tense of the embedded clause
    Returns whether deletion is possible. -/
def sotDeletionApplicable (matrixTense embeddedTense : GramTense) : Bool :=
  matrixTense == embeddedTense

/-- Deletion is applicable for past-under-past (the core SOT case). -/
theorem past_past_deletion :
    sotDeletionApplicable .past .past = true := rfl

/-- Deletion is NOT applicable for present-under-past (no morphological
    identity between present and past). -/
theorem present_past_no_deletion :
    sotDeletionApplicable .past .present = false := rfl

/-- When SOT deletion applies, the embedded reference time becomes
    the matrix event time (the embedded clause inherits matrix temporal
    coordinates). -/
def applyDeletion {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) : ReichenbachFrame Time where
  speechTime := matrixFrame.speechTime
  perspectiveTime := matrixFrame.eventTime
  referenceTime := matrixFrame.eventTime  -- R' = E_matrix after deletion
  eventTime := matrixFrame.eventTime


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Kratzer derives the simultaneous reading via SOT deletion.
    When deletion applies, R' = E_matrix, giving the PRESENT relation. -/
theorem kratzer_derives_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time)
    (hDeletion : sotDeletionApplicable .past .past = true) :
    (applyDeletion matrixFrame).isPresent := by
  simp [applyDeletion, ReichenbachFrame.isPresent]

/-- Kratzer derives the shifted reading: genuine past (no deletion).
    When deletion does not apply (or is not chosen), the embedded
    past tense contributes its own temporal precedence. -/
theorem kratzer_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time)
    (hPast : embeddedR < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame embeddedR embeddedE).isPast := by
  simp [embeddedFrame, ReichenbachFrame.isPast]
  exact hPast

/-- SOT deletion yields the simultaneous reading: R' = E_matrix. -/
theorem kratzer_deletion_yields_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) :
    (applyDeletion matrixFrame).referenceTime = matrixFrame.eventTime :=
  rfl

-- ════════════════════════════════════════════════════════════════
-- § Theory Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Kratzer (1998) theory identity card. -/
def KratzerTense : TenseTheory where
  name := "Kratzer 1998"
  citation := "Kratzer, A. (1998). More structural analogies between pronouns and tenses. SALT VIII, 92-110."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := false
  hasSOTDeletion := true
  simultaneousMechanism := "SOT deletion of morphologically identical embedded tense"

/-- Kratzer's key claim: past is NEVER zero tense. The simultaneous
    reading comes from deletion, not from an ambiguity in what "past"
    means. This is a categorical structural difference from Ogihara. -/
theorem kratzer_no_zero_tense :
    KratzerTense.hasZeroTense = false := rfl

/-- Kratzer uses deletion (not ambiguity) for the simultaneous reading. -/
theorem kratzer_uses_deletion :
    KratzerTense.hasSOTDeletion = true := rfl


-- ════════════════════════════════════════════════════════════════
-- § Tense Decomposition Structure
-- ════════════════════════════════════════════════════════════════

/-- Kratzer's decomposition of surface tense morphology into
    underlying tense head + optional aspect head (Kratzer 1998 §4).

    The key insight: surface morphology can fuse tense and aspect,
    hiding the underlying tense head. English "simple past" fuses
    PRESENT + PERFECT; German Preterit is a bare PAST. -/
structure KratzerDecomposition where
  /-- Language -/
  language : String
  /-- Surface morphological form -/
  surfaceForm : String
  /-- The underlying tense pronoun (tense head proper) -/
  tensePronoun : TensePronoun
  /-- Whether a PERFECT aspect head intervenes between VP and Tense -/
  hasPerfect : Bool
  deriving Repr, DecidableEq, BEq

/-- Can this form be used deictically ("out of the blue")?
    Derived: indexical tense head → deictic-compatible. -/
def KratzerDecomposition.canBeDeictic (d : KratzerDecomposition) : Bool :=
  d.tensePronoun.isIndexical

/-- Phonological overtness of the tense head, given locality. -/
def KratzerDecomposition.tenseOvertness (d : KratzerDecomposition)
    (localDomain : Bool) : Overtness :=
  Overtness.fromBinding d.tensePronoun.mode localDomain


-- ════════════════════════════════════════════════════════════════
-- § Aspect Decomposition: English Simple Past = PRES + PERF
-- ════════════════════════════════════════════════════════════════

/-! Kratzer (1998 §4): English "simple past" is morphologically fused but
semantically decomposes into PRESENT tense + PERFECT aspect. The tense head
is present (indexical, anchored to speech time); the aspect head (PERF)
introduces temporal precedence. This is literally `presPerfSimple` from
`TenseAspectComposition.lean`.

German Preterit, by contrast, has a genuine PAST tense head with no
intervening PERF. The PAST pronoun is anaphoric — it requires a
discourse-salient temporal antecedent. This explains the striking contrast:

  English: "I didn't turn off the stove." ✓ (out of the blue — deictic)
  German:  #"Ich schaltete den Herd nicht aus." ✗ (needs narrative context)
  German:  "Ich habe den Herd nicht ausgeschaltet." ✓ (present perfect ok) -/

open Semantics.TenseAspectComposition
open Semantics.Lexical.Verb.ViewpointAspect

/-- Kratzer's English simple past = PRESENT tense + PERFECT aspect.
    The tense head is PRESENT (indexical-compatible), so the surface form
    can be used deictically. Pastness comes from the PERF aspect head. -/
def kratzerEnglishPast : TensePronoun where
  varIndex := 0
  constraint := .present   -- KEY: present, not past!
  mode := .indexical        -- Can be deictic ("out of the blue")

/-- German Preterit: a genuine PAST pronoun.
    Must be anaphoric — requires a discourse-established temporal antecedent.
    Cannot be used "out of the blue" in modern German. -/
def kratzerGermanPreterit (n : ℕ) : TensePronoun where
  varIndex := n
  constraint := .past       -- Genuine past
  mode := .anaphoric         -- Must find antecedent in discourse

/-- English simple past has PRESENT tense constraint.
    Pastness is in the aspect (PERF), not the tense head. -/
theorem english_past_is_present :
    kratzerEnglishPast.constraint = .present := rfl

/-- German Preterit has PAST tense constraint. -/
theorem german_preterit_is_past (n : ℕ) :
    (kratzerGermanPreterit n).constraint = .past := rfl

/-- English simple past is indexical-compatible: can be used "out of the blue."
    German Preterit forces anaphoric mode: cannot be used "out of the blue." -/
theorem english_deictic_german_anaphoric (n : ℕ) :
    kratzerEnglishPast.isIndexical = true ∧
    (kratzerGermanPreterit n).isIndexical = false :=
  ⟨rfl, rfl⟩

/-- Kratzer's aspect decomposition bridge: the English simple past
    (PRESENT + PERFECT) maps to `presPerfSimple` from the compositional
    tense–aspect pipeline. The PRESENT tense head contributes `evalPres`;
    the PERFECT aspect head contributes `PERF (PRFV V)`.

    `presPerfSimple V tc w = evalPres (PERF (PRFV V)) tc w`

    This is the central prediction: English simple past and English
    present perfect have the SAME compositional semantics. They differ
    only in whether the PERF is morphologically fused or transparent. -/
theorem english_past_eq_presPerfSimple {W Time : Type*} [LinearOrder Time]
    (V : EventPred W Time) (tc : Time) (w : W) :
    presPerfSimple V tc w ↔
    ∃ pts : Core.Time.Interval Time, RB pts tc ∧ PRFV V w pts := Iff.rfl

/-- German Preterit maps to `simplePast` from the pipeline: genuine
    past tense (existential over past times) + perfective aspect. -/
theorem german_preterit_eq_simplePast {W Time : Type*} [LinearOrder Time]
    (V : EventPred W Time) (tc : Time) (w : W) :
    simplePast V tc w ↔
    ∃ t : Time, t < tc ∧ PRFV V w (Core.Time.Interval.point t) := Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- § Zero Tense and Locality
-- ════════════════════════════════════════════════════════════════

/-! Kratzer (1998 §3): zero (phonologically empty) referential expressions
arise when a bound variable is in a local agreement domain. This applies
uniformly to pronouns and tenses:

  - Zero tense under SOT: the embedded tense is locally bound by the
    attitude verb's Agr → surfaces as ∅
  - Japanese subject pro: locally bound by Agr → surfaces as ∅
  - Persian: zero PRONOUNS (locally bound by Agr) but NOT zero TENSE
    (tense is in C, outside the local domain of Agr in Infl)

The distribution of overt vs. zero follows from `Core.Tense.Overtness`. -/

/-- Zero tense: a bound present tense in a local agreement domain (Kratzer 1998).

    Under SOT in English, the embedded "past" morphology is analyzed as
    a locally bound PRESENT tense that surfaces as zero because of
    agreement locality. This is Kratzer's alternative to Ogihara's
    zero-tense ambiguity: the "zero" isn't an ambiguity of PAST — it's
    a genuinely different morpheme (bound PRESENT) licensed by locality. -/
def kratzerZeroTense (n : ℕ) : TensePronoun where
  varIndex := n
  constraint := .present    -- Present, not past
  mode := .bound            -- Locally bound → surfaces as zero

/-- Zero tense has present constraint (not past).
    Past is NEVER zero/ambiguous in Kratzer's theory. -/
theorem zero_tense_is_present (n : ℕ) :
    (kratzerZeroTense n).constraint = .present := rfl

/-- Zero tense surfaces as zero (from Core.Tense.Overtness). -/
theorem zero_tense_overtness (n : ℕ) :
    Overtness.fromBinding (kratzerZeroTense n).mode true = .zero := rfl

/-- Kratzer's key claim: past is NEVER zero tense (hasZeroTense = false).
    The zero morpheme under SOT is a bound PRESENT, not an ambiguous PAST.
    Contrast with `kratzerZeroTense` which IS zero but is PRESENT. -/
theorem past_never_zero :
    KratzerTense.hasZeroTense = false ∧
    (kratzerZeroTense 1).constraint = .present :=
  ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § Reflexive ↔ Simultaneous Parallel
-- ════════════════════════════════════════════════════════════════

/-! Kratzer (1998 §3) draws an explicit structural parallel between
reflexive binding and simultaneous tense:

  - Reflexive pronouns = locally bound entity pronouns → zero/reduced form
  - Simultaneous tense = locally bound temporal pronoun → zero tense

Both are instances of the same generalization: local binding by an
agreeing head yields a phonologically reduced (zero) referential expression.
The locality condition is the same; only the domain differs (entities
vs. times). -/

/-- The reflexive ↔ simultaneous parallel: both are locally bound
    referential expressions that surface as zero.

    Left conjunct: zero tense is bound (like a reflexive).
    Right conjunct: it surfaces as zero (like reflexive morphology). -/
theorem reflexive_simultaneous_parallel (n : ℕ) :
    (kratzerZeroTense n).isBound = true ∧
    Overtness.fromBinding (kratzerZeroTense n).mode true = .zero :=
  ⟨rfl, rfl⟩

/-- The German Preterit is NOT zero-compatible: it's free (anaphoric),
    so it surfaces as overt morphology regardless of locality.
    This parallels overt (non-reflexive) pronouns. -/
theorem german_preterit_always_overt (n : ℕ) (localDomain : Bool) :
    Overtness.fromBinding (kratzerGermanPreterit n).mode localDomain = .overt := by
  cases localDomain <;> rfl

/-- English indexical tense is also always overt: free expressions
    surface as overt regardless of locality. -/
theorem english_indexical_always_overt (localDomain : Bool) :
    Overtness.fromBinding kratzerEnglishPast.mode localDomain = .overt := by
  cases localDomain <;> rfl


end Semantics.Tense.Kratzer
