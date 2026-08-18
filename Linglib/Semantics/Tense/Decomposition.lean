import Linglib.Semantics.Tense.Basic

/-!
# Tense decomposition and SOT deletion

[kratzer-1998]'s architecture relating tense morphology to underlying
tense–aspect structure, extending [partee-1973]'s tense–pronoun analogy.
A surface tense form is a `SurfaceTense`: an underlying tense pronoun plus
an optional PERFECT aspect head. The three pronoun values the account uses
are `indexicalPresent` (the head of the English simple past — pastness from
PERF, hence deictic), `anaphoricPast` (the German Preterit — requires a
discourse antecedent), and `boundPresent` (zero tense — locally bound,
surfaces as zero via `Overtness`). SOT deletion (`sotDeletionApplicable`,
`applyDeletion`) deletes an embedded tense under morphological identity with
the matrix, leaving the embedded clause temporally dependent on the matrix
event time (`applyDeletion_isPresent`).

The paper-attributed predictions, the Fragment instances, and the
divergence from [ogihara-1996] live in `Studies/Kratzer1998.lean`.
-/

namespace Tense.Decomposition

open Time Tense

/-! ### SOT deletion -/

/-- [kratzer-1998]'s SOT deletion condition: an embedded tense whose
    morphology is identical to the matrix tense can be optionally deleted,
    making the embedded clause temporally dependent on the matrix event
    time. -/
def sotDeletionApplicable (matrixTense embeddedTense : Finset Ordering) : Bool :=
  decide (matrixTense = embeddedTense)

/-- Deletion is applicable for past-under-past (the core SOT case). -/
theorem past_past_deletion :
    sotDeletionApplicable past past = true := by decide

/-- Deletion is not applicable for present-under-past (no morphological
    identity between present and past). -/
theorem present_past_no_deletion :
    sotDeletionApplicable past present = false := by decide

/-- The embedded frame after SOT deletion: the embedded reference time
    becomes the matrix event time (the embedded clause inherits the matrix
    temporal coordinates). -/
def applyDeletion {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) : ReichenbachFrame Time where
  speechTime := matrixFrame.speechTime
  perspectiveTime := matrixFrame.eventTime
  referenceTime := matrixFrame.eventTime
  eventTime := matrixFrame.eventTime

/-- Deletion and the SOT `simultaneousFrame` agree definitionally: deleting
    the embedded tense yields exactly the simultaneous-reading frame whose
    embedded event time is the matrix event time — the formal core of the
    Kratzer/Ogihara "same predictions" agreement. -/
theorem applyDeletion_eq_simultaneousFrame {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) :
    applyDeletion matrixFrame = simultaneousFrame matrixFrame matrixFrame.eventTime :=
  rfl

/-- Deletion derives the simultaneous reading: after deletion the embedded
    reference time is the matrix event time, the PRESENT relation. -/
theorem applyDeletion_isPresent {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) :
    (applyDeletion matrixFrame).isPresent := rfl

/-! ### Surface tense -/

/-- [kratzer-1998] §4's decomposition of a surface tense form: an
    underlying tense pronoun plus an optional PERFECT aspect head between
    VP and Tense. Surface morphology can fuse the two (English simple past
    = `indexicalPresent` + PERFECT); surface-form metadata lives with the
    Fragment entries that instantiate this structure. -/
structure SurfaceTense where
  /-- The underlying tense pronoun (tense head proper) -/
  tensePronoun : TensePronoun
  /-- Whether a PERFECT aspect head intervenes between VP and Tense -/
  hasPerfect : Bool
  deriving DecidableEq

/-- A surface form can be used deictically ("out of the blue") iff its
    tense head is indexical. -/
def SurfaceTense.canBeDeictic (d : SurfaceTense) : Prop :=
  d.tensePronoun.isIndexical

instance (d : SurfaceTense) : Decidable d.canBeDeictic :=
  inferInstanceAs (Decidable d.tensePronoun.isIndexical)

/-- Phonological overtness of the tense head, given locality. -/
def SurfaceTense.tenseOvertness (d : SurfaceTense)
    (localDomain : Bool) : Overtness :=
  Overtness.fromBinding d.tensePronoun.mode localDomain

/-! ### The tense pronouns -/

/-- The indexical PRESENT pronoun — [kratzer-1998] §4's tense head of the
    English simple past (and German Perfekt): pastness comes from the
    PERFECT aspect head, so the form can be used deictically ("out of the
    blue"). English simple past and present perfect share this head; they
    differ only in whether the PERF is morphologically fused. -/
def indexicalPresent : TensePronoun where
  varIndex := 0
  constraint := present
  mode := .indexical

/-- The anaphoric PAST pronoun — the German Preterit: a genuine past
    requiring a discourse-established temporal antecedent, so it cannot be
    used "out of the blue". -/
def anaphoricPast (n : ℕ) : TensePronoun where
  varIndex := n
  constraint := past
  mode := .anaphoric

/-- The bound PRESENT pronoun — [kratzer-1998] §3's zero tense: locally
    bound by the attitude verb's agreement head, it surfaces as zero
    (`Overtness.fromBinding`), by the same locality that reduces locally
    bound entity pronouns to reflexives. This is Kratzer's alternative to
    [ogihara-1996]'s ambiguous past: the "zero" is not a reading of PAST
    but a distinct bound PRESENT morpheme. -/
def boundPresent (n : ℕ) : TensePronoun where
  varIndex := n
  constraint := present
  mode := .bound

end Tense.Decomposition
