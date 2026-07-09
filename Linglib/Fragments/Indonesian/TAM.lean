/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Features.Register

/-!
# Indonesian temporal markers

The temporal markers of [sneddon-1996] (§§2.142–52). Indonesian verbs are
invariant for tense and aspect (§2.142: "the form of the verb does not change
to indicate tense or aspect"); time is inferred from context, indicated by
adjuncts, or marked by these words within the predicate. Relative to a past
reference point the same markers shift readings: *sudah* and *telah* 'had
V-ed', *sedang* 'was V-ing', *akan* 'would' (§2.152).

Excluded: *sempat* 'have the opportunity', which [sneddon-1996] classifies as
a modal (§2.153), and *belum* 'not yet', listed with the negatives and
analysed as negation plus *sudah* (§2.156). WALS codings for Indonesian live
in `Data.WALS.Features` (iso `ind`), not here.
-/

namespace Indonesian

/-- What a temporal marker indicates about the action relative to the moment
of utterance or a reference event ([sneddon-1996] §§2.143–51). -/
inductive TemporalMeaning where
  /-- Action has occurred or a state has been achieved (§2.143). -/
  | occurred
  /-- Action is in progress (§2.145). -/
  | inProgress
  /-- Action is still occurring (§2.147). -/
  | stillOccurring
  /-- Future event or state (§2.148). -/
  | future
  /-- Future event a considerable time ahead (§2.149). -/
  | distantFuture
  /-- Action has just occurred or a state has just been reached (§2.150). -/
  | justOccurred
  /-- Action occurred in the far past; 'ever, once' (§2.151). -/
  | farPast
  deriving DecidableEq, Repr

/-- A temporal marker ([sneddon-1996] §2.142): a word within the predicate
indicating that the action has occurred, is occurring, or is yet to occur.
Traditional studies call these 'aspect markers', grouping *akan* with the
modals. -/
structure TemporalMarker where
  form : String
  meaning : TemporalMeaning
  /-- `.formal` for *telah*, "almost entirely confined to writing and very
      formal speech"; `.neutral` for the rest, which [sneddon-1996] leaves
      unrestricted (§2.144). -/
  register : Features.Register.Level
  /-- `some b`: §§2.143–51 states or illustrates that the marker does
      (`true`) or does not (`false`) occur with non-verbal predicates;
      `none`: not addressed there. -/
  nonverbalPredicates : Option Bool
  deriving DecidableEq, Repr

/-- *sudah*: action occurred or state achieved; with state verbs, inception
and/or continuation (*Dia sudah tidur* 'He has gone to bed/is asleep'); with
non-verbal predicates ≈ 'already' (*Dia sudah tinggi/guru*) (§2.143). -/
def sudah : TemporalMarker := ⟨"sudah", .occurred, .neutral, some true⟩

/-- *telah*: same meaning as *sudah*, differing only in register (§2.144). -/
def telah : TemporalMarker := ⟨"telah", .occurred, .formal, none⟩

/-- *sedang*: action in progress, 'in the process of' (§2.145). -/
def sedang : TemporalMarker := ⟨"sedang", .inProgress, .neutral, none⟩

/-- *lagi*: replaces *sedang*; less frequent and not used by all speakers
(§2.146). -/
def lagi : TemporalMarker := ⟨"lagi", .inProgress, .neutral, none⟩

/-- *tengah*: replaces *sedang*; less frequent and not used by all speakers
(§2.146). -/
def tengah : TemporalMarker := ⟨"tengah", .inProgress, .neutral, none⟩

/-- *masih*: action still occurring; with non-verbal predicates 'still'
(*Dia masih muda/pegawai*) (§2.147). -/
def masih : TemporalMarker := ⟨"masih", .stillOccurring, .neutral, some true⟩

/-- *akan*: future event or state (*Tugasnya akan berat* 'His task will be
heavy') (§2.148). -/
def akan : TemporalMarker := ⟨"akan", .future, .neutral, some true⟩

/-- *bakal*: future a considerable time ahead only; verbal predicates only
(within a noun phrase it means 'prospective': *bakal presiden*). Colloquial
*bakalan* is similar but cannot occur in a noun phrase (§2.149). -/
def bakal : TemporalMarker := ⟨"bakal", .distantFuture, .neutral, some false⟩

/-- *baru*: action just occurred or state just reached (*Umurnya baru empat
tahun* 'She's just four years old'); often followed by *saja* for emphasis
(§2.150). -/
def baru : TemporalMarker := ⟨"baru", .justOccurred, .neutral, some true⟩

/-- *pernah*: action in the far past, never of recent events; 'ever', but
unlike English *ever* not restricted to negative and interrogative contexts;
also 'once' (§2.151). *belum pernah* is the negative of *sudah pernah* and
differs from *tidak pernah* 'never (habitually)' (§2.157). -/
def pernah : TemporalMarker := ⟨"pernah", .farPast, .neutral, none⟩

/-- The temporal markers of [sneddon-1996] §§2.143–51, in order of
presentation. -/
def temporalMarkers : List TemporalMarker :=
  [sudah, telah, sedang, lagi, tengah, masih, akan, bakal, baru, pernah]

/-- *telah* has the same meaning as *sudah*; the difference between the two
is in register (§2.144). -/
theorem telah_sudah_same_meaning_distinct_register :
    telah.meaning = sudah.meaning ∧ telah.register ≠ sudah.register := by decide

/-- *lagi* and *tengah* are the replacements for progressive *sedang*
(§2.146). -/
theorem inProgress_markers :
    (temporalMarkers.filter (·.meaning == .inProgress)).map (·.form) =
      ["sedang", "lagi", "tengah"] := by decide

/-- The markers §§2.143–51 attests with non-verbal predicates: *sudah*,
*masih*, *akan*, *baru*. -/
theorem nonverbal_attested :
    (temporalMarkers.filter (·.nonverbalPredicates == some true)).map (·.form) =
      ["sudah", "masih", "akan", "baru"] := by decide

end Indonesian
