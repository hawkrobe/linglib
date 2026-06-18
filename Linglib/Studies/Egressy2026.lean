import Linglib.Syntax.Minimalist.Probe
import Linglib.Semantics.Tense.Basic
import Linglib.Semantics.Tense.Sequence.Basic
import Linglib.Fragments.Hungarian.Predicates

/-!
# [egressy-2026]: Size-Sensitive Sequence of Tense in Hungarian
[egressy-2026]

János Egressy shows that the availability of the *simultaneous* reading of a
past-under-past configuration in Hungarian depends on a **clause-internal**
property of the embedded clause, not on the matrix verb or on the
complementizer *hogy* (which is an edge marker, not a C head — Hungarian has no
CP, [kiss-2023]):

* **Non-speech-reporting clauses** (perception, dreaming, belief — clauses that
  do *not* encode the content of a verbal/representational sign) pattern like
  English: a past-under-past clause has a simultaneous reading (and, pragmatics
  permitting, a back-shifted one).
* **Speech-reporting clauses** (the content of *say*/*shout*/*growl*) pattern
  like Japanese: only the back-shifted reading.

The analysis: speech-reporting clauses carry an extra `Say` layer (Say > Foc >
T) above the bare TP of non-speech-reporting clauses ([major-2021],
[krifka-2023]). The simultaneous reading comes from the optional LF deletion of
the embedded `PAST` under an agreeing matrix `PAST` — the Sequence of Tense
Rule of [ogihara-1996] / [ogihara-sharvit-2012]. Crucially this SOT-Agree obeys
the **Williams Cycle** ([williams-2003]), i.e. [keine-2019]'s *selective
opacity* generalized from movement to Agree: an Agree dependency from `T`
cannot cross a larger `Say` projection. So it crosses a TP (simultaneous
available) but is blocked by a SayP (back-shift only). Williams-Cycle
sensitivity favors the SOT-Agree analysis over a *res*-movement (de re) account
of simultaneity ([abusch-1988], [abusch-1997]), which would be unboundedly free
(see `de_re_overgenerates`).

## Formalization strategy

The opacity is **derived, not stipulated**: the `Say` head sits at `fValue 5`
in the shared functional sequence (`Syntax.Minimalist`), and the SOT
transparency of a complement is exactly `ComplementSize.transparentToSOTAgree`
(`fLevel < fValue .Say`). This reuses the very machinery that derives the ban
on hyperraising and Hindi long-distance Agree ([keine-2020]); see
`sot_is_selective_opacity`. There is no language-wide "SOT stage" parameter —
the two Hungarian clause types reproduce the two values of the binary
`SOTParameter` clause-internally (`nonSpeech_eq_relative`, `speech_eq_absolute`).
-/

namespace Egressy2026

open Tense (EmbeddedTenseReading SOTParameter availableReadings)
open SequenceOfTense
open Core.Order (notAfter before after unrestricted overlapping)
open Minimalist
open Hungarian.Predicates


/-! ### The two clause types and their size -/

/-- The clause-internal distinction [egressy-2026] draws: whether an embedded
    clause encodes the content of a verbal/representational sign. This is a
    property of the *clause*, independent of the matrix verb (`hall` 'hear' and
    `gondol` 'think' embed either type) and of *hogy*. -/
inductive ClauseType where
  /-- Perception, dreaming, belief: no `Say` layer, a bare TP. -/
  | nonSpeechReporting
  /-- The content of a verbal/representational sign: an extra `Say` layer (SayP). -/
  | speechReporting
  deriving DecidableEq, Repr

/-- The structural size of each clause type in the shared functional sequence:
    non-speech-reporting = TP, speech-reporting = SayP (Say > Foc > T). -/
def ClauseType.complementSize : ClauseType → ComplementSize
  | .nonSpeechReporting => .tP
  | .speechReporting    => .sayP

/-- Speech-reporting clauses are strictly larger than non-speech-reporting
    ones (SayP dominates TP). -/
theorem speech_larger_than_nonspeech :
    ClauseType.nonSpeechReporting.complementSize.fLevel <
    ClauseType.speechReporting.complementSize.fLevel := by decide


/-! ### SOT-Agree opacity is selective opacity (the Williams Cycle) -/

/-- The Sequence-of-Tense probe: a `T`-probe whose horizon is the `Say` layer.
    Deletion-under-Agree of an embedded `PAST` searches down from a matrix `T`
    and is terminated by a `Say` head ([egressy-2026], generalizing
    [keine-2019]). -/
def sotProbe : Probe.Profile := ⟨.T, some .Say⟩

/-- Projected heads of a non-speech-reporting clause (a bare TP): no `Say`. -/
def nonSpeechSpine : List Cat := [.V, .v, .T]

/-- Projected heads of a speech-reporting clause (a SayP): contains `Say`. -/
def speechSpine : List Cat := [.V, .v, .T, .Say]

/-- The SOT probe crosses a TP: a non-speech-reporting clause is transparent. -/
theorem sot_crosses_TP : sotProbe.transparentToLabel nonSpeechSpine = true := by decide

/-- The SOT probe is blocked by a SayP: a speech-reporting clause is opaque. -/
theorem sot_blocked_by_SayP : sotProbe.transparentToLabel speechSpine = false := by decide

/-- **The unification.** SOT-Agree opacity is the *same* selective-opacity
    mechanism that the syntax layer uses for movement and Agree: the
    fValue-keyed `ComplementSize.transparentToSOTAgree` agrees with the
    horizon-keyed `Probe.transparentToLabel` of `sotProbe` on both clause
    types. (Compare `Minimalist.Probe` `a_movement_typology` for hyperraising.) -/
theorem sot_is_selective_opacity :
    ClauseType.nonSpeechReporting.complementSize.transparentToSOTAgree =
      sotProbe.transparentToLabel nonSpeechSpine ∧
    ClauseType.speechReporting.complementSize.transparentToSOTAgree =
      sotProbe.transparentToLabel speechSpine := by decide

/-- **Upward entailment** ([keine-2020]): the SayP boundary is monotone — any
    complement at or above the `Say` layer is opaque to SOT-Agree. (Speas–Tenny
    `SA`, `Force`, and `C` all sit at or above `Say`.) -/
theorem sot_opaque_above_say (cs : ComplementSize)
    (h : fValue .Say ≤ cs.fLevel) :
    cs.transparentToSOTAgree = false := by
  simp only [ComplementSize.transparentToSOTAgree, ComplementSize.fLevel,
    decide_eq_false_iff_not, Nat.not_lt] at h ⊢
  omega


/-! ### The Egressy license and the predictions

The Sequence-of-Tense rule is a `SequenceOfTense.LocalLicense`: the `Say`-boundary
size gate, refined by an agreeing-past gate (SOT deletion needs an agreeing
`PAST`). Built from the shared schemas, so the predictions are the foundation's
`Simultaneous`/`Backshifted`, not a study-local reading function. -/

/-- The `Say` boundary as a framework-neutral `Clause.Size`. -/
def sayBoundary : Clause.Size := ComplementSize.sayP.toClauseSize

/-- A clause node: a tense cell (`notAfter` = past, `after` = future — the
    ungated reading set of [kauf-zeijlstra-2018]) and the neutral size of its
    `ClauseType`. -/
def clauseNode (tense : Finset Ordering) (ct : ClauseType) : Node :=
  ⟨tense, ct.complementSize.toClauseSize⟩

/-- A past matrix clause (the container; only its tense matters to licensing). -/
def pastMatrix : Node := ⟨notAfter, 0⟩

/-- The agreeing-past gate: SOT deletion needs both the container and the
    contained clause to be morphologically past ([ogihara-1996]). -/
def agreeingPast : Node → Node → Bool :=
  fun a c => (a.tense == notAfter) && (c.tense == notAfter)

/-- [egressy-2026]'s license: the `Say`-boundary size gate refined by the
    agreeing-past gate. The size gate blocks simultaneity in speech-reporting
    (SayP) clauses; the agreeing-past refinement additionally blocks it under an
    intervening future (see `ex18`). -/
def egressyLicense : LocalLicense := (sizeGatedLicense sayBoundary).gate agreeingPast

/-- The framework-neutral `Clause.transparentTo` at the `Say` boundary reproduces
    the Minimalist `ComplementSize.transparentToSOTAgree` — the bridge that
    justifies stating SOT over `Clause.Size` rather than `Cat`. -/
theorem transparentToSOTAgree_iff_clause (cs : ComplementSize) :
    cs.transparentToSOTAgree = true ↔ Clause.transparentTo cs.toClauseSize sayBoundary := by
  simp [ComplementSize.transparentToSOTAgree, ComplementSize.toClauseSize, sayBoundary,
    ComplementSize.sayP, ComplementSize.fLevel, Clause.transparentTo_iff]

/-- Bridge from licensed atoms to the legacy `EmbeddedTenseReading` (atoms are
    canonical; this adapter feeds the binary `SOTParameter` comparison). -/
def toReadings (s : Finset Ordering) : List EmbeddedTenseReading :=
  (if Backshifted s then [EmbeddedTenseReading.shifted] else []) ++
  (if Simultaneous s then [EmbeddedTenseReading.simultaneous] else [])

/-- Non-speech-reporting (TP) clauses license both readings. -/
theorem nonSpeech_both :
    Simultaneous (egressyLicense pastMatrix (clauseNode notAfter .nonSpeechReporting)) ∧
    Backshifted  (egressyLicense pastMatrix (clauseNode notAfter .nonSpeechReporting)) := by decide

/-- Speech-reporting (SayP) clauses license only the back-shifted reading. -/
theorem speech_backshift_only :
    ¬ Simultaneous (egressyLicense pastMatrix (clauseNode notAfter .speechReporting)) ∧
    Backshifted    (egressyLicense pastMatrix (clauseNode notAfter .speechReporting)) := by decide

/-- The core asymmetry: simultaneity is blocked exactly in speech-reporting clauses. -/
theorem simultaneous_iff_nonSpeech (ct : ClauseType) :
    Simultaneous (egressyLicense pastMatrix (clauseNode notAfter ct)) ↔ ct = .nonSpeechReporting := by
  cases ct <;> decide


/-! ### Unification with the binary SOT parameter

Hungarian is *not* at a language-wide "SOT stage": its two clause types realize
the two values of the binary `SOTParameter` ([ogihara-sharvit-2012])
clause-internally — a non-speech-reporting clause behaves like an English
(`.relative`) complement, a speech-reporting one like a Japanese (`.absolute`) one. -/

/-- A non-speech-reporting clause reproduces the English (`.relative`) parameter. -/
theorem nonSpeech_eq_relative :
    toReadings (egressyLicense pastMatrix (clauseNode notAfter .nonSpeechReporting))
      = availableReadings .relative := by decide

/-- A speech-reporting clause reproduces the Japanese (`.absolute`) parameter. -/
theorem speech_eq_absolute :
    toReadings (egressyLicense pastMatrix (clauseNode notAfter .speechReporting))
      = availableReadings .absolute := by decide


/-! ### Empirical data ([egressy-2026], §2)

The verbs are grounded in `Hungarian.Predicates`; clause types are assigned by
the embedding predicate (perception/cognition → non-speech-reporting;
communication → speech-reporting). All examples are past-under-past with the
embedded copula *volt* 'was'. -/

/-- A past-under-past judgment: matrix verb, the embedded clause type, and
    whether the simultaneous reading is observed. -/
structure SOTDatum where
  /-- Matrix verb (Hungarian surface form) -/
  matrixVerb : String
  /-- English gloss of the matrix verb -/
  matrixGloss : String
  /-- The embedded clause type -/
  clauseType : ClauseType
  /-- Example sentence -/
  example_ : String
  /-- Is the simultaneous reading observed? -/
  simultaneousObserved : Bool
  deriving Repr

/-- ex. (4): direct perception with *lát* 'see' — simultaneous (only). -/
def ex4_lat : SOTDatum where
  matrixVerb := "látta"; matrixGloss := "saw"; clauseType := .nonSpeechReporting
  example_ := "Peti saját szemével látta, hogy Mari szomorú volt."
  simultaneousObserved := true

/-- ex. (5): direct perception with *hall* 'hear' — simultaneous (only). -/
def ex5_hall : SOTDatum where
  matrixVerb := "hallotta"; matrixGloss := "heard"; clauseType := .nonSpeechReporting
  example_ := "Peti saját fülével hallotta, hogy Mari sírt."
  simultaneousObserved := true

/-- ex. (6): dreaming with *álmodik* — simultaneous (only). -/
def ex6_almodik : SOTDatum where
  matrixVerb := "álmodta"; matrixGloss := "dreamed"; clauseType := .nonSpeechReporting
  example_ := "Peti azt álmodta, hogy Mari szomorú volt."
  simultaneousObserved := true

/-- ex. (7): belief with *gondol* 'think' — simultaneous and back-shifted. -/
def ex7_gondol : SOTDatum where
  matrixVerb := "gondolta"; matrixGloss := "thought"; clauseType := .nonSpeechReporting
  example_ := "Peti azt gondolta, hogy Mari szomorú volt."
  simultaneousObserved := true

/-- ex. (8): subject clause with *aggaszt* 'worry' — simultaneous and back-shifted. -/
def ex8_aggaszt : SOTDatum where
  matrixVerb := "aggasztotta"; matrixGloss := "worried"; clauseType := .nonSpeechReporting
  example_ := "Az aggasztotta Petit, hogy Mari szomorú volt."
  simultaneousObserved := true

/-- ex. (11a): saying with *mond* 'say' — back-shifted only. -/
def ex11_mond : SOTDatum where
  matrixVerb := "mondta"; matrixGloss := "said"; clauseType := .speechReporting
  example_ := "Peti azt mondta, hogy (sajnos) Mari szomorú volt."
  simultaneousObserved := false

/-- ex. (11b): shouting with *rikolt* 'shout' — back-shifted only. -/
def ex11_rikolt : SOTDatum where
  matrixVerb := "rikoltotta"; matrixGloss := "shouted"; clauseType := .speechReporting
  example_ := "Peti azt rikoltotta, hogy (sajnos) Mari szomorú volt."
  simultaneousObserved := false

/-- ex. (11c): growling with *morog* 'growl' — back-shifted only. -/
def ex11_morog : SOTDatum where
  matrixVerb := "morogta"; matrixGloss := "growled"; clauseType := .speechReporting
  example_ := "Peti azt morogta, hogy (sajnos) Mari szomorú volt."
  simultaneousObserved := false

/-- All single-embedding judgments. -/
def allData : List SOTDatum :=
  [ex4_lat, ex5_hall, ex6_almodik, ex7_gondol, ex8_aggaszt,
   ex11_mond, ex11_rikolt, ex11_morog]

/-- The grammatical prediction via the Egressy license: is the simultaneous
    reading available for this datum's clause type (under a past matrix)? -/
def predictsSimultaneous (d : SOTDatum) : Bool :=
  decide (Simultaneous (egressyLicense pastMatrix (clauseNode notAfter d.clauseType)))

/-- Every datum's observed simultaneous availability matches the prediction. -/
theorem all_data_match :
    allData.all (fun d => d.simultaneousObserved == predictsSimultaneous d) = true := by decide

/-! Fragment grounding: matrix verbs are the past forms of the lexical entries. -/

theorem ex4_verb_from_fragment : ex4_lat.matrixVerb = lat.formPastDef := rfl
theorem ex5_verb_from_fragment : ex5_hall.matrixVerb = hall.formPastDef := rfl
theorem ex7_verb_from_fragment : ex7_gondol.matrixVerb = gondol.formPastDef := rfl
theorem ex11_verb_from_fragment : ex11_mond.matrixVerb = mond.formPastDef := rfl


/-! ### Pragmatic narrowing: direct perception is simultaneous-only

For the direct-perception examples (4)–(6) the back-shifted reading is excluded
for *pragmatic* reasons — one cannot directly perceive a past event — even
though it is grammatically available (`nonSpeech_both`). This is the layer-2
`Narrowing` from the foundation: direct perception intersects the grammatical
reading set with the `overlapping` (=) constraint, leaving simultaneous-only
(`direct_perception_narrows`). -/

/-- The direct-perception data (perception and dreaming). -/
def directPerceptionData : List SOTDatum := [ex4_lat, ex5_hall, ex6_almodik]

/-- Direct-perception clauses are observed with the simultaneous reading, while
    grammatically they are non-speech-reporting (both readings available); the
    absence of the back-shifted reading is pragmatic. -/
theorem direct_perception_simultaneous :
    directPerceptionData.all (fun d =>
      d.simultaneousObserved &&
        (toReadings (egressyLicense pastMatrix (clauseNode notAfter d.clauseType))
          == [EmbeddedTenseReading.shifted, EmbeddedTenseReading.simultaneous])) = true := by
  decide

/-- Direct perception as a layer-2 `Narrowing`: it imposes the `overlapping` (=)
    constraint — only a simultaneous reading is perceivable. -/
def directPerception : Narrowing Unit := fun _ => overlapping

/-- The prose fact as a theorem: direct perception narrows the grammatically
    both-readings non-speech license down to simultaneous-only. -/
theorem direct_perception_narrows :
    directPerception.apply ()
        (egressyLicense pastMatrix (clauseNode notAfter .nonSpeechReporting)) = overlapping := by
  decide


/-! ### Multiple embedding and locality ([egressy-2026], §2.3)

Simultaneity is computed **locally** between structurally adjacent clauses
([ogihara-1996]): `SequenceOfTense.profile` folds `egressyLicense` pairwise down
the chain (matrix first). The simultaneity at each level is `Simultaneous` of
the licensed atoms. -/

/-- The per-level simultaneity profile of an embedded chain under a past matrix. -/
def simProfile (chain : List Node) : List Bool :=
  (profile egressyLicense pastMatrix chain).map (fun s => decide (Simultaneous s))

/-- ex. (16): shout > see > be. The intermediate (content of the shout) is
    speech-reporting → back-shifted; the deepest (Mari's perception) is
    non-speech-reporting → simultaneous. Only adjacent clauses interact. -/
def ex16 : List Node :=
  [clauseNode notAfter .speechReporting, clauseNode notAfter .nonSpeechReporting]
theorem ex16_profile : simProfile ex16 = [false, true] := by decide

/-- ex. (17): hear > shout > be. Intermediate (perception of the shouting) →
    simultaneous; deepest (content of the shout) → back-shifted. Opposite of (16). -/
def ex17 : List Node :=
  [clauseNode notAfter .nonSpeechReporting, clauseNode notAfter .speechReporting]
theorem ex17_profile : simProfile ex17 = [true, false] := by decide

/-- ex. (10): dream > see > be, all non-speech-reporting → simultaneous throughout. -/
def ex10 : List Node :=
  [clauseNode notAfter .nonSpeechReporting, clauseNode notAfter .nonSpeechReporting]
theorem ex10_profile : simProfile ex10 = [true, true] := by decide

/-- ex. (15): shout > growl > be, all speech-reporting → back-shifted throughout. -/
def ex15 : List Node :=
  [clauseNode notAfter .speechReporting, clauseNode notAfter .speechReporting]
theorem ex15_profile : simProfile ex15 = [false, false] := by decide

/-- Past-under-*will*-under-past (English; [ogihara-1996], discussed by
    [egressy-2026]): *said* > *will claim* > *was*. The intervening future *will*
    (`after`) is not an agreeing past, so the deepest `was` has no simultaneous
    reading — the `agreeingPast` gate blocks it, independently of size (English
    is size-insensitive here). -/
def ex18 : List Node :=
  [clauseNode after .speechReporting, clauseNode notAfter .speechReporting]
theorem ex18_no_simultaneous : simProfile ex18 = [false, false] := by decide


/-! ### Williams-Cycle support over an *unbounded* de re alternative ([egressy-2026], §3.3)

An *unbounded* res-movement (de re) derivation would move the embedded `PAST` to
an A-position inside the matrix VP, unstopped by the `Say` layer — hence
*size-blind*. Egressy argues the Williams Cycle rules this out: a size-blind
mechanism would license simultaneity for speech-reporting clauses, contrary to
fact. The foil below ([abusch-1988], [abusch-1997]) is exactly that size-blind
account; the *restricted* de re of [ogihara-sharvit-2012] (and the Polish
account of Mucha, Renans & Romoli) is a different, constrained mechanism this
argument does not, on its own, refute. -/

/-- The unbounded (size-blind) de re foil: it licenses every reading. Local to
    this study — it is Egressy's reductio against unbounded res-movement, not a
    neutral SOT mechanism. -/
def deReUnrestricted : LocalLicense := fun _ _ => unrestricted

/-- The *unbounded* de re foil overgenerates: size-blind, it licenses
    simultaneity for a speech-reporting clause, which `egressyLicense` correctly
    blocks. This refutes unbounded res-movement, not the restricted de re of
    [ogihara-sharvit-2012]. -/
theorem de_re_overgenerates :
    Simultaneous (deReUnrestricted pastMatrix (clauseNode notAfter .speechReporting)) ∧
    ¬ Simultaneous (egressyLicense pastMatrix (clauseNode notAfter .speechReporting)) := by decide


end Egressy2026
