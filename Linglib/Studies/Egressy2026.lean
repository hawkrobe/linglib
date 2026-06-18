import Linglib.Syntax.Minimalist.Probe
import Linglib.Semantics.Tense.Basic
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


/-! ### The reading rule (language-independent) and the predictions -/

/-- The language-independent rule mapping a boundary's transparency to the
    available embedded-tense readings: a transparent boundary licenses both the
    back-shifted and the simultaneous reading (SOT deletion is optional), an
    opaque boundary only the back-shifted one. -/
def readingsOf (transparent : Bool) : List EmbeddedTenseReading :=
  if transparent then [.shifted, .simultaneous] else [.shifted]

/-- The embedded-tense readings available for a clause type — derived from its
    size via `transparentToSOTAgree`, not stipulated. -/
def ClauseType.availableReadings (ct : ClauseType) : List EmbeddedTenseReading :=
  readingsOf ct.complementSize.transparentToSOTAgree

/-- Non-speech-reporting (TP) clauses have *both* readings. -/
theorem nonSpeech_both :
    ClauseType.nonSpeechReporting.availableReadings = [.shifted, .simultaneous] := by decide

/-- Speech-reporting (SayP) clauses have *only* the back-shifted reading. -/
theorem speech_backshift_only :
    ClauseType.speechReporting.availableReadings = [.shifted] := by decide

/-- The core asymmetry: the simultaneous reading is blocked exactly in
    speech-reporting clauses. -/
theorem simultaneous_iff_nonSpeech (ct : ClauseType) :
    .simultaneous ∈ ct.availableReadings ↔ ct = .nonSpeechReporting := by
  cases ct <;> decide


/-! ### Unification with the binary SOT parameter

[egressy-2026]'s point is that Hungarian is *not* at a language-wide "SOT
stage": its two clause types realize the two values of the binary
`SOTParameter` ([ogihara-sharvit-2012]) clause-internally. A non-speech-reporting
clause behaves like an English (`.relative`) complement; a speech-reporting one
like a Japanese (`.absolute`) complement. -/

/-- A non-speech-reporting clause reproduces the English (`.relative`) parameter. -/
theorem nonSpeech_eq_relative :
    ClauseType.nonSpeechReporting.availableReadings = availableReadings .relative := by decide

/-- A speech-reporting clause reproduces the Japanese (`.absolute`) parameter. -/
theorem speech_eq_absolute :
    ClauseType.speechReporting.availableReadings = availableReadings .absolute := by decide


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

/-- The grammatical prediction: the simultaneous reading is available iff the
    clause is transparent to SOT-Agree. -/
def predictsSimultaneous (d : SOTDatum) : Bool :=
  d.clauseType.complementSize.transparentToSOTAgree

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
though it is grammatically available (`nonSpeech_both`). This is prose in the
paper, recorded here as the data fact that direct-perception clauses are
observed simultaneous. -/

/-- The direct-perception data (perception and dreaming). -/
def directPerceptionData : List SOTDatum := [ex4_lat, ex5_hall, ex6_almodik]

/-- Direct-perception clauses are observed with the simultaneous reading, while
    grammatically they are non-speech-reporting (both readings available); the
    absence of the back-shifted reading is pragmatic. -/
theorem direct_perception_simultaneous :
    directPerceptionData.all (fun d =>
      d.simultaneousObserved && (d.clauseType.availableReadings == [.shifted, .simultaneous])) = true := by
  decide


/-! ### Multiple embedding and locality ([egressy-2026], §2.3)

Simultaneity is computed **locally** between structurally adjacent clauses
([ogihara-1996]): the simultaneous reading between a container and its
immediate complement is licensed iff the complement is transparent
(non-speech-reporting) *and* both carry `PAST` (an agreeing past for SOT
deletion). The type of a non-adjacent clause is irrelevant. -/

/-- Tense of a clause, coarse enough for the locality facts (past vs. the
    intervening future of [ogihara-1995]'s past-under-*will*-under-past). -/
inductive ClTense where
  | past | pres | fut
  deriving DecidableEq, Repr

/-- Is this `PAST`? (SOT deletion needs an agreeing past above.) -/
def ClTense.isPast : ClTense → Bool
  | .past => true
  | _     => false

/-- A node in an embedding chain: its tense and clause type. -/
structure ClauseNode where
  tense : ClTense
  type  : ClauseType
  deriving Repr

/-- A multiple-embedding configuration: the matrix tense and the embedded
    clauses, ordered from the highest complement down to the deepest. -/
structure EmbConfig where
  matrixTense : ClTense
  embedded : List ClauseNode

/-- Local SOT licensing for a (container, contained) adjacency: the contained
    clause is read simultaneously with its container iff it is transparent
    (non-speech) and both are `PAST`. -/
def simLicensed (containerTense : ClTense) (contained : ClauseNode) : Bool :=
  containerTense.isPast && contained.tense.isPast &&
    contained.type.complementSize.transparentToSOTAgree

/-- The per-level simultaneity profile, top-to-bottom: for each embedded clause,
    whether it is simultaneous with its immediate container. -/
def simProfileAux : ClTense → List ClauseNode → List Bool
  | _, [] => []
  | container, c :: rest => simLicensed container c :: simProfileAux c.tense rest

/-- The simultaneity profile of a configuration. -/
def EmbConfig.simProfile (cfg : EmbConfig) : List Bool :=
  simProfileAux cfg.matrixTense cfg.embedded

/-- ex. (16): shout > see > be. The intermediate (content of the shout) is
    speech-reporting → back-shifted; the deepest (Mari's perception) is
    non-speech-reporting → simultaneous. Only adjacent clauses interact. -/
def ex16 : EmbConfig where
  matrixTense := .past
  embedded := [⟨.past, .speechReporting⟩, ⟨.past, .nonSpeechReporting⟩]

theorem ex16_profile : ex16.simProfile = [false, true] := by decide

/-- ex. (17): hear > shout > be. The intermediate (Mari's perception of the
    shouting) is non-speech-reporting → simultaneous; the deepest (content of
    the shout) is speech-reporting → back-shifted. The opposite of (16). -/
def ex17 : EmbConfig where
  matrixTense := .past
  embedded := [⟨.past, .nonSpeechReporting⟩, ⟨.past, .speechReporting⟩]

theorem ex17_profile : ex17.simProfile = [true, false] := by decide

/-- ex. (10): dream > see > be, all non-speech-reporting → simultaneous on both
    levels. -/
def ex10 : EmbConfig where
  matrixTense := .past
  embedded := [⟨.past, .nonSpeechReporting⟩, ⟨.past, .nonSpeechReporting⟩]

theorem ex10_profile : ex10.simProfile = [true, true] := by decide

/-- ex. (15): shout > growl > be, all speech-reporting → back-shifted on both
    levels. -/
def ex15 : EmbConfig where
  matrixTense := .past
  embedded := [⟨.past, .speechReporting⟩, ⟨.past, .speechReporting⟩]

theorem ex15_profile : ex15.simProfile = [false, false] := by decide

/-- [ogihara-1995]'s ex. (18) (English): *said* > *will claim* > *was*. The
    deepest `was` has no simultaneous reading with the matrix `said`: its
    immediate container is the future *will claim*, so there is no agreeing
    `PAST` above it. Simultaneity needs the *next lowest* tense to be past —
    locality is over the agreeing tense, independently of clause size. (English
    is size-insensitive in [egressy-2026]'s terms, so the SayP opacity is not
    what is at issue here; the `simLicensed` agreeing-past conjunct is.) -/
def ex18 : EmbConfig where
  matrixTense := .past
  embedded := [⟨.fut, .speechReporting⟩, ⟨.past, .speechReporting⟩]

theorem ex18_no_simultaneous : ex18.simProfile = [false, false] := by decide


/-! ### Williams-Cycle support over a de re alternative ([egressy-2026], §3.3)

A *res*-movement (de re) derivation of the simultaneous reading ([abusch-1988],
[abusch-1997]) moves the embedded `PAST` to an A-position inside the matrix VP.
Such movement would not be stopped by the `Say` layer, so it is *size-blind*:
it predicts the simultaneous reading for speech-reporting clauses too. The
observed asymmetry (`speech_backshift_only`) therefore favors the SOT-Agree
analysis, whose dependency obeys the Williams Cycle. -/

/-- The size-blind prediction of an unbounded res-movement de re account. -/
def deReReadings (_ct : ClauseType) : List EmbeddedTenseReading := [.shifted, .simultaneous]

/-- The de re account overgenerates: it makes the simultaneous reading available
    for speech-reporting clauses, contradicting the data, whereas the SOT-Agree
    account correctly blocks it. -/
theorem de_re_overgenerates :
    .simultaneous ∈ deReReadings .speechReporting ∧
    .simultaneous ∉ ClauseType.speechReporting.availableReadings := by decide


end Egressy2026
