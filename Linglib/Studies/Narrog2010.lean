import Linglib.Semantics.Modality.Narrog

/-!
# Narrog (2010): (Inter)subjectification in Modality and Mood
[narrog-2010]

Study file connecting [narrog-2010]'s theoretical claims to the
cross-linguistic data in `Semantics.Modality.DeonticNecessity`. The chapter argues
that strong obligation markers are cross-linguistically uncommon because
obligation is inherently face-threatening and socially costly, so languages
tend not to grammaticalize it — or to do so only indirectly.

[narrog-2012] ch. 2 decomposes the face-threatening potential of obligation
into three independent dimensions — performativity, volitivity, and
speaker-orientation. Face-threat is derived from this decomposition (see
`NarrogPosition.isFaceThreatening`), not stipulated per deontic necessity type.

## Key Empirical Claims

1. Strong obligation (*must*-type) markers exist in only 60/200 languages,
   barely more than weak obligation (*should*-type) at 62/200.
2. Japanese avoids strong obligation with 2nd-person subjects entirely
   (0 instances of *-(a)nakereba naranai* with 2nd-person subject).
3. The deontic-to-epistemic polyfunctionality (English *must*) is
   cross-linguistically rare: only 3 of 42 changes in Bybee et al.'s
   sample involve this shift.

## Bridges

- `Semantics.Modality.DeonticNecessity`: provides the 200-language data.
- `Semantics.Modality.Narrog`: provides the theoretical framework
  (volitivity, speaker-orientation, performativity, directionality).
-/

namespace Narrog2010

open Semantics.Modality.Narrog

-- ============================================================================
-- §−1. Diachronic Modal Change (Bybee et al. 1994, Table 2)
-- ============================================================================

/-! Cross-linguistic patterns of diachronic change in modal and mood
meanings, formalized on Narrog's 2D semantic map
(`Semantics.Modality.Narrog`). The central claim: modal meanings always
shift **upward** in the semantic map — toward increased
speaker-orientation — regardless of volitivity. The well-known deontic →
epistemic shift is just one instance.

Data: [bybee-perkins-pagliuca-1994] ch. 6, tabulated in
[narrog-2010] Table 2. -/

/-- An attested cross-linguistic modal meaning change.
    `gramCount` = number of "grams" (markers) in Bybee et al.'s sample
    exhibiting this change. -/
structure Change where
  label : String
  source : NarrogRegion
  target : NarrogRegion
  gramCount : Nat
  deriving Repr

/-- The 8 most common cross-linguistic changes in modal meanings.
    Source: [bybee-perkins-pagliuca-1994] ch. 6, tabulated in
    [narrog-2010] Table 2. -/
def commonChanges : List Change :=
  [ -- #1: future/prediction → imperative (13 grams)
    ⟨"future/prediction → imperative",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .mood⟩, 13⟩
  , -- #2: root possibility → permission (9 grams)
    ⟨"root possibility → permission",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .speakerOriented⟩, 9⟩
  , -- #3: root/epistemic possibility → admonitive (5 grams)
    ⟨"root/epistemic possibility → admonitive",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.volitive, .mood⟩, 5⟩
  , -- #4: obligation → imperative (4 grams)
    ⟨"obligation → imperative",
     ⟨.volitive, .speakerOriented⟩, ⟨.volitive, .mood⟩, 4⟩
  , -- #5: ability/root possibility → epistemic possibility (4 grams)
    ⟨"ability → epistemic possibility",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.nonVolitive, .speakerOriented⟩, 4⟩
  , -- #6: strong obligation → certainty (3 grams)
    ⟨"strong obligation → certainty",
     ⟨.volitive, .speakerOriented⟩, ⟨.nonVolitive, .speakerOriented⟩, 3⟩
  , -- #7: weak obligation → probability (2 grams)
    ⟨"weak obligation → probability",
     ⟨.volitive, .speakerOriented⟩, ⟨.nonVolitive, .speakerOriented⟩, 2⟩
  , -- #8: prediction/future → probability (2 grams)
    ⟨"prediction/future → probability",
     ⟨.nonVolitive, .eventOriented⟩, ⟨.nonVolitive, .speakerOriented⟩, 2⟩
  ]

/-- **Directionality of change**: every attested change increases (or maintains)
    speaker-orientation. This is Narrog's central diachronic claim.

    [narrog-2010] §3.1: "modal meanings always shift in the direction
    of increased speaker-orientation." -/
theorem directionality :
    commonChanges.all (fun c => c.source.orientation ≤ c.target.orientation) = true := by
  decide

/-- No attested change decreases speaker-orientation. -/
theorem no_decrease :
    commonChanges.all (fun c => !(c.target.orientation.toNat < c.source.orientation.toNat))
    = true := by decide

/-- Changes #6 and #7 cross the volitivity boundary (volitive → non-volitive)
    while maintaining speaker-orientation level. This shows volitivity is
    orthogonal to the directionality of change. -/
theorem volitivity_crossing :
    (commonChanges.filter (fun c =>
      c.source.volitivity != c.target.volitivity &&
      c.source.orientation == c.target.orientation)).length = 2 := by decide

/-- Changes #1, #2, #3 go from non-volitive to volitive: the "unexpected"
    direction per [narrog-2010] p. 397. These are the three most frequent
    cross-linguistic changes (13, 9, 5 grams respectively). -/
theorem nonvolitive_to_volitive_changes :
    (commonChanges.filter (fun c =>
      c.source.volitivity == .nonVolitive &&
      c.target.volitivity == .volitive)).length = 3 := by decide

/-- End-to-end: the speaker-orientation → subjectivity bridge preserves
    the directionality claim. Every attested change that increases
    speaker-orientation also increases (or maintains) subjectivity level. -/
theorem directionality_via_subjectivity :
    commonChanges.all (fun c =>
      c.source.orientation.toSubjectivityLevel ≤
      c.target.orientation.toSubjectivityLevel) = true := by decide

-- ============================================================================
-- §0. Cross-Linguistic Survey Data (Tables 3 + 4)
-- ============================================================================

/-! Survey data on deontic necessity from a genealogically diverse sample of
200 languages ([narrog-2010] appendix; [narrog-2012] Table 6.6).

- **Table 3 / Table 6.5**: Area-level counts of NEC (obligation) and POT
  (ability/situational possibility) markers, split by 6 geographic areas.
- **Table 4 / Table 6.6**: Aggregate counts of deontic necessity type
  (strong, weak, neutral, indeterminate) — the finest-grained published
  data; per-language type assignments are not available.

The Table 4 total (60 + 62 + 22 + 32 = 176) exceeds 131 (languages with
any NEC marker) because 44 languages have markers of multiple types
([narrog-2010] fn. 17). -/

/-- How a language grammaticalizes deontic necessity.
    From [narrog-2010] Table 4 / [narrog-2012] Table 6.6. -/
inductive DeonticNecessityType where
  | strong          -- grammaticalized strong deontic necessity (*must*-type)
  | weak            -- grammaticalized weak deontic necessity (*should*-type)
  | neutral         -- grammaticalized but unspecified for strength
  | indeterminate   -- unclear from available descriptions
  deriving DecidableEq, Repr

/-- Language counts by deontic necessity type. -/
def deonticNecessityCounts : List (DeonticNecessityType × Nat) :=
  [ (.strong, 60), (.weak, 62), (.neutral, 22), (.indeterminate, 32) ]

/-- The sample size: 200 genealogically diverse languages. -/
def sampleSize : Nat := 200

/-- Geographic area classification used in the sample. -/
inductive Area where
  | africa
  | americas
  | australia
  | eurasia
  | pacific              -- Austronesian and Papuan
  | southSoutheastAsia
  deriving DecidableEq, Repr

/-- Per-area counts of obligation (NEC) and ability/possibility (POT) marking.
    Source: [narrog-2010] Table 3 / [narrog-2012] Table 6.5. -/
structure AreaModalPresence where
  area : Area
  bothNecPot : Nat   -- languages with both NEC and POT markers
  onlyNec : Nat      -- languages with only NEC markers
  onlyPot : Nat      -- languages with only POT markers
  neither : Nat      -- languages with neither
  deriving Repr, BEq

def AreaModalPresence.total (a : AreaModalPresence) : Nat :=
  a.bothNecPot + a.onlyNec + a.onlyPot + a.neither

def areaData : List AreaModalPresence :=
  [ ⟨.africa,             27, 3,  9, 7,  ⟩
  , ⟨.americas,           32, 4,  7, 4,  ⟩
  , ⟨.australia,           1, 2,  1, 12, ⟩
  , ⟨.eurasia,            15, 0,  0, 0,  ⟩
  , ⟨.pacific,            27, 1, 17, 11, ⟩
  , ⟨.southSoutheastAsia, 19, 0,  1, 0,  ⟩
  ]

/-- Count of a specific deontic necessity type. -/
def countOf (t : DeonticNecessityType) : Nat :=
  match deonticNecessityCounts.find? (·.1 == t) with
  | some (_, n) => n
  | none => 0

/-- Total languages across all areas. -/
def areaSampleTotal : Nat := areaData.foldl (· + ·.total) 0

/-- Total languages with any NEC marker (both + onlyNec). -/
def languagesWithNec : Nat :=
  areaData.foldl (fun acc a => acc + a.bothNecPot + a.onlyNec) 0

/-- Total languages with any POT marker (both + onlyPot). -/
def languagesWithPot : Nat :=
  areaData.foldl (fun acc a => acc + a.bothNecPot + a.onlyPot) 0

/-- Area totals sum to the sample size. -/
theorem area_totals_sum_to_200 : areaSampleTotal = sampleSize := by native_decide

/-- Languages with any NEC marker: 121 + 10 = 131. -/
theorem nec_count : languagesWithNec = 131 := by native_decide

/-- Languages with any POT marker: 121 + 35 = 156.
    (Paper says 157 = 121 + 35 + 1; the discrepancy is in the original.) -/
theorem pot_count : languagesWithPot = 156 := by native_decide

theorem strong_count : countOf .strong = 60 := by native_decide
theorem weak_count : countOf .weak = 62 := by native_decide
theorem neutral_count : countOf .neutral = 22 := by native_decide
theorem indeterminate_count : countOf .indeterminate = 32 := by native_decide

/-- POT markers are more common than NEC markers cross-linguistically.
    [narrog-2010] p. 406: 156 vs 131. -/
theorem pot_more_common_than_nec : languagesWithPot > languagesWithNec := by native_decide

-- ============================================================================
-- §1. Face-Threatening Potential of Obligation (Derived)
-- ============================================================================

/-- Map deontic necessity type to its position in Narrog's 3D space.

    Strong obligation is performative + volitive + speaker-oriented: the
    speaker creates the obligation by uttering it. Weak obligation is
    descriptive: the speaker reports an existing norm. This difference
    explains the cross-linguistic asymmetry in grammaticalization. -/
def toNarrogPosition : DeonticNecessityType → NarrogPosition
  | .strong => strongObligation           -- performative, volitive, speaker-oriented
  | .weak => weakObligation               -- descriptive, volitive, speaker-oriented
  | .neutral => weakObligation            -- unspecified → conservative (descriptive)
  | .indeterminate => dynamicAbility      -- unclear → event-oriented default

/-- Strong obligation is face-threatening (derived from 3D position). -/
theorem strong_face_threatening :
    (toNarrogPosition .strong).isFaceThreatening = true := rfl

/-- Weak obligation is NOT face-threatening (descriptive, not performative). -/
theorem weak_not_face_threatening :
    (toNarrogPosition .weak).isFaceThreatening = false := rfl

/-- The face-threat asymmetry between strong and weak obligation is
    structurally explained: they differ only in performativity. -/
theorem face_threat_from_performativity :
    (toNarrogPosition .strong).performativity ≠
    (toNarrogPosition .weak).performativity ∧
    (toNarrogPosition .strong).toRegion =
    (toNarrogPosition .weak).toRegion := by
  exact ⟨by decide, rfl⟩

-- ============================================================================
-- §2. Empirical Claims as Theorems
-- ============================================================================

/-- Strong obligation is a minority pattern: only 60/200 languages. -/
theorem strong_obligation_minority : countOf .strong < sampleSize / 2 := by
  native_decide

/-- Weak obligation (*should*-type) is at least as common as strong (*must*-type). -/
theorem weak_ge_strong : countOf .weak ≥ countOf .strong := by native_decide

/-- The deontic → epistemic shift is uncommon cross-linguistically.

    Of the 8 most common modal changes (Bybee et al. 1994), only changes #6
    and #7 go from volitive (deontic) to non-volitive (epistemic), and these
    are among the least frequent (3 and 2 grams respectively). -/
theorem deontic_epistemic_shift_uncommon :
    (commonChanges.filter (λ c =>
      c.source.volitivity == .volitive &&
      c.target.volitivity == .nonVolitive)).length = 2 := by native_decide

-- ============================================================================
-- §3. Japanese Person-Distribution Data (Tables 5-6)
-- ============================================================================

/-- Person distribution for Japanese strong necessity *-(a)nakereba naranai*.

    [narrog-2010] Table 5 (Chiang 2007: 72): of 115 tokens, 0 have a
    2nd-person subject. This avoidance reflects the face-threatening nature
    of strong obligation directed at the addressee. -/
structure PersonDistribution where
  construction : String
  firstPerson : Nat
  secondPerson : Nat
  thirdPerson : Nat
  deriving Repr

def japaneseStrongNecessity : PersonDistribution :=
  ⟨"-(a)nakereba naranai", 52, 0, 63⟩

def japaneseAbbreviated : PersonDistribution :=
  ⟨"-(a)nakya/naktya", 35, 13, 4⟩

/-- Strong necessity completely avoids 2nd-person subjects. -/
theorem strong_avoids_second_person :
    japaneseStrongNecessity.secondPerson = 0 := rfl

/-- The abbreviated form allows 2nd-person (mitigated by omitting the
    negative consequent). -/
theorem abbreviated_allows_second_person :
    japaneseAbbreviated.secondPerson > 0 := by decide

/-- Total tokens for strong necessity. -/
theorem strong_total :
    japaneseStrongNecessity.firstPerson +
    japaneseStrongNecessity.secondPerson +
    japaneseStrongNecessity.thirdPerson = 115 := by decide

/-- Total tokens for abbreviated form. -/
theorem abbreviated_total :
    japaneseAbbreviated.firstPerson +
    japaneseAbbreviated.secondPerson +
    japaneseAbbreviated.thirdPerson = 52 := by decide

-- ============================================================================
-- §4. Connecting Face-Threat to Person Avoidance
-- ============================================================================

/-- The 2nd-person avoidance pattern is predicted by face-threat:
    strong necessity (face-threatening) avoids 2nd-person, while the
    abbreviated form (mitigated → less face-threatening) allows it.

    This connects the pragmatic dimension (face-threat from performativity)
    to the distributional observation (person restrictions). -/
theorem face_threat_predicts_avoidance :
    (toNarrogPosition .strong).isFaceThreatening = true ∧
    japaneseStrongNecessity.secondPerson = 0 :=
  ⟨rfl, rfl⟩

end Narrog2010
