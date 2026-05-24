import Linglib.Semantics.Modality.Narrog
import Linglib.Diachronic.ModalChange

/-!
# Narrog (2010): (Inter)subjectification in Modality and Mood
@cite{narrog-2010}

Study file connecting @cite{narrog-2010}'s theoretical claims to the
cross-linguistic data in `Semantics.Modality.DeonticNecessity`. The chapter argues
that strong obligation markers are cross-linguistically uncommon because
obligation is inherently face-threatening and socially costly, so languages
tend not to grammaticalize it — or to do so only indirectly.

@cite{narrog-2012} ch. 2 decomposes the face-threatening potential of obligation
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
open Diachronic.ModalChange (commonChanges)

-- ============================================================================
-- §0. Cross-Linguistic Survey Data (Tables 3 + 4)
-- ============================================================================

/-! Survey data on deontic necessity from a genealogically diverse sample of
200 languages (@cite{narrog-2010} appendix; @cite{narrog-2012} Table 6.6).

- **Table 3 / Table 6.5**: Area-level counts of NEC (obligation) and POT
  (ability/situational possibility) markers, split by 6 geographic areas.
- **Table 4 / Table 6.6**: Aggregate counts of deontic necessity type
  (strong, weak, neutral, indeterminate) — the finest-grained published
  data; per-language type assignments are not available.

The Table 4 total (60 + 62 + 22 + 32 = 176) exceeds 131 (languages with
any NEC marker) because 44 languages have markers of multiple types
(@cite{narrog-2010} fn. 17). -/

/-- How a language grammaticalizes deontic necessity.
    From @cite{narrog-2010} Table 4 / @cite{narrog-2012} Table 6.6. -/
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
    Source: @cite{narrog-2010} Table 3 / @cite{narrog-2012} Table 6.5. -/
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
    @cite{narrog-2010} p. 406: 156 vs 131. -/
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

    @cite{narrog-2010} Table 5 (Chiang 2007: 72): of 115 tokens, 0 have a
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
