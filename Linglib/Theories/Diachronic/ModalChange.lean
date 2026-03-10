import Linglib.Theories.Semantics.Modality.Narrog

/-!
# Diachronic Modal Change
@cite{narrog-2010} @cite{bybee-perkins-pagliuca-1994}

Cross-linguistic patterns of diachronic change in modal and mood meanings,
formalized using Narrog's 2D semantic map (`Semantics.Modality.Narrog`).

The central claim: modal meanings always shift **upward** in the semantic
map — toward increased speaker-orientation — regardless of volitivity.
The well-known deontic → epistemic shift is just one instance of this
general pattern.

## Main definitions

- `ModalChange`: an attested cross-linguistic modal meaning change
- `commonChanges`: the 8 most frequent changes from Bybee et al. (1994)
- `directionality`: every attested change increases speaker-orientation

## Data source

Bybee, Perkins & Pagliuca (1994) *The Evolution of Grammar*, ch. 6,
tabulated in @cite{narrog-2010} Table 2.
-/

namespace Diachronic.ModalChange

open Semantics.Modality.Narrog

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
    Source: @cite{bybee-perkins-pagliuca-1994} ch. 6, tabulated in
    @cite{narrog-2010} Table 2. -/
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

-- ============================================================================
-- §1. Directionality
-- ============================================================================

/-- **Directionality of change**: every attested change increases (or maintains)
    speaker-orientation. This is Narrog's central diachronic claim.

    @cite{narrog-2010} §3.1: "modal meanings always shift in the direction
    of increased speaker-orientation." -/
theorem directionality :
    commonChanges.all (fun c => c.source.orientation ≤ c.target.orientation) = true := by
  native_decide

/-- No attested change decreases speaker-orientation. -/
theorem no_decrease :
    commonChanges.all (fun c => !(c.target.orientation.toNat < c.source.orientation.toNat))
    = true := by native_decide

-- ============================================================================
-- §2. Volitivity Is Orthogonal to Directionality
-- ============================================================================

/-- Changes #6 and #7 cross the volitivity boundary (volitive → non-volitive)
    while maintaining speaker-orientation level. This shows volitivity is
    orthogonal to the directionality of change. -/
theorem volitivity_crossing :
    (commonChanges.filter (fun c =>
      c.source.volitivity != c.target.volitivity &&
      c.source.orientation == c.target.orientation)).length = 2 := by native_decide

/-- Changes #1, #2, #3 go from non-volitive to volitive: the "unexpected"
    direction per @cite{narrog-2010} p. 397. These are the three most frequent
    cross-linguistic changes (13, 9, 5 grams respectively). -/
theorem nonvolitive_to_volitive_changes :
    (commonChanges.filter (fun c =>
      c.source.volitivity == .nonVolitive &&
      c.target.volitivity == .volitive)).length = 3 := by native_decide

/-- End-to-end: the speaker-orientation → subjectivity bridge preserves
    the directionality claim. Every attested change that increases
    speaker-orientation also increases (or maintains) subjectivity level. -/
theorem directionality_via_subjectivity :
    commonChanges.all (fun c =>
      c.source.orientation.toSubjectivityLevel ≤
      c.target.orientation.toSubjectivityLevel) = true := by native_decide

end Diachronic.ModalChange
