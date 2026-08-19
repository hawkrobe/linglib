import Linglib.Semantics.Tense.Compositional

/-!
# [ogihara-1989]: Temporal Reference in English and Japanese

[ogihara-1989] §2.3 reconciles [prior-1967]'s operator analysis of tense
with [partee-1973]'s referential analysis: tense is a variable that picks
a time and must satisfy a temporal presupposition (the picked time is
past/present/future). The referential analysis picks the time; the
operator imposes the constraint. They are complementary layers, not
competitors (`referential_past_decomposition`).
-/

open Tense

namespace Ogihara1989

open Tense (interpTense PAST)
open Intensional (Index)

/-- The Priorean `PAST` operator, applied at a referentially determined
    time g(n), decomposes into the conjunction of (1) the referential
    time precedes the speech situation and (2) the predicate holds at the
    referential time: the referential analysis picks the time, the
    operator imposes the constraint. -/
theorem referential_past_decomposition {W Time : Type*} [LinearOrder Time]
    (P : (Index W Time → Prop)) (g : TemporalAssignment Time) (n : ℕ)
    (w : W) (speechTime : Time) :
    PAST P ⟨w, interpTense n g⟩ ⟨w, speechTime⟩ ↔
    (g n < speechTime ∧ P ⟨w, g n⟩) := by
  simp [Tense.constrain]

end Ogihara1989
