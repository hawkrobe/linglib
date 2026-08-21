import Linglib.Semantics.Attitudes.Desire.BestWorlds
import Linglib.Core.Order.OfCriteria
import Linglib.Semantics.Presupposition.Basic

/-!
# Question-based desire semantics

`a wants p` relative to a contextual question `Q`: the answers compatible with `a`'s beliefs
are ordered by the desires they entail, and the ascription holds iff every best such answer
entails `p` — [phillips-brown-2025]'s semantics. Its definedness conditions are the paper's
metasemantic constraints — `IsConsidered` (every answer settles `p`), `IsDiverse` (both
`p`- and `¬p`-answers), `IsAntiDeckstacking` (a salient proposition some answer entails is
itself settled; [condoravdi-2002]), `IsBelSensitive` (the beliefs discriminate among the
answers; [yalcin-2018]) — bundled as `Defined` and as the presupposition of `toPartialProp`,
under which the ascription is Strawson upward monotone (`toPartialProp_strawsonEntails`).
On the finest question the semantics is the best-worlds one (`want_finest_iff`).
-/

namespace Desire.QuestionBased

open Semantics.Presupposition (PartialProp)

variable {W : Type*} (G N Q : List (Finset W)) (bel p : Set W)

/-- `le G a a'`: every desire in `G` entailed by `a'` is entailed by `a` — the
criteria-derived order with entailment as satisfaction. -/
def le (a a' : Finset W) : Prop :=
  (Preorder.ofCriteria (fun a s : Finset W => a ⊆ s) {s | s ∈ G}).le a a'

theorem le_iff (a a' : Finset W) : le G a a' ↔ ∀ s ∈ G, a' ⊆ s → a ⊆ s := Iff.rfl

/-- An answer compatible with the beliefs. -/
def Live (a : Finset W) : Prop := ∃ w ∈ a, w ∈ bel

/-- `a wants p`: every best live answer of `Q` entails `p`. -/
def Want : Prop :=
  ∀ a ∈ Q, Live bel a → (∀ a' ∈ Q, Live bel a' → le G a' a → le G a a') → ∀ w ∈ a, w ∈ p

/-- Every answer settles `p`. -/
def IsConsidered : Prop := ∀ a ∈ Q, (∀ w ∈ a, w ∈ p) ∨ (∀ w ∈ a, w ∉ p)

/-- Some answer entails `p` and some entails `¬p`. -/
def IsDiverse : Prop := (∃ a ∈ Q, ∀ w ∈ a, w ∈ p) ∧ ∃ a ∈ Q, ∀ w ∈ a, w ∉ p

/-- Every salient proposition in `N` that some answer entails is itself settled. -/
def IsAntiDeckstacking : Prop := ∀ q ∈ N, (∃ a ∈ Q, a ⊆ q) → IsConsidered Q (↑q : Set W)

/-- The beliefs discriminate among the answers: some answer is live and some is not. -/
def IsBelSensitive : Prop := (∃ a ∈ Q, Live bel a) ∧ ∃ a ∈ Q, ¬ Live bel a

/-- The four metasemantic constraints jointly. -/
def Defined : Prop :=
  IsConsidered Q p ∧ IsDiverse Q p ∧ IsAntiDeckstacking N Q ∧ IsBelSensitive Q bel

/-- Question-based *want* with its definedness conditions as presupposition. -/
def toPartialProp : PartialProp W :=
  ⟨fun _ => Defined N Q bel p, fun _ => Want G Q bel p⟩

section Decidable

instance [DecidableEq W] (a a' : Finset W) : Decidable (le G a a') :=
  inferInstanceAs (Decidable (∀ s ∈ G, a' ⊆ s → a ⊆ s))

instance [DecidablePred (· ∈ bel)] (a : Finset W) : Decidable (Live bel a) :=
  inferInstanceAs (Decidable (∃ w ∈ a, w ∈ bel))

instance [DecidableEq W] [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] :
    Decidable (Want G Q bel p) :=
  inferInstanceAs (Decidable (∀ a ∈ Q, Live bel a →
    (∀ a' ∈ Q, Live bel a' → le G a' a → le G a a') → ∀ w ∈ a, w ∈ p))

instance [DecidablePred (· ∈ p)] : Decidable (IsConsidered Q p) :=
  inferInstanceAs (Decidable (∀ a ∈ Q, (∀ w ∈ a, w ∈ p) ∨ (∀ w ∈ a, w ∉ p)))

instance [DecidablePred (· ∈ p)] : Decidable (IsDiverse Q p) :=
  inferInstanceAs (Decidable ((∃ a ∈ Q, ∀ w ∈ a, w ∈ p) ∧ ∃ a ∈ Q, ∀ w ∈ a, w ∉ p))

instance [DecidableEq W] : Decidable (IsAntiDeckstacking N Q) :=
  inferInstanceAs (Decidable (∀ q ∈ N, (∃ a ∈ Q, a ⊆ q) → IsConsidered Q (↑q : Set W)))

instance [DecidablePred (· ∈ bel)] : Decidable (IsBelSensitive Q bel) :=
  inferInstanceAs (Decidable ((∃ a ∈ Q, Live bel a) ∧ ∃ a ∈ Q, ¬ Live bel a))

instance [DecidableEq W] [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] :
    Decidable (Defined N Q bel p) :=
  inferInstanceAs (Decidable (IsConsidered Q p ∧ IsDiverse Q p ∧ IsAntiDeckstacking N Q ∧
    IsBelSensitive Q bel))

end Decidable

variable {G N Q bel p}

theorem Want.mono {q : Set W} (hpq : p ⊆ q) (h : Want G Q bel p) : Want G Q bel q :=
  fun a ha hl hb w hw => hpq (h a ha hl hb w hw)

/-- Strawson upward monotonicity: where both ascriptions are defined, `want p` entails
`want q` for `p ⊆ q`. -/
theorem toPartialProp_strawsonEntails {q : Set W} (hpq : p ⊆ q) :
    (toPartialProp G N Q bel p).strawsonEntails (toPartialProp G N Q bel q) :=
  fun _ _ _ h => h.mono hpq

/-! ### The finest question -/

/-- The finest question over a world list: one singleton answer per world. -/
def finest (worlds : List W) : List (Finset W) := worlds.map ({·})

theorem le_singleton_iff (G : List (Finset W)) (w z : W) :
    le G {w} {z} ↔ BestWorlds.le G w z := by
  simp [le_iff, BestWorlds.le_iff]

/-- On the finest question over an exhaustive world list, question-based *want* is
best-worlds *want*. -/
theorem want_finest_iff {worlds : List W} (h : ∀ w, w ∈ worlds) :
    Want G (finest worlds) bel p ↔ BestWorlds.Want G bel p := by
  simp [Want, BestWorlds.Want, BestWorlds.Undominated, finest, Live, le_singleton_iff, h]

end Desire.QuestionBased
