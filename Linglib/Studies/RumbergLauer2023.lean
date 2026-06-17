import Linglib.Semantics.Modality.BranchingTime
import Mathlib.Tactic.DeriveFintype

/-!
# [rumberg-lauer-2023]: Conditionals, tense, and branching time — the settledness contrast
[rumberg-lauer-2023] [kaufmann-2005-truth] [schulz-2008]

[rumberg-lauer-2023] (§2.1) observe that the eventive **futurate present** is felicitous only when
the eventuality is *settled* — historically necessary, i.e. **true on every possible future**.
Their minimal pair:

- (6a)  *The Red Sox play the Yankees tomorrow.* — felicitous: the game is scheduled, so on every
  way the future might go, they play.
- (6b) #*The Red Sox beat the Yankees tomorrow.* — infelicitous out of the blue: the outcome is
  open, so that they win is **not settled-true** (felicitous only if the game is fixed *for them*).

We formalize the contrast against the `BranchingTime` substrate (the 𝔗 model). In a model where the
game's *outcome* branches, *play* is `IsInevitable` (settled-true on every history through the
utterance moment), while *beat* is **not** `IsInevitable`. Both members of the minimal pair are
measured by the *same* unilateral notion (settled = historically necessary), which is R&L's actual
constraint — a settled *loss* would not rescue (6b). (The bilateral `IsSettledWhether`/`PresumedSettled`
in the substrate serves the [phillips-2021] apprehensional consumer, not R&L here.)

R&L (§4) reconstruct Kaufmann (2005) as an **Ockhamist** account and Schulz (2008) as a **Peircean**
one. Both *agree* that the bare futurate present requires settledness; they differ in mechanism. The
Ockhamism-vs-Peirceanism axis itself is the gap between history-relative future truth (`oFut`) and
settledness (`IsInevitable`), which the same branching model exhibits.
-/

namespace RumbergLauer2023

open BranchingTime

/-! ### A minimal branching model: the game's outcome branches

Three moments: `now` (game scheduled) below the two incomparable outcomes `win` / `lose`. -/

/-- The moments of the Red Sox scenario. -/
inductive Moment | now | win | lose
  deriving DecidableEq, Fintype, Repr

open Moment

/-- `now` is below everything; otherwise the order is discrete, so `win` and `lose` are maximal
    and incomparable. -/
instance : LE Moment where
  le a b := a = now ∨ a = b

instance : DecidableRel (· ≤ · : Moment → Moment → Prop) :=
  fun a b => inferInstanceAs (Decidable (a = now ∨ a = b))

instance : PartialOrder Moment where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLT Moment := decidableLTOfDecidableLE

/-- Left-linear: `now` is the only predecessor of anything, so any two predecessors of a moment
    are comparable. -/
instance : IsLeftLinear Moment := ⟨by decide⟩

/-- Historically connected: `now` is a global minimum, hence a common lower bound of any two
    moments. -/
instance : IsCodirectedOrder Moment := ⟨by decide⟩

/-- The outcome model is a genuine branching frame ([rumberg-lauer-2023] Def 1). -/
instance : IsBranchingTime Moment := ⟨⟩

theorem now_lt_win : (now : Moment) < win := by decide
theorem now_lt_lose : (now : Moment) < lose := by decide

/-! ### The two eventualities (minimal pair) -/

/-- *The Red Sox play* — true at **both** outcomes (the game is played either way). -/
def played : MProp Moment := fun m => m = win ∨ m = lose

/-- *The Red Sox beat the Yankees* — true **only** at the `win` outcome. -/
def beat : MProp Moment := fun m => m = win

/-! ### The contrast -/

/-- **(6a) is felicitous**: *play* is inevitable. On every history through `now`, the game is
    played — because every history contains a future moment (`exists_mem_gt_of_lt`), and every
    successor of `now` is a playing moment. -/
theorem played_inevitable : IsInevitable played now := by
  intro h hh
  obtain ⟨y, hy, hlt⟩ := exists_mem_gt_of_lt hh now_lt_win
  refine ⟨y, hy, hlt, ?_⟩
  cases y with
  | now => exact absurd hlt (lt_irrefl now)
  | win => exact Or.inl rfl
  | lose => exact Or.inr rfl

/-- **(6b) is infelicitous**: *beat* is not inevitable. The lose-history passes through `now` but
    has no winning future, so winning is not settled-true (not historically necessary) — the same
    unilateral notion that makes (6a) felicitous. -/
theorem beat_not_inevitable : ¬ IsInevitable beat now := by
  obtain ⟨hl, hnow_l, hlose_l⟩ := Flag.exists_mem_mem (le_of_lt now_lt_lose)
  intro hinev
  obtain ⟨m', hm'l, _, hbeat⟩ := hinev hl hnow_l
  rw [beat] at hbeat; subst hbeat
  exact absurd (hl.le_or_le hm'l hlose_l) (by decide)

/-- The Ockhamism-vs-Peirceanism axis underlying R&L's two reconstructions
    ([rumberg-lauer-2023] §3.2, §4): on the win-history, *beat* is Ockhamist-future-true (`oFut`,
    history-relative), yet it is not settled (not `IsInevitable`/Peircean) — future truth and
    settledness come apart. Kaufmann's account is Ockhamist, Schulz's Peircean. -/
theorem oFut_beat_but_not_inevitable :
    (∃ h ∈ Hist now, oFut (oAtom beat) now h) ∧ ¬ IsInevitable beat now := by
  refine ⟨?_, beat_not_inevitable⟩
  obtain ⟨hw, hnow_w, hwin_w⟩ := Flag.exists_mem_mem (le_of_lt now_lt_win)
  exact ⟨hw, hnow_w, win, hwin_w, now_lt_win, rfl⟩

end RumbergLauer2023
