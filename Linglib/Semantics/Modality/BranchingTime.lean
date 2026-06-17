import Linglib.Core.Order.LeftLinear
import Mathlib.Order.Zorn
import Mathlib.Order.Directed

/-!
# Branching time (the 𝔗 model)

The **branching-times** model of Prior–Thomason: an order-theoretic tree of **moments**,
whose maximal chains are the **histories**. This is the sibling of the **T×W parallel-worlds**
model in `Semantics/Modality/HistoricalAlternatives.lean`; the two are inter-translatable by
quotienting the historical-equivalence relation ([rumberg-lauer-2023] §4.1.3, deferred).

A branching-time structure is a left-linear (`Core.Order.IsLeftLinear`: no backward
branching) and downward-directed (`IsCodirectedOrder`: historically connected) partial order
([rumberg-lauer-2023] Def 1). Histories are mathlib `Flag`s (maximal chains).

Temporal-modal formulas are evaluated in one of two **postsemantics** ([rumberg-lauer-2023]
§3.2): **Peircean** at a moment (future truth requires settledness) and **Ockhamist** at a
`moment/history` pair (future truth is history-relative). Settledness `oSettled` (`□_O`)
quantifies over the histories through a moment.

The conceptual heart ([rumberg-lauer-2023] pp. 541, 546): the Ockhamist **history parameter
is not fixed by a context of utterance** ("there is no actual future") — only the moment is.
`oSettled` is precisely the operator that quantifies the unfixed parameter away, which is why
the felicity facts (eventive futurate present, apprehensionals) turn on it.

## Main definitions

* `IsBranchingTime`, `IsBranchingMeetTree` — the frame ([rumberg-lauer-2023] Def 1; the
  meet-tree form adds branching points as `⊓`, R&L Def 1(ii) / fn. 9).
* `Hist` — the histories through a moment.
* `pPast`; `oAtom`/`oPast`/`oFut`/`oSettled`/`oSupervaluation` — the Peircean/Ockhamist operators.
* `IsInevitable`, `PresumedSettled`, `IsSettledWhether` — settledness (context-relative).
* `kaufmannPresent`, `kaufmannPast` — [kaufmann-2005-truth]'s non-deictic tenses, reconstructed in
  Ockhamist branching time by [rumberg-lauer-2023] §4.1.3 (NOT framework-neutral primitives).

## Main results

* `oSettled_oAtom` — atomic propositions are settled ([rumberg-lauer-2023] fn. 10).
* `isInevitable_iff_oSupervaluation_oFut` — Peircean future = Ockhamist settled future.
* `Iic_subset_of_mem` — the past sits inside every history through a moment (the past is
  history-independent), the payoff of left-linearity.
-/

namespace BranchingTime

variable {M : Type*}

/-! ### The frame -/

/-- A **branching-time structure** ([rumberg-lauer-2023] Def 1): a left-linear, downward-directed
    partial order. Left-linearity (`IsLeftLinear`) is no backward branching; downward-directedness
    (`IsCodirectedOrder`) is historical connectedness. Weaker than R&L Def 1(ii), which asks for a
    *greatest* common lower bound (fn. 9) — that strengthening is `IsBranchingMeetTree`. -/
class IsBranchingTime (M : Type*) [PartialOrder M] : Prop
    extends IsLeftLinear M, IsCodirectedOrder M

/-- The **meet-tree** form ([rumberg-lauer-2023] Def 1(ii) + fn. 9): branching points exist as
    meets, `m₁ ⊓ m₂` being the moment where the histories of `m₁` and `m₂` diverge. (The same `⊓`
    that `Core.Order.Branching.Positions` uses for syntactic least common ancestors.) -/
class IsBranchingMeetTree (M : Type*) [SemilatticeInf M] : Prop
    extends IsLeftLinear M

/-! ### Histories -/

/-- The **histories** through a moment: the maximal `≤`-chains (mathlib `Flag`) containing `m`
    ([rumberg-lauer-2023] Def 2). -/
def Hist [PartialOrder M] (m : M) : Set (Flag M) := {h | m ∈ h}

/-- Every moment lies on a history. -/
theorem hist_nonempty [PartialOrder M] (m : M) : (Hist m).Nonempty :=
  let ⟨s, hs⟩ := Flag.exists_mem m; ⟨s, hs⟩

/-- The past of a moment sits inside **every** history through it — the past is
    history-independent. The payoff of left-linearity: `Iic m` is a chain
    (`IsLeftLinear.isChain_Iic`), so `(h : Set M) ∪ Iic m` is a chain extending the maximal
    chain `h`, forcing `Iic m ⊆ h`. -/
theorem Iic_subset_of_mem [PartialOrder M] [IsLeftLinear M] {m : M} {h : Flag M}
    (hm : m ∈ h) : Set.Iic m ⊆ (h : Set M) := by
  have hchain : IsChain (· ≤ ·) ((h : Set M) ∪ Set.Iic m) := by
    rintro a (ha | ha) b (hb | hb) _
    · exact h.le_or_le ha hb
    · rcases h.le_or_le ha hm with hab | hma
      · exact IsLeftLinear.comparable_of_le_common hab (Set.mem_Iic.mp hb)
      · exact Or.inr (le_trans (Set.mem_Iic.mp hb) hma)
    · rcases h.le_or_le hm hb with hmb | hbm
      · exact Or.inl (le_trans (Set.mem_Iic.mp ha) hmb)
      · exact IsLeftLinear.comparable_of_le_common (Set.mem_Iic.mp ha) hbm
    · exact IsLeftLinear.comparable_of_le_common (Set.mem_Iic.mp ha) (Set.mem_Iic.mp hb)
  have heq : (h : Set M) = (h : Set M) ∪ Set.Iic m := h.max_chain' hchain Set.subset_union_left
  intro x hx
  have hmem : x ∈ (h : Set M) ∪ Set.Iic m := Or.inr hx
  rwa [← heq] at hmem

/-- A history through a non-maximal moment contains a **future** moment: if `m ∈ h` and `m < x`
    for some `x`, then `h` contains some `y > m`. (Otherwise `insert x h` would be a strictly
    larger chain, contradicting `h`'s maximality.) The engine of inevitability reasoning: a
    history cannot stop at a moment that still has a future. -/
theorem exists_mem_gt_of_lt [PartialOrder M] {m x : M} {h : Flag M}
    (hm : m ∈ h) (hx : m < x) : ∃ y ∈ h, m < y := by
  by_contra hcon
  push_neg at hcon
  have hbx : ∀ b ∈ (h : Set M), b ≤ x := by
    intro b hb
    rcases h.le_or_le hb hm with hbm | hmb
    · exact le_of_lt (lt_of_le_of_lt hbm hx)
    · have hbeq : m = b := (hmb.lt_or_eq).resolve_left (hcon b hb)
      exact le_of_lt (hbeq ▸ hx)
  have hchain : IsChain (· ≤ ·) (insert x (h : Set M)) := by
    rintro a ha b hb _
    simp only [Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Or.inl le_rfl
    · exact Or.inr (hbx b hb)
    · exact Or.inl (hbx a ha)
    · exact h.le_or_le ha hb
  have heq : (h : Set M) = insert x (h : Set M) := h.max_chain' hchain (Set.subset_insert x _)
  have hxh : x ∈ (h : Set M) := by rw [heq]; exact Set.mem_insert x _
  exact hcon x hxh hx

/-! ### Postsemantics

`MProp` = truth at a moment (Peircean); `OProp` = truth at a moment/history pair (Ockhamist;
intended `m ∈ h`). Atomic propositions depend only on the moment ([rumberg-lauer-2023] Def 3). -/

/-- A Peircean proposition: truth at a moment. -/
abbrev MProp (M : Type*) := M → Prop

/-- An Ockhamist proposition: truth at a moment/history pair. -/
abbrev OProp (M : Type*) [PartialOrder M] := M → Flag M → Prop

/-- Peircean past: `φ` held at some earlier moment ([rumberg-lauer-2023] §3.2.1). -/
def pPast [PartialOrder M] (φ : MProp M) : MProp M := fun m => ∃ m' < m, φ m'

/-- Lift a moment-proposition to an Ockhamist one, ignoring the history (atoms depend only on
    the moment). -/
def oAtom [PartialOrder M] (φ : MProp M) : OProp M := fun m _h => φ m

/-- Ockhamist past: `φ` held at some earlier moment, along the same history. -/
def oPast [PartialOrder M] (φ : OProp M) : OProp M := fun m h => ∃ m' < m, φ m' h

/-- Ockhamist future (`F_O`): `φ` holds at some later moment **on the fixed history `h`**
    ([rumberg-lauer-2023] §3.2.2). -/
def oFut [PartialOrder M] (φ : OProp M) : OProp M :=
  fun m h => ∃ m' ∈ h, m < m' ∧ φ m' h

/-- Ockhamist settledness (`□_O`): `φ` holds at `m` on **every** history through `m`
    ([rumberg-lauer-2023] §3.2.2). The history argument is ignored — settledness quantifies
    the (contextually unfixed) history parameter away. -/
def oSettled [PartialOrder M] (φ : OProp M) : OProp M :=
  fun m _h => ∀ h' ∈ Hist m, φ m h'

/-- Supervaluationist truth at a moment (Thomason 1970): `□_O` read off the moment. The third
    classic postsemantics; makes the settledness connection explicit. -/
def oSupervaluation [PartialOrder M] (φ : OProp M) : MProp M :=
  fun m => ∀ h ∈ Hist m, φ m h

/-! ### Settledness (context-relative)

The objective "all histories through `m` agree" is the special case of agreement over the
histories compatible with a context/common ground ([phillips-2021]'s "presumed settled" is
over `∩cg`, not all histories; the T×W sibling carries the same `cg` parameter). -/

/-- A future-directed claim `φ` is **inevitable** at `m`: on every history through `m`, `φ`
    eventually holds. This is the Peircean future. -/
def IsInevitable [PartialOrder M] (φ : MProp M) (m : M) : Prop :=
  ∀ h ∈ Hist m, ∃ m' ∈ h, m < m' ∧ φ m'

/-- **Presumed settled-whether** relative to a context set `C` of histories: all `C`-histories
    agree on whether `φ` will hold ([phillips-2021]'s "(not) presumed settled"). -/
def PresumedSettled [PartialOrder M] (C : Set (Flag M)) (φ : MProp M) (m : M) : Prop :=
  (∀ h ∈ C, ∃ m' ∈ h, m < m' ∧ φ m') ∨ (∀ h ∈ C, ¬ ∃ m' ∈ h, m < m' ∧ φ m')

/-- Objective settledness = presumed-settled relative to the maximal context (all histories). -/
abbrev IsSettledWhether [PartialOrder M] (φ : MProp M) (m : M) : Prop :=
  PresumedSettled (Hist m) φ m

/-! ### Tense translations ([kaufmann-2005-truth] via [rumberg-lauer-2023] §4.1.3)

`PRESENT Q := Q ∨ F_O Q`, `PAST Q := P_O Q`. These encode [kaufmann-2005-truth]'s non-deictic-present
analysis (morphological present = non-pastness) reconstructed in Ockhamism — *not* neutral
branching primitives ([schulz-2008]'s Peircean reconstruction gives the same surface forms). -/

/-- [kaufmann-2005-truth]'s present (non-deictic), Ockhamist reconstruction. -/
def kaufmannPresent [PartialOrder M] (φ : OProp M) : OProp M := fun m h => φ m h ∨ oFut φ m h

/-- [kaufmann-2005-truth]'s past, Ockhamist reconstruction. -/
def kaufmannPast [PartialOrder M] (φ : OProp M) : OProp M := oPast φ

/-! ### Theorems -/

/-- **Atomic propositions are settled** ([rumberg-lauer-2023] fn. 10): the valuation depends
    only on the moment, so `□_O Q ↔ Q`. Uses history-nonemptiness. -/
@[simp] theorem oSettled_oAtom [PartialOrder M] (φ : MProp M) (m : M) (h : Flag M) :
    oSettled (oAtom φ) m h ↔ φ m := by
  unfold oSettled oAtom
  refine ⟨fun hall => ?_, fun hφ _ _ => hφ⟩
  obtain ⟨h', hh'⟩ := hist_nonempty m
  exact hall h' hh'

/-- **Peircean future = Ockhamist settled future** ([rumberg-lauer-2023] §3.2): inevitability
    of `φ` is `□_O F_O φ` read off the moment. Holds by construction — the two postsemantics'
    notions of "settled that φ will happen" coincide. -/
theorem isInevitable_iff_oSupervaluation_oFut [PartialOrder M] (φ : MProp M) (m : M) :
    IsInevitable φ m ↔ oSupervaluation (oFut (oAtom φ)) m := Iff.rfl

end BranchingTime
