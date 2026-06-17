import Linglib.Semantics.Modality.BranchingTime
import Linglib.Semantics.Modality.HistoricalAlternatives
import Mathlib.Order.Antisymmetrization

/-!
# The T×W → 𝔗 collapse
[rumberg-lauer-2023] [thomason-1984]

[rumberg-lauer-2023] §4.1.3 show that every **T×W parallel-worlds frame** (worlds × linear time
+ a backward-closed historical-equivalence relation `≈_t`; their Def 5, our
`Semantics/Modality/HistoricalAlternatives.lean`) transforms into a **branching-time structure**
(the 𝔗 model, `Semantics/Modality/BranchingTime.lean`) by *collapsing the historical-accessibility
relation into identity*: `≈`-related world-time pairs are merged into a single **moment**, and the
tree order `◁` mirrors `<` between world-time pairs (cf. Reynolds 2002). Worlds map onto histories,
times onto moments.

We realize this collapse with mathlib's `Antisymmetrization`. The **strand preorder** on world-time
pairs — `s₁ ⊑ s₂` iff `s₁.time ≤ s₂.time` and the worlds agree up to `s₁.time` — has the property
that its antisymmetrization-equivalence `s₁ ⊑ s₂ ∧ s₂ ⊑ s₁` is *exactly* historical equivalence
(`collapse_antisymmRel_iff`). So the quotient `Antisymmetrization (Strand F) (· ≤ ·)` is the moment
poset, and the central theorem `isBranchingTime_collapse` proves it is a genuine `IsBranchingTime`
frame: **left-linearity falls out of linear time + backward-closure of `≈`** (the past is linear
because times are linear and historical equivalence only shrinks toward the past), and
**connectedness from the frame's historical connectedness**.

## Main definitions
* `TxWFrame` — a T×W frame ([rumberg-lauer-2023] Def 5): historical alternatives + the equivalence
  properties + historical connectedness.
* `Strand` — a world-time pair, carrying the collapse preorder.

## Main results
* `isLeftLinear_antisymmetrization`, `isCodirectedOrder_antisymmetrization` — the antisymmetrization
  of a left-linear / downward-directed preorder is left-linear / downward-directed (pure order theory).
* `strand_comparable` — the strand preorder is left-linear (the deep step: linear time + backward
  closure of `≈` ⟹ no backward branching).
* `collapse_antisymmRel_iff` — the merge is *exactly* historical equivalence.
* `isBranchingTime_collapse` — the collapse of a T×W frame is an `IsBranchingTime` frame.
-/

namespace BranchingTime

/-! ### Antisymmetrization of a left-linear / codirected preorder (pure order theory) -/

section General

variable {α : Type*} [Preorder α]

/-- The antisymmetrization of a **left-linear** preorder is left-linear: comparability of the
    predecessors of a point survives the quotient (it is detected on the `ofAntisymmetrization`
    representatives). -/
theorem isLeftLinear_antisymmetrization
    (hll : ∀ a b c : α, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a) :
    IsLeftLinear (Antisymmetrization α (· ≤ ·)) where
  comparable_of_le_common {_x _y _z} hxz hyz :=
    (hll _ _ _ (ofAntisymmetrization_le_ofAntisymmetrization_iff.2 hxz)
              (ofAntisymmetrization_le_ofAntisymmetrization_iff.2 hyz)).imp
      ofAntisymmetrization_le_ofAntisymmetrization_iff.1
      ofAntisymmetrization_le_ofAntisymmetrization_iff.1

/-- The antisymmetrization of a downward-directed preorder is downward-directed: a common lower
    bound of two representatives projects to a common lower bound of their classes. -/
instance isCodirectedOrder_antisymmetrization [IsCodirectedOrder α] :
    IsCodirectedOrder (Antisymmetrization α (· ≤ ·)) := by
  constructor
  intro x y
  obtain ⟨c, hcx, hcy⟩ :=
    exists_le_le (ofAntisymmetrization (· ≤ ·) x) (ofAntisymmetrization (· ≤ ·) y)
  refine ⟨toAntisymmetrization (· ≤ ·) c, ?_, ?_⟩
  · have h := toAntisymmetrization_le_toAntisymmetrization_iff.2 hcx
    rwa [toAntisymmetrization_ofAntisymmetrization] at h
  · have h := toAntisymmetrization_le_toAntisymmetrization_iff.2 hcy
    rwa [toAntisymmetrization_ofAntisymmetrization] at h

end General

/-! ### The T×W frame and its strand preorder -/

open HistoricalAlternatives Core

variable {W Time : Type*} [LinearOrder Time]

/-- A **T×W frame** ([rumberg-lauer-2023] Def 5; [thomason-1984]): a historical-alternatives
    relation with the standard equivalence/monotonicity properties (`≈_t` an equivalence, backward
    closed) plus **historical connectedness** — any two worlds share a common past. -/
structure TxWFrame (W Time : Type*) [LinearOrder Time] where
  /-- The historical-accessibility relation `≈_t`. -/
  hist : HistoricalAlternatives W Time
  /-- `≈_t` is an equivalence, monotone in time ([condoravdi-2002]). -/
  props : HistoricalProperties hist
  /-- Historical connectedness ([rumberg-lauer-2023] Def 5(iv.c)): any two worlds agree at some
      time. -/
  connected : ∀ w₁ w₂ : W, ∃ t : Time, histEquiv hist t w₁ w₂

/-- A **strand**: a world-time pair, to be ordered by the collapse preorder. -/
structure Strand (F : TxWFrame W Time) where
  /-- The underlying world-time pair. -/
  pt : WorldTimeIndex W Time

namespace Strand

variable {F : TxWFrame W Time}

/-- The **strand preorder** ([rumberg-lauer-2023] §4.1.3): `s₁ ⊑ s₂` iff `s₁` is no later than `s₂`
    and their worlds agree up to `s₁`'s time. The branching order before collapse. -/
instance instPreorder : Preorder (Strand F) where
  le s₁ s₂ := s₁.pt.time ≤ s₂.pt.time ∧ histEquiv F.hist s₁.pt.time s₁.pt.world s₂.pt.world
  le_refl s := ⟨le_refl _, histEquiv_refl F.props.refl s.pt.time s.pt.world⟩
  le_trans s₁ s₂ s₃ h12 h23 := by
    refine ⟨le_trans h12.1 h23.1, ?_⟩
    exact histEquiv_trans F.props.trans s₁.pt.time h12.2
      (histEquiv_mono F.props.backwards s₂.pt.world s₃.pt.world h12.1 h23.2)

theorem le_def {s₁ s₂ : Strand F} :
    s₁ ≤ s₂ ↔ s₁.pt.time ≤ s₂.pt.time ∧ histEquiv F.hist s₁.pt.time s₁.pt.world s₂.pt.world :=
  Iff.rfl

/-- **The deep step**: the strand preorder is **left-linear** — the predecessors of any strand are
    comparable. This is where the T×W → branching transformation works: because time is linearly
    ordered and `≈` is backward-closed, two strands below a common one cannot branch in the past. -/
theorem strand_comparable {a b c : Strand F} (hac : a ≤ c) (hbc : b ≤ c) : a ≤ b ∨ b ≤ a := by
  rcases le_total a.pt.time b.pt.time with hab | hba
  · refine Or.inl ⟨hab, ?_⟩
    have h1 : histEquiv F.hist a.pt.time b.pt.world c.pt.world :=
      histEquiv_mono F.props.backwards b.pt.world c.pt.world hab hbc.2
    exact histEquiv_trans F.props.trans a.pt.time hac.2 (histEquiv_symm F.props.symm a.pt.time h1)
  · refine Or.inr ⟨hba, ?_⟩
    have h1 : histEquiv F.hist b.pt.time a.pt.world c.pt.world :=
      histEquiv_mono F.props.backwards a.pt.world c.pt.world hba hac.2
    exact histEquiv_trans F.props.trans b.pt.time hbc.2 (histEquiv_symm F.props.symm b.pt.time h1)

/-- Historical connectedness lifts to downward-directedness of the strand preorder: any two strands
    share a common past (take the earlier of their times and a time where their worlds agree). -/
instance instIsCodirectedOrder : IsCodirectedOrder (Strand F) := by
  constructor
  intro a b
  obtain ⟨t, ht⟩ := F.connected a.pt.world b.pt.world
  refine ⟨⟨⟨a.pt.world, min (min a.pt.time b.pt.time) t⟩⟩, ?_, ?_⟩
  · exact ⟨le_trans (min_le_left _ _) (min_le_left _ _),
      histEquiv_refl F.props.refl _ a.pt.world⟩
  · exact ⟨le_trans (min_le_left _ _) (min_le_right _ _),
      histEquiv_mono F.props.backwards a.pt.world b.pt.world (min_le_right _ _) ht⟩

/-- **The collapse is exactly historical equivalence** ([rumberg-lauer-2023] §4.1.3): two strands
    are merged into one moment iff they share a time and their worlds are historically equivalent
    there. The antisymmetrization quotient *is* the merge of `≈`-classes. -/
theorem collapse_antisymmRel_iff {s₁ s₂ : Strand F} :
    AntisymmRel (· ≤ ·) s₁ s₂ ↔
      s₁.pt.time = s₂.pt.time ∧ histEquiv F.hist s₁.pt.time s₁.pt.world s₂.pt.world := by
  constructor
  · rintro ⟨h12, h21⟩
    exact ⟨le_antisymm h12.1 h21.1, h12.2⟩
  · rintro ⟨ht, he⟩
    refine ⟨⟨le_of_eq ht, he⟩, ⟨le_of_eq ht.symm, ?_⟩⟩
    have := histEquiv_symm F.props.symm s₁.pt.time he
    rwa [ht] at this

end Strand

/-! ### The collapse is a branching-time frame -/

/-- **The bridge** ([rumberg-lauer-2023] §4.1.3): the collapse of a T×W frame — the
    antisymmetrization of its strand preorder — is a genuine `IsBranchingTime` frame. Left-linearity
    comes from `Strand.strand_comparable` (linear time + backward closure), connectedness from
    `Strand.instIsCodirectedOrder` (historical connectedness). -/
theorem isBranchingTime_collapse (F : TxWFrame W Time) :
    IsBranchingTime (Antisymmetrization (Strand F) (· ≤ ·)) :=
  haveI : IsLeftLinear (Antisymmetrization (Strand F) (· ≤ ·)) :=
    isLeftLinear_antisymmetrization (fun _ _ _ hac hbc => Strand.strand_comparable hac hbc)
  ⟨⟩

end BranchingTime
