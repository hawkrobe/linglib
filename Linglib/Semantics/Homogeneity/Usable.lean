import Linglib.Semantics.Homogeneity.Defs
import Linglib.Semantics.Questions.Partition.QUD

/-!
# Pragmatic usability of trivalent propositions

[kriz-2016]'s pragmatics over `Trivalent.Prop3`: a proposition is
`sufficientlyTrue` at a world when its issue cell contains a literally-true
world, `addressesIssue` when no cell straddles the true/false boundary, and
`usable` when it is not false, sufficiently true, and addresses the issue.
Non-maximal readings are exactly usability at gap-worlds
(`gap_enables_nonmax`); gap removal blocks them
(`metaAssert_prevents_nonmax`); tolerated exceptions cannot be mentioned
(`exception_unaddressable`). `communicatedContent` is what the hearer
learns; strong relevance ([kriz-spector-2021]) is the bivalent counterpart
of Addressing.

## Main definitions

* `sufficientlyTrue`, `addressesIssue`, `usable`: Križ's weakened Quality.
* `communicatedContent`: worlds compatible with what is communicated.
* `isStronglyRelevantProp`: constancy on issue cells.
* `bivalentPred`: `Bool`-valued truth predicate of a bivalent proposition.

## References

* [M. Križ, *Homogeneity, Non-Maximality, and All*][kriz-2016]
* [M. Križ and B. Spector, *Interpreting Plural Predication*][kriz-spector-2021]
-/

namespace Semantics.Homogeneity

open Trivalent (Prop3)

variable {W : Type*}

/-- `p` is "true enough" at `w` relative to issue `q`: some `q`-equivalent
    world makes `p` literally true. This weakens the maxim of Quality — a
    speaker need only assert something equivalent, for current purposes, to
    something true. -/
def sufficientlyTrue (q : QUD W) (p : Prop3 W) (w : W) : Prop :=
  ∃ w', q.r w w' ∧ p w' = .true

instance sufficientlyTrue.instDecidable [Fintype W] (q : QUD W) (p : Prop3 W)
    (w : W) : Decidable (sufficientlyTrue q p w) :=
  inferInstanceAs (Decidable (∃ w', q.r w w' ∧ p w' = .true))

/-- Literal truth implies sufficient truth, for any issue. -/
theorem literal_imp_sufficient (q : QUD W) (p : Prop3 W) (w : W)
    (h : p w = .true) : sufficientlyTrue q p w :=
  ⟨w, q.iseqv.refl w, h⟩

/-- `p` addresses issue `q` when no cell of `q` overlaps both the positive
    and the negative extension. Gap-worlds are invisible: only cells
    straddling the true/false boundary disqualify. -/
def addressesIssue (q : QUD W) (p : Prop3 W) : Prop :=
  ¬∃ w₁ w₂, q.r w₁ w₂ ∧ p w₁ = .true ∧ p w₂ = .false

instance addressesIssue.instDecidable [Fintype W] (q : QUD W) (p : Prop3 W) :
    Decidable (addressesIssue q p) :=
  inferInstanceAs (Decidable (¬∃ w₁ w₂, q.r w₁ w₂ ∧ p w₁ = .true ∧ p w₂ = .false))

/-- `p` may be used at `w`: it is not false at `w`, sufficiently true at
    `w`, and addresses the issue. -/
def usable (q : QUD W) (p : Prop3 W) (w : W) : Prop :=
  p w ≠ .false ∧ sufficientlyTrue q p w ∧ addressesIssue q p

instance usable.instDecidable [Fintype W] (q : QUD W) (p : Prop3 W) (w : W) :
    Decidable (usable q p w) :=
  inferInstanceAs
    (Decidable (p w ≠ .false ∧ sufficientlyTrue q p w ∧ addressesIssue q p))

/-- For a bivalent proposition, usability is literal truth plus addressing:
    sufficient truth adds nothing without gap-worlds. -/
theorem usable_iff_of_isBivalent {p : Prop3 W} (hbiv : p.isBivalent)
    (q : QUD W) (w : W) :
    usable q p w ↔ p w = .true ∧ addressesIssue q p := by
  constructor
  · intro ⟨hNotFalse, _, hAddr⟩
    exact ⟨(hbiv w).resolve_right (absurd · hNotFalse), hAddr⟩
  · intro ⟨hTrue, hAddr⟩
    exact ⟨by simp [hTrue], literal_imp_sufficient q p w hTrue, hAddr⟩

/-! ### Usability at gap-worlds -/

/-- The gap enables non-maximal use: a gapped world whose cell contains a
    true-world is usable, given addressing. -/
theorem gap_enables_nonmax (q : QUD W) (p : Prop3 W) (w w' : W)
    (hGap : p w = .indet) (hEquiv : q.r w w') (hTrue : p w' = .true)
    (hAddr : addressesIssue q p) :
    usable q p w :=
  ⟨by simp [hGap], ⟨w', hEquiv, hTrue⟩, hAddr⟩

/-- Gap removal forces literal truth for usability: the general form of the
    headline result that homogeneity removers prevent non-maximal use. -/
theorem metaAssert_prevents_nonmax (q : QUD W) (p : Prop3 W) (w : W)
    (h : usable q p.metaAssert w) : p.metaAssert w = .true :=
  ((usable_iff_of_isBivalent (Prop3.isBivalent_metaAssert p) q w).mp h).1

/-- Unmentionability of exceptions ([kriz-2016] §4.1): when `p` is used at
    `w` under issue `q`, an exception-mentioning sentence `e` — true at `w`
    but false wherever `p` is literally true — cannot address the same
    issue. `w`'s cell contains a literally-true world, and `e` straddles the
    true/false boundary between `w` and that world. -/
theorem exception_unaddressable (q : QUD W) (p e : Prop3 W) (w : W)
    (hUse : usable q p w) (hEw : e w = .true)
    (hEfalse : ∀ w', p w' = .true → e w' = .false) :
    ¬ addressesIssue q e := by
  obtain ⟨-, ⟨w', hEq, hTrue⟩, -⟩ := hUse
  exact λ hAddr => hAddr ⟨w, w', hEq, hEw, hEfalse w' hTrue⟩

/-! ### Communicated content -/

/-- The worlds the hearer considers possible after hearing `p` under issue
    `q`: those indistinguishable, for current purposes, from a world where
    `p` is literally true. -/
def communicatedContent (q : QUD W) (p : Prop3 W) : Set W :=
  {w | sufficientlyTrue q p w}

@[simp] theorem mem_communicatedContent {q : QUD W} {p : Prop3 W} {w : W} :
    w ∈ communicatedContent q p ↔ sufficientlyTrue q p w :=
  Iff.rfl

instance communicatedContent.instDecidableMem [Fintype W] (q : QUD W)
    (p : Prop3 W) (w : W) : Decidable (w ∈ communicatedContent q p) :=
  inferInstanceAs (Decidable (sufficientlyTrue q p w))

/-- Literal truth is always communicated. -/
theorem posExt_subset_communicated (q : QUD W) (p : Prop3 W) :
    p.posExt ⊆ communicatedContent q p :=
  λ _ hw => literal_imp_sufficient q p _ hw

/-- For a bivalent proposition that addresses the issue, communicated
    content is exactly the positive extension: no pragmatic weakening. -/
theorem communicatedContent_eq_posExt {p : Prop3 W} (hbiv : p.isBivalent)
    (q : QUD W) (hAddr : addressesIssue q p) :
    communicatedContent q p = p.posExt := by
  ext w
  constructor
  · intro ⟨w', hEq, hTrue⟩
    cases hbiv w with
    | inl h => exact h
    | inr hFalse =>
      exact absurd ⟨w', w, q.iseqv.symm hEq, hTrue, hFalse⟩ hAddr
  · exact literal_imp_sufficient q p w

/-- Coarser issues communicate more: if `q'` refines `q`, everything
    communicated under `q'` is communicated under `q`. This is
    [kriz-2016]'s key prediction that coarse issues enable non-maximal
    use. -/
theorem communicatedContent_antitone (q q' : QUD W) (p : Prop3 W)
    (hRef : ∀ w₁ w₂, q'.r w₁ w₂ → q.r w₁ w₂) :
    communicatedContent q' p ⊆ communicatedContent q p :=
  fun _ ⟨w', hEq, hTrue⟩ => ⟨w', hRef _ _ hEq, hTrue⟩

/-! ### Strong relevance

Bivalent counterpart of `addressesIssue`, from [kriz-spector-2021]: a
`W → Prop` is *strongly relevant* to an issue when it is constant on each
cell. The bivalent bridge to `addressesIssue` is
`KrizSpector2021.bivalent_addressing_iff_stronglyRelevant`. -/

/-- A proposition is strongly relevant to an issue iff it is constant on
    each cell of the partition. -/
def isStronglyRelevantProp (q : QUD W) (p : W → Prop) : Prop :=
  ∀ w₁ w₂ : W, q.r w₁ w₂ → (p w₁ ↔ p w₂)

/-- Filter a set of propositions to those strongly relevant to `q`. -/
def stronglyRelevantSet (q : QUD W) (candidates : Set (W → Prop)) :
    Set (W → Prop) :=
  { p ∈ candidates | isStronglyRelevantProp q p }

/-- With the trivial QUD, strong relevance is constancy on `W`. -/
theorem trivial_relevant_iff_constant (p : W → Prop) :
    isStronglyRelevantProp (QUD.trivial (M := W)) p ↔
    ∀ w₁ w₂ : W, p w₁ ↔ p w₂ := by
  simp only [isStronglyRelevantProp, QUD.trivial_r]
  exact ⟨fun h w₁ w₂ => h w₁ w₂ ⟨⟩, fun h _ _ _ => h _ _⟩

/-- With the exact QUD, every proposition is strongly relevant. -/
theorem exact_all_relevant [BEq W] [LawfulBEq W] (p : W → Prop) :
    isStronglyRelevantProp (QUD.exact (M := W)) p := by
  intro w₁ w₂ h
  rw [show w₁ = w₂ from h]

/-- With the exact QUD, the strongly-relevant filter is the identity. -/
theorem exact_stronglyRelevantSet_eq [BEq W] [LawfulBEq W]
    (candidates : Set (W → Prop)) :
    stronglyRelevantSet (QUD.exact (M := W)) candidates = candidates := by
  ext p
  simp only [stronglyRelevantSet, Set.mem_sep_iff]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, exact_all_relevant p⟩⟩

/-- The `Bool` truth predicate of a proposition. Bridges the trivalent
    Addressing constraint to bivalent strong-relevance filtering
    ([kriz-spector-2021]). -/
def bivalentPred (p : Prop3 W) : W → Bool :=
  λ w => p w == .true

end Semantics.Homogeneity
