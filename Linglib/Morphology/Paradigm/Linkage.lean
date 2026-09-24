module

public import Linglib.Morphology.Realization
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Card

/-!
# Paradigm linkage

This file defines Stump's paradigm linkage, which realizes a lexeme's content cell `⟨l, σ⟩`
through form cells `⟨z, τ⟩` of its stems. A linkage is a stem selection, a `Realization` of
lexemes by stems, together with a lexeme-sensitive property mapping. Each deviation from
canonical linkage negates one of its axes, after Corbett's canonical typology. Stump maintains
that PRAMEN, whose stem is phonologically constant across two inflection classes, exhibits "a
kind of stem suppletion", on which view heteroclisis "simply entails suppletion".

## Main definitions

* `Linkage`, `Linkage.corr`, `Linkage.realized`: the linkage, its form correspondents, and the
  realized paradigm.
* `Linkage.IsCanonical`, with the deviations `IsDefective`, `IsSyncretic`, `IsUnfaithful`.
* `Linkage.IsInvariantAlong`, `Linkage.IsHeteroclite`: per-lexeme invariance and variance of
  stems along a projection, such as their inflection class.
* `Linkage.ofFun`, `Linkage.canonical`: the linkage of a stem-choice function.

## Main results

* `Linkage.IsHeteroclite.isSuppletive`: heteroclisis entails suppletion.
* `Linkage.realized_eq_of_corr_eq`: equal correspondent sets force equal realizations.

## Implementation notes

`IsTotal`, `IsUnivalent`, and the per-lexeme `IsInvariant`, `IsSuppletive`, and
`IsOverabundant` ([thornton-2011]'s cell-mates) are inherited from `Realization`.

## References

* [corbett-2007]
* [stump-2006]
* [stump-2012-mmm8]
* [stump-2016]
* [thornton-2011]
-/

@[expose] public section

namespace Morphology

/-- A paradigm linkage ([stump-2012-mmm8]) consists of a stem selection, the inherited
`realize`, which gives the finite set of stems realizing each content cell `⟨l, σ⟩`, and a
property mapping `pm`. The stem set is empty at a gap in the stem specification and has several
members at an overabundant cell. -/
structure Linkage (L Z P : Type*) extends Realization L P Z where
  /-- The property mapping carries a content cell's property set to that of its form
  correspondents, and may consult the lexeme. -/
  pm : L → P → P

namespace Linkage

variable {L Z P W X Y K : Type*} (ℓ : Linkage L Z P)

/-- The form correspondents of a content cell `⟨l, σ⟩` pair each of its stems with the mapped
property set `ℓ.pm l σ`. -/
def corr (l : L) (σ : P) : Finset (Z × P) := ℓ.realize l σ ×ˢ {ℓ.pm l σ}

@[simp] theorem mem_corr {l : L} {σ : P} {zτ : Z × P} :
    zτ ∈ ℓ.corr l σ ↔ zτ.1 ∈ ℓ.realize l σ ∧ zτ.2 = ℓ.pm l σ := by
  rw [corr, Finset.mem_product, Finset.mem_singleton]

@[simp] theorem corr_nonempty (l : L) (σ : P) :
    (ℓ.corr l σ).Nonempty ↔ (ℓ.realize l σ).Nonempty := by
  simp [corr]

@[simp] theorem card_corr (l : L) (σ : P) : (ℓ.corr l σ).card = (ℓ.realize l σ).card := by
  simp [corr]

/-- The realized paradigm of a content cell realizes each form correspondent `⟨z, τ⟩` as
`rf z τ`, keeping the property set `τ`. -/
def realized [DecidableEq W] (rf : Z → P → W) (l : L) (σ : P) : Finset (W × P) :=
  ((ℓ.realize l σ).image fun z ↦ rf z (ℓ.pm l σ)) ×ˢ {ℓ.pm l σ}

@[simp] theorem mem_realized [DecidableEq W] {rf : Z → P → W} {l : L} {σ : P} {wτ : W × P} :
    wτ ∈ ℓ.realized rf l σ ↔ ∃ z ∈ ℓ.realize l σ, (rf z (ℓ.pm l σ), ℓ.pm l σ) = wτ := by
  simp [realized, Prod.ext_iff]

/-! ### Canonical linkage -/

/-- A linkage is stem-invariant when each lexeme draws the stems of all its cells from a single
stem. -/
def IsStemInvariant : Prop := ∀ l, ℓ.IsInvariant l

/-- A linkage is injective when no two content cells of a lexeme share a form correspondent. -/
def IsInjective : Prop := ∀ l ⦃σ₁ σ₂ : P⦄, σ₁ ≠ σ₂ → Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)

/-- A linkage is property-preserving when every form correspondent carries its content cell's
own property set. -/
def IsPropertyPreserving : Prop := ∀ l σ, ℓ.pm l σ = σ

/-- A linkage is canonical ([stump-2012-mmm8]) when it satisfies all five axes. -/
structure IsCanonical : Prop where
  /-- Every content cell has a form correspondent. -/
  total : ℓ.IsTotal
  /-- No content cell has more than one form correspondent. -/
  univalent : ℓ.IsUnivalent
  /-- Each lexeme draws on a single stem. -/
  stemInvariant : ℓ.IsStemInvariant
  /-- No two content cells of a lexeme share a form correspondent. -/
  injective : ℓ.IsInjective
  /-- Every form correspondent carries its content cell's own property set. -/
  propertyPreserving : ℓ.IsPropertyPreserving

/-! ### Deviations from canonical linkage -/

/-- A linkage is defective ([stump-2012-mmm8]) when some content cell has no stem. -/
def IsDefective : Prop := ∃ l σ, ℓ.realize l σ = ∅

/-- A linkage is syncretic ([stump-2012-mmm8]) when two distinct content cells of a lexeme share
a form correspondent. -/
def IsSyncretic : Prop := ∃ l σ₁ σ₂, σ₁ ≠ σ₂ ∧ ¬ Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)

/-- A linkage is unfaithful ([stump-2012-mmm8]) when some content cell's form correspondents
carry a different property set, as under deponency and functor-argument reversal. -/
def IsUnfaithful : Prop := ∃ l σ, ℓ.pm l σ ≠ σ

/-- A form cell is virtual ([stump-2012-mmm8]) when no content cell corresponds to it. -/
def IsVirtual (zτ : Z × P) : Prop := ∀ l σ, zτ ∉ ℓ.corr l σ

/-- Defectiveness is exactly the failure of totality. -/
@[simp, push] theorem not_isTotal_iff : ¬ ℓ.IsTotal ↔ ℓ.IsDefective := by
  simp [IsDefective, Realization.IsTotal, Finset.not_nonempty_iff_eq_empty]

/-- Syncretism is exactly the failure of injectivity. -/
@[simp, push] theorem not_isInjective_iff : ¬ ℓ.IsInjective ↔ ℓ.IsSyncretic := by
  simp [IsSyncretic, IsInjective]

/-- Unfaithfulness is exactly the failure of property preservation. -/
@[simp, push] theorem not_isPropertyPreserving_iff :
    ¬ ℓ.IsPropertyPreserving ↔ ℓ.IsUnfaithful := by
  simp [IsUnfaithful, IsPropertyPreserving]

/-! ### Invariance along a projection -/

/-- A lexeme is invariant along `p` when the stems of all its cells have one image under `p`;
along `id` this is `IsInvariant`. -/
def IsInvariantAlong (p : Z → X) (l : L) : Prop :=
  ∀ ⦃σ σ' : P⦄, ∀ z ∈ ℓ.realize l σ, ∀ z' ∈ ℓ.realize l σ', p z = p z'

/-- A lexeme is heteroclite along a classification `cls` of stems ([stump-2006]) when two of
its cells draw on stems of distinct classes; along `id` this is `IsSuppletive`. -/
def IsHeteroclite (cls : Z → K) (l : L) : Prop :=
  ∃ σ σ', ∃ z ∈ ℓ.realize l σ, ∃ z' ∈ ℓ.realize l σ', cls z ≠ cls z'

variable {ℓ} {p : Z → X} {cls : Z → K} {l : L}

/-- Invariance along `id` is invariance. -/
theorem isInvariantAlong_id_iff : ℓ.IsInvariantAlong id l ↔ ℓ.IsInvariant l := Iff.rfl

/-- Heteroclisis along `id` is suppletion. -/
theorem isHeteroclite_id_iff : ℓ.IsHeteroclite id l ↔ ℓ.IsSuppletive l := Iff.rfl

/-- A lexeme fails to be invariant along `p` exactly when it is heteroclite along `p`. -/
@[simp, push] theorem not_isInvariantAlong_iff :
    ¬ ℓ.IsInvariantAlong p l ↔ ℓ.IsHeteroclite p l := by
  simp [IsInvariantAlong, IsHeteroclite]

/-- Invariance along `p` transfers to invariance along any coarsening `q ∘ p`. -/
theorem IsInvariantAlong.comp (h : ℓ.IsInvariantAlong p l) (q : X → Y) :
    ℓ.IsInvariantAlong (q ∘ p) l :=
  fun _ _ z hz z' hz' ↦ congrArg q (h z hz z' hz')

/-- An invariant lexeme is invariant along every projection. -/
theorem _root_.Morphology.Realization.IsInvariant.isInvariantAlong (h : ℓ.IsInvariant l)
    (p : Z → X) : ℓ.IsInvariantAlong p l :=
  fun _ _ z hz z' hz' ↦ congrArg p (h z hz z' hz')

/-- Heteroclisis entails suppletion, since stems of two classes are two stems. -/
theorem IsHeteroclite.isSuppletive (h : ℓ.IsHeteroclite cls l) : ℓ.IsSuppletive l :=
  let ⟨σ, σ', z, hz, z', hz', hne⟩ := h
  ⟨σ, σ', z, hz, z', hz', ne_of_apply_ne cls hne⟩

/-! ### Decidability

Each instance is `inferInstanceAs` on the definition's body, so that `decide` reduces in the
kernel. The per-lexeme instances quantify over stem sets and need no `Fintype Z`. -/

section Decidable

variable (ℓ) [Fintype P]

instance [DecidableEq X] (p : Z → X) (l : L) : Decidable (ℓ.IsInvariantAlong p l) :=
  inferInstanceAs
    (Decidable (∀ σ σ' : P, ∀ z ∈ ℓ.realize l σ, ∀ z' ∈ ℓ.realize l σ', p z = p z'))

instance [DecidableEq K] (cls : Z → K) (l : L) : Decidable (ℓ.IsHeteroclite cls l) :=
  inferInstanceAs
    (Decidable (∃ σ σ', ∃ z ∈ ℓ.realize l σ, ∃ z' ∈ ℓ.realize l σ', cls z ≠ cls z'))

variable [Fintype L]

instance [DecidableEq Z] : Decidable ℓ.IsStemInvariant :=
  inferInstanceAs (Decidable (∀ l, ℓ.IsInvariant l))

instance [DecidableEq Z] [DecidableEq P] : Decidable ℓ.IsInjective :=
  inferInstanceAs
    (Decidable (∀ l, ∀ σ₁ σ₂ : P, σ₁ ≠ σ₂ → Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)))

instance [DecidableEq P] : Decidable ℓ.IsPropertyPreserving :=
  inferInstanceAs (Decidable (∀ l σ, ℓ.pm l σ = σ))

instance [DecidableEq Z] : Decidable ℓ.IsDefective :=
  inferInstanceAs (Decidable (∃ l σ, ℓ.realize l σ = ∅))

instance [DecidableEq Z] [DecidableEq P] : Decidable ℓ.IsSyncretic :=
  inferInstanceAs
    (Decidable (∃ l σ₁ σ₂, σ₁ ≠ σ₂ ∧ ¬ Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)))

instance [DecidableEq P] : Decidable ℓ.IsUnfaithful :=
  inferInstanceAs (Decidable (∃ l σ, ℓ.pm l σ ≠ σ))

instance [DecidableEq Z] [DecidableEq P] (zτ : Z × P) : Decidable (ℓ.IsVirtual zτ) :=
  inferInstanceAs (Decidable (∀ l σ, zτ ∉ ℓ.corr l σ))

end Decidable

/-! ### Realization through correspondents -/

section Realized

variable (ℓ) [DecidableEq W] (rf : Z → P → W)

/-- A content cell realizes as the image of its form correspondents under `rf`. -/
theorem realized_eq_image_corr [DecidableEq P] (l : L) (σ : P) :
    ℓ.realized rf l σ = (ℓ.corr l σ).image fun zτ ↦ (rf zτ.1 zτ.2, zτ.2) := by
  ext; simp

/-- Equal correspondent sets force equal realizations, within a lexeme (the mechanism of
syncretism) and across lexemes. -/
theorem realized_eq_of_corr_eq {l₁ l₂ : L} {σ₁ σ₂ : P} (h : ℓ.corr l₁ σ₁ = ℓ.corr l₂ σ₂) :
    ℓ.realized rf l₁ σ₁ = ℓ.realized rf l₂ σ₂ := by
  classical
  rw [realized_eq_image_corr, realized_eq_image_corr, h]

end Realized

/-! ### Linkages of stem-choice functions -/

/-- The linkage of a stem choice `f` gives the content cell `⟨l, σ⟩` the single stem `f l σ`
and preserves its property set. -/
def ofFun (f : L → P → Z) : Linkage L Z P where
  realize l σ := {f l σ}
  pm _ σ := σ

section OfFun

variable (f : L → P → Z)

@[simp] theorem ofFun_realize (l : L) (σ : P) : (ofFun f).realize l σ = {f l σ} := rfl

@[simp] theorem ofFun_pm (l : L) (σ : P) : (ofFun f).pm l σ = σ := rfl

@[simp] theorem ofFun_corr (l : L) (σ : P) : (ofFun f).corr l σ = {(f l σ, σ)} :=
  Finset.singleton_product_singleton

@[simp] theorem ofFun_realized [DecidableEq W] (rf : Z → P → W) (l : L) (σ : P) :
    (ofFun f).realized rf l σ = {(rf (f l σ) σ, σ)} := by
  simp [realized]

variable {f}

@[simp] theorem ofFun_isInvariantAlong_iff :
    (ofFun f).IsInvariantAlong p l ↔ ∀ σ σ', p (f l σ) = p (f l σ') := by
  simp [IsInvariantAlong]

@[simp] theorem ofFun_isHeteroclite_iff :
    (ofFun f).IsHeteroclite cls l ↔ ∃ σ σ', cls (f l σ) ≠ cls (f l σ') := by
  simp [IsHeteroclite]

/-- The linkage of a stem choice is canonical exactly when each lexeme's stem is independent of
the property set. -/
theorem ofFun_isCanonical_iff : (ofFun f).IsCanonical ↔ ∀ l σ σ', f l σ = f l σ' := by
  refine ⟨fun h l ↦ ofFun_isInvariantAlong_iff.mp (h.stemInvariant l), fun h ↦
    ⟨fun _ _ ↦ Finset.singleton_nonempty _, fun _ _ ↦ (Finset.card_singleton _).le,
      fun l ↦ ofFun_isInvariantAlong_iff.mpr (h l), fun l σ σ' hne ↦ ?_, fun _ _ ↦ rfl⟩⟩
  simp [hne]

end OfFun

/-- The canonical linkage of `st` gives every cell of the lexeme `l` the stem `st l`, the graph
of the universal default rule of paradigm linkage ([stump-2006]) with `st l` the root of `l`. -/
abbrev canonical (st : L → Z) : Linkage L Z P := ofFun fun l _ ↦ st l

/-- The canonical linkage is canonical. -/
theorem canonical_isCanonical (st : L → Z) : (canonical (P := P) st).IsCanonical :=
  ofFun_isCanonical_iff.mpr fun _ _ _ ↦ rfl

end Linkage

end Morphology
