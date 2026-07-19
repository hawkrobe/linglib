import Linglib.Morphology.Realization
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card

/-!
# Paradigm linkage: content paradigms, form paradigms, and correspondence

Inflectional morphology relates three levels of representation ([stump-2012-mmm8];
the book-length apparatus is [stump-2016]): a lexeme's **content paradigm** of
cells `⟨L, σ⟩` pairing a lexeme with a syntacticosemantic property set, a stem's
**form paradigm** of cells `⟨Z, τ⟩` pairing a stem with a property set it inflects
for, and the **realized paradigm** of word forms. A content cell is realized by
being linked to its **form correspondents**, whose realizations it shares. The
correspondence is a finite relation in factored presentation: a stem selection
`stems : L → P → Finset Z` and a lexeme-sensitive property mapping `pm : L → P → P`.
Canonically the relation is the graph of `⟨l, σ⟩ ↦ ⟨root l, σ⟩` ([stump-2006]'s
universal default rule of paradigm linkage).

Canonical linkage is the typological extreme against which deviations are
calibrated — [corbett-2007]'s canonical-typology method, with the axes read off
the correspondence relation's standard properties. `IsTotal`: every content cell
has a form correspondent. `IsUnivalent`: at most one. `IsStemInvariant`: one stem
serves all of a lexeme's cells. `IsInjective`: no two content cells share a
correspondent. `IsPropertyPreserving`: a correspondent carries the content cell's
own property set. Each named noncanonical phenomenon negates one axis:
defectiveness totality ([stump-2012-mmm8] §3.1), overabundance univalence
([thornton-2011]'s cell-mates), suppletion stem invariance (§3.4), syncretism
injectivity (§3.2), and deponency and functor-argument reversal property
preservation (§3.3).

Stem invariance is one instance of a projection-indexed family: `InvariantAlong p`
asks the composite `p ∘ stems` to be constant per lexeme. Instantiated at a
consumer-supplied inflection-class projection `cls : Z → K` it yields
**heteroclisis** — form correspondents drawn from form paradigms of two or more
inflection classes ([stump-2006]). Because constancy transfers along any
projection (`InvariantAlong.comp`), heteroclisis entails stem non-invariance
(`IsHeteroclite.isSuppletive`): heteroclisis is "a kind of stem alternation" even
when the stems are phonologically identical, [stump-2006]'s reading of Czech
PRAMEN, whose two stems differ in class but not in form.

## Main declarations

* `Linkage L Z P` — the correspondence in factored presentation: finite stem
  selection and lexeme-sensitive property mapping
* `Linkage.corr`, `Linkage.realize` — the form-correspondent set of a content
  cell and the realized paradigm over it
* `Linkage.IsTotal`, `IsUnivalent`, `IsStemInvariant`, `IsInjective`,
  `IsPropertyPreserving` — the axes of canonical linkage; `IsCanonical` bundles
  them; `InvariantAlong` is the projection-indexed generalization of stem
  invariance
* `Linkage.IsDefective`, `IsOverabundant`, `IsSuppletive`, `IsHeteroclite`,
  `IsSyncretic`, `IsUnfaithful` — the six deviations, each an axis failure
  (`isDefective_iff_not_isTotal`, `isOverabundant_iff_not_isUnivalent`,
  `isSyncretic_iff_not_isInjective`, …)
* `Linkage.IsHeteroclite.isSuppletive` — heteroclisis entails stem non-invariance
* `Linkage.HasCellMates` — distinct realized forms at one cell; entails
  `IsOverabundant`
* `Linkage.IsVirtual` — a form cell no content cell corresponds to
* `Linkage.canonical` / `canonical_isCanonical` — the total, lexeme-blind,
  one-stem linkage, canonical on all axes
* `Linkage.realize_eq_of_corr_eq`, `realize_eq_of_corr_eq_lexeme` — shared
  correspondents force shared realizations, within and across lexemes
-/

namespace Morphology

/-- A **paradigm linkage** ([stump-2012-mmm8]) from the vantage of a single
lexeme: the two components of the form-correspondence relation. `stems` selects
the finite set of stems realizing a content cell — empty at a gap in the stem
specification, more than one at an overabundant cell; `pm` carries a content
cell's property set to its form correspondents', and may consult the lexeme.
Canonically `stems` is singleton-valued and constant in the property set and
`pm` is the identity. -/
structure Linkage (L Z P : Type*) where
  /-- The stems realizing a content cell `⟨l, σ⟩`: empty where the stem
  specification has a gap, non-singleton where the cell is overabundant. -/
  stems : L → P → Finset Z
  /-- The property mapping carrying a content cell's property set to its form
  correspondents', consulting the lexeme for functor-argument reversal. -/
  pm : L → P → P

namespace Linkage

variable {L Z P W X Y K : Type*} (ℓ : Linkage L Z P)

/-- The **form correspondents** of a content cell `⟨l, σ⟩`: each selected stem
paired with the mapped property set — empty where the stem specification has a
gap. -/
def corr (l : L) (σ : P) : Finset (Z × P) := ℓ.stems l σ ×ˢ {ℓ.pm l σ}

@[simp] theorem mem_corr {l : L} {σ : P} {zτ : Z × P} :
    zτ ∈ ℓ.corr l σ ↔ zτ.1 ∈ ℓ.stems l σ ∧ zτ.2 = ℓ.pm l σ := by
  rw [corr, Finset.mem_product, Finset.mem_singleton]

@[simp] theorem corr_nonempty (l : L) (σ : P) :
    (ℓ.corr l σ).Nonempty ↔ (ℓ.stems l σ).Nonempty := by
  simp [corr]

@[simp] theorem card_corr (l : L) (σ : P) :
    (ℓ.corr l σ).card = (ℓ.stems l σ).card := by
  simp [corr]

/-- The **realized paradigm** on content cells: a content cell realizes as its
form correspondents do. `realizeForm` supplies the form-cell realization; the
result is empty exactly where the correspondent set is. -/
def realize [DecidableEq W] (realizeForm : Z → P → W) (l : L) (σ : P) :
    Finset (W × P) :=
  ((ℓ.stems l σ).image fun z => realizeForm z (ℓ.pm l σ)) ×ˢ {ℓ.pm l σ}

@[simp] theorem mem_realize [DecidableEq W] {realizeForm : Z → P → W} {l : L}
    {σ : P} {wτ : W × P} :
    wτ ∈ ℓ.realize realizeForm l σ ↔
      ∃ z ∈ ℓ.stems l σ, wτ = (realizeForm z (ℓ.pm l σ), ℓ.pm l σ) := by
  obtain ⟨w, τ⟩ := wτ
  simp [realize, Prod.ext_iff, eq_comm (a := w), eq_comm (a := τ)]

/-! ### The axes of canonical linkage -/

/-- **Totality**: every content cell has a form correspondent. Defectiveness is
the failure. -/
def IsTotal : Prop := ∀ l σ, (ℓ.stems l σ).Nonempty

/-- **Univalence**: every content cell has at most one form correspondent.
Overabundance is the failure. -/
def IsUnivalent : Prop := ∀ l σ, (ℓ.stems l σ).card ≤ 1

/-- **Invariance along a projection**: the composite `p ∘ stems` is constant on
each lexeme's paradigm. At `p := id` this is stem invariance; at an
inflection-class projection it is the axis heteroclisis negates. Undefined cells
impose no constraint. -/
def InvariantAlong (p : Z → X) : Prop :=
  ∀ l ⦃σ₁ σ₂ : P⦄ ⦃z₁ z₂ : Z⦄,
    z₁ ∈ ℓ.stems l σ₁ → z₂ ∈ ℓ.stems l σ₂ → p z₁ = p z₂

/-- **Stem invariance**: one stem serves all of a lexeme's cells, so its
correspondents come from a single form paradigm. Stem suppletion is the
failure. -/
def IsStemInvariant : Prop := ℓ.InvariantAlong id

/-- **Injectivity**: no two content cells of a lexeme share a form
correspondent. Syncretism is the failure. -/
def IsInjective : Prop :=
  ∀ l ⦃σ₁ σ₂ : P⦄, σ₁ ≠ σ₂ → Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)

/-- **Property preservation**: a form correspondent carries the content cell's
own property set. Deponency, functor-argument reversal, and directional
syncretism are failures. -/
def IsPropertyPreserving : Prop := ∀ l σ, ℓ.pm l σ = σ

/-- **Canonical paradigm linkage** ([stump-2012-mmm8], axes per [corbett-2007]'s
canonical-typology method): all five axes at once. -/
structure IsCanonical : Prop where
  total : ℓ.IsTotal
  univalent : ℓ.IsUnivalent
  stemInvariant : ℓ.IsStemInvariant
  injective : ℓ.IsInjective
  propertyPreserving : ℓ.IsPropertyPreserving

/-- Constancy transfers along any further projection. -/
theorem InvariantAlong.comp {ℓ : Linkage L Z P} {p : Z → X}
    (h : ℓ.InvariantAlong p) (q : X → Y) : ℓ.InvariantAlong (q ∘ p) :=
  fun l _ _ _ _ h₁ h₂ => congrArg q (h l h₁ h₂)

/-- A stem-invariant linkage is invariant along every projection. -/
theorem IsStemInvariant.invariantAlong {ℓ : Linkage L Z P}
    (h : ℓ.IsStemInvariant) (p : Z → X) : ℓ.InvariantAlong p :=
  fun l _ _ _ _ h₁ h₂ => congrArg p (h l h₁ h₂)

/-! ### Deviations from canonical linkage

Each noncanonical phenomenon negates one axis. -/

/-- **Defectiveness**: some content cell lacks a form correspondent
([stump-2012-mmm8] §3.1). Negates totality. -/
def IsDefective : Prop := ∃ l σ, ℓ.stems l σ = ∅

/-- **Overabundance**: some content cell has two or more form correspondents —
[thornton-2011]'s cell-mates, at the level of the correspondence. Negates
univalence. -/
def IsOverabundant : Prop := ∃ l σ, 2 ≤ (ℓ.stems l σ).card

/-- **Suppletion**: a lexeme's correspondents draw on more than one stem
([stump-2012-mmm8] §3.4). Negates stem invariance. -/
def IsSuppletive : Prop := ¬ ℓ.IsStemInvariant

/-- **Heteroclisis**: a lexeme's correspondents draw on form paradigms of two or
more inflection classes ([stump-2006]), the classes given by a projection
`cls : Z → K`. Negates invariance along `cls`. -/
def IsHeteroclite (cls : Z → K) : Prop := ¬ ℓ.InvariantAlong cls

/-- **Syncretism**: two distinct content cells share a form correspondent
([stump-2012-mmm8] §3.2). Negates injectivity. -/
def IsSyncretic : Prop :=
  ∃ l σ₁ σ₂, σ₁ ≠ σ₂ ∧ ¬ Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)

/-- **Unfaithfulness**: some content cell's form correspondents carry a
different property set — deponency and functor-argument reversal
([stump-2012-mmm8] §3.3). Negates property preservation. -/
def IsUnfaithful : Prop := ∃ l σ, ℓ.pm l σ ≠ σ

/-- Defectiveness is exactly the failure of totality. -/
theorem isDefective_iff_not_isTotal : ℓ.IsDefective ↔ ¬ ℓ.IsTotal := by
  simp [IsDefective, IsTotal, Finset.not_nonempty_iff_eq_empty]

/-- Overabundance is exactly the failure of univalence. -/
theorem isOverabundant_iff_not_isUnivalent :
    ℓ.IsOverabundant ↔ ¬ ℓ.IsUnivalent := by
  simp [IsOverabundant, IsUnivalent, Nat.lt_iff_add_one_le, not_le]

/-- Syncretism is exactly the failure of injectivity. -/
theorem isSyncretic_iff_not_isInjective : ℓ.IsSyncretic ↔ ¬ ℓ.IsInjective := by
  simp [IsSyncretic, IsInjective, not_forall]

/-- Unfaithfulness is exactly the failure of property preservation. -/
theorem isUnfaithful_iff_not_isPropertyPreserving :
    ℓ.IsUnfaithful ↔ ¬ ℓ.IsPropertyPreserving := by
  simp [IsUnfaithful, IsPropertyPreserving]

/-- Heteroclisis entails stem non-invariance: drawing on two inflection classes
is drawing on two stems, [stump-2006]'s "a kind of stem alternation" — even when
the stems are phonologically identical, as in Czech PRAMEN. -/
theorem IsHeteroclite.isSuppletive {cls : Z → K} (h : ℓ.IsHeteroclite cls) :
    ℓ.IsSuppletive :=
  fun hinv => h (IsStemInvariant.invariantAlong hinv cls)

theorem IsCanonical.not_isDefective (h : ℓ.IsCanonical) : ¬ ℓ.IsDefective :=
  fun hd => ℓ.isDefective_iff_not_isTotal.mp hd h.total

theorem IsCanonical.not_isOverabundant (h : ℓ.IsCanonical) :
    ¬ ℓ.IsOverabundant :=
  fun ho => ℓ.isOverabundant_iff_not_isUnivalent.mp ho h.univalent

theorem IsCanonical.not_isSuppletive (h : ℓ.IsCanonical) : ¬ ℓ.IsSuppletive :=
  not_not.mpr h.stemInvariant

theorem IsCanonical.not_isHeteroclite (h : ℓ.IsCanonical) (cls : Z → K) :
    ¬ ℓ.IsHeteroclite cls :=
  not_not.mpr (IsStemInvariant.invariantAlong h.stemInvariant cls)

theorem IsCanonical.not_isSyncretic (h : ℓ.IsCanonical) : ¬ ℓ.IsSyncretic :=
  fun hs => ℓ.isSyncretic_iff_not_isInjective.mp hs h.injective

theorem IsCanonical.not_isUnfaithful (h : ℓ.IsCanonical) : ¬ ℓ.IsUnfaithful :=
  fun ⟨l, σ, hne⟩ => hne (h.propertyPreserving l σ)

/-- A **virtual cell**: a form cell no content cell corresponds to
([stump-2012-mmm8] §4). Realization rules still define a value there, which
language change can release by suppressing a linkage override. -/
def IsVirtual (zτ : Z × P) : Prop := ∀ l σ, zτ ∉ ℓ.corr l σ

/-! ### Decidability

Instances by `inferInstanceAs` on the definitional unfolding, so `decide`
reduces in the kernel. -/

section Decidable

variable [Fintype L] [Fintype P] [Fintype Z] [DecidableEq Z] [DecidableEq P]

instance : Decidable ℓ.IsTotal :=
  inferInstanceAs (Decidable (∀ l σ, (ℓ.stems l σ).Nonempty))

instance : Decidable ℓ.IsUnivalent :=
  inferInstanceAs (Decidable (∀ l σ, (ℓ.stems l σ).card ≤ 1))

instance {p : Z → X} [DecidableEq X] : Decidable (ℓ.InvariantAlong p) :=
  inferInstanceAs (Decidable (∀ l, ∀ σ₁ σ₂ : P, ∀ z₁ z₂ : Z,
    z₁ ∈ ℓ.stems l σ₁ → z₂ ∈ ℓ.stems l σ₂ → p z₁ = p z₂))

instance : Decidable ℓ.IsStemInvariant :=
  inferInstanceAs (Decidable (ℓ.InvariantAlong id))

instance : Decidable ℓ.IsInjective :=
  inferInstanceAs (Decidable (∀ l, ∀ σ₁ σ₂ : P,
    σ₁ ≠ σ₂ → Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)))

instance : Decidable ℓ.IsPropertyPreserving :=
  inferInstanceAs (Decidable (∀ l σ, ℓ.pm l σ = σ))

instance : Decidable ℓ.IsDefective :=
  inferInstanceAs (Decidable (∃ l σ, ℓ.stems l σ = ∅))

instance : Decidable ℓ.IsOverabundant :=
  inferInstanceAs (Decidable (∃ l σ, 2 ≤ (ℓ.stems l σ).card))

instance : Decidable ℓ.IsSuppletive :=
  inferInstanceAs (Decidable (¬ ℓ.IsStemInvariant))

instance {cls : Z → K} [DecidableEq K] : Decidable (ℓ.IsHeteroclite cls) :=
  inferInstanceAs (Decidable (¬ ℓ.InvariantAlong cls))

instance : Decidable ℓ.IsSyncretic :=
  inferInstanceAs (Decidable (∃ l σ₁ σ₂,
    σ₁ ≠ σ₂ ∧ ¬ Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)))

instance : Decidable ℓ.IsUnfaithful :=
  inferInstanceAs (Decidable (∃ l σ, ℓ.pm l σ ≠ σ))

end Decidable

/-! ### Realization -/

section Realize

variable [DecidableEq W] (realizeForm : Z → P → W)

/-- Equal correspondent sets force equal realizations ([stump-2012-mmm8] §3.2):
the mechanism of syncretism. -/
theorem realize_eq_of_corr_eq {l : L} {σ₁ σ₂ : P}
    (h : ℓ.corr l σ₁ = ℓ.corr l σ₂) :
    ℓ.realize realizeForm l σ₁ = ℓ.realize realizeForm l σ₂ := by
  rcases (ℓ.stems l σ₁).eq_empty_or_nonempty with he | ⟨z, hz⟩
  · have he₂ : ℓ.stems l σ₂ = ∅ := by
      by_contra hne
      obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have : (z, ℓ.pm l σ₂) ∈ ℓ.corr l σ₁ := h ▸ ℓ.mem_corr.mpr ⟨hz, rfl⟩
      simp [he] at this
    simp [realize, he, he₂]
  · have hmem : (z, ℓ.pm l σ₁) ∈ ℓ.corr l σ₂ := h ▸ ℓ.mem_corr.mpr ⟨hz, rfl⟩
    have hpm : ℓ.pm l σ₁ = ℓ.pm l σ₂ := (ℓ.mem_corr.mp hmem).2
    have hstems : ℓ.stems l σ₁ = ℓ.stems l σ₂ := by
      ext x
      constructor <;> intro hx
      · exact (ℓ.mem_corr.mp (h ▸ ℓ.mem_corr.mpr ⟨hx, rfl⟩ :
          (x, ℓ.pm l σ₁) ∈ ℓ.corr l σ₂)).1
      · exact (ℓ.mem_corr.mp (h.symm ▸ ℓ.mem_corr.mpr ⟨hx, rfl⟩ :
          (x, ℓ.pm l σ₂) ∈ ℓ.corr l σ₁)).1
    simp [realize, hpm, hstems]

/-- Correspondent sets shared across two *lexemes* force shared realizations:
the cross-lexeme companion of `realize_eq_of_corr_eq`. This is the mechanism
behind [jackendoff-audring-2020]'s Same Verb solution — homophones with a shared
morphosyntactic-form pivot inflect alike, however their distinct semantics. -/
theorem realize_eq_of_corr_eq_lexeme {l₁ l₂ : L} {σ : P}
    (h : ℓ.corr l₁ σ = ℓ.corr l₂ σ) :
    ℓ.realize realizeForm l₁ σ = ℓ.realize realizeForm l₂ σ := by
  rcases (ℓ.stems l₁ σ).eq_empty_or_nonempty with he | ⟨z, hz⟩
  · have he₂ : ℓ.stems l₂ σ = ∅ := by
      by_contra hne
      obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have : (z, ℓ.pm l₂ σ) ∈ ℓ.corr l₁ σ := h ▸ ℓ.mem_corr.mpr ⟨hz, rfl⟩
      simp [he] at this
    simp [realize, he, he₂]
  · have hmem : (z, ℓ.pm l₁ σ) ∈ ℓ.corr l₂ σ := h ▸ ℓ.mem_corr.mpr ⟨hz, rfl⟩
    have hpm : ℓ.pm l₁ σ = ℓ.pm l₂ σ := (ℓ.mem_corr.mp hmem).2
    have hstems : ℓ.stems l₁ σ = ℓ.stems l₂ σ := by
      ext x
      constructor <;> intro hx
      · exact (ℓ.mem_corr.mp (h ▸ ℓ.mem_corr.mpr ⟨hx, rfl⟩ :
          (x, ℓ.pm l₁ σ) ∈ ℓ.corr l₂ σ)).1
      · exact (ℓ.mem_corr.mp (h.symm ▸ ℓ.mem_corr.mpr ⟨hx, rfl⟩ :
          (x, ℓ.pm l₂ σ) ∈ ℓ.corr l₁ σ)).1
    simp [realize, hpm, hstems]

/-- A shared form correspondent already forces a shared realized form, even when
the full correspondent sets differ: the multi-valued syncretism mechanism. -/
theorem not_disjoint_realize_of_not_disjoint_corr {l : L} {σ₁ σ₂ : P}
    (h : ¬ Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)) :
    ¬ Disjoint (ℓ.realize realizeForm l σ₁) (ℓ.realize realizeForm l σ₂) := by
  obtain ⟨⟨z, τ⟩, h₁, h₂⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨hz₁, hτ₁⟩ := ℓ.mem_corr.mp h₁
  obtain ⟨hz₂, hτ₂⟩ := ℓ.mem_corr.mp h₂
  exact Finset.not_disjoint_iff.mpr
    ⟨(realizeForm z τ, τ),
     ℓ.mem_realize.mpr ⟨z, hz₁, by rw [← hτ₁]⟩,
     ℓ.mem_realize.mpr ⟨z, hz₂, by rw [← hτ₂]⟩⟩

/-- **Cell-mates** ([thornton-2011]): some content cell realizes as two or more
distinct word forms. -/
def HasCellMates : Prop := ∃ l σ, 2 ≤ (ℓ.realize realizeForm l σ).card

/-- Realization cannot outnumber the stems that feed it. -/
theorem card_realize_le_card_stems (l : L) (σ : P) :
    (ℓ.realize realizeForm l σ).card ≤ (ℓ.stems l σ).card := by
  simpa [realize] using Finset.card_image_le

/-- Cell-mates certify overabundance: distinct realized forms at one cell need
distinct form correspondents there. The converse fails — distinct correspondents
may realize alike. -/
theorem HasCellMates.isOverabundant (h : ℓ.HasCellMates realizeForm) :
    ℓ.IsOverabundant := by
  obtain ⟨l, σ, hcard⟩ := h
  exact ⟨l, σ, hcard.trans (ℓ.card_realize_le_card_stems realizeForm l σ)⟩

end Realize

/-! ### The canonical linkage -/

/-- The **canonical one-stem linkage**: a total, univalent, lexeme-blind stem
selection with the identity property mapping — the graph of [stump-2006]'s
universal default rule of paradigm linkage. -/
def canonical (st : L → Z) : Linkage L Z P where
  stems := fun l _ => {st l}
  pm := fun _ σ => σ

@[simp] theorem canonical_stems (st : L → Z) (l : L) (σ : P) :
    (canonical (P := P) st).stems l σ = {st l} := rfl

@[simp] theorem canonical_pm (st : L → Z) (l : L) (σ : P) :
    (canonical (P := P) st).pm l σ = σ := rfl

@[simp] theorem canonical_corr (st : L → Z) (l : L) (σ : P) :
    (canonical (P := P) st).corr l σ = {(st l, σ)} :=
  Finset.singleton_product_singleton

@[simp] theorem canonical_realize [DecidableEq W] (st : L → Z)
    (realizeForm : Z → P → W) (l : L) (σ : P) :
    (canonical (P := P) st).realize realizeForm l σ
      = {(realizeForm (st l) σ, σ)} := by
  simp [realize]

/-- The canonical linkage is canonical on all five axes. -/
theorem canonical_isCanonical (st : L → Z) :
    (canonical (P := P) st).IsCanonical where
  total := fun l _ => ⟨st l, Finset.mem_singleton_self _⟩
  univalent := fun _ _ => (Finset.card_singleton _).le
  stemInvariant := fun l _ _ _ _ h₁ h₂ =>
    (Finset.mem_singleton.mp h₁).trans (Finset.mem_singleton.mp h₂).symm
  injective := fun l _ _ hne => by
    simpa [canonical_corr, Finset.disjoint_singleton] using hne
  propertyPreserving := fun _ _ => rfl

/-! ### The realization view -/

/-- The stem selection as a realization: lexemes as indices, property sets
as contexts, stems as forms. A lossless embedding — the linkage adds only
the property mapping `pm` on top of it. -/
def toRealization (ℓ : Linkage L Z P) : Realization L P Z := ⟨ℓ.stems⟩

@[simp] theorem toRealization_realize (ℓ : Linkage L Z P) (l : L) (σ : P) :
    ℓ.toRealization.realize l σ = ℓ.stems l σ := rfl

/-- The linkage and its realization agree on univalence. -/
theorem toRealization_isUnivalent_iff (ℓ : Linkage L Z P) :
    ℓ.toRealization.IsUnivalent ↔ ℓ.IsUnivalent := Iff.rfl

end Linkage

end Morphology
