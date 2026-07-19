import Mathlib.Data.Set.Function

/-!
# Paradigm linkage: content paradigms, form paradigms, and correspondence

Inflectional morphology relates three levels of representation ([stump-2012-mmm8];
the book-length apparatus is [stump-2016]): a lexeme's **content paradigm** of
cells `⟨L, σ⟩` pairing a lexeme with a syntacticosemantic property set, a stem's
**form paradigm** of cells `⟨Z, τ⟩` pairing a stem with a property set it inflects
for, and the **realized paradigm** of word forms. A content cell is realized by
being linked to a **form correspondent**, whose realization it shares. The
correspondence factors into a stem selection `stem : L → P → Option Z` and a
lexeme-sensitive property mapping `pm : L → P → P`. Both partiality and lexeme
sensitivity are load-bearing: a gap in the stem specification is the seat of
defectiveness, and functor-argument reversal computes a form correspondent's
property set from the lexeme.

Canonical paradigm linkage is the typological extreme against which deviations
are calibrated, characterized by four independent axes. `IsTotal`: every content
cell has a form correspondent. `IsStemInvariant`: one stem realizes all of a
lexeme's cells. `IsInjective`: no two content cells share a form correspondent.
`IsPropertyPreserving`: a form correspondent carries the content cell's own
property set. Each named noncanonical phenomenon is the failure of exactly one
axis — defectiveness negates totality, suppletion stem invariance, syncretism
injectivity, and deponency and functor-argument reversal property preservation.

## Main declarations

* `Linkage L Z P` — a lexeme-level linkage: partial stem selection and
  lexeme-sensitive property mapping
* `Linkage.corr`, `Linkage.realize` — the form-correspondence function and the
  realized paradigm, both partial
* `Linkage.IsTotal`, `IsStemInvariant`, `IsInjective`, `IsPropertyPreserving` —
  the four axes of canonical linkage; `IsCanonical` conjoins them
* `Linkage.IsDefective`, `IsSuppletive`, `IsSyncretic`, `IsUnfaithful` — the four
  deviation predicates, each negating one axis (`IsCanonical.not_isDefective`,
  …), with `isSyncretic_iff_not_isInjective`
* `Linkage.IsVirtual` — a form cell no content cell corresponds to
* `Linkage.canonical` / `canonical_isCanonical` — the total, lexeme-blind,
  one-stem linkage, canonical on all four axes
* `Linkage.realize_eq_of_corr_eq` — a shared form correspondent forces a shared
  realization
* `Linkage.realize_eq_of_corr_eq_lexeme` — the cross-lexeme companion: two
  lexemes sharing a correspondent share their realization
-/

namespace Morphology

/-- A **paradigm linkage** ([stump-2012-mmm8]) from the vantage of a single
lexeme: the two components of the form-correspondence function. `stem` selects
the stem realizing a content cell, or `none` where the stem specification has a
gap; `pm` carries a content cell's property set to its form correspondent's, and
may consult the lexeme. Canonically `stem` is total and constant in the property
set and `pm` is the identity. -/
structure Linkage (L Z P : Type*) where
  /-- The stem realizing a content cell `⟨l, σ⟩`, or `none` where the stem
  specification has a gap. -/
  stem : L → P → Option Z
  /-- The property mapping carrying a content cell's property set to its form
  correspondent's, consulting the lexeme for functor-argument reversal. -/
  pm : L → P → P

namespace Linkage

variable {L Z P W : Type*} (ℓ : Linkage L Z P)

/-- The **form correspondent** of a content cell `⟨l, σ⟩`: the stem paired with
its mapped property set, or `none` where the stem specification has a gap. -/
def corr (l : L) (σ : P) : Option (Z × P) := (ℓ.stem l σ).map (·, ℓ.pm l σ)

/-- The **realized paradigm** on content cells: a content cell realizes as its
form correspondent does. `realizeForm` supplies the form-cell realization; the
result is `none` exactly where the form correspondent is. -/
def realize (realizeForm : Z → P → W) (l : L) (σ : P) : Option (W × P) :=
  (ℓ.corr l σ).map fun zτ => (realizeForm zτ.1 zτ.2, zτ.2)

/-- **Totality**: every content cell has a form correspondent. Defectiveness is
the failure. -/
def IsTotal : Prop := ∀ l σ, (ℓ.stem l σ).isSome

/-- **Stem invariance**: a lexeme's cells that have a stem all share one, so its
correspondents come from a single form paradigm. Stem suppletion is the failure.
Independent of totality — undefined cells impose no constraint. -/
def IsStemInvariant : Prop :=
  ∀ l ⦃σ₁ σ₂⦄ ⦃z₁ z₂⦄, ℓ.stem l σ₁ = some z₁ → ℓ.stem l σ₂ = some z₂ → z₁ = z₂

/-- **Injectivity**: no two content cells of a lexeme share a form correspondent,
over the cells that have one. Syncretism is the failure. -/
def IsInjective : Prop := ∀ l, Set.InjOn (ℓ.corr l) {σ | (ℓ.corr l σ).isSome}

/-- **Property preservation**: a form correspondent carries the content cell's
own property set. Deponency, functor-argument reversal, and directional
syncretism are failures. -/
def IsPropertyPreserving : Prop := ∀ l σ, ℓ.pm l σ = σ

/-- **Canonical paradigm linkage** ([stump-2012-mmm8]): all four axes. -/
def IsCanonical : Prop :=
  ℓ.IsTotal ∧ ℓ.IsStemInvariant ∧ ℓ.IsInjective ∧ ℓ.IsPropertyPreserving

/-! ### Deviations from canonical linkage

Each noncanonical phenomenon negates exactly one axis. -/

/-- **Defectiveness**: some content cell lacks a form correspondent
([stump-2012-mmm8] §3.1). Negates totality. -/
def IsDefective : Prop := ∃ l σ, ℓ.stem l σ = none

/-- **Suppletion**: a lexeme's correspondents draw on more than one stem
([stump-2012-mmm8] §3.4). Negates stem invariance. -/
def IsSuppletive : Prop := ¬ ℓ.IsStemInvariant

/-- **Syncretism**: two distinct content cells share a form correspondent
([stump-2012-mmm8] §3.2). Negates injectivity; the `isSome` requirement excludes
cells vacuously agreeing at `none`. -/
def IsSyncretic : Prop :=
  ∃ l σ₁ σ₂, σ₁ ≠ σ₂ ∧ ℓ.corr l σ₁ = ℓ.corr l σ₂ ∧ (ℓ.corr l σ₁).isSome

/-- **Unfaithfulness**: some content cell's form correspondent carries a
different property set — deponency and functor-argument reversal
([stump-2012-mmm8] §3.3). Negates property preservation. -/
def IsUnfaithful : Prop := ∃ l σ, ℓ.pm l σ ≠ σ

theorem IsCanonical.not_isDefective (h : ℓ.IsCanonical) : ¬ ℓ.IsDefective := by
  rintro ⟨l, σ, hnone⟩; simpa [hnone] using h.1 l σ

theorem IsCanonical.not_isSuppletive (h : ℓ.IsCanonical) : ¬ ℓ.IsSuppletive :=
  not_not.mpr h.2.1

theorem IsCanonical.not_isSyncretic (h : ℓ.IsCanonical) : ¬ ℓ.IsSyncretic := by
  rintro ⟨l, σ₁, σ₂, hne, heq, hsome⟩
  have hsome₂ : (ℓ.corr l σ₂).isSome = true := by rw [← heq]; exact hsome
  exact hne (h.2.2.1 l hsome hsome₂ heq)

theorem IsCanonical.not_isUnfaithful (h : ℓ.IsCanonical) : ¬ ℓ.IsUnfaithful := by
  rintro ⟨l, σ, hne⟩; exact hne (h.2.2.2 l σ)

/-- Syncretism is exactly the failure of injectivity — the one deviation whose
predicate is not a definitional negation of its axis. -/
theorem isSyncretic_iff_not_isInjective : ℓ.IsSyncretic ↔ ¬ ℓ.IsInjective := by
  constructor
  · rintro ⟨l, σ₁, σ₂, hne, heq, hsome⟩ hinj
    have hsome₂ : (ℓ.corr l σ₂).isSome = true := by rw [← heq]; exact hsome
    exact hne (hinj l hsome hsome₂ heq)
  · intro h
    simp only [IsInjective, not_forall] at h
    obtain ⟨l, hl⟩ := h
    unfold Set.InjOn at hl
    push Not at hl
    obtain ⟨σ₁, hσ₁, σ₂, hσ₂, heq, hne⟩ := hl
    exact ⟨l, σ₁, σ₂, hne, heq, hσ₁⟩

/-- A **virtual cell**: a form cell no content cell corresponds to
([stump-2012-mmm8] §4). Realization rules still define a value there, which
language change can release by suppressing a linkage override. -/
def IsVirtual (zτ : Z × P) : Prop := ∀ l σ, ℓ.corr l σ ≠ some zτ

/-- A shared form correspondent forces a shared realization ([stump-2012-mmm8]
§3.2): the mechanism of syncretism. -/
theorem realize_eq_of_corr_eq (realizeForm : Z → P → W) {l : L} {σ₁ σ₂ : P}
    (h : ℓ.corr l σ₁ = ℓ.corr l σ₂) :
    ℓ.realize realizeForm l σ₁ = ℓ.realize realizeForm l σ₂ := by
  simp only [realize, h]

/-- A form correspondent shared across two *lexemes* forces a shared realization:
the cross-lexeme companion of `realize_eq_of_corr_eq`. This is the mechanism
behind [jackendoff-audring-2020]'s Same Verb solution — homophones with a shared
morphosyntactic-form pivot inflect alike, however their distinct semantics. -/
theorem realize_eq_of_corr_eq_lexeme (realizeForm : Z → P → W) {l₁ l₂ : L} {σ : P}
    (h : ℓ.corr l₁ σ = ℓ.corr l₂ σ) :
    ℓ.realize realizeForm l₁ σ = ℓ.realize realizeForm l₂ σ := by
  simp only [realize, h]

/-! ### The canonical linkage -/

/-- The **canonical one-stem linkage**: a total, lexeme-blind stem selection with
the identity property mapping. Recovers the pre-deviation content-form
isomorphism. -/
def canonical (st : L → Z) : Linkage L Z P where
  stem := fun l _ => some (st l)
  pm := fun _ σ => σ

@[simp] theorem canonical_stem (st : L → Z) (l : L) (σ : P) :
    (canonical (P := P) st).stem l σ = some (st l) := rfl

@[simp] theorem canonical_pm (st : L → Z) (l : L) (σ : P) :
    (canonical (P := P) st).pm l σ = σ := rfl

@[simp] theorem canonical_corr (st : L → Z) (l : L) (σ : P) :
    (canonical (P := P) st).corr l σ = some (st l, σ) := rfl

@[simp] theorem canonical_realize (st : L → Z) (realizeForm : Z → P → W)
    (l : L) (σ : P) :
    (canonical (P := P) st).realize realizeForm l σ = some (realizeForm (st l) σ, σ) :=
  rfl

@[simp] theorem corr_eq_some {l : L} {σ : P} {zτ : Z × P} :
    ℓ.corr l σ = some zτ ↔ ∃ z, ℓ.stem l σ = some z ∧ (z, ℓ.pm l σ) = zτ := by
  simp [corr]

@[simp] theorem corr_isSome (l : L) (σ : P) :
    (ℓ.corr l σ).isSome = (ℓ.stem l σ).isSome := by
  simp [corr]

/-- The canonical linkage is canonical on all four axes. -/
theorem canonical_isCanonical (st : L → Z) :
    (canonical (P := P) st).IsCanonical :=
  ⟨fun _ _ => rfl,
   fun _ _ _ _ _ h₁ h₂ => (Option.some.inj h₁).symm.trans (Option.some.inj h₂),
   fun _ _ _ _ _ heq => congrArg Prod.snd (Option.some.inj heq),
   fun _ _ => rfl⟩

end Linkage

end Morphology
