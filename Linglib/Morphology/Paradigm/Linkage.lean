import Mathlib.Logic.Function.Basic

/-!
# Paradigm linkage: content paradigms, form paradigms, and correspondence
[stump-2016]

The paradigm-linkage hypothesis ([stump-2016] Ch. 7) splits a lexeme's
realizations into three corresponding paradigms:

* the **content paradigm** — cells `⟨L, σ⟩` pairing a lexeme `L` with a
  morphosyntactic property set `σ`; the interface with syntax and semantics;
* the **form paradigm** — cells `⟨Z, τ⟩` pairing a stem `Z` from `L`'s stem
  set with a property set `τ` for which `Z` inflects; the basis for inflection;
* the **realized paradigm** — cells `⟨w, τ⟩` pairing a word form `w` with the
  property set it realizes.

Each content cell is realized by being linked to a **form correspondent** — a
form cell whose realization it shares. The correspondence function `Corr`
decomposes (§7.2) as a **stem selection** and a **property mapping** `pm`:
`Corr(⟨L, σ⟩) = ⟨Stem(⟨L, σ⟩), pm(σ)⟩`, and the paradigm function factors as
`PF(⟨L, σ⟩) = PF(Corr(⟨L, σ⟩))`. Canonically `pm` is the identity and each
lexeme has a single stem, so content and form paradigms are isomorphic; the
book's later chapters catalogue the deviation modes — morphomic properties
(Ch. 8), defectiveness/overabundance (Ch. 9), syncretism as many-to-one `Corr`
(Ch. 10), suppletion/heteroclisis (Ch. 11), deponency as a voice-flipping `pm`
(Ch. 12, formalized in `Studies/Stump2016.lean`), and polyfunctionality
(Ch. 13).

## Main declarations

* `Linkage L Z P` — a lexeme-level linkage: stem selection `Stem` plus
  property mapping `pm`
* `Linkage.corr` — the form-correspondence function `Corr = ⟨Stem, pm⟩`
* `Linkage.realize` — the realized paradigm `PF(⟨L, σ⟩) = PF(Corr(⟨L, σ⟩))`
* `Linkage.IsCanonical` — cell-level canonical linkage: property-set
  preservation (`pm = id`, §7.1 (2a)) and stem invariance (§7.1 (2b))
* `Linkage.canonical` / `canonical_isCanonical` — the canonical one-stem linkage
* `Linkage.realize_eq_of_corr_eq` — a many-to-one `Corr` forces content-side
  syncretism (the Ch. 10 deviation mode)
-/

namespace Morphology

/-- A **paradigm linkage** ([stump-2016] §7.2), presented from the vantage of a
single lexeme: the two components of the form-correspondence function `Corr`.
`stem` is the stem selection `Stem(⟨L, σ⟩)` picking the stem that realizes a
content cell; `pm` is the property mapping `σ ↦ τ`. Canonically `pm` is the
identity and `stem` is constant in the property set (one stem per lexeme). -/
structure Linkage (L Z P : Type*) where
  /-- Stem selection `Stem(⟨L, σ⟩)`: the stem realizing the content cell. -/
  stem : L → P → Z
  /-- The property mapping `pm : σ ↦ τ` carrying a content cell's property set
  to its form correspondent's. -/
  pm : P → P

namespace Linkage

variable {L Z P W : Type*} (ℓ : Linkage L Z P)

/-- The **form-correspondence function** `Corr(⟨L, σ⟩) = ⟨Stem(⟨L, σ⟩), pm(σ)⟩`
([stump-2016] §7.2): the form cell realizing content cell `⟨l, σ⟩`. -/
def corr (l : L) (σ : P) : Z × P := (ℓ.stem l σ, ℓ.pm σ)

/-- The **realized paradigm** on content cells: `PF(⟨L, σ⟩) = PF(Corr(⟨L, σ⟩))`.
Given the form-cell realization `realizeForm` (the rules of exponence, `PF` on
form cells), the content cell `⟨l, σ⟩` realizes as `⟨w, τ⟩` where `⟨Z, τ⟩` is
its form correspondent and `w` is `Z`'s realization at `τ`. -/
def realize (realizeForm : Z → P → W) (l : L) (σ : P) : W × P :=
  (realizeForm (ℓ.corr l σ).1 (ℓ.corr l σ).2, (ℓ.corr l σ).2)

/-- **Property-set preservation** ([stump-2016] §7.1, canonical characteristic
(2a)): the property mapping is the identity, so a content cell and its form
correspondent share a property set. -/
def IsPropertyPreserving : Prop := ∀ σ, ℓ.pm σ = σ

/-- **Stem invariance** ([stump-2016] §7.1, canonical characteristic (2b)): each
lexeme has a single stem realizing all of its cells. -/
def IsStemInvariant : Prop := ∀ l, ∃ z, ∀ σ, ℓ.stem l σ = z

/-- **Canonical paradigm linkage** at the cell level ([stump-2016] §7.1):
property-set preservation together with stem invariance. The remaining
canonical characteristics — unambiguity and isomorphism within/across syntactic
categories (2c–e) — quantify over sets of paradigms, not a single linkage. -/
def IsCanonical : Prop := ℓ.IsPropertyPreserving ∧ ℓ.IsStemInvariant

/-- Under property-set preservation, each content cell's form correspondent
carries the content cell's own property set — the canonical, mismatch-free
alignment of content and form. -/
theorem corr_snd_eq_of_propertyPreserving (h : ℓ.IsPropertyPreserving)
    (l : L) (σ : P) : (ℓ.corr l σ).2 = σ := h σ

/-- **A many-to-one `Corr` forces content-side syncretism**: content cells with
a common form correspondent share their realization ([stump-2016] Ch. 10's
syncretism deviation mode). -/
theorem realize_eq_of_corr_eq (realizeForm : Z → P → W) {l : L} {σ₁ σ₂ : P}
    (h : ℓ.corr l σ₁ = ℓ.corr l σ₂) :
    ℓ.realize realizeForm l σ₁ = ℓ.realize realizeForm l σ₂ := by
  simp only [realize, h]

/-- The **canonical one-stem linkage**: the identity property mapping together
with a designated stem `st l` for each lexeme. -/
def canonical (st : L → Z) : Linkage L Z P where
  stem := fun l _ => st l
  pm := id

@[simp] theorem canonical_pm (st : L → Z) (σ : P) :
    (canonical (P := P) st).pm σ = σ := rfl

theorem canonical_isCanonical (st : L → Z) :
    (canonical (P := P) st).IsCanonical :=
  ⟨fun _ => rfl, fun l => ⟨st l, fun _ => rfl⟩⟩

end Linkage

end Morphology
