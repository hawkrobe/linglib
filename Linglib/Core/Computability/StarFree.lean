/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Variety.Langs

/-!
# Star-free languages

A language is **star-free** when it is regular with an aperiodic syntactic monoid
([schutzenberger-1965]) — the algebraic characterization of the star-free regular expressions
(built from finite sets by `∪`, `·`, complement, *no* Kleene star), equivalently the counter-free /
`FO[<]`-definable stringsets ([mcnaughton-papert-1971]). Taking the syntactic-monoid
characterization as the definition mirrors the project's treatment of regularity
(`Language.isRegular_iff_finite_syntacticMonoid`).

Star-free is the `V = Monoid.aperiodicVariety` instance of the Eilenberg correspondence: it is
defined as `aperiodicVariety.langs`, so its closure properties are corollaries of the general
keystone (`Monoid.Pseudovariety.langs_*`) rather than hand-written syntactic-monoid arguments.

## Main definitions

* `Language.IsStarFree` — `Monoid.aperiodicVariety.langs`; equivalently regular with an aperiodic
  syntactic monoid (`isStarFree_iff`).

## Main results

* `Language.IsStarFree.compl` / `.inter` / `.union` — boolean closure.
* `Language.IsStarFree.of_recognizes` — recognized by a finite aperiodic monoid ⟹ star-free.
* `Language.IsStarFree.comap` — closure under inverse homomorphism.
-/

namespace Language

variable {α : Type*} {L : Language α}

/-- A language is **star-free** ([schutzenberger-1965]): the `Monoid.aperiodicVariety` instance of
`Monoid.Pseudovariety.langs` — regular with an aperiodic syntactic monoid (`isStarFree_iff`).
Star-free = `FO[<]`-definable = counter-free ([mcnaughton-papert-1971]). -/
def IsStarFree (L : Language α) : Prop := Monoid.aperiodicVariety.langs L

/-- Star-free unfolds to: regular with an aperiodic syntactic monoid. -/
theorem isStarFree_iff : L.IsStarFree ↔ L.IsRegular ∧ Monoid.IsAperiodic L.syntacticMonoid :=
  Iff.rfl

theorem IsStarFree.isRegular (h : L.IsStarFree) : L.IsRegular := h.1

theorem IsStarFree.isAperiodic (h : L.IsStarFree) :
    Monoid.IsAperiodic L.syntacticMonoid := h.2

/-- **Star-free languages are closed under complement.** -/
theorem IsStarFree.compl (h : L.IsStarFree) : Lᶜ.IsStarFree :=
  Monoid.aperiodicVariety.langs_compl h

/-- **Star-free languages are closed under intersection.** -/
theorem IsStarFree.inter {M : Language α} (hL : L.IsStarFree) (hM : M.IsStarFree) :
    (L ⊓ M).IsStarFree :=
  Monoid.aperiodicVariety.langs_inf hL hM

/-- **Star-free languages are closed under union.** -/
theorem IsStarFree.union {M : Language α} (hL : L.IsStarFree) (hM : M.IsStarFree) :
    (L ⊔ M).IsStarFree :=
  Monoid.aperiodicVariety.langs_sup hL hM

/-- **A language recognized by a finite aperiodic monoid is star-free** — the algebraic
characterization of star-free ([schutzenberger-1965]). The engine for placing a constraint class
inside `SF`: exhibit a finite aperiodic recognizer. Stays universe-polymorphic in the recognizer
`M` (the keystone `Monoid.Pseudovariety.langs_of_recognizes` is its fixed-universe form). -/
theorem IsStarFree.of_recognizes {M : Type*} [Monoid M] [Finite M]
    (hM : Monoid.IsAperiodic M) (η : FreeMonoid α →* M) (P : Set M)
    (hL : ∀ w : List α, w ∈ L ↔ η (FreeMonoid.ofList w) ∈ P) : L.IsStarFree := by
  have hle : Con.ker η ≤ L.syntacticCon :=
    ker_le_syntacticCon_of_recognizes ⟨P, Set.ext hL⟩
  have hker : Monoid.IsAperiodic (Con.ker η).Quotient :=
    (hM.of_injective (MonoidHom.mrange η).subtype_injective).of_mulEquiv
      (Con.quotientKerEquivRange η).symm
  have hfin : Finite (Con.ker η).Quotient :=
    Finite.of_equiv _ (Con.quotientKerEquivRange η).symm.toEquiv
  have hsurj : Function.Surjective (Con.map (Con.ker η) L.syntacticCon hle) :=
    Con.lift_surjective_of_surjective _ Con.mk'_surjective
  exact ⟨isRegular_of_finite_syntacticMonoid (Finite.of_surjective _ hsurj),
    hker.of_surjective hsurj⟩

/-- **Star-free languages are closed under inverse homomorphism.** The engine for transferring a
star-free upper bound across a string-rewriting projection (e.g. tier erasure: `TSL ⊆ SF`). -/
theorem IsStarFree.comap {α β : Type*} {L : Language β} (h : L.IsStarFree)
    (φ : FreeMonoid α →* FreeMonoid β) :
    Language.IsStarFree {w : List α | φ (FreeMonoid.ofList w) ∈ L} := by
  have : Finite L.syntacticMonoid := finite_syntacticMonoid h.1
  refine IsStarFree.of_recognizes (M := L.syntacticMonoid) h.2 (L.toSyntacticMonoid.comp φ)
    {m | ∃ u : FreeMonoid β, L.toSyntacticMonoid u = m ∧ u ∈ L} fun w => ?_
  refine ⟨fun hw => ⟨φ (FreeMonoid.ofList w), rfl, hw⟩, fun ⟨u, hu, hmem⟩ => ?_⟩
  exact (mem_iff_of_syntacticCon ((toSyntacticMonoid_eq_iff (L := L)).mp hu)).mp hmem

/-- **The full language is star-free** — recognized by the trivial monoid. -/
theorem isStarFree_univ : IsStarFree (Set.univ : Language α) :=
  Monoid.aperiodicVariety.langs_univ

end Language
