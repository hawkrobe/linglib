import Linglib.Semantics.Composition.Reduction

/-!
# Syllogistic forms as composition-engine trees

The A/I/E/O forms as QR'd Heim-Kratzer trees over the default logical
vocabulary, with the first-figure syllogisms (Barbara, Celarent, Darii,
Ferio) as **cross-model tree entailments**: each is a one-line instance of
`holdsAt_of_models` — the first-order consequence is stated once, and the
engine-level entailment over every composition model, world, and assignment
follows through the agreement theorem. Complements `Forms.lean`'s
Venn-state semantics (grounded in the same `every_sem`/`some_sem`/`no_sem`
denotations via `Model.lexiconFO`).
-/

namespace Quantification.Syllogistic

open FirstOrder Language
open FirstOrder.Language.Formula (all₁ ex₁ realize_all₁ realize_ex₁)
open Semantics.Composition
open Syntax (Tree)

universe u v

/-! ### The four forms as trees -/

/-- A-form: "every x y" after QR. -/
def aTree (x y : String) : Tree Unit String :=
  .bin (.bin (.leaf "every") (.leaf x)) (.binder 1 (.bin (.tr 1) (.leaf y)))

/-- I-form: "some x y" after QR. -/
def iTree (x y : String) : Tree Unit String :=
  .bin (.bin (.leaf "some") (.leaf x)) (.binder 1 (.bin (.tr 1) (.leaf y)))

/-- E-form: "no x y" after QR. -/
def eTree (x y : String) : Tree Unit String :=
  .bin (.bin (.leaf "no") (.leaf x)) (.binder 1 (.bin (.tr 1) (.leaf y)))

/-- O-form: "not every x y" (the modern reading's `¬A`). -/
def oTree (x y : String) : Tree Unit String :=
  .bin (.leaf "not") (aTree x y)

/-- Premise pair: "p₁ and p₂". -/
def andTree (p₁ p₂ : Tree Unit String) : Tree Unit String :=
  .bin p₁ (.bin (.leaf "and") p₂)

section Compile

variable {L : Language.{u, v}} {nm : LexNaming L} {x y : String}
  {X Y : L.Relations 1}

private theorem compile_aTree (hx : nm.preds₁ x = some X)
    (hy : nm.preds₁ y = some Y) :
    compileFO {} nm (aTree x y)
      = some (all₁ 1 ((X.formula₁ (Term.var 1)).imp
          (Y.formula₁ (Term.var 1)))) := by
  simp [aTree, compileFO, compilePred, hx, hy]

private theorem compile_iTree (hx : nm.preds₁ x = some X)
    (hy : nm.preds₁ y = some Y) :
    compileFO {} nm (iTree x y)
      = some (ex₁ 1 (X.formula₁ (Term.var 1) ⊓ Y.formula₁ (Term.var 1))) := by
  simp [iTree, compileFO, compilePred, hx, hy]

private theorem compile_eTree (hx : nm.preds₁ x = some X)
    (hy : nm.preds₁ y = some Y) :
    compileFO {} nm (eTree x y)
      = some (all₁ 1 ((X.formula₁ (Term.var 1)).imp
          (Y.formula₁ (Term.var 1)).not)) := by
  simp [eTree, compileFO, compilePred, hx, hy]

private theorem compile_oTree (hx : nm.preds₁ x = some X)
    (hy : nm.preds₁ y = some Y) :
    compileFO {} nm (oTree x y)
      = some (BoundedFormula.not (all₁ 1 ((X.formula₁ (Term.var 1)).imp
          (Y.formula₁ (Term.var 1))))) := by
  simp [oTree, compileFO, compile_aTree hx hy]

private theorem compile_andTree {c₁ : Unit} {ch₁ : List (Tree Unit String)}
    {t₂ : Tree Unit String} {φ₁ φ₂ : L.Formula ℕ}
    (h₁ : compileFO {} nm (.node c₁ ch₁) = some φ₁)
    (h₂ : compileFO {} nm t₂ = some φ₂) :
    compileFO {} nm (andTree (.node c₁ ch₁) t₂) = some (φ₁ ⊓ φ₂) := by
  simp [andTree, compileFO, h₁, h₂]

end Compile

/-! ### First-figure syllogisms as cross-model tree entailments

Each is `holdsAt_of_models` applied to the compiled premises and a
three-line first-order argument: state the consequence once over `Realize`,
and the entailment between the *trees* holds in every composition model,
world, and assignment. -/

section Syllogisms

variable {L : Language.{u, v}} {nm : LexNaming L}
  (hfr : FOWords.FreshFor {} nm) (hdj : nm.Disjoint)
  {x y z : String} {X Y Z : L.Relations 1}
  (hx : nm.preds₁ x = some X) (hy : nm.preds₁ y = some Y)
  (hz : nm.preds₁ z = some Z)
  (m : Model L) (w : m.W) (g : Core.Assignment m.E)

include hfr hdj hx hy hz

/-- **Barbara** (AAA-1): "every y z and every x y" entails "every x z". -/
theorem barbara :
    HoldsAt m (m.lexiconFO {} nm w) g (andTree (aTree y z) (aTree x y)) →
      HoldsAt m (m.lexiconFO {} nm w) g (aTree x z) :=
  holdsAt_of_models m {} nm w FOWords.nodup_default hfr hdj
    (compile_andTree (compile_aTree hy hz) (compile_aTree hx hy))
    (compile_aTree hx hz)
    (fun M S v h => by
      letI := S
      simp only [Formula.realize_inf, realize_all₁, Formula.realize_imp] at h ⊢
      exact fun a hXa => h.1 a (h.2 a hXa)) g

/-- **Celarent** (EAE-1): "no y z and every x y" entails "no x z". -/
theorem celarent :
    HoldsAt m (m.lexiconFO {} nm w) g (andTree (eTree y z) (aTree x y)) →
      HoldsAt m (m.lexiconFO {} nm w) g (eTree x z) :=
  holdsAt_of_models m {} nm w FOWords.nodup_default hfr hdj
    (compile_andTree (compile_eTree hy hz) (compile_aTree hx hy))
    (compile_eTree hx hz)
    (fun M S v h => by
      letI := S
      simp only [Formula.realize_inf, realize_all₁, Formula.realize_imp,
        Formula.realize_not] at h ⊢
      exact fun a hXa => h.1 a (h.2 a hXa)) g

/-- **Darii** (AII-1): "every y z and some x y" entails "some x z". -/
theorem darii :
    HoldsAt m (m.lexiconFO {} nm w) g (andTree (aTree y z) (iTree x y)) →
      HoldsAt m (m.lexiconFO {} nm w) g (iTree x z) :=
  holdsAt_of_models m {} nm w FOWords.nodup_default hfr hdj
    (compile_andTree (compile_aTree hy hz) (compile_iTree hx hy))
    (compile_iTree hx hz)
    (fun M S v h => by
      letI := S
      simp only [Formula.realize_inf, realize_all₁, realize_ex₁,
        Formula.realize_imp] at h ⊢
      obtain ⟨hYZ, a, hXa, hYa⟩ := h
      exact ⟨a, hXa, hYZ a hYa⟩) g

/-- **Ferio** (EIO-1): "no y z and some x y" entails "not every x z". -/
theorem ferio :
    HoldsAt m (m.lexiconFO {} nm w) g (andTree (eTree y z) (iTree x y)) →
      HoldsAt m (m.lexiconFO {} nm w) g (oTree x z) :=
  holdsAt_of_models m {} nm w FOWords.nodup_default hfr hdj
    (compile_andTree (compile_eTree hy hz) (compile_iTree hx hy))
    (compile_oTree hx hz)
    (fun M S v h => by
      letI := S
      simp only [Formula.realize_inf, realize_all₁, realize_ex₁,
        Formula.realize_imp, Formula.realize_not] at h ⊢
      obtain ⟨hYZ, a, hXa, hYa⟩ := h
      exact fun hall => hYZ a hYa (hall a hXa)) g

end Syllogisms

end Quantification.Syllogistic
