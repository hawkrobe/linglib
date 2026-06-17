import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# The Ginsberg–Fitting bilattice product (twist structure)
[avron-1996] [arieli-avron-1996]

A *bilattice* carries two lattice orders on one carrier — a *truth* order `≤_t`
and a *knowledge/information* order `≤_k` — with the four operations monotone
w.r.t. *both* (an *interlaced* bilattice, [avron-1996] Def 2.1). The fundamental
construction is the **twist product** (Ginsberg–Fitting product) `L ⊙ R` of two
bounded lattices ([avron-1996] Def 2.4): the carrier is `L × R`, where a value
`(a, b)` records evidence *for* (`a ∈ L`) and *against* (`b ∈ R`).

* the **knowledge** order `≤_k` is the product order on `L × R` (more evidence
  both ways) — i.e. mathlib's `Prod` lattice, with `⊗ = ⊓`, `⊕ = ⊔`;
* the **truth** order `≤_t` dualizes the second factor (more for, less against);
  its operations `∧`/`∨` are `tInf`/`tSup`.

Following the project's plain-`Prop` convention (and avoiding the `Prod`-instance
clash of putting two `Lattice`s on one type), the knowledge structure *is*
mathlib's `Prod` lattice (`≤`, `⊓`, `⊔`), while the truth structure is the named
relations/operations `tLE`, `tInf`, `tSup`.

This file proves the **constructive half** of the structure theory ([avron-1996]
Thm 2.5): the twist product is an interlaced bilattice — the truth relations form
a lattice, and all four operations are interlaced.

`Evidential S` (`Core.Logic.Bilattice`) is the diagonal case `S ⊙ S`; `FOUR =
Bool ⊙ Bool`, `PRESUP = Fin 3 ⊙ Fin 3`.

## Main results

* `Bilattice.TwistProduct.tLE`/`tInf`/`tSup` — the truth order, meet `∧`, join `∨`
* `tInf_isGLB`-style lemmas (`tInf_tLE_left`, `le_tInf`, …) — the truth lattice
* `tInf_kmono`/`tSup_kmono`/`kInf_tmono`/`kSup_tmono` — the four interlacing laws
  (truth ops are `≤_k`-monotone; knowledge ops `⊓`/`⊔` are `≤_t`-monotone)
* `neg`, `neg_neg`, `neg_tLE`, `neg_kLE` — Ginsberg negation on the diagonal `L ⊙ L`

## TODO

The **representation theorem** ([avron-1996] Thm 4.3), the converse of Thm 2.5:
every interlaced bilattice `B` is isomorphic to `L_B ⊙ R_B` for bounded lattices
`L_B = {x | ⊥ ≤_t x}`, `R_B = {x | x ≤_t ⊥}`, via `g x = (x ∨ ⊥, x ∧ ⊥)` with
inverse `(a, b) ↦ a ⊕ b`; `L_B`, `R_B` are unique up to isomorphism, and with a
negation `L_B ≅ R_B`. This needs an abstract `InterlacedBilattice` class and the
interlacing-algebra chain (Avron Prop 3.2 → Cor 3.8 → Thm 4.3); it is the theorem
that earns the abstract class.
-/

universe u v

variable {L : Type u} {R : Type v}

namespace Bilattice.TwistProduct

section Lattice

variable [Lattice L] [Lattice R]

/-- Truth order `≤_t` on `L × R`: more evidence-for, less evidence-against
([avron-1996] Def 2.4(ii)). The knowledge order `≤_k` is the `Prod` order `≤`. -/
def tLE (x y : L × R) : Prop := x.1 ≤ y.1 ∧ y.2 ≤ x.2

/-- Truth meet `∧`: meet the evidence-for, join the evidence-against
([avron-1996] Def 2.4(iv)). The knowledge meet `⊗` is the `Prod` meet `⊓`. -/
def tInf (x y : L × R) : L × R := (x.1 ⊓ y.1, x.2 ⊔ y.2)

/-- Truth join `∨`: join the evidence-for, meet the evidence-against
([avron-1996] Def 2.4(iii)). The knowledge join `⊕` is the `Prod` join `⊔`. -/
def tSup (x y : L × R) : L × R := (x.1 ⊔ y.1, x.2 ⊓ y.2)

@[refl] theorem tLE_refl (x : L × R) : tLE x x := ⟨le_rfl, le_rfl⟩

theorem tLE_trans {x y z : L × R} (h₁ : tLE x y) (h₂ : tLE y z) : tLE x z :=
  ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩

theorem tLE_antisymm {x y : L × R} (h₁ : tLE x y) (h₂ : tLE y x) : x = y :=
  Prod.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₂.2 h₁.2)

/-! ### The truth order is a lattice -/

theorem tInf_tLE_left (x y : L × R) : tLE (tInf x y) x := ⟨inf_le_left, le_sup_left⟩
theorem tInf_tLE_right (x y : L × R) : tLE (tInf x y) y := ⟨inf_le_right, le_sup_right⟩
theorem tLE_tInf {x y z : L × R} (h₁ : tLE z x) (h₂ : tLE z y) : tLE z (tInf x y) :=
  ⟨le_inf h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩

theorem tLE_tSup_left (x y : L × R) : tLE x (tSup x y) := ⟨le_sup_left, inf_le_left⟩
theorem tLE_tSup_right (x y : L × R) : tLE y (tSup x y) := ⟨le_sup_right, inf_le_right⟩
theorem tSup_tLE {x y z : L × R} (h₁ : tLE x z) (h₂ : tLE y z) : tLE (tSup x y) z :=
  ⟨sup_le h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩

end Lattice

/-! ### Interlacing

The four operations are monotone w.r.t. *both* orders ([avron-1996] Def 2.1(3)).
The knowledge structure is mathlib's `Prod` lattice (`≤`, `⊓`, `⊔`); the truth
operations are `tInf`/`tSup`. -/

section Interlaced

variable [Lattice L] [Lattice R]

/-- **Interlacing 1**: the truth meet `∧` is `≤_k`-monotone. -/
theorem tInf_kmono {x y : L × R} (z : L × R) (h : x ≤ y) : tInf x z ≤ tInf y z :=
  ⟨inf_le_inf h.1 le_rfl, sup_le_sup h.2 le_rfl⟩

/-- **Interlacing 2**: the truth join `∨` is `≤_k`-monotone. -/
theorem tSup_kmono {x y : L × R} (z : L × R) (h : x ≤ y) : tSup x z ≤ tSup y z :=
  ⟨sup_le_sup h.1 le_rfl, inf_le_inf h.2 le_rfl⟩

/-- **Interlacing 3**: the knowledge meet `⊗ = ⊓` is `≤_t`-monotone. -/
theorem kInf_tmono {x y : L × R} (z : L × R) (h : tLE x y) : tLE (x ⊓ z) (y ⊓ z) :=
  ⟨inf_le_inf h.1 le_rfl, inf_le_inf h.2 le_rfl⟩

/-- **Interlacing 4**: the knowledge join `⊕ = ⊔` is `≤_t`-monotone. -/
theorem kSup_tmono {x y : L × R} (z : L × R) (h : tLE x y) : tLE (x ⊔ z) (y ⊔ z) :=
  ⟨sup_le_sup h.1 le_rfl, sup_le_sup h.2 le_rfl⟩

end Interlaced

/-! ### Bounds

With bounded factors the twist product has four extremes ([avron-1996]
Def 2.4(vii)): truth bounds `t = (⊤, ⊥)`, `f = (⊥, ⊤)`, and knowledge bounds
`⊤ = (⊤, ⊤)`, `⊥ = (⊥, ⊥)` (the latter are the `Prod` `BoundedOrder`). -/

section Bounds

variable [Lattice L] [Lattice R] [BoundedOrder L] [BoundedOrder R]

/-- Truth top `t = (⊤, ⊥)` (maximal for, minimal against). -/
def tTop : L × R := (⊤, ⊥)
/-- Truth bottom `f = (⊥, ⊤)`. -/
def tBot : L × R := (⊥, ⊤)

theorem tLE_tTop (x : L × R) : tLE x tTop := ⟨le_top, bot_le⟩
theorem tBot_tLE (x : L × R) : tLE tBot x := ⟨bot_le, le_top⟩

end Bounds

/-! ### Negation

On the diagonal `L ⊙ L`, Ginsberg's negation swaps the coordinates: it reverses
`≤_t`, preserves `≤_k`, and is an involution ([avron-1996] Thm 2.5(2)). -/

section Negation

/-- Ginsberg negation on `L ⊙ L`: swap evidence for/against. -/
def neg (x : L × L) : L × L := (x.2, x.1)

@[simp] theorem neg_neg (x : L × L) : neg (neg x) = x := rfl

variable [Lattice L]

/-- Negation reverses the truth order ([avron-1996] Def 2.3(ii)). -/
theorem neg_tLE {x y : L × L} (h : tLE x y) : tLE (neg y) (neg x) := ⟨h.2, h.1⟩

/-- Negation preserves the knowledge order ([avron-1996] Def 2.3(iii)). -/
theorem neg_kLE {x y : L × L} (h : x ≤ y) : neg x ≤ neg y := ⟨h.2, h.1⟩

end Negation

end Bilattice.TwistProduct
