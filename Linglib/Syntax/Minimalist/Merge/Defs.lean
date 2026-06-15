import Linglib.Syntax.Minimalist.Basic
import Linglib.Syntax.Minimalist.HeadFunction
import Linglib.Core.Combinatorics.RootedTree.Nonplanar

/-!
# Carrier projection `toHc`: Linguistic Specialization
[marcolli-chomsky-berwick-2025]

Specialization of the canonical Connes-Kreimer substrate to the Minimalism
instantiation with leaf alphabet `LIToken ⊕ Unit`: the projection of a plain
`SyntacticObject` into the bialgebra carrier `RootedTree.Nonplanar (LIToken ⊕
Unit)` (lexical leaves `Sum.inl`, trace leaves `Sum.inr ()`). The Merge
operators on `ConnesKreimer R (Nonplanar α)` live in `Merge/Basic.lean`.

`SyntacticObject.toHc` and `HeadFunction.toHcWith` perform the projection. Since
`Nonplanar` nodes carry a label, each internal node is decorated with its **head
leaf** (`headLeafPlanar`, MCB Lemma 1.13.5) under the chosen side convention;
this labeling convention is validated in `Merge.External`'s `matches_Step`
bridges, which apply `mergeOp` with that same head label.
-/

namespace Minimalist

open RootedTree

/-- Head leaf of a planar representative under a side convention
    (MCB Lemma 1.13.5): leftmost leaf for `.initial`, rightmost for `.final`.
    Used to label internal `Nonplanar` nodes in `toHcPlanarN`. -/
def headLeafPlanar : ConventionDir → FreeMagma (LIToken ⊕ Nat) → LIToken
  | .initial, t => leftmostLeafPlanar t
  | .final,   t => rightmostLeafPlanar t

/-- Underlying `FreeMagma`-side toHc on a planar representative, into the
    canonical nonplanar carrier. Lexical leaves go to `Sum.inl`, trace leaves
    to `Sum.inr ()`; each internal node is labeled with its head leaf
    (`headLeafPlanar side`) since `Nonplanar.node` requires a label.

    `noncomputable` because `Nonplanar.node` is a noncomputable smart
    constructor. Public so `HeadFunction.toHcWith` can compose it with a
    chosen section. -/
noncomputable def toHcPlanarN (side : ConventionDir) :
    FreeMagma (LIToken ⊕ Nat) → Nonplanar (LIToken ⊕ Unit)
  | .of (.inl tok) => Nonplanar.leaf (Sum.inl tok)
  | .of (.inr _)   => Nonplanar.leaf (Sum.inr ())
  | .mul l r       => Nonplanar.node (Sum.inl (headLeafPlanar side (.mul l r)))
                        {toHcPlanarN side l, toHcPlanarN side r}

/-- Project a `SyntacticObject` directly to the bialgebra carrier
    `Nonplanar (LIToken ⊕ Unit)`.

    Since `SyntacticObject := FreeCommMagma (LIToken ⊕ Nat)`, this picks a
    representative via `Quot.out` and projects under the head-initial
    convention. Noncomputable; the parameterized `HeadFunction.toHcWith`
    takes an explicit section + side. -/
noncomputable def SyntacticObject.toHc (so : SyntacticObject) :
    Nonplanar (LIToken ⊕ Unit) :=
  toHcPlanarN .initial so.out

/-- Parameterized projection: `toHc` under head function `h`, using
    `h.section_.σ` to pick the planar representative and `h.headSide` for
    the node-labeling convention. -/
noncomputable def HeadFunction.toHcWith (h : HeadFunction) (so : SyntacticObject) :
    Nonplanar (LIToken ⊕ Unit) :=
  toHcPlanarN h.headSide (h.section_.σ so)

/-! ### Singleton-class simp lemmas

`toHc_leaf` / `toHc_trace` are recoverable as `simp` lemmas because
leaf-only equivalence classes under `FreeMagma.CommRel` are singletons
(no `swap` constructor fires on `.of _`). The proof routes through
`Quot.out_eq` + `mk_eq_iff_commEqv` + the singleton structure of `.of`.

`toHc_mul` does NOT recover at this level: `(l * r).out` may pick
either `mul l.out r.out` or `mul r.out l.out`, and `Nonplanar.node`'s
head label depends on which planar representative is chosen. The
`HeadFunction`-parameterized `toHcWith` canonicalizes the orientation. -/

@[simp] theorem SyntacticObject.toHc_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).toHc = Nonplanar.leaf (Sum.inl tok) := by
  show toHcPlanarN .initial (SyntacticObject.leaf tok).out = _
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.leaf tok).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inl tok)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.leaf tok).out with
  | .of x =>
    rw [h] at hmk
    show toHcPlanarN .initial (.of x) = _
    cases x with
    | inl t =>
      simp only [toHcPlanarN]
      exact congrArg (fun tk => Nonplanar.leaf (Sum.inl tk))
        (Sum.inl.inj (hmk : Sum.inl t = Sum.inl tok))
    | inr n => exact absurd (hmk : Sum.inr n = Sum.inl tok) (by intro; contradiction)
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

@[simp] theorem SyntacticObject.toHc_trace (n : Nat) :
    (SyntacticObject.trace n).toHc = Nonplanar.leaf (Sum.inr ()) := by
  show toHcPlanarN .initial (SyntacticObject.trace n).out = _
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.trace n).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inr n)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.trace n).out with
  | .of x =>
    rw [h] at hmk
    show toHcPlanarN .initial (.of x) = _
    cases x with
    | inl t => exact absurd (hmk : Sum.inl t = Sum.inr n) (by intro; contradiction)
    | inr m => simp only [toHcPlanarN]
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

/-! ### Singleton-class simp lemmas for `toHcWith`/`toHWith` (parameterized)

All three lemmas reduce via the keystone `FreeCommMagma.Section.σ_of` helper:
the section's image of `FreeCommMagma.of x` is exactly `FreeMagma.of x`. -/

/-- `toHcWith h` on a leaf returns the corresponding `Nonplanar.leaf`. -/
@[simp] theorem HeadFunction.toHcWith_leaf (h : HeadFunction) (tok : LIToken) :
    h.toHcWith (.leaf tok) = Nonplanar.leaf (Sum.inl tok) := by
  show toHcPlanarN h.headSide (h.section_.σ (FreeCommMagma.of (.inl tok))) = _
  rw [h.section_.σ_of]
  cases h.headSide <;> rfl

/-- `toHcWith h` on a trace returns `Nonplanar.leaf (Sum.inr ())`. -/
@[simp] theorem HeadFunction.toHcWith_trace (h : HeadFunction) (n : Nat) :
    h.toHcWith (.trace n) = Nonplanar.leaf (Sum.inr ()) := by
  show toHcPlanarN h.headSide (h.section_.σ (FreeCommMagma.of (.inr n))) = _
  rw [h.section_.σ_of]
  cases h.headSide <;> rfl

end Minimalist

/-- `mkTrace n = .trace n`, so `isTrace (.trace n) = some n`. -/
theorem Minimalist.isTrace_mkTrace (n : Nat) :
    Minimalist.isTrace (Minimalist.mkTrace n) = some n := rfl

/-- `(mkTrace n).toHc = Nonplanar.leaf (Sum.inr ())` — the IM bridge identity. -/
theorem Minimalist.mkTrace_toHc (n : Nat) :
    (Minimalist.mkTrace n).toHc = RootedTree.Nonplanar.leaf (Sum.inr ()) :=
  Minimalist.SyntacticObject.toHc_trace n
