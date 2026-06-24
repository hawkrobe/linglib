import Linglib.Syntax.Minimalist.Basic
import Linglib.Syntax.Minimalist.HeadFunction
import Linglib.Core.Combinatorics.RootedTree.Nonplanar

/-!
# Carrier projection `toNonplanar`: Linguistic Specialization
[marcolli-chomsky-berwick-2025]

Specialization of the canonical Connes-Kreimer substrate to the Minimalism
instantiation with leaf alphabet `LIToken ⊕ Unit`: the projection of a plain
`SyntacticObject` into the bialgebra carrier `RootedTree.Nonplanar (LIToken ⊕
Unit)` (lexical leaves `Sum.inl`, trace leaves `Sum.inr ()`). The Merge
operators on `ConnesKreimer R (Nonplanar α)` live in `Merge/Basic.lean`.

`SyntacticObject.toNonplanar` and `HeadFunction.toNonplanarWith` perform the
projection. Since `Nonplanar` nodes carry a label, each internal node is
decorated with its **head
leaf** (`headLeafPlanar`, MCB Lemma 1.13.5) under the chosen side convention;
this labeling convention is validated in `Merge.External`'s `matches_Step`
bridges, which apply `mergeOp` with that same head label.
-/

namespace Minimalist

open RootedTree

/-- Head leaf of a planar representative under a side convention
    (MCB Lemma 1.13.5): leftmost leaf for `.initial`, rightmost for `.final`.
    Used to label internal `Nonplanar` nodes in `planarToNonplanar`. -/
def headLeafPlanar : ConventionDir → FreeMagma (LIToken ⊕ Nat) → LIToken
  | .initial, t => leftmostLeafPlanar t
  | .final,   t => rightmostLeafPlanar t

/-- Underlying `FreeMagma`-side toNonplanar on a planar representative, into the
    canonical nonplanar carrier. Lexical leaves go to `Sum.inl`, trace leaves
    to `Sum.inr ()`; each internal node is labeled with its head leaf
    (`headLeafPlanar side`) since `Nonplanar.node` requires a label.

    `noncomputable` because `Nonplanar.node` is a noncomputable smart
    constructor. Public so `HeadFunction.toNonplanarWith` can compose it with a
    chosen section. -/
noncomputable def planarToNonplanar (side : ConventionDir) :
    FreeMagma (LIToken ⊕ Nat) → Nonplanar (LIToken ⊕ Unit)
  | .of (.inl tok) => Nonplanar.leaf (Sum.inl tok)
  | .of (.inr _)   => Nonplanar.leaf (Sum.inr ())
  | .mul l r       => Nonplanar.node (Sum.inl (headLeafPlanar side (.mul l r)))
                        {planarToNonplanar side l, planarToNonplanar side r}

/-- Project a `SyntacticObject` directly to the bialgebra carrier
    `Nonplanar (LIToken ⊕ Unit)`.

    Since `SyntacticObject := FreeCommMagma (LIToken ⊕ Nat)`, this picks a
    representative via `Quot.out` and projects under the head-initial
    convention. Noncomputable; the parameterized `HeadFunction.toNonplanarWith`
    takes an explicit section + side. -/
noncomputable def SyntacticObject.toNonplanar (so : SyntacticObject) :
    Nonplanar (LIToken ⊕ Unit) :=
  planarToNonplanar .initial so.out

/-- Parameterized projection: `toNonplanar` under head function `h`, using
    `h.section_.σ` to pick the planar representative and `h.headSide` for
    the node-labeling convention. -/
noncomputable def HeadFunction.toNonplanarWith (h : HeadFunction) (so : SyntacticObject) :
    Nonplanar (LIToken ⊕ Unit) :=
  planarToNonplanar h.headSide (h.section_.σ so)

/-! ### Singleton-class simp lemmas

`toNonplanar_leaf` / `toNonplanar_trace` are recoverable as `simp` lemmas because
leaf-only equivalence classes under `FreeMagma.CommRel` are singletons
(no `swap` constructor fires on `.of _`). The proof routes through
`Quot.out_eq` + `mk_eq_iff_commEqv` + the singleton structure of `.of`.

`toNonplanar_mul` does NOT recover at this level: `(l * r).out` may pick
either `mul l.out r.out` or `mul r.out l.out`, and `Nonplanar.node`'s
head label depends on which planar representative is chosen. The
`HeadFunction`-parameterized `toNonplanarWith` canonicalizes the orientation. -/

@[simp] theorem SyntacticObject.toNonplanar_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).toNonplanar = Nonplanar.leaf (Sum.inl tok) := by
  show planarToNonplanar .initial (SyntacticObject.leaf tok).out = _
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.leaf tok).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inl tok)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.leaf tok).out with
  | .of x =>
    rw [h] at hmk
    show planarToNonplanar .initial (.of x) = _
    cases x with
    | inl t =>
      simp only [planarToNonplanar]
      exact congrArg (fun tk => Nonplanar.leaf (Sum.inl tk))
        (Sum.inl.inj (hmk : Sum.inl t = Sum.inl tok))
    | inr n => exact absurd (hmk : Sum.inr n = Sum.inl tok) (by intro; contradiction)
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

@[simp] theorem SyntacticObject.toNonplanar_trace (n : Nat) :
    (SyntacticObject.trace n).toNonplanar = Nonplanar.leaf (Sum.inr ()) := by
  show planarToNonplanar .initial (SyntacticObject.trace n).out = _
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.trace n).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inr n)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.trace n).out with
  | .of x =>
    rw [h] at hmk
    show planarToNonplanar .initial (.of x) = _
    cases x with
    | inl t => exact absurd (hmk : Sum.inl t = Sum.inr n) (by intro; contradiction)
    | inr m => simp only [planarToNonplanar]
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

/-! ### Singleton-class simp lemmas for `toNonplanarWith` (parameterized)

All three lemmas reduce via the keystone `FreeCommMagma.Section.σ_of` helper:
the section's image of `FreeCommMagma.of x` is exactly `FreeMagma.of x`. -/

/-- `toNonplanarWith h` on a leaf returns the corresponding `Nonplanar.leaf`. -/
@[simp] theorem HeadFunction.toNonplanarWith_leaf (h : HeadFunction) (tok : LIToken) :
    h.toNonplanarWith (.leaf tok) = Nonplanar.leaf (Sum.inl tok) := by
  show planarToNonplanar h.headSide (h.section_.σ (FreeCommMagma.of (.inl tok))) = _
  rw [h.section_.σ_of]
  cases h.headSide <;> rfl

/-- `toNonplanarWith h` on a trace returns `Nonplanar.leaf (Sum.inr ())`. -/
@[simp] theorem HeadFunction.toNonplanarWith_trace (h : HeadFunction) (n : Nat) :
    h.toNonplanarWith (.trace n) = Nonplanar.leaf (Sum.inr ()) := by
  show planarToNonplanar h.headSide (h.section_.σ (FreeCommMagma.of (.inr n))) = _
  rw [h.section_.σ_of]
  cases h.headSide <;> rfl

end Minimalist

/-- `mkTrace n = .trace n`, so `isTrace (.trace n) = some n`. -/
theorem Minimalist.isTrace_mkTrace (n : Nat) :
    Minimalist.isTrace (Minimalist.mkTrace n) = some n := rfl

/-- `(mkTrace n).toNonplanar = Nonplanar.leaf (Sum.inr ())` — the IM bridge identity. -/
theorem Minimalist.mkTrace_toNonplanar (n : Nat) :
    (Minimalist.mkTrace n).toNonplanar = RootedTree.Nonplanar.leaf (Sum.inr ()) :=
  Minimalist.SyntacticObject.toNonplanar_trace n
