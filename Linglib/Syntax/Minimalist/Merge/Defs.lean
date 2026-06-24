import Linglib.Syntax.Minimalist.Basic
import Linglib.Syntax.Minimalist.HeadFunction
import Linglib.Syntax.Minimalist.Selection
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

/-- Project a `SyntacticObject` to the bialgebra carrier
    `Nonplanar (LIToken ⊕ Unit)`, under the **selection-induced** head-initial
    embedding `selLinearize .initial` (= `HeadFunction.leftSpine.toNonplanarWith`):
    each internal node is labeled with the genuine **selector** head
    ([marcolli-chomsky-berwick-2025] Lemma 1.13.5/1.13.7), not an arbitrary
    `Quot.out` representative, so the orientation is canonical and `toNonplanar_mul`
    holds. Noncomputable only because `Nonplanar.node` is a noncomputable smart
    constructor. -/
noncomputable def SyntacticObject.toNonplanar (so : SyntacticObject) :
    Nonplanar (LIToken ⊕ Unit) :=
  planarToNonplanar .initial (selLinearize .initial so)

/-- Parameterized projection: `toNonplanar` under head function `h`, using
    `h.section_.σ` to pick the planar representative and `h.headSide` for
    the node-labeling convention. -/
noncomputable def HeadFunction.toNonplanarWith (h : HeadFunction) (so : SyntacticObject) :
    Nonplanar (LIToken ⊕ Unit) :=
  planarToNonplanar h.headSide (h.section_.σ so)

/-! ### Reduction lemmas

With the selection-induced section, leaves/traces reduce **definitionally**
(`selLinearize .initial` of a singleton class is that singleton), and
`toNonplanar_mul` (below) now holds — the orientation is canonical, not a
`Quot.out` artifact. -/

@[simp] theorem SyntacticObject.toNonplanar_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).toNonplanar = Nonplanar.leaf (Sum.inl tok) := rfl

@[simp] theorem SyntacticObject.toNonplanar_trace (n : Nat) :
    (SyntacticObject.trace n).toNonplanar = Nonplanar.leaf (Sum.inr ()) := rfl

/-- **Canonical-orientation coherence.** `toNonplanar` distributes over Merge:
    the node is labeled with the genuine selector head (`leftmostLeafPlanar` of the
    selection-induced embedding, [marcolli-chomsky-berwick-2025] Lemma 1.13.7) and
    its children are exactly `{l.toNonplanar, r.toNonplanar}`. Holds because the
    embedding's orientation is selection-determined (head-side) or, at exocentric
    nodes, the canonical `smallerFirst` — never an arbitrary `Quot.out`. This is the
    externalize-respect property the `mergeOp_*_matches_Step` bridges need. -/
theorem SyntacticObject.toNonplanar_mul (l r : SyntacticObject) :
    (l * r).toNonplanar =
      Nonplanar.node (Sum.inl (leftmostLeafPlanar (selLinearize .initial (l * r))))
        {l.toNonplanar, r.toNonplanar} := by
  show planarToNonplanar .initial (selLinearize .initial (l * r)) = _
  rw [selLinearize_mul]
  -- the head label is uniform (`leftmostLeafPlanar`); only child orientation varies
  split <;>
    first
    | (unfold smallerFirst
       split <;>
         simp only [planarToNonplanar, headLeafPlanar, leftmostLeafPlanar,
           SyntacticObject.toNonplanar] <;>
         try rw [Multiset.pair_comm])
    | (simp only [placeHead, planarToNonplanar, headLeafPlanar, leftmostLeafPlanar,
         SyntacticObject.toNonplanar] <;>
       try rw [Multiset.pair_comm])

/-- On the endocentric domain `Dom(h)`, the Merge node's head label is the genuine
    **selector** `selHead` ([marcolli-chomsky-berwick-2025] Lemma 1.13.7). The form
    the `mergeOp_*_matches_Step` bridges consume. -/
theorem SyntacticObject.toNonplanar_mul_selHead (l r : SyntacticObject) (hd : LIToken)
    (hsel : selHead (l * r) = some hd) :
    (l * r).toNonplanar = Nonplanar.node (Sum.inl hd) {l.toNonplanar, r.toNonplanar} := by
  rw [toNonplanar_mul, leftmost_selLinearize_eq_selHead _ _ hsel]

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
