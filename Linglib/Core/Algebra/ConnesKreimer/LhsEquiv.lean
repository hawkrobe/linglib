import Linglib.Core.Algebra.ConnesKreimer.LhsBridge

/-!
# Substantive Foissy bijection: `LhsIndex T ≃ GeoCut T .top`
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-2002}

The substantive Foissy cut-commutation content (M-C-B Lemma 1.2.10), bundled
as an `Equiv` between the LHS-style structurally indexed enumeration
(`LhsIndex T`) and the geometric 3-coloring (`GeoCut T .top`).

## The bijection geometrically

A `LhsIndex T` value encodes a `(cl_outer, π)` pair where `cl_outer : CutShape T`
is the outer cut (deciding TOP-vs-not-TOP) and `π` is a per-T'-in-cutForest
choice of `AugCutShape T'` (deciding MID-vs-BOT for each extracted subtree).

This corresponds geometrically to a 3-coloring (`GeoCut T .top`):
- The outer cut's TRUNK vertices ↔ TOP layer.
- For each extracted subtree T', the AugCutShape choice determines:
  * `extractWhole` ↔ T' rooted at BOT (no inner cut).
  * `real C'` ↔ T' rooted at MID with internal cut C' producing BOT-children.

## The 9 sub-cases per `.node`

| LhsIndex ctor (with AugCut split)          | GeoCut.node (lL, rL) |
|--------------------------------------------|----------------------|
| `bothCut hl hr (.inr ()) (.inr ())`        | `.bot, .bot`         |
| `bothCut hl hr (.inr ()) (.inl C_r)`       | `.bot, .mid`         |
| `bothCut hl hr (.inl C_l) (.inr ())`       | `.mid, .bot`         |
| `bothCut hl hr (.inl C_l) (.inl C_r)`      | `.mid, .mid`         |
| `onlyLeftCut hl (.inr ()) rhs`             | `.bot, .top`         |
| `onlyLeftCut hl (.inl C_l) rhs`            | `.mid, .top`         |
| `onlyRightCut hr lhs (.inr ())`            | `.top, .bot`         |
| `onlyRightCut hr lhs (.inl C_r)`           | `.top, .mid`         |
| `bothRecurse lhs rhs`                      | `.top, .top`         |

## Layer status

`[UPSTREAM]` candidate, paired with `LhsIndex.lean` and `LhsBridge.lean`.
Future home: `Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.LhsEquiv`.
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {α : Type*} [DecidableEq α]

/-! ## §1: `lhsToGeoCut` — forward map

By structural recursion on `LhsIndex T`. The 4 `bothCut`/`onlyLeftCut`/
`onlyRightCut` sub-cases (per AugCutShape) decide BOT vs MID for the
extracted children; recursive constructors (`onlyLeftCut`, `onlyRightCut`,
`bothRecurse`) carry the recursive children at TOP layer. -/

/-- Forward map: `LhsIndex T → GeoCut T .top`. Each `LhsIndex` constructor
    maps to a `GeoCut.node` with child layers determined by the AugCutShape
    choices: `.inr ()` (extractWhole) → `.bot`, `.inl C` (real C) → `.mid`,
    recursive `LhsIndex` arg → `.top`. -/
noncomputable def lhsToGeoCut : ∀ {T : TraceTree α Unit}, LhsIndex T → GeoCut T Layer.top
  | .leaf _, .atLeaf => GeoCut.leaf Layer.top
  | .trace _, .atTrace => GeoCut.trace Layer.top
  | .node l r, .bothCut hl hr (.inl C_l) (.inl C_r) =>
      GeoCut.node (by decide : Layer.mid ≤ Layer.top)
                  (by decide : Layer.mid ≤ Layer.top)
        (Or.inl hl) (Or.inl hr) (midGeoCut l C_l) (midGeoCut r C_r)
  | .node l r, .bothCut hl hr (.inl C_l) (.inr ()) =>
      GeoCut.node (by decide : Layer.mid ≤ Layer.top)
                  (by decide : Layer.bot ≤ Layer.top)
        (Or.inl hl) (Or.inl hr) (midGeoCut l C_l) (botGeoCut r)
  | .node l r, .bothCut hl hr (.inr ()) (.inl C_r) =>
      GeoCut.node (by decide : Layer.bot ≤ Layer.top)
                  (by decide : Layer.mid ≤ Layer.top)
        (Or.inl hl) (Or.inl hr) (botGeoCut l) (midGeoCut r C_r)
  | .node l r, .bothCut hl hr (.inr ()) (.inr ()) =>
      GeoCut.node (by decide : Layer.bot ≤ Layer.top)
                  (by decide : Layer.bot ≤ Layer.top)
        (Or.inl hl) (Or.inl hr) (botGeoCut l) (botGeoCut r)
  | .node l r, .onlyLeftCut hl (.inl C_l) rhs =>
      GeoCut.node (by decide : Layer.mid ≤ Layer.top) (le_refl _)
        (Or.inl hl) (Or.inr rfl) (midGeoCut l C_l) (lhsToGeoCut rhs)
  | .node l r, .onlyLeftCut hl (.inr ()) rhs =>
      GeoCut.node (by decide : Layer.bot ≤ Layer.top) (le_refl _)
        (Or.inl hl) (Or.inr rfl) (botGeoCut l) (lhsToGeoCut rhs)
  | .node l r, .onlyRightCut hr lhs (.inl C_r) =>
      GeoCut.node (le_refl _) (by decide : Layer.mid ≤ Layer.top)
        (Or.inr rfl) (Or.inl hr) (lhsToGeoCut lhs) (midGeoCut r C_r)
  | .node l r, .onlyRightCut hr lhs (.inr ()) =>
      GeoCut.node (le_refl _) (by decide : Layer.bot ≤ Layer.top)
        (Or.inr rfl) (Or.inl hr) (lhsToGeoCut lhs) (botGeoCut r)
  | .node l r, .bothRecurse lhs rhs =>
      GeoCut.node (le_refl _) (le_refl _)
        (Or.inr rfl) (Or.inr rfl) (lhsToGeoCut lhs) (lhsToGeoCut rhs)

/-! ## §2: `geoCutToLhs` — inverse map

By structural recursion on `T` with case analysis on `(lL, rL)` at `.node`.
The 9 `(lL, rL)` cells map to the 9 LhsIndex sub-cases above (one per cell). -/

/-- Inverse map: `GeoCut T .top → LhsIndex T`. Inverts `lhsToGeoCut` by
    case analysis on the GeoCut node's child layers `(lL, rL)`. -/
noncomputable def geoCutToLhs : ∀ {T : TraceTree α Unit} (_g : GeoCut T Layer.top),
    LhsIndex T
  | .leaf _, .leaf _ => .atLeaf
  | .trace _, .trace _ => .atTrace
  | .node l r, .node (lL := lL) (rL := rL) _ _ hlNT hrNT gl gr =>
    match lL, rL, hlNT, hrNT, gl, gr with
    | .bot, .bot, hlNT, hrNT, _, _ =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        let hr_NT := hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        .bothCut hl_NT hr_NT (.inr ()) (.inr ())
    | .bot, .mid, hlNT, hrNT, _, gr =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        let hr_NT := hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        .bothCut hl_NT hr_NT (.inr ()) (.inl (fromMidGeoCut gr))
    | .bot, .top, hlNT, _, _, gr =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        .onlyLeftCut hl_NT (.inr ()) (geoCutToLhs (T := r) gr)
    | .mid, .bot, hlNT, hrNT, gl, _ =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        let hr_NT := hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        .bothCut hl_NT hr_NT (.inl (fromMidGeoCut gl)) (.inr ())
    | .mid, .mid, hlNT, hrNT, gl, gr =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        let hr_NT := hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        .bothCut hl_NT hr_NT (.inl (fromMidGeoCut gl)) (.inl (fromMidGeoCut gr))
    | .mid, .top, hlNT, _, gl, gr =>
        let hl_NT := hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        .onlyLeftCut hl_NT (.inl (fromMidGeoCut gl)) (geoCutToLhs (T := r) gr)
    | .top, .bot, _, hrNT, gl, _ =>
        let hr_NT := hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)
        .onlyRightCut hr_NT (geoCutToLhs (T := l) gl) (.inr ())
    | .top, .mid, _, hrNT, gl, gr =>
        let hr_NT := hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)
        .onlyRightCut hr_NT (geoCutToLhs (T := l) gl) (.inl (fromMidGeoCut gr))
    | .top, .top, _, _, gl, gr =>
        .bothRecurse (geoCutToLhs (T := l) gl) (geoCutToLhs (T := r) gr)

/-! ## §3: Inverses

Both round-trips by structural induction. The `geoCutToLhs ∘ lhsToGeoCut`
direction is per-LhsIndex-ctor with `simp only` unfolding + IH for recursive
ctors + `fromMidGeoCut_midGeoCut` for `.mid` AugCut choices. The
`lhsToGeoCut ∘ geoCutToLhs` direction is per-`(lL, rL)` cell with
`botGeoCut_unique` for `.bot`, `midGeoCut_fromMidGeoCut` for `.mid`, IH for
`.top`, and `Or.inl_resolve_right_eq` to collapse the `Or.inl ∘ resolve_right`
disjunction reconstructions. -/

omit [DecidableEq α] in
/-- Left inverse: `geoCutToLhs (lhsToGeoCut idx) = idx`.
    By structural induction on `idx`. The 9 `.node` sub-cases each close
    via `simp only` unfolding + `fromMidGeoCut_midGeoCut` for `.mid` AugCut
    choices + IH for recursive `LhsIndex` arguments. -/
theorem geoCutToLhs_lhsToGeoCut : ∀ {T : TraceTree α Unit} (idx : LhsIndex T),
    geoCutToLhs (lhsToGeoCut idx) = idx
  | .leaf _, .atLeaf => rfl
  | .trace _, .atTrace => rfl
  | .node l r, .bothCut hl hr (.inl C_l) (.inl C_r) => by
      simp only [lhsToGeoCut, geoCutToLhs]
      rw [fromMidGeoCut_midGeoCut l C_l, fromMidGeoCut_midGeoCut r C_r]
  | .node l r, .bothCut hl hr (.inl C_l) (.inr ()) => by
      simp only [lhsToGeoCut, geoCutToLhs]
      rw [fromMidGeoCut_midGeoCut l C_l]
  | .node l r, .bothCut hl hr (.inr ()) (.inl C_r) => by
      simp only [lhsToGeoCut, geoCutToLhs]
      rw [fromMidGeoCut_midGeoCut r C_r]
  | .node l r, .bothCut hl hr (.inr ()) (.inr ()) => rfl
  | .node l r, .onlyLeftCut hl (.inl C_l) rhs => by
      simp only [lhsToGeoCut, geoCutToLhs]
      rw [fromMidGeoCut_midGeoCut l C_l, geoCutToLhs_lhsToGeoCut rhs]
  | .node l r, .onlyLeftCut hl (.inr ()) rhs => by
      simp only [lhsToGeoCut, geoCutToLhs]
      rw [geoCutToLhs_lhsToGeoCut rhs]
  | .node l r, .onlyRightCut hr lhs (.inl C_r) => by
      simp only [lhsToGeoCut, geoCutToLhs]
      rw [geoCutToLhs_lhsToGeoCut lhs, fromMidGeoCut_midGeoCut r C_r]
  | .node l r, .onlyRightCut hr lhs (.inr ()) => by
      simp only [lhsToGeoCut, geoCutToLhs]
      rw [geoCutToLhs_lhsToGeoCut lhs]
  | .node l r, .bothRecurse lhs rhs => by
      simp only [lhsToGeoCut, geoCutToLhs]
      rw [geoCutToLhs_lhsToGeoCut lhs, geoCutToLhs_lhsToGeoCut rhs]

omit [DecidableEq α] in
/-- Right inverse: `lhsToGeoCut (geoCutToLhs g) = g`.
    By structural induction on `T` + case analysis on the `GeoCut.node` `(lL, rL)`.
    For each of the 9 `(lL, rL)` cells: `botGeoCut_unique` for `.bot`,
    `midGeoCut_fromMidGeoCut` for `.mid`, IH for `.top`. The
    `Or.inl ∘ resolve_right` reconstructions collapse via
    `Or.inl_resolve_right_eq`. -/
theorem lhsToGeoCut_geoCutToLhs : ∀ {T : TraceTree α Unit} (g : GeoCut T Layer.top),
    lhsToGeoCut (geoCutToLhs g) = g
  | .leaf _, .leaf _ => rfl
  | .trace _, .trace _ => rfl
  | .node l r, .node (lL := lL) (rL := rL) hl hr hlNT hrNT gl gr => by
    cases lL with
    | bot =>
      have hglEq : gl = botGeoCut l := botGeoCut_unique gl
      subst hglEq
      cases rL with
      | bot =>
        have hgrEq : gr = botGeoCut r := botGeoCut_unique gr
        subst hgrEq
        show GeoCut.node _ _
              (Or.inl (hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
              (Or.inl (hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top))) _ _ = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.bot ≠ Layer.top),
            Or.inl_resolve_right_eq hrNT (by decide : Layer.bot ≠ Layer.top)]
      | mid =>
        show GeoCut.node _ _
              (Or.inl (hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
              (Or.inl (hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top))) _
              (midGeoCut r (fromMidGeoCut gr)) = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.bot ≠ Layer.top),
            Or.inl_resolve_right_eq hrNT (by decide : Layer.mid ≠ Layer.top),
            midGeoCut_fromMidGeoCut gr]
      | top =>
        have ihr := lhsToGeoCut_geoCutToLhs gr
        show GeoCut.node _ _
              (Or.inl (hlNT.resolve_right (by decide : Layer.bot ≠ Layer.top))) hrNT _
              (lhsToGeoCut (geoCutToLhs gr)) = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.bot ≠ Layer.top), ihr]
    | mid =>
      cases rL with
      | bot =>
        have hgrEq : gr = botGeoCut r := botGeoCut_unique gr
        subst hgrEq
        show GeoCut.node _ _
              (Or.inl (hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
              (Or.inl (hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
              (midGeoCut l (fromMidGeoCut gl)) _ = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.mid ≠ Layer.top),
            Or.inl_resolve_right_eq hrNT (by decide : Layer.bot ≠ Layer.top),
            midGeoCut_fromMidGeoCut gl]
      | mid =>
        show GeoCut.node _ _
              (Or.inl (hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
              (Or.inl (hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
              (midGeoCut l (fromMidGeoCut gl))
              (midGeoCut r (fromMidGeoCut gr)) = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.mid ≠ Layer.top),
            Or.inl_resolve_right_eq hrNT (by decide : Layer.mid ≠ Layer.top),
            midGeoCut_fromMidGeoCut gl, midGeoCut_fromMidGeoCut gr]
      | top =>
        have ihr := lhsToGeoCut_geoCutToLhs gr
        show GeoCut.node _ _
              (Or.inl (hlNT.resolve_right (by decide : Layer.mid ≠ Layer.top))) hrNT
              (midGeoCut l (fromMidGeoCut gl))
              (lhsToGeoCut (geoCutToLhs gr)) = _
        rw [Or.inl_resolve_right_eq hlNT (by decide : Layer.mid ≠ Layer.top),
            midGeoCut_fromMidGeoCut gl, ihr]
    | top =>
      cases rL with
      | bot =>
        have hgrEq : gr = botGeoCut r := botGeoCut_unique gr
        subst hgrEq
        have ihl := lhsToGeoCut_geoCutToLhs gl
        show GeoCut.node _ _ hlNT
              (Or.inl (hrNT.resolve_right (by decide : Layer.bot ≠ Layer.top)))
              (lhsToGeoCut (geoCutToLhs gl)) _ = _
        rw [Or.inl_resolve_right_eq hrNT (by decide : Layer.bot ≠ Layer.top), ihl]
      | mid =>
        have ihl := lhsToGeoCut_geoCutToLhs gl
        show GeoCut.node _ _ hlNT
              (Or.inl (hrNT.resolve_right (by decide : Layer.mid ≠ Layer.top)))
              (lhsToGeoCut (geoCutToLhs gl))
              (midGeoCut r (fromMidGeoCut gr)) = _
        rw [Or.inl_resolve_right_eq hrNT (by decide : Layer.mid ≠ Layer.top),
            ihl, midGeoCut_fromMidGeoCut gr]
      | top =>
        have ihl := lhsToGeoCut_geoCutToLhs gl
        have ihr := lhsToGeoCut_geoCutToLhs gr
        show GeoCut.node _ _ hlNT hrNT
              (lhsToGeoCut (geoCutToLhs gl))
              (lhsToGeoCut (geoCutToLhs gr)) = _
        rw [ihl, ihr]

/-! ## §4: The Equiv -/

/-- The substantive Foissy bijection as an `Equiv` between LhsIndex and the
    top-rooted GeoCut. Combines `lhsToGeoCut` (forward), `geoCutToLhs`
    (inverse), and the two roundtrip theorems above. -/
noncomputable def lhsGeoCutEquiv (T : TraceTree α Unit) :
    LhsIndex T ≃ GeoCut T Layer.top where
  toFun := lhsToGeoCut
  invFun := geoCutToLhs
  left_inv := geoCutToLhs_lhsToGeoCut
  right_inv := lhsToGeoCut_geoCutToLhs

/-! ## §5: Per-element forest agreement under `lhsToGeoCut`

The Equiv `lhsGeoCutEquiv` between `LhsIndex T` and `GeoCut T .top` preserves
the triple-tensor data, which means the substantive Foissy identity reduces
to per-element agreement on each forest projection. Three lemmas, analogous
to `geoBotForest_rhsToGeoCut` / `geoMidForest_rhsToGeoCut` /
`geoStackItem_rhsToGeoCut` in DoubleCut.lean. -/

omit [DecidableEq α] in
/-- `geoBotForest (lhsToGeoCut idx) = LhsIndex.botForest idx`. By structural
    induction on `idx` with case analysis on the AugCutShape Sum decomposition. -/
theorem geoBotForest_lhsToGeoCut : ∀ {T : TraceTree α Unit} (idx : LhsIndex T),
    geoBotForest (lhsToGeoCut idx) = LhsIndex.botForest idx
  | .leaf _, .atLeaf => rfl
  | .trace _, .atTrace => rfl
  | .node l r, .bothCut _ _ (.inl C_l) (.inl C_r) => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest, AugCutShape.cutForest_aug]
      rw [geoBotForest_midGeoCut l C_l, geoBotForest_midGeoCut r C_r]
  | .node l r, .bothCut _ _ (.inl C_l) (.inr ()) => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest, AugCutShape.cutForest_aug]
      rw [geoBotForest_midGeoCut l C_l]
  | .node l r, .bothCut _ _ (.inr ()) (.inl C_r) => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest, AugCutShape.cutForest_aug]
      rw [geoBotForest_midGeoCut r C_r]
  | .node l r, .bothCut _ _ (.inr ()) (.inr ()) => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest, AugCutShape.cutForest_aug]
  | .node l r, .onlyLeftCut _ (.inl C_l) rhs => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest, AugCutShape.cutForest_aug]
      rw [geoBotForest_midGeoCut l C_l, geoBotForest_lhsToGeoCut rhs]
  | .node l r, .onlyLeftCut _ (.inr ()) rhs => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest, AugCutShape.cutForest_aug]
      rw [geoBotForest_lhsToGeoCut rhs]
  | .node l r, .onlyRightCut _ lhs (.inl C_r) => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest, AugCutShape.cutForest_aug]
      rw [geoBotForest_lhsToGeoCut lhs, geoBotForest_midGeoCut r C_r]
  | .node l r, .onlyRightCut _ lhs (.inr ()) => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest, AugCutShape.cutForest_aug]
      rw [geoBotForest_lhsToGeoCut lhs]
  | .node l r, .bothRecurse lhs rhs => by
      simp only [lhsToGeoCut, geoBotForest, LhsIndex.botForest]
      rw [geoBotForest_lhsToGeoCut lhs, geoBotForest_lhsToGeoCut rhs]

omit [DecidableEq α] in
/-- `geoMidForest (lhsToGeoCut idx) = LhsIndex.midForest idx`. -/
theorem geoMidForest_lhsToGeoCut : ∀ {T : TraceTree α Unit} (idx : LhsIndex T),
    geoMidForest (lhsToGeoCut idx) = LhsIndex.midForest idx
  | .leaf _, .atLeaf => rfl
  | .trace _, .atTrace => rfl
  | .node l r, .bothCut _ _ (.inl C_l) (.inl C_r) => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest, AugCutShape.remainderForest]
      rw [geoOuterSkeleton_midGeoCut l C_l, geoOuterSkeleton_midGeoCut r C_r]
  | .node l r, .bothCut _ _ (.inl C_l) (.inr ()) => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest, AugCutShape.remainderForest]
      rw [geoOuterSkeleton_midGeoCut l C_l]
  | .node l r, .bothCut _ _ (.inr ()) (.inl C_r) => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest, AugCutShape.remainderForest]
      rw [geoOuterSkeleton_midGeoCut r C_r]
  | .node l r, .bothCut _ _ (.inr ()) (.inr ()) => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest, AugCutShape.remainderForest]
  | .node l r, .onlyLeftCut _ (.inl C_l) rhs => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest, AugCutShape.remainderForest]
      rw [geoOuterSkeleton_midGeoCut l C_l, geoMidForest_lhsToGeoCut rhs]
  | .node l r, .onlyLeftCut _ (.inr ()) rhs => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest, AugCutShape.remainderForest]
      rw [geoMidForest_lhsToGeoCut rhs]
  | .node l r, .onlyRightCut _ lhs (.inl C_r) => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest, AugCutShape.remainderForest]
      rw [geoMidForest_lhsToGeoCut lhs, geoOuterSkeleton_midGeoCut r C_r]
  | .node l r, .onlyRightCut _ lhs (.inr ()) => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest, AugCutShape.remainderForest]
      rw [geoMidForest_lhsToGeoCut lhs]
  | .node l r, .bothRecurse lhs rhs => by
      simp only [lhsToGeoCut, geoMidForest, LhsIndex.midForest]
      rw [geoMidForest_lhsToGeoCut lhs, geoMidForest_lhsToGeoCut rhs]

omit [DecidableEq α] in
/-- `geoStackItem (lhsToGeoCut idx) = CutShape.remainder (LhsIndex.outerCut idx)`.
    The TOP-skeleton of `lhsToGeoCut idx` matches the outer cut's remainder. -/
theorem geoStackItem_lhsToGeoCut : ∀ {T : TraceTree α Unit} (idx : LhsIndex T),
    geoStackItem (lhsToGeoCut idx) = CutShape.remainder (LhsIndex.outerCut idx)
  | .leaf _, .atLeaf => rfl
  | .trace _, .atTrace => rfl
  | .node l r, .bothCut _ _ (.inl C_l) (.inl C_r) => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut,
                 CutShape.remainder, geoStackItem_midGeoCut]
  | .node l r, .bothCut _ _ (.inl C_l) (.inr ()) => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut,
                 CutShape.remainder, geoStackItem_midGeoCut]
  | .node l r, .bothCut _ _ (.inr ()) (.inl C_r) => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut,
                 CutShape.remainder, geoStackItem_midGeoCut]
  | .node l r, .bothCut _ _ (.inr ()) (.inr ()) => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut, CutShape.remainder]
  | .node l r, .onlyLeftCut _ (.inl C_l) rhs => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut,
                 CutShape.remainder, geoStackItem_midGeoCut]
      rw [geoStackItem_lhsToGeoCut rhs]
  | .node l r, .onlyLeftCut _ (.inr ()) rhs => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut, CutShape.remainder]
      rw [geoStackItem_lhsToGeoCut rhs]
  | .node l r, .onlyRightCut _ lhs (.inl C_r) => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut,
                 CutShape.remainder, geoStackItem_midGeoCut]
      rw [geoStackItem_lhsToGeoCut lhs]
  | .node l r, .onlyRightCut _ lhs (.inr ()) => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut, CutShape.remainder]
      rw [geoStackItem_lhsToGeoCut lhs]
  | .node l r, .bothRecurse lhs rhs => by
      simp only [lhsToGeoCut, geoStackItem, LhsIndex.outerCut, CutShape.remainder]
      rw [geoStackItem_lhsToGeoCut lhs, geoStackItem_lhsToGeoCut rhs]

/-- Per-element triple agreement: `LhsIndex.tripleTensor` matches `geoCutToTriple`
    after applying `lhsToGeoCut`. Combines the three forest-agreement lemmas. -/
theorem tripleTensor_lhsIndex_eq_geoCutToTriple
    {R : Type*} [CommSemiring R]
    {T : TraceTree α Unit} (idx : LhsIndex T) :
    LhsIndex.tripleTensor R idx = geoCutToTriple R (lhsToGeoCut idx) := by
  unfold LhsIndex.tripleTensor geoCutToTriple
  rw [geoBotForest_lhsToGeoCut, geoMidForest_lhsToGeoCut, geoStackItem_lhsToGeoCut]

/-! ## §6: Cuts-of-cuts identity via the GeoCut chain

`lhsRealCuts T = geoMultiset T` proven directly via `lhsRealCuts_eq_lhsIndexSum`
(Session 2) + `tripleTensor_lhsIndex_eq_geoCutToTriple` (Session 4) +
`lhsGeoCutEquiv` (Session 3). This bypasses the `perLayerContrib_top` hub
entirely — the substantive Foissy bijection is now sorry-free.

The chain:
  lhsRealCuts T
  = univ_LhsIndex.map LhsIndex.tripleTensor               (Session 2)
  = univ_LhsIndex.map (geoCutToTriple ∘ lhsToGeoCut)      (Session 4)
  = (univ_LhsIndex.map lhsToGeoCut).map geoCutToTriple    (map_map)
  = univ_GeoCut.map geoCutToTriple                        (lhsGeoCutEquiv)
  = geoMultiset T                                          (def)

Then the cuts-of-cuts identity `lhsRealCuts = rhsRealRealInner` follows by
chaining with `rhsRealRealInner_eq_geoMultiset_direct`. -/

variable {R : Type*} [CommSemiring R]

/-- **LHS bijection** (sorry-free, direct via lhsGeoCutEquiv): `lhsRealCuts T`
    enumerates the same multiset of triples as `geoMultiset T`. -/
theorem lhsRealCuts_eq_geoMultiset (T : TraceTree α Unit) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = geoMultiset T := by
  rw [lhsRealCuts_eq_lhsIndexSum]
  rw [show (Finset.univ : Finset (LhsIndex T))
        = (Finset.univ : Finset (GeoCut T Layer.top)).map
            (lhsGeoCutEquiv T).symm.toEmbedding from
       (Finset.map_univ_equiv (lhsGeoCutEquiv T).symm).symm]
  rw [Finset.map_val, Multiset.map_map]
  unfold geoMultiset
  refine Multiset.map_congr rfl (fun g _ => ?_)
  rw [Function.comp_apply]
  show LhsIndex.tripleTensor R (geoCutToLhs g) = geoCutToTriple R g
  rw [tripleTensor_lhsIndex_eq_geoCutToTriple, lhsToGeoCut_geoCutToLhs]

/-- The substantive cuts-of-cuts identity at the section level: LHS sections
    and RHS double-cut innermost real-real triples agree. Chains through
    `geoMultiset T` via the LHS and RHS GeoCut bijections. -/
theorem lhsRealCuts_eq_rhsRealRealInner (T : TraceTree α Unit) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = rhsRealRealInner T :=
  (lhsRealCuts_eq_geoMultiset T).trans (rhsRealRealInner_eq_geoMultiset T).symm

/-- **The substantive cuts-of-cuts identity** (@cite{foissy-2002} §2 /
    @cite{connes-kreimer-1998}): for `T = .node l r`, the LHS-section
    multiset and the RHS-DoubleCut multiset are equal as multisets of
    triple-tensors. Composes the easy half + substantive half +
    `rhsMultiset_decomp`. -/
theorem lhsMultiset_eq_rhsMultiset_node (l r : TraceTree α Unit) :
    (lhsMultiset (.node l r) : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = rhsMultiset (.node l r) := by
  rw [lhsMultiset_decomp,
      lhsExtractWhole_eq_rhsExtractWhole_add_realExtractInner,
      lhsRealCuts_eq_rhsRealRealInner,
      rhsMultiset_decomp]
  abel

/-- LHS direction of the cuts-of-cuts bijection: the left-iterated coproduct
    on a single-tree workspace, after the canonical associator, reorganizes
    as a sum over `DoubleCut T`.

    - `.leaf`, `.trace`: primitive (only the trivial cut) → apply
      `lhs_eq_sum_DoubleCut_of_primitive_tree`.
    - `.node l r`: substantive Foissy "cut-commutation" bijection, reduces
      to `lhsMultiset_eq_rhsMultiset_node`. -/
theorem lhs_eq_sum_DoubleCut (T : TraceTree α Unit) :
    (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
        ((Algebra.TensorProduct.map (comulAlgHom : Hc R α →ₐ[R] _)
          (AlgHom.id R (Hc R α))) (comulTree T : Hc R α ⊗[R] Hc R α))
      = ∑ dc : DoubleCut T, dc.tripleTensor R := by
  match T with
  | .leaf a =>
    apply lhs_eq_sum_DoubleCut_of_primitive_tree
    rw [comulTree_eq_sum_AugCutShape, Fintype.sum_sum_type,
        show (Finset.univ : Finset (CutShape (.leaf a))) = {CutShape.atLeaf} from rfl,
        Finset.sum_singleton, Fintype.sum_unique]
    simp only [AugCutShape.cutForest_aug_real, AugCutShape.remainderForest_real,
               CutShape.cutForest_atLeaf, CutShape.remainder_atLeaf, forestToHc_zero]
    abel
  | .trace t =>
    apply lhs_eq_sum_DoubleCut_of_primitive_tree
    rw [comulTree_eq_sum_AugCutShape, Fintype.sum_sum_type,
        show (Finset.univ : Finset (CutShape (.trace t))) = {CutShape.atTrace} from rfl,
        Finset.sum_singleton, Fintype.sum_unique]
    simp only [AugCutShape.cutForest_aug_real, AugCutShape.remainderForest_real,
               CutShape.cutForest_atTrace, CutShape.remainder_atTrace, forestToHc_zero]
    abel
  | .node l r =>
    rw [lhs_eq_sum_lhsMultiset, rhs_eq_sum_rhsMultiset, lhsMultiset_eq_rhsMultiset_node]

end ConnesKreimer
