import Linglib.Core.Algebra.ConnesKreimer.DoubleCut

namespace ConnesKreimer.GeoCutCheck

abbrev Atom := ULift (Fin 2)
abbrev a : Atom := ⟨0⟩
abbrev b : Atom := ⟨1⟩

abbrev T : DecoratedTree Atom := .node (.leaf a) (.leaf b)

-- For T = .node (.leaf a) (.leaf b), root layer top:
-- Each .leaf has 1 GeoCut per layer, and node has #(lL ≤ top) × #(rL ≤ top) = 3×3 = 9.
example : Fintype.card (GeoCut T Layer.top) = 9 := by decide
example : Fintype.card (GeoCut T Layer.mid) = 4 := by decide  -- 2×2: lL∈{bot,mid}, rL∈{bot,mid}
example : Fintype.card (GeoCut T Layer.bot) = 1 := by decide  -- 1×1: only bot

/-! ### Sanity checks on geo-projection helpers

Verify the 3-slot computation for a few specific GeoCut examples on `.node l r`. -/

-- All-top GeoCut: gl=.leaf top, gr=.leaf top, root=top.
example :
    let g : GeoCut T Layer.top :=
      .node (le_refl _) (le_refl _) (.leaf .top) (.leaf .top)
    geoBotForest g = (0 : Forest Atom) := by decide

example :
    let g : GeoCut T Layer.top :=
      .node (le_refl _) (le_refl _) (.leaf .top) (.leaf .top)
    geoMidForest g = (0 : Forest Atom) := by decide

example :
    let g : GeoCut T Layer.top :=
      .node (le_refl _) (le_refl _) (.leaf .top) (.leaf .top)
    geoStackItem g = T := by decide

-- All-bot GeoCut on T = .node leaf leaf: gl=.leaf bot, gr=.leaf bot, root=top.
example :
    let g : GeoCut T Layer.top :=
      .node (by decide : Layer.bot ≤ Layer.top) (by decide : Layer.bot ≤ Layer.top)
        (.leaf .bot) (.leaf .bot)
    geoBotForest g = ({.leaf a, .leaf b} : Forest Atom) := by decide

example :
    let g : GeoCut T Layer.top :=
      .node (by decide : Layer.bot ≤ Layer.top) (by decide : Layer.bot ≤ Layer.top)
        (.leaf .bot) (.leaf .bot)
    geoMidForest g = (0 : Forest Atom) := by decide

example :
    let g : GeoCut T Layer.top :=
      .node (by decide : Layer.bot ≤ Layer.top) (by decide : Layer.bot ≤ Layer.top)
        (.leaf .bot) (.leaf .bot)
    geoStackItem g = .node (.trace (.leaf a)) (.trace (.leaf b)) := by decide

-- Mixed GeoCut: lL=bot, rL=top.
example :
    let g : GeoCut T Layer.top :=
      .node (by decide : Layer.bot ≤ Layer.top) (by decide : Layer.top ≤ Layer.top)
        (.leaf .bot) (.leaf .top)
    geoBotForest g = ({.leaf a} : Forest Atom) := by decide

example :
    let g : GeoCut T Layer.top :=
      .node (by decide : Layer.bot ≤ Layer.top) (by decide : Layer.top ≤ Layer.top)
        (.leaf .bot) (.leaf .top)
    geoStackItem g = .node (.trace (.leaf a)) (.leaf b) := by decide

-- Mixed GeoCut: lL=mid, rL=top.
example :
    let g : GeoCut T Layer.top :=
      .node (by decide : Layer.mid ≤ Layer.top) (by decide : Layer.top ≤ Layer.top)
        (.leaf .mid) (.leaf .top)
    geoBotForest g = (0 : Forest Atom) := by decide

example :
    let g : GeoCut T Layer.top :=
      .node (by decide : Layer.mid ≤ Layer.top) (by decide : Layer.top ≤ Layer.top)
        (.leaf .mid) (.leaf .top)
    geoMidForest g = ({.leaf a} : Forest Atom) := by decide

example :
    let g : GeoCut T Layer.top :=
      .node (by decide : Layer.mid ≤ Layer.top) (by decide : Layer.top ≤ Layer.top)
        (.leaf .mid) (.leaf .top)
    geoStackItem g = .node (.trace (.leaf a)) (.leaf b) := by decide

/-! ### Deeper test: `.node`-rooted subtree at MID

This test case caught a bug in geoStackItem where `myL = .mid` on a `.node`-rooted
subtree wrongly used `.trace (geoOuterSkeleton g)` instead of `.trace T`. The fix:
slot 3 trace data must be the **whole** original subtree T (since the outer cut
extracts T untouched; the inner cut's decomposition of T is orthogonal). -/

abbrev c : Atom := ⟨0⟩
abbrev d : Atom := ⟨1⟩
abbrev lDeep : DecoratedTree Atom := .node (.leaf c) (.leaf d)
abbrev TDeep : DecoratedTree Atom := .node lDeep (.leaf b)

example :
    let gl : GeoCut lDeep Layer.mid :=
      .node (by decide : Layer.bot ≤ Layer.mid) (by decide : Layer.bot ≤ Layer.mid)
        (.leaf .bot) (.leaf .bot)
    let g : GeoCut TDeep Layer.top :=
      .node (by decide : Layer.mid ≤ Layer.top) (by decide : Layer.top ≤ Layer.top)
        gl (.leaf .top)
    geoStackItem g = .node (.trace lDeep) (.leaf b) := by decide

example :
    let gl : GeoCut lDeep Layer.mid :=
      .node (by decide : Layer.bot ≤ Layer.mid) (by decide : Layer.bot ≤ Layer.mid)
        (.leaf .bot) (.leaf .bot)
    let g : GeoCut TDeep Layer.top :=
      .node (by decide : Layer.mid ≤ Layer.top) (by decide : Layer.top ≤ Layer.top)
        gl (.leaf .top)
    geoBotForest g = ({.leaf c, .leaf d} : Forest Atom) := by decide

example :
    let gl : GeoCut lDeep Layer.mid :=
      .node (by decide : Layer.bot ≤ Layer.mid) (by decide : Layer.bot ≤ Layer.mid)
        (.leaf .bot) (.leaf .bot)
    let g : GeoCut TDeep Layer.top :=
      .node (by decide : Layer.mid ≤ Layer.top) (by decide : Layer.top ≤ Layer.top)
        gl (.leaf .top)
    geoMidForest g
      = ({(.node (.trace (.leaf c)) (.trace (.leaf d)) : DecoratedTree Atom)} :
          Forest Atom) := by decide

end ConnesKreimer.GeoCutCheck
