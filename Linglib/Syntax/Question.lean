/-!
# The syntax of questions

This file records two syntactic parameters of content questions that studies and fragments
share. `WhInterpMechanism` is how a wh-phrase reaches its scope position: overt movement,
covert movement at LF ([huang-1982]), the overt-then-covert partial movement that
[sato-ngui-2017] propose for Singlish, or binding in situ by an operator in C, with no movement
([pesetsky-1987]). The same surface position can arise from different mechanisms, which differ
in island sensitivity. `MWFParameter` is [rudin-1988]'s multiple-wh-fronting parameter in the
three-valued form of [citko-gracanin-yuksek-2025], who split the languages without multiple
fronting by the phase edges at which several wh-specifiers incur a PF asterisk
(`MWFParameter.EdgeAsterisk`). The declarations share the root `Question` namespace with the
semantics of questions in `Semantics/Questions/`.

## Implementation notes

The mechanisms commit to a division between movement and binding that is contested:
choice-function and intervention-based accounts derive the same surface positions otherwise.
The surface typology of questions, the position of wh-phrases and of polar question particles
and the marking of polar questions, is read from `Data.WALS` chapters 92A, 93A and 116A
directly and is not re-labelled here.

## References

* [huang-1982]
* [pesetsky-1987]
* [sato-ngui-2017]
* [rudin-1988]
* [citko-gracanin-yuksek-2025]
-/

namespace Question

/-- How a wh-phrase is interpreted at the syntax-semantics interface. The mechanism is distinct
from the surface position of the phrase: a phrase in situ may move covertly or be bound without
moving, with different consequences for island sensitivity and modifier licensing. -/
inductive WhInterpMechanism where
  /-- Successive cyclic overt movement to matrix Spec-CP. -/
  | overtMovement
  /-- Single LF movement to Spec-CP ([huang-1982]; Mandarin *daodi*). -/
  | covertMovement
  /-- Two-step: overt to intermediate Spec-CP, *then* covert to matrix
      Spec-CP. This is Singlish partial wh-movement
      ([sato-ngui-2017]). Distinct from `.covertMovement` because
      the overt-then-covert derivation has both a Spell-Out landing site
      and a separate covert step that crosses islands at LF. -/
  | partialMovement
  /-- Q operator in C binds variable in situ; no movement (overt or
      covert). Island-insensitive. -/
  | unselectiveBinding
  deriving DecidableEq, Repr

/-- Does this mechanism involve the wh-phrase reaching matrix Spec-CP
    (overtly or covertly, in one step or two)? -/
def WhInterpMechanism.ReachesSpecCP : WhInterpMechanism → Prop
  | .overtMovement      => True
  | .covertMovement     => True
  | .partialMovement    => True
  | .unselectiveBinding => False

instance (m : WhInterpMechanism) : Decidable m.ReachesSpecCP := by
  cases m <;> unfold WhInterpMechanism.ReachesSpecCP <;> infer_instance

/-- Is this mechanism sensitive to syntactic islands? Partial movement
    *is* island-sensitive at its covert step ([sato-ngui-2017]: ex 15). -/
def WhInterpMechanism.IslandSensitive : WhInterpMechanism → Prop
  | .overtMovement      => True
  | .covertMovement     => True
  | .partialMovement    => True
  | .unselectiveBinding => False

instance (m : WhInterpMechanism) : Decidable m.IslandSensitive := by
  cases m <;> unfold WhInterpMechanism.IslandSensitive <;> infer_instance

/-- Does this mechanism involve a covert movement step? Distinguishes
    overt-only from covert/partial. Used by analyses that care about
    LF-only operations (e.g., island sensitivity diagnostics). -/
def WhInterpMechanism.HasCovertStep : WhInterpMechanism → Prop
  | .overtMovement      => False
  | .covertMovement     => True
  | .partialMovement    => True
  | .unselectiveBinding => False

instance (m : WhInterpMechanism) : Decidable m.HasCovertStep := by
  cases m <;> unfold WhInterpMechanism.HasCovertStep <;> infer_instance

/-- For all current mechanisms, `ReachesSpecCP` and `IslandSensitive`
    coincide. This is a contingent fact about the current taxonomy, not
    a necessary truth: a future mechanism (e.g., long-distance Agree) could
    be island-sensitive without reaching Spec-CP, or reach Spec-CP without
    island sensitivity. The predicates are kept separate for this reason. -/
theorem reachesSpecCP_iff_islandSensitive (m : WhInterpMechanism) :
    m.ReachesSpecCP ↔ m.IslandSensitive := by
  cases m <;> exact Iff.rfl

/-! ### Multiple wh-fronting -/

/-- The MWF parameter as in [rudin-1988] + [citko-gracanin-yuksek-2025].

    The textbook contrast ([rudin-1988]) is binary — MWF (Bulgarian,
    Romanian) vs non-MWF (English, German, Greek). C&G-Y refine the
    non-MWF case by where the PF asterisk for multiple wh-specifiers
    lands: vP-only (sluicing repairs by deleting vP) vs both vP and CP
    (sluicing leaves the CP-edge asterisk unrepaired). The tripartition
    lets the multiple-sluicing asymmetry be **derived** from the
    parameter rather than stipulated as an independent flag. -/
inductive MWFParameter where
  /-- Multiple wh-fronting language (Bulgarian, Romanian). No PF asterisk
      at any edge. -/
  | fronts
  /-- Non-MWF with vP-only asterisk (German, Greek;
      [citko-gracanin-yuksek-2025] "English variety B"). Sluicing
      (deleting the vP edge) repairs. -/
  | nonFrontsVPOnly
  /-- Non-MWF with asterisks at *both* vP and CP edges
      ([citko-gracanin-yuksek-2025] "English variety A"). Sluicing
      cannot repair — the CP-edge asterisk survives ellipsis. -/
  | nonFrontsBothEdges
  deriving DecidableEq, Repr

/-- Which phase edge is being checked for an MWF asterisk. -/
inductive PhaseEdge where
  | vP
  | CP
  deriving DecidableEq, Repr

namespace MWFParameter

/-- The language allows multiple wh-fronting in matrix questions. -/
def AllowsMWF : MWFParameter → Prop
  | .fronts => True
  | .nonFrontsVPOnly | .nonFrontsBothEdges => False

instance (p : MWFParameter) : Decidable (AllowsMWF p) := by
  cases p <;> unfold AllowsMWF <;> infer_instance

/-- The given phase edge incurs a PF asterisk under `n > 1`
    wh-specifiers. Generalizes the per-edge `vPEdgeAsterisk` /
    `cPEdgeAsterisk` distinction earlier revisions of this code carried
    as separate definitions. -/
def EdgeAsterisk : MWFParameter → PhaseEdge → Nat → Prop
  | .fronts,             _,    _ => False
  | .nonFrontsVPOnly,    .vP,  n => n > 1
  | .nonFrontsVPOnly,    .CP,  _ => False
  | .nonFrontsBothEdges, _,    n => n > 1

instance (p : MWFParameter) (e : PhaseEdge) (n : Nat) :
    Decidable (EdgeAsterisk p e n) := by
  cases p <;> cases e <;> unfold EdgeAsterisk <;> infer_instance

end MWFParameter

end Question

