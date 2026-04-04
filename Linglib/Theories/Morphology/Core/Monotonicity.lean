/-!
# The Monotonicity Hypothesis

@cite{koontz-garboden-2009} @cite{koontz-garboden-2007}

The Monotonicity Hypothesis (MH) states that word formation operations
do not remove operators from lexical semantic representations (LSRs).

## Formal statement

Given an LSR modeled as a set of operators, a word formation operation
`f : LSR → LSR` satisfies the MH iff for all inputs `r`, the operators
in `r` are a subset of the operators in `f(r)`.

## Status

The MH is an empirical hypothesis, not a logical necessity. Whether
all natural language word formation operations satisfy it is debated.
@cite{koontz-garboden-2009} argues that anticausativization — the
strongest apparent counterexample — is consistent with the MH under
a reflexivization analysis. The deletion analysis of anticausativization
would violate it. See `Phenomena/Causation/Studies/KoontzGarboden2009`
for arguments in favor.

The MH is distinct from the Bifurcation Thesis (whether *roots* can
introduce templatic meanings like CAUSE/BECOME) and Manner/Result
Complementarity (whether roots can entail both manner and result).
@cite{beavers-koontz-garboden-2020} argue both of those are false,
but this does not directly bear on the MH, which constrains
*operations*, not *representations*.

## This module

This module provides the formal apparatus — `isMonotonic`, `satisfiesMH`,
and their mathematical properties — without taking a position on
whether the MH holds empirically. Study files use these definitions
to argue for or against specific analyses.
-/

namespace Morphology.Core.Monotonicity

-- ════════════════════════════════════════════════════
-- § 1. Definitions
-- ════════════════════════════════════════════════════

/-- An operation over operator lists is monotonic if every operator
    in the input is preserved in the output. -/
def isMonotonic {Op : Type} [BEq Op] (inputOps outputOps : List Op) : Bool :=
  inputOps.all (outputOps.contains ·)

/-- A word formation operation `f` satisfies the Monotonicity Hypothesis
    if it is monotonic for all inputs. -/
def satisfiesMH {Op : Type} [BEq Op] (f : List Op → List Op) : Prop :=
  ∀ ops, isMonotonic ops (f ops) = true

/-- Identity on operator lists. Models any operation that constrains
    argument structure without adding or removing operators (e.g.,
    reflexivization: λℜλx[ℜ(x,x)]). -/
def identityOp {Op : Type} (ops : List Op) : List Op := ops

/-- Deletion of a specific operator from the list. -/
def deleteOp {Op : Type} [BEq Op] (target : Op) (ops : List Op) : List Op :=
  ops.filter (· != target)

-- ════════════════════════════════════════════════════
-- § 2. Properties of `isMonotonic`
-- ════════════════════════════════════════════════════

/-- Monotonicity is reflexive: the identity is monotonic. -/
theorem isMonotonic_refl {Op : Type} [BEq Op] [LawfulBEq Op] (ops : List Op) :
    isMonotonic ops ops = true := by
  simp only [isMonotonic, List.all_eq_true]
  intro x hx
  exact List.contains_iff_mem.mpr hx

/-- Appending operators to the output preserves monotonicity. -/
theorem isMonotonic_append_right {Op : Type} [BEq Op] [LawfulBEq Op]
    (input output extra : List Op)
    (h : isMonotonic input output = true) :
    isMonotonic input (output ++ extra) = true := by
  simp only [isMonotonic, List.all_eq_true] at *
  intro x hx
  exact List.contains_iff_mem.mpr
    (List.mem_append_left extra (List.contains_iff_mem.mp (h x hx)))

-- ════════════════════════════════════════════════════
-- § 3. Properties of `satisfiesMH`
-- ════════════════════════════════════════════════════

/-- The identity operation satisfies the MH. -/
theorem identityOp_satisfiesMH {Op : Type} [BEq Op] [LawfulBEq Op] :
    satisfiesMH (identityOp (Op := Op)) := by
  intro ops; exact isMonotonic_refl ops

/-- Deletion of any operator does not satisfy the MH. -/
theorem deleteOp_not_satisfiesMH {Op : Type} [DecidableEq Op] (target : Op) :
    ¬ satisfiesMH (deleteOp target) := by
  intro h
  have := h [target]
  simp only [isMonotonic, deleteOp, List.all_cons, List.all_nil, Bool.and_true,
    List.contains_iff_mem, List.filter, bne_self_eq_false] at this
  cases this

/-- Characterization: `satisfiesMH f` iff `f` never removes any
    element from its input. -/
theorem satisfiesMH_iff_noRemoval {Op : Type} [BEq Op] [LawfulBEq Op]
    (f : List Op → List Op) :
    satisfiesMH f ↔ ∀ (ops : List Op) (x : Op), x ∈ ops → x ∈ f ops := by
  constructor
  · intro h ops x hx
    have := h ops
    simp only [isMonotonic, List.all_eq_true] at this
    exact List.contains_iff_mem.mp (this x hx)
  · intro h ops
    simp only [isMonotonic, List.all_eq_true]
    intro x hx
    exact List.contains_iff_mem.mpr (h ops x hx)

/-- The MH is closed under composition. -/
theorem satisfiesMH_comp {Op : Type} [BEq Op] [LawfulBEq Op]
    (f g : List Op → List Op)
    (hf : satisfiesMH f) (hg : satisfiesMH g) :
    satisfiesMH (g ∘ f) := by
  intro ops
  simp only [Function.comp]
  have hf' : isMonotonic ops (f ops) = true := hf ops
  have hg' : isMonotonic (f ops) (g (f ops)) = true := hg (f ops)
  simp only [isMonotonic, List.all_eq_true] at *
  intro x hx
  have hxf : x ∈ f ops := List.contains_iff_mem.mp (hf' x hx)
  exact List.contains_iff_mem.mpr (List.contains_iff_mem.mp (hg' x hxf))

end Morphology.Core.Monotonicity
