import Linglib.Core.Algebra.ConnesKreimer.LhsIndex
import Linglib.Core.Algebra.ConnesKreimer.DoubleCut

/-!
# Bridge: `lhsRealCuts T = LhsIndex.tripleTensor` sum
@cite{marcolli-chomsky-berwick-2025} @cite{marcolli-skigin-2025}

The substantive bridge between the existing `Sections`-based LHS double-cut
enumeration (`lhsRealCuts T` in `DoubleCut.lean`) and the new structurally
indexed enumeration (`LhsIndex T` in `LhsIndex.lean`).

**Theorem**: `lhsRealCuts T = (Finset.univ : Finset (LhsIndex T)).val.map
(LhsIndex.tripleTensor R)`.

**Proof**: by structural induction on `T`. Base cases (`.leaf`, `.trace`)
unfold both sides to a single triple-tensor and verify equality. The
inductive case (`.node l r`) decomposes both sums by the 4 CutShape
constructors (with conditional inclusion based on `IsNotTrace l/r`),
applies the per-ctor bridge lemmas, and recurses on `l`/`r` for the
recursive ctors (`onlyLeftCut`, `onlyRightCut`, `bothRecurse`).

## Layer status

`[UPSTREAM]` candidate, paired with `LhsIndex.lean` and the upcoming
`LhsEquiv.lean`. Future home:
`Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.LhsBridge`.
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ## §1: Helper — `forestToHc_pair_prod` adapted for LhsIndex slot accumulation

The key algebraic identity: a multiset of pair-tensors, when product'd,
gives the tensor of (sum-of-firsts) and (sum-of-seconds). Already exists
in `DoubleCut.lean` as `forestToHc_pair_prod` (private). Re-stated here
non-private for use in the bridge proof. -/

-- Note: forestToHc_pair_prod is private in DoubleCut.lean. We restate.
-- TODO (cleanup session): promote to non-private + move here.
private lemma forestToHc_pair_prod' (s : Multiset (TraceForest α Unit × TraceForest α Unit)) :
    (s.map (fun p => (forestToHc (R := R) p.1) ⊗ₜ[R] (forestToHc (R := R) p.2))).prod
    = (forestToHc (R := R) (s.map Prod.fst).sum)
        ⊗ₜ[R] (forestToHc (R := R) (s.map Prod.snd).sum) := by
  induction s using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero, forestToHc_zero,
               Algebra.TensorProduct.one_def]
  | cons p s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [ih, Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, ← forestToHc_add]

/-! ## §2: The bridge theorem

`lhsRealCuts T` (defined via `Sections` over `cutForest C`) equals the
direct sum of `LhsIndex.tripleTensor` over all LhsIndex values.

**Status**: skeleton with sorry, detailed structural plan in proof comments.
Closing this is Session 2's deliverable. -/

theorem lhsRealCuts_eq_lhsIndexSum (T : TraceTree α Unit) :
    (lhsRealCuts T : Multiset ((Hc R α) ⊗[R] ((Hc R α) ⊗[R] (Hc R α))))
      = (Finset.univ : Finset (LhsIndex T)).val.map (LhsIndex.tripleTensor R) := by
  match T with
  | .leaf a =>
      -- Both sides reduce to a single triple: forestToHc 0 ⊗ (forestToHc 0 ⊗ forestToHc {.leaf a}).
      unfold lhsRealCuts
      show ((Finset.univ : Finset (CutShape (.leaf a))).val.bind fun C =>
              (Multiset.Sections ((CutShape.cutForest C).map (comulTreeMS R))).map fun s =>
                (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
                  (s.prod ⊗ₜ[R] forestToHc (R := R)
                    ({CutShape.remainder C} : TraceForest α Unit)))
            = (Finset.univ : Finset (LhsIndex (.leaf a))).val.map (LhsIndex.tripleTensor R)
      -- Univ on CutShape (.leaf a) = {.atLeaf}; same for LhsIndex (.leaf a).
      -- For C = .atLeaf: cutForest = 0, Sections (0.map _) = {0}, s = 0, s.prod = 1.
      -- Triple = assoc(1 ⊗ forestToHc {.leaf a}).
      -- RHS LhsIndex .atLeaf: tripleTensor = forestToHc 0 ⊗ (forestToHc 0 ⊗ forestToHc {.leaf a}).
      rfl
  | .trace t =>
      -- Symmetric to .leaf case (β = Unit so t = ()).
      unfold lhsRealCuts
      show ((Finset.univ : Finset (CutShape (.trace t))).val.bind fun C =>
              (Multiset.Sections ((CutShape.cutForest C).map (comulTreeMS R))).map fun s =>
                (Algebra.TensorProduct.assoc R R R (Hc R α) (Hc R α) (Hc R α)).toAlgHom
                  (s.prod ⊗ₜ[R] forestToHc (R := R)
                    ({CutShape.remainder C} : TraceForest α Unit)))
            = (Finset.univ : Finset (LhsIndex (.trace t))).val.map (LhsIndex.tripleTensor R)
      -- t : Unit so t = (). Both sides reduce to singleton triples.
      cases t
      rfl
  | .node l r =>
      -- The substantive .node case: 4-ctor decomposition with IH.
      -- Each CutShape ctor's bind contribution matches a corresponding LhsIndex
      -- ctor's enumeration. For onlyLeftCut/onlyRightCut/bothRecurse, the
      -- recursive structure of LhsIndex absorbs the per-T'-in-cutForest section
      -- data via IH on l/r.
      --
      -- Detailed wiring is deferred to Session 2 continuation; the .leaf and
      -- .trace base cases above demonstrate the proof skeleton.
      sorry

end ConnesKreimer
