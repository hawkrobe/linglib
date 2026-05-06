/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.Subsequential

/-!
# Weakly Deterministic (WD) Functions

The **Weakly Deterministic** function class sits between Subsequential
and the full Non-Deterministic regular relations in the function-level
subregular hierarchy (`Function/{ISL,OSL,Subsequential}.lean`;
@cite{aksenova-rawski-graf-heinz-2020} Fig. 1;
@cite{meinhardt-mai-bakovic-mccollum-2024} Fig. 1):

```
Non-Deterministic (regular relations)
       ↓
Weakly Deterministic ← THIS FILE
       ↓
Subsequential (Left and Right)
       ↓
OSL (Left and Right)
       ↓
ISL
       ↓
Finite
```

WD captures bidirectional iterative phonological maps — a left-to-right
pass plus a right-to-left pass — and was introduced by
@cite{heinz-lai-2013} to delimit attested patterns (Maasai/Turkana ATR
harmony) from unattested ones (sour-grapes-style spreading;
@cite{wilson-2003}, @cite{wilson-2006}).

## Substrate scope: structural decomposition only

This file defines `IsWeaklyDeterministic` as the **structural backbone**
shared by every formalisation of the class: a function decomposes as
the composition of two subsequential functions reading from opposite
directions, **without alphabet enrichment** (the intermediate alphabet
equals the input/output alphabet).

The "no alphabet enrichment" condition (`β = α` in the type signature
of the inner subsequential) is the @cite{heinz-lai-2013} no-markup
framing made structural. Under this signature, no separate non-
interaction predicate is needed for the basic class membership: any
decomposition into two contradirectional subseq passes that share the
input/output alphabet IS WD by the no-markup criterion.

## Open conjecture: HL2013 vs MMBM2024

@cite{meinhardt-mai-bakovic-mccollum-2024} argue that the structural
"no-markup" criterion above is **too permissive**: some patterns
satisfy it but still require unbounded bilateral information at output
time (paper §§4.3, 5). Their patched definition (Def. 6, p. 1219)
strengthens the criterion via a bimachine output-function condition:
the bimachine implementing `f` must have an output function `ω` such
that for all `q^L, x, y, q^R`, `ω(q^L, x, q^R) = y` iff `y` is
licensed by `q^L` alone OR by `q^R` alone (never simultaneously).

The **open conjecture**: under the strengthened MMBM2024 definition,
some functions in `IsWeaklyDeterministic` (per this file's structural
definition, equivalent to the HL2013 framing) would NOT count as WD —
the MMBM2024 patch refuses them. The paper's Maasai analysis is
WD-by-both-definitions; the unattested counterexamples that
distinguish them are sour-grapes-style functions.

Formalising this distinction in Lean requires bimachine substrate
(Schützenberger's sequential bimachines; see @cite{mohri-1997} §6 for
the canonical reference), which is non-trivial new substrate. Land in
a follow-up `Function/Bimachine.lean` once a Studies file needs the
distinction; the current file's structural `IsWeaklyDeterministic`
suffices for both:

* **Maasai/Turkana classification** (@cite{meinhardt-mai-bakovic-mccollum-2024}
  §§3-4): WD by both HL2013 and MMBM2024 definitions, so the
  structural predicate suffices.
* **Sour-grapes refutations** (@cite{wilson-2003};
  @cite{wilson-2006}): claimed non-WD by MMBM2024; under HL2013 the
  status depends on the markup criterion. Formal refutation is
  deferred until bimachine substrate.

## Out of scope

* Bimachine substrate (deferred — large substrate; only needed to
  formalise the MMBM2024 patch and the sour-grapes refutation).
* Non-trivial decomposition theorems (e.g. Maasai is structurally WD
  via explicit `leftwardATR ∘ rightwardATR` composition; lives in
  `Phenomena/Phonology/Studies/MeinhardtEtAl2024.lean`).
-/

namespace Core.Computability.Subregular.Function

variable {α : Type}

/-- **Weakly Deterministic** function class. A function `f : List α →
List α` is WD iff it decomposes as the composition of two
subsequential functions reading from opposite directions, with no
alphabet enrichment (intermediate alphabet equals input/output
alphabet — the structural form of @cite{heinz-lai-2013}'s no-markup
condition).

Per the file docstring, this is the structural backbone shared by both
HL2013 and MMBM2024 formalisations. The MMBM2024 patch adds a
bimachine output-function condition that further refines the class;
that refinement is deferred until bimachine substrate exists. -/
def IsWeaklyDeterministic (f : List α → List α) : Prop :=
  (∃ g h : List α → List α,
    IsLeftSubsequential h ∧ IsRightSubsequential g ∧ f = g ∘ h) ∨
  (∃ g h : List α → List α,
    IsRightSubsequential h ∧ IsLeftSubsequential g ∧ f = g ∘ h)

/-- Every Left-Subsequential function is WD: take the inner function as
itself and the outer function as the identity (Right-Subsequential
trivially via the identity FST). The composition `id ∘ f = f`. -/
theorem IsLeftSubsequential.isWeaklyDeterministic
    {f : List α → List α} (hf : IsLeftSubsequential f) :
    IsWeaklyDeterministic f := by
  refine Or.inl ⟨id, f, hf, ?_, ?_⟩
  · -- identity is Right-Subsequential: pick the trivial 1-state SFST
    -- with finalOutput := id, step := pass-through.
    refine ⟨Unit, ?_, ?_⟩
    · exact { initial := (), step := fun _ x => ((), [x]),
              finalOutput := fun _ => [] }
    · funext xs
      show SFST.runRight _ xs = id xs
      show (SFST.run _ xs.reverse).reverse = xs
      have hrun : ∀ s : Unit, ∀ ys : List α,
          SFST.runFrom { initial := (), step := fun _ x => ((), [x]),
                         finalOutput := fun _ => [] } s ys = ys := by
        intro s ys
        induction ys generalizing s with
        | nil => rfl
        | cons y ys ih =>
          show [y] ++ _ = y :: ys
          show y :: _ = y :: ys
          exact congrArg (y :: ·) (ih _)
      rw [show SFST.run _ xs.reverse = xs.reverse from hrun () xs.reverse]
      exact List.reverse_reverse xs
  · funext xs
    rfl

/-- Every Right-Subsequential function is WD: dual of the left case.
Take the inner function as itself and the outer as the identity. -/
theorem IsRightSubsequential.isWeaklyDeterministic
    {f : List α → List α} (hf : IsRightSubsequential f) :
    IsWeaklyDeterministic f := by
  refine Or.inr ⟨id, f, hf, ?_, ?_⟩
  · -- identity is Left-Subsequential: trivial 1-state SFST.
    refine ⟨Unit, ?_, ?_⟩
    · exact { initial := (), step := fun _ x => ((), [x]),
              finalOutput := fun _ => [] }
    · funext xs
      show SFST.run _ xs = id xs
      have hrun : ∀ s : Unit, ∀ ys : List α,
          SFST.runFrom { initial := (), step := fun _ x => ((), [x]),
                         finalOutput := fun _ => [] } s ys = ys := by
        intro s ys
        induction ys generalizing s with
        | nil => rfl
        | cons y ys ih =>
          show [y] ++ _ = y :: ys
          show y :: _ = y :: ys
          exact congrArg (y :: ·) (ih _)
      exact hrun () xs
  · funext xs
    rfl

end Core.Computability.Subregular.Function
