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
[aksenova-rawski-graf-heinz-2020] Fig. 1;
[meinhardt-mai-bakovic-mccollum-2024] Fig. 1):

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
[heinz-lai-2013] to delimit attested patterns (Maasai/Turkana ATR
harmony) from unattested ones (sour-grapes-style spreading;
[wilson-2003], [wilson-2006]).

## Substrate scope: structural decomposition only

This file defines `IsWeaklyDeterministic` as the **structural backbone**
shared by every formalisation of the class: a function decomposes as
the composition of two subsequential functions reading from opposite
directions, **without alphabet enrichment** (the intermediate alphabet
equals the input/output alphabet).

The "no alphabet enrichment" condition (`β = α` in the type signature
of the inner subsequential) is the [heinz-lai-2013] no-markup
framing made structural. Under this signature, no separate non-
interaction predicate is needed for the basic class membership: any
decomposition into two contradirectional subseq passes that share the
input/output alphabet IS WD by the no-markup criterion.

## Open conjecture: HL2013 vs MMBM2024

[meinhardt-mai-bakovic-mccollum-2024] argue that the structural
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
(Schützenberger's sequential bimachines; see [mohri-1997] §6 for
the canonical reference), which is non-trivial new substrate. Land in
a follow-up `Function/Bimachine.lean` once a Studies file needs the
distinction; the current file's structural `IsWeaklyDeterministic`
suffices for both:

* **Maasai/Turkana classification** ([meinhardt-mai-bakovic-mccollum-2024]
  §§3-4): WD by both HL2013 and MMBM2024 definitions, so the
  structural predicate suffices.
* **Sour-grapes refutations** ([wilson-2003];
  [wilson-2006]): claimed non-WD by MMBM2024; under HL2013 the
  status depends on the markup criterion. Formal refutation is
  deferred until bimachine substrate.

## Out of scope

* Bimachine substrate (deferred — large substrate; only needed to
  formalise the MMBM2024 patch and the sour-grapes refutation).
* Non-trivial decomposition theorems (e.g. Maasai is structurally WD
  via explicit `leftwardATR ∘ rightwardATR` composition; lives in
  `Studies/MeinhardtEtAl2024.lean`).
-/

namespace Subregular.Function

variable {α : Type*}

/-- **Weakly Deterministic** function class. A function `f : List α →
List α` is WD iff it decomposes as the composition of two
subsequential functions reading from opposite directions, with no
alphabet enrichment (intermediate alphabet equals input/output
alphabet — the structural form of [heinz-lai-2013]'s no-markup
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

/-- The trivial pass-through SFST over alphabet `α`: a one-state machine
that emits each input symbol unchanged. Its `run` is the identity, which
makes it a convenient witness for `IsLeftSubsequential id` / `IsRightSubsequential id`. -/
private def idSFST (α : Type*) : SFST Unit α α where
  initial := ()
  step _ x := ((), [x])
  finalOutput _ := []

private lemma idSFST_runFrom (α : Type*) (s : Unit) (xs : List α) :
    (idSFST α).runFrom s xs = xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons y ys ih =>
    show [y] ++ (idSFST α).runFrom () ys = y :: ys
    exact congrArg (y :: ·) (ih _)

private lemma idSFST_run (α : Type*) : (idSFST α).run = id := by
  funext xs; exact idSFST_runFrom α () xs

private lemma idSFST_runRight (α : Type*) : (idSFST α).runRight = id := by
  funext xs
  show ((idSFST α).run xs.reverse).reverse = id xs
  rw [idSFST_run α]
  exact List.reverse_reverse xs

/-- The identity is Left-Subsequential (witnessed by the trivial
one-state pass-through SFST). -/
theorem isLeftSubsequential_id {α : Type*} :
    IsLeftSubsequential (id : List α → List α) :=
  idSFST_run α ▸ (idSFST α).isLeftSubsequential

/-- The identity is Right-Subsequential (witnessed by the trivial
one-state pass-through SFST). -/
theorem isRightSubsequential_id {α : Type*} :
    IsRightSubsequential (id : List α → List α) :=
  idSFST_runRight α ▸ (idSFST α).isRightSubsequential

/-- Every Left-Subsequential function is WD: take the inner function as
itself and the outer function as the identity (Right-Subsequential
trivially via the identity FST). The composition `id ∘ f = f`. -/
theorem IsLeftSubsequential.isWeaklyDeterministic
    {f : List α → List α} (hf : IsLeftSubsequential f) :
    IsWeaklyDeterministic f := by
  refine Or.inl ⟨id, f, hf, isRightSubsequential_id, ?_⟩
  funext xs
  rfl

/-- Every Right-Subsequential function is WD: dual of the left case.
Take the inner function as itself and the outer as the identity. -/
theorem IsRightSubsequential.isWeaklyDeterministic
    {f : List α → List α} (hf : IsRightSubsequential f) :
    IsWeaklyDeterministic f := by
  refine Or.inr ⟨id, f, hf, isLeftSubsequential_id, ?_⟩
  funext xs
  rfl

/-- **Direction-parameterised WD inclusion**: every subsequential function
(in either scan direction) is Weakly Deterministic. Delegates to the
Left- / Right- specialised theorems. -/
theorem IsSubsequential.isWeaklyDeterministic {d : Direction}
    {f : List α → List α} (hf : IsSubsequential d f) :
    IsWeaklyDeterministic f := by
  cases d with
  | left => exact IsLeftSubsequential.isWeaklyDeterministic hf
  | right => exact IsRightSubsequential.isWeaklyDeterministic hf

end Subregular.Function
