/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Finite.Basic

/-!
# `{ aⁿ bⁿ | n ≥ 0 }`: a two-symbol non-regular witness language

The classical two-symbol witness language showing that the regular
languages are a proper subclass of the context-free languages: `aⁿbⁿ`
is context-free (trivially) but not regular. The non-regularity proof is
the textbook Myhill–Nerode argument: distinct prefixes `aⁿ` give
distinct left quotients of `{ aⁿ bⁿ }`, so `Set.range
balancedAB.leftQuotient` is infinite, contradicting
`Language.IsRegular.finite_range_leftQuotient`.

Sibling of `Linglib/Core/Computability/NonContextFree/{AnBnCn, AnBnCnDn,
AmBnCmDn}.lean` (those use the CFL pumping lemma to escape the
context-free hierarchy; this one uses Myhill–Nerode to escape the
regular hierarchy). Independent of those files — uses its own `AB`
alphabet rather than the `ThreeSymbol`/`FourSymbol` alphabets there.

## Main definitions

* `AB`: the two-symbol alphabet `{a, b}`.
* `IsBalanced w`: decidable predicate: `w = aⁿbⁿ` for `n = w.length / 2`.
* `balancedAB : Language AB`: `{ w | IsBalanced w }`.

## Main results

* `replicate_a_append_replicate_b_isBalanced`: witness side.
* `replicate_a_append_replicate_b_not_isBalanced`: anti-witness via
  letter-counting on both sides of the supposed decomposition.
* `leftQuotient_replicate_a_injective`: Myhill–Nerode separator: the
  test word `bⁿ` distinguishes left quotients by `aⁿ` for distinct `n`.
* `balancedAB_not_isRegular`: the headline non-regularity theorem,
  composing the injectivity with `Set.infinite_of_injective_forall_mem`
  + `Language.IsRegular.finite_range_leftQuotient`.

## Mathlib placement

Promotable to `Mathlib.Computability.NonRegular.AnBn` as a sibling of
the existing `Mathlib.Computability.MyhillNerode` machinery. The proof
uses only mathlib primitives (`Language.IsRegular.finite_range_leftQuotient`,
`Set.infinite_of_injective_forall_mem`, `List.count_replicate`,
`List.count_append`).
-/

/-- The two-symbol alphabet `{a, b}`. -/
inductive AB | a | b
  deriving DecidableEq, Repr

/-- `AB` has exactly two inhabitants. -/
instance : Fintype AB :=
  ⟨{AB.a, AB.b}, fun x => by cases x <;> decide⟩

/-- A word over `AB` is *balanced* iff it consists of `n` copies of `a`
followed by `n` copies of `b`, where `n = w.length / 2`. The total
length of any balanced word is `2 n`, so `n` is recoverable from the
length and the equation is decidable via list equality. -/
def IsBalanced (w : List AB) : Prop :=
  w = List.replicate (w.length / 2) AB.a ++ List.replicate (w.length / 2) AB.b

instance : DecidablePred IsBalanced := fun _ => decEq _ _

/-- The classical non-regular language `{ aⁿ bⁿ | n ≥ 0 }`, packaged as
a `Language AB`. -/
def balancedAB : Language AB := { w | IsBalanced w }

@[simp] lemma mem_balancedAB (w : List AB) :
    w ∈ balancedAB ↔ IsBalanced w := Iff.rfl

/-- The witness side: `aⁿ ++ bⁿ` is balanced. The forward direction of
the language description, packaged for use in the Myhill–Nerode
distinguishing-prefix argument. -/
lemma replicate_a_append_replicate_b_isBalanced (n : ℕ) :
    IsBalanced (List.replicate n AB.a ++ List.replicate n AB.b) := by
  unfold IsBalanced
  have hlen :
      (List.replicate n AB.a ++ List.replicate n AB.b).length = 2 * n := by
    simp [List.length_append, List.length_replicate, two_mul]
  rw [hlen]
  congr 2 <;> omega

/-- The anti-witness side: `aᵐ ++ bⁿ` with `m ≠ n` is *not* balanced.
The proof counts `a`s and `b`s on both sides of the supposed balanced
decomposition. -/
lemma replicate_a_append_replicate_b_not_isBalanced
    {m n : ℕ} (hmn : m ≠ n) :
    ¬ IsBalanced (List.replicate m AB.a ++ List.replicate n AB.b) := by
  intro heq
  unfold IsBalanced at heq
  set k := (List.replicate m AB.a ++ List.replicate n AB.b).length / 2 with hk
  have hcount_a :
      List.count AB.a (List.replicate m AB.a ++ List.replicate n AB.b) =
      List.count AB.a (List.replicate k AB.a ++ List.replicate k AB.b) := by
    rw [heq]
  have hcount_b :
      List.count AB.b (List.replicate m AB.a ++ List.replicate n AB.b) =
      List.count AB.b (List.replicate k AB.a ++ List.replicate k AB.b) := by
    rw [heq]
  simp [List.count_append, List.count_replicate] at hcount_a hcount_b
  exact hmn (hcount_a.trans hcount_b.symm)

/-- The Myhill–Nerode separation: for `m ≠ n`, the test word `bⁿ` is in
`leftQuotient balancedAB (replicate n a)` but not in
`leftQuotient balancedAB (replicate m a)`. Hence the two left quotients
differ, and the map `n ↦ balancedAB.leftQuotient (replicate n a)` is
injective. -/
lemma leftQuotient_replicate_a_injective :
    Function.Injective fun n : ℕ =>
      balancedAB.leftQuotient (List.replicate n AB.a) := by
  intro m n hmn
  by_contra hne
  have hin : List.replicate n AB.b ∈
      balancedAB.leftQuotient (List.replicate n AB.a) :=
    replicate_a_append_replicate_b_isBalanced n
  have hout : List.replicate n AB.b ∉
      balancedAB.leftQuotient (List.replicate m AB.a) :=
    replicate_a_append_replicate_b_not_isBalanced hne
  have hmn' : balancedAB.leftQuotient (List.replicate m AB.a) =
              balancedAB.leftQuotient (List.replicate n AB.a) := hmn
  exact hout (hmn'.symm ▸ hin)

/-- **`{ aⁿ bⁿ }` is not regular**. Classical Myhill–Nerode argument:
the left quotients by `aⁿ` for distinct `n` are all distinct, so
`Set.range balancedAB.leftQuotient` is infinite, contradicting
`Language.IsRegular.finite_range_leftQuotient`. -/
theorem balancedAB_not_isRegular : ¬ balancedAB.IsRegular := by
  intro h
  have hfin := h.finite_range_leftQuotient
  have hinf : (Set.range balancedAB.leftQuotient).Infinite :=
    Set.infinite_of_injective_forall_mem
      leftQuotient_replicate_a_injective
      (fun _ => Set.mem_range_self _)
  exact hinf hfin
