/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Theories.Phonology.Subregular.ForbidPairs
import Mathlib.Computability.MyhillNerode

/-!
# OT–Subregular Bridge: Bound and Counterexample

A `NamedConstraint`'s zero-set — `{ w | c.eval w = 0 }` — sometimes lands
in a subregular class (TSL_2, SP_2, …) and sometimes does not. This file
makes the bound visible:

1. **Existing bridges, in zero-set form**: every `mkForbidPairsOnTier`
   constraint has a TSL_2 zero-set (`mkForbidPairsOnTier_zeroSet_eq`).
   Restatement of `mkForbidPairsOnTier_zero_iff_in_lang` in `Language α`
   form so it composes with mathlib's `Language.IsRegular`.

2. **Supraregular counterexample**: there is a `NamedConstraint (List AB)`
   whose zero-set is the classical non-regular language `{ aⁿ bⁿ | n ≥ 0 }`
   (`exists_namedConstraint_zeroSet_not_isRegular`). Shows the bridge
   cannot be stated as "every NamedConstraint has a subregular zero-set"
   — only constraints in specific schema classes (forbidden-pair on
   tier, OCP on tier, agree on tier, …) inherit the bridge.

The argument for non-regularity uses mathlib's
`Language.IsRegular.finite_range_leftQuotient`: distinct prefixes `aⁿ`
give distinct left quotients of `{ aⁿ bⁿ }`, so the range of
`leftQuotient` is infinite, contradicting regularity. This is the
classical Myhill–Nerode argument @cite{nerode-1958} @cite{myhill-1957}.

Phonologically the takeaway is *negative*: `NamedConstraint`s are too
expressive to be classified by subregular complexity alone. Phonologists
who want a subregular guarantee on their constraint set must restrict to
one of the schema-specific constructors with a known bridge —
`mkForbidPairsOnTier`, `mkOCPOnTier`, `mkAgreeOnTier`,
`mkForbidSingletonOnTier`. The `mkMarkGrad` escape hatch (arbitrary
violation count) admits supraregular constraints.

This file is the OT-side dual of the existing class-specific bridges in
`Phonology/Subregular/ForbidPairs.lean`, `OCP.lean`, `Agree.lean`. The
positive bridges show *which* constraint constructors land inside
TSL_2; this file shows *that* the OT vocabulary is broader than the
subregular hierarchy.
-/

-- ============================================================================
-- § 1. (NamedConstraint zero-set API moved to Core/Constraint/OT/Basic.lean
--       in PR-7d to make it visible to non-phonology consumers.)
-- ============================================================================

namespace Phonology.Subregular.OTBound

open Phonology.Constraints
open Core Core.Computability.Subregular
open Core.Constraint.OT (NamedConstraint mkMarkGrad)

-- ============================================================================
-- § 2. Existing bridges, restated in zero-set form
-- ============================================================================

variable {α : Type}

/-- **Zero-set bridge** (forbidden-pair on tier): the zero-set of a
forbidden-pair markedness constraint *is* the language of the
corresponding TSL_2 grammar. Restatement of
`mkForbidPairsOnTier_zero_iff_in_lang` (with `extract := id`) in
`Language α` form so downstream regularity arguments can use the
zero-set side directly. -/
theorem mkForbidPairsOnTier_zeroSet_eq
    (name : String) (R : α → α → Prop) [DecidableRel R]
    (p : α → Prop) [DecidablePred p] :
    (mkForbidPairsOnTier name R (Tier.byClass p) (id : List α → List α)).zeroSet =
      (TSLGrammar.ofForbiddenPairs R p).lang := by
  ext w
  exact mkForbidPairsOnTier_zero_iff_in_lang name R p id w

-- ============================================================================
-- § 3. Supraregular counterexample: `{ aⁿ bⁿ | n ≥ 0 }`
-- ============================================================================

/-- The 2-letter alphabet `{a, b}` over which the classical non-regular
language `{ aⁿ bⁿ }` is defined. -/
inductive AB | a | b
  deriving DecidableEq, Repr

/-- Decidable equality is enough for `Fintype` here; the type has only two
inhabitants. -/
instance : Fintype AB :=
  ⟨{AB.a, AB.b}, fun x => by cases x <;> decide⟩

/-- A word over `AB` is *balanced* iff it consists of `n` copies of `a`
followed by `n` copies of `b`, where `n = w.length / 2`. The total
length of any balanced word is `2 n`, so the count is recoverable from
the length and the equation is decidable. -/
def IsBalanced (w : List AB) : Prop :=
  w = List.replicate (w.length / 2) AB.a ++ List.replicate (w.length / 2) AB.b

instance : DecidablePred IsBalanced := fun _ => decEq _ _

/-- The classical non-regular language `{ aⁿ bⁿ | n ≥ 0 }`, packaged as a
`Language AB`. -/
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

/-- The anti-witness side: `aᵐ ++ bⁿ` with `m ≠ n` is *not* balanced. The
proof counts `a`s and `b`s on both sides of the supposed balanced
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
  -- After simp: hcount_a : m = k, hcount_b : n = k
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
  -- The separator `replicate n .b` distinguishes the two quotients.
  have hin : List.replicate n AB.b ∈
      balancedAB.leftQuotient (List.replicate n AB.a) :=
    replicate_a_append_replicate_b_isBalanced n
  have hout : List.replicate n AB.b ∉
      balancedAB.leftQuotient (List.replicate m AB.a) :=
    replicate_a_append_replicate_b_not_isBalanced hne
  -- Beta-reduce hmn to the plain quotient equality.
  have hmn' : balancedAB.leftQuotient (List.replicate m AB.a) =
              balancedAB.leftQuotient (List.replicate n AB.a) := hmn
  exact hout (hmn'.symm ▸ hin)

/-- **`{ aⁿ bⁿ }` is not regular**. Classical Myhill–Nerode argument: the
left quotients by `aⁿ` for distinct `n` are all distinct, so
`Set.range balancedAB.leftQuotient` is infinite, contradicting
`Language.IsRegular.finite_range_leftQuotient`. -/
theorem balancedAB_not_isRegular : ¬ balancedAB.IsRegular := by
  intro h
  have hfin := h.finite_range_leftQuotient
  have hinf : (Set.range balancedAB.leftQuotient).Infinite :=
    Set.infinite_of_injective_forall_mem
      leftQuotient_replicate_a_injective
      (fun n => Set.mem_range_self _)
  exact hinf hfin

-- ============================================================================
-- § 4. Headline existence theorem
-- ============================================================================

/-- The supraregular `NamedConstraint`: violates iff the candidate is not
balanced. Built via `mkMarkGrad` (the escape-hatch constructor that
admits arbitrary `Nat`-valued violation counts) — *not* via any of the
schema constructors with a TSL_k/SP_k/BTC bridge. -/
def supraregularConstraint : NamedConstraint (List AB) :=
  mkMarkGrad "BAL" (fun w => if IsBalanced w then 0 else 1)

@[simp] lemma supraregularConstraint_eval (w : List AB) :
    supraregularConstraint.eval w = if IsBalanced w then 0 else 1 := rfl

/-- The zero-set of `supraregularConstraint` is exactly `balancedAB` —
the classical non-regular `{ aⁿ bⁿ }`. -/
theorem supraregularConstraint_zeroSet :
    supraregularConstraint.zeroSet = balancedAB := by
  ext w
  show supraregularConstraint.eval w = 0 ↔ IsBalanced w
  rw [supraregularConstraint_eval]
  by_cases h : IsBalanced w <;> simp [h]

/-- **Headline**: there exists a `NamedConstraint` whose zero-set is not
regular. The OT→subregular bridge cannot be stated as "every
NamedConstraint has a subregular zero-set" — class-specific schema
restrictions are necessary. The witness is built via the
`mkMarkGrad` escape hatch with a `{ aⁿ bⁿ }`-membership predicate as
the violation count. -/
theorem exists_namedConstraint_zeroSet_not_isRegular :
    ∃ c : NamedConstraint (List AB), ¬ c.zeroSet.IsRegular := by
  refine ⟨supraregularConstraint, ?_⟩
  rw [supraregularConstraint_zeroSet]
  exact balancedAB_not_isRegular

end Phonology.Subregular.OTBound
