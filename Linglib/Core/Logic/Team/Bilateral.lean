import Mathlib.Data.Finset.Basic

/-!
# Bilateral team-semantic evaluation — generic polarity theorems

@cite{anttila-2021} @cite{aloni-2022} @cite{aloni-vanormondt-2023}

The bilateral team-semantic pattern shared by BSML, QBSML, and (in principle)
truthmaker semantics: a formula is evaluated against (Model, polarity, state)
producing Prop, and negation flips polarity, making Double Negation
Elimination definitional.

This file extracts the **polarity-flip-on-negation** pattern as a parametric
theorem, parameterized over the evaluation function and the negation
constructor. Both BSML and QBSML get DNE for free by instantiating with their
specific eval / negation function.

## Why parametric functions, not a typeclass

A typeclass `BilateralTeamLogic Form Model Point` runs into Lean's typeclass
resolution limitations: with three orthogonal type parameters, projection
calls like `BilateralTeamLogic.negate φ` cannot infer `Model` and `Point`
from `φ : Form` alone, leading to elaboration errors. The parametric-function
approach sidesteps this entirely — caller passes the eval and negation
explicitly (one-time call site), and gets DNE / polarity unfolding generically.

This mirrors mathlib's pattern where pure functions parametrized over an
operator are often preferable to typeclasses when the typeclass has multiple
"essential" parameters that can't be related by `outParam`.

## What this provides

Three generic theorems:

1. `dne_support_of_eval_negate`: `eval pol (negate (negate φ)) ↔ eval pol φ`
2. `support_negate_of_eval_negate`: `eval true (negate φ) ↔ eval false φ`
3. `antiSupport_negate_of_eval_negate`: `eval false (negate φ) ↔ eval true φ`

Each consumer (BSML, QBSML) provides its eval function, its negation
constructor, and a one-line proof that polarity flips on negation
(typically `Iff.rfl` because the eval is defined that way). The three
theorems then specialize.

## Why not extract the bilateral mutual induction PATTERN?

The "joint property: support and antiSupport, prove for both polarities,
extract support side as corollary" pattern that repeats in BSML's and
QBSML's `Properties.lean` is a PROOF TECHNIQUE, not a theorem. It can be
documented (here, in this docstring, and in each consumer) but not
extracted as a Lean theorem — it requires inducting over the formula type,
which is logic-specific.
-/

namespace Core.Logic.Team

variable {Form Model Point : Type*}

-- ============================================================================
-- §1 Generic polarity-flip theorems
-- ============================================================================

/-- **Generic Double Negation Elimination**: given a bilateral evaluation
    function `eval` and a negation constructor `negate` such that negation
    flips polarity, `eval pol (negate (negate φ))` is equivalent to `eval pol φ`.

    Anttila 2021 Fact 6 / Aloni 2022 Fact 6 in the abstract setting. -/
theorem dne_of_polarity_flip
    {eval : Model → Bool → Form → Finset Point → Prop}
    {negate : Form → Form}
    (heval_negate :
      ∀ (M : Model) (pol : Bool) (φ : Form) (s : Finset Point),
        eval M pol (negate φ) s ↔ eval M (!pol) φ s)
    (M : Model) (pol : Bool) (φ : Form) (s : Finset Point) :
    eval M pol (negate (negate φ)) s ↔ eval M pol φ s := by
  rw [heval_negate, heval_negate]
  cases pol <;> simp

/-- **Generic support-of-negation lemma**: support of ¬φ equals anti-support
    of φ. Specializes from `heval_negate` with `pol := true`. -/
theorem support_negate_of_polarity_flip
    {eval : Model → Bool → Form → Finset Point → Prop}
    {negate : Form → Form}
    (heval_negate :
      ∀ (M : Model) (pol : Bool) (φ : Form) (s : Finset Point),
        eval M pol (negate φ) s ↔ eval M (!pol) φ s)
    (M : Model) (φ : Form) (s : Finset Point) :
    eval M true (negate φ) s ↔ eval M false φ s := by
  exact heval_negate M true φ s

/-- **Generic anti-support-of-negation lemma**: anti-support of ¬φ equals
    support of φ. Specializes from `heval_negate` with `pol := false`. -/
theorem antiSupport_negate_of_polarity_flip
    {eval : Model → Bool → Form → Finset Point → Prop}
    {negate : Form → Form}
    (heval_negate :
      ∀ (M : Model) (pol : Bool) (φ : Form) (s : Finset Point),
        eval M pol (negate φ) s ↔ eval M (!pol) φ s)
    (M : Model) (φ : Form) (s : Finset Point) :
    eval M false (negate φ) s ↔ eval M true φ s := by
  exact heval_negate M false φ s

end Core.Logic.Team
