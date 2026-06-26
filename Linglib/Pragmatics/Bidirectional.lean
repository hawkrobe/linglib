import Linglib.Core.Optimization.Evaluation
import Linglib.Pragmatics.Superoptimal

/-!
# Bidirectional Optimality Theory

[blutner-2000] [horn-1984] [atlas-levinson-1981]

Bidirectional OT integrates production and comprehension optimality into
a single framework. The key insight is that the Gricean maxims decompose
into two opposing optimization pressures:

- **Q-principle** (production optimality): for a given meaning τ, the
  optimal form A is the one that produces ⟨A, τ⟩ most harmonically.
  Blocking mechanism: suppresses interpretations that can be expressed
  more economically by an alternative form. Corresponds to the first
  part of Grice's Quantity maxim ("be as informative as required") and
  the force of diversification / auditor's economy
  ([atlas-levinson-1981], [horn-1984]).

- **I-principle** (comprehension optimality): for a given form A, the
  optimal meaning τ is the one that produces ⟨A, τ⟩ most harmonically.
  Interpretation mechanism: selects the most coherent/stereotypical
  reading. Corresponds to the second part of Grice's Quantity maxim
  ("do not make your contribution more informative than required"),
  Relation, Manner, and the force of unification / speaker's economy
  ([atlas-levinson-1981], [horn-1984]'s R-principle).

These correspond to the speaker/hearer optimization layers in RSA
([frank-goodman-2012]) and IBR ([franke-2011]).

## Strong vs Weak BiOT

[blutner-2000] defines two versions:

- **Strong** (eq. 9): Q and I are independent — ⟨A, τ⟩ is optimal iff
  it survives BOTH Q and I evaluated against the full candidate set.
  Solution concept: Nash Equilibrium. Substrate: `strongOptimal`
  (Finset, computable) + `IsStrongOptimal` (Set-valued Prop).

- **Weak** (eq. 14): Q and I mutually constrain each other — competition
  under Q is restricted to I-surviving pairs, and vice versa.
  Solution concept: greatest fixed point of the blocking operator.
  Substrate: `superoptimal` (Finset, computable) + `superoptimalSet`
  (Set-valued, anchored in mathlib's `OrderHom.gfp`).

The weak version derives [horn-1984]'s **division of pragmatic
labour**: unmarked forms pair with unmarked (stereotypical) meanings,
and marked forms pair with marked (marked) meanings. The strong
version incorrectly predicts that marked forms are blocked in ALL
their interpretations.

The structural meta-theorem `strong ⊂ weak` ([blutner-2000] p. 12)
lives in `Phonology/Constraint/Superoptimal.lean` as
`isStrongOptimal_imp_mem_superoptimalSet` (Set-valued, coinductive
proof against `OrderHom.gfp`) and its Finset corollary
`strongOptimal_subset_superoptimal`.

## Connection to RSA and IBR

All three frameworks — BiOT, IBR, RSA — perform alternating
speaker/hearer optimization. They differ in the optimization criterion:

| Framework | Comparison | Solution |
|-----------|-----------|----------|
| Strong BiOT | lexicographic (OT) | Nash equilibrium |
| Weak BiOT | lexicographic (OT) | greatest fixed point |
| IBR | argmax (set-level) | iterated best response |
| RSA | softmax (probabilistic) | Bayesian posterior |

The relationship: RSA α→∞ approximates IBR, and IBR fixed points
correspond to weak-BiOT super-optimal pairs for scalar games
(see `IBR/ScalarGames.lean`).
-/

set_option autoImplicit false

namespace Pragmatics.Bidirectional

open Core.Optimization.Evaluation

-- ============================================================================
-- § 1: Q-Principle and I-Principle as Bool Predicates (List-based, decidable)
-- ============================================================================

/-! These are List-Bool versions of the per-pair Q and I checks, used by
    consumer studies (e.g. `Blutner2000.lean`'s `accommodation_blocked_is_Q`)
    that want to check Q or I in isolation rather than the conjunction. The
    relationship to the substrate's Set-valued `Blocks` predicate:

    `¬ Blocks profile S p ↔ (no Q-blocker in S for p) ∧ (no I-blocker in S for p)`

    where Q-blocker = same meaning, different form; I-blocker = same form,
    different meaning. So `satisfiesQ` and `satisfiesI` together pin down the
    `¬ Blocks` condition that defines `IsStrongOptimal` and (via the gfp)
    `superoptimalSet`. -/

/-- **Q-principle** (production optimality, [blutner-2000] eq. 9(Q)):
    ⟨A, τ⟩ satisfies Q iff no other pair with the same meaning τ
    but a different form A' is strictly more harmonic.

    Operationally: the speaker chose A because it is the best way
    to express τ. If a better form A' existed, A would be blocked.
    This is the blocking mechanism — it suppresses interpretations
    that can be triggered more economically by an alternative form
    ([horn-1984]'s Q-based implicature). -/
def satisfiesQ {F M : Type} [DecidableEq F] [DecidableEq M]
    (gen : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) : Bool :=
  gen.all fun q =>
    decide (q.2 = p.2 → q.1 ≠ p.1 → ¬LexLT (profile q) (profile p))

/-- **I-principle** (comprehension optimality, [blutner-2000] eq. 9(I)):
    ⟨A, τ⟩ satisfies I iff no other pair with the same form A
    but a different meaning τ' is strictly more harmonic.

    Operationally: the hearer chose τ because it is the best
    interpretation of A. If a better meaning τ' existed, τ would
    be dispreferred. This is the interpretation mechanism — it
    selects the most coherent/stereotypical reading
    ([horn-1984]'s R-based inference). -/
def satisfiesI {F M : Type} [DecidableEq F] [DecidableEq M]
    (gen : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) : Bool :=
  gen.all fun q =>
    decide (q.1 = p.1 → q.2 ≠ p.2 → ¬LexLT (profile q) (profile p))

-- ============================================================================
-- § 2: Horn's Division of Pragmatic Labour
-- ============================================================================

/-! [horn-1984]'s division of pragmatic labour: "unmarked forms tend
    to be used for unmarked situations and marked forms for marked
    situations." This emerges naturally from weak BiOT but NOT from
    strong BiOT. The example below formalizes [blutner-2000]'s
    tableau (15).

    Classic examples:
    - kill (unmarked) / cause to die (marked): kill ↔ stereotypical
      causation (direct), cause to die ↔ non-stereotypical (indirect)
    - pork (unmarked) / pig-meat (marked, blocked): pork ↔ meat reading,
      pig ↔ animal reading — *pig-meat is totally blocked because pork
      exists
    - him (unmarked) / himself (marked): himself ↔ coreferential,
      him ↔ disjoint reference -/

/-- Forms in Horn's division example. -/
inductive HornForm where
  | unmarked  -- e.g., "kill", "him"
  | marked    -- e.g., "cause to die", "himself"
  deriving DecidableEq, Repr

/-- Meanings in Horn's division example. -/
inductive HornMeaning where
  | stereotypical     -- e.g., direct causation, disjoint reference
  | nonStereotypical  -- e.g., indirect causation, coreferential
  deriving DecidableEq, Repr

/-- All form-meaning pairs (forms are semantically equivalent). -/
def hornPairs : Finset (HornForm × HornMeaning) :=
  { (.unmarked, .stereotypical), (.unmarked, .nonStereotypical),
    (.marked, .stereotypical),   (.marked, .nonStereotypical) }

/-- Constraint profile: [F-violations, C-violations].
    F penalizes marked forms; C penalizes non-stereotypical meanings. -/
def hornProfile : HornForm × HornMeaning → List Nat
  | (.unmarked, .stereotypical)    => [0, 0]
  | (.unmarked, .nonStereotypical) => [0, 1]
  | (.marked,   .stereotypical)    => [1, 0]
  | (.marked,   .nonStereotypical) => [1, 1]

/-- **Weak BiOT** derives Horn's division: unmarked ↔ stereotypical,
    marked ↔ non-stereotypical. Both pairs survive. -/
theorem horn_weak_biot :
    superoptimal hornPairs hornProfile =
      ({(.unmarked, .stereotypical), (.marked, .nonStereotypical)} :
        Finset (HornForm × HornMeaning)) := by
  decide

/-- **Strong BiOT** blocks the marked form entirely — only the
    unmarked pair survives. This is empirically wrong: marked forms
    DO get used (for marked meanings). -/
theorem horn_strong_biot :
    strongOptimal hornPairs hornProfile =
      ({(.unmarked, .stereotypical)} : Finset (HornForm × HornMeaning)) := by
  decide

/-- The weak version admits strictly MORE pairs than the strong version
    for this case. This is the key empirical argument for weak BiOT. -/
theorem weak_strictly_larger :
    (strongOptimal hornPairs hornProfile).card <
    (superoptimal hornPairs hornProfile).card := by
  decide

-- ============================================================================
-- § 3: Total Blocking (Lexical Blocking)
-- ============================================================================

/-! When an unmarked form has a SPECIALIZED meaning (not semantically
    equivalent to the marked form), the marked form can be **totally
    blocked** — it loses ALL its interpretations.

    Example: pork (= pig-meat) blocks *pig in the meat reading.
    Unlike Horn's division, here the unmarked form doesn't compete
    for the non-stereotypical meaning because Gen doesn't pair them. -/

/-- Forms for total blocking: a listed (lexicalized) form and
    a derived (productive) form. -/
inductive LexForm where
  | listed   -- e.g., "pork", "fury"
  | derived  -- e.g., "pig-meat", "furiosity"
  deriving DecidableEq, Repr

/-- Meanings for total blocking. -/
inductive LexMeaning where
  | specialized  -- the meaning covered by the listed form
  | general      -- the broader/derived meaning
  deriving DecidableEq, Repr

/-- Gen for total blocking: the listed form only covers the specialized
    meaning; the derived form covers both meanings. -/
def totalBlockPairs : Finset (LexForm × LexMeaning) :=
  { (.listed, .specialized),
    (.derived, .specialized), (.derived, .general) }

/-- Profile: listed form is less marked (0 F-violations); specialized
    meaning is less marked (0 C-violations). -/
def totalBlockProfile : LexForm × LexMeaning → List Nat
  | (.listed,  .specialized) => [0, 0]
  | (.derived, .specialized) => [1, 0]
  | (.derived, .general)     => [1, 1]
  | (.listed,  .general)     => [0, 1]  -- not in Gen, but need exhaustive match

/-- Total blocking: the derived form loses the specialized meaning
    (blocked by the listed form) but retains the general meaning.
    Result: listed ↔ specialized, derived ↔ general. -/
theorem total_blocking_weak :
    superoptimal totalBlockPairs totalBlockProfile =
      ({(.listed, .specialized), (.derived, .general)} :
        Finset (LexForm × LexMeaning)) := by
  decide

/-- Strong BiOT over-blocks: the derived form loses ALL interpretations
    because (.derived, .specialized) is I-better than (.derived, .general)
    under the same form. This makes strong BiOT too aggressive for
    partial blocking — only the listed form survives. -/
theorem total_blocking_strong :
    strongOptimal totalBlockPairs totalBlockProfile =
      ({(.listed, .specialized)} : Finset (LexForm × LexMeaning)) := by
  decide

/-- Weak BiOT correctly handles partial blocking — the derived form
    keeps the general meaning because its I-competitor (.derived, .specialized)
    was removed by Q-blocking from (.listed, .specialized). -/
theorem total_blocking_weak_vs_strong :
    (strongOptimal totalBlockPairs totalBlockProfile).card <
    (superoptimal totalBlockPairs totalBlockProfile).card := by
  decide

-- ============================================================================
-- § 4: Strong ⊂ Weak — applied to the worked examples
-- ============================================================================

/-! The structural meta-theorem `strongOptimal pairs profile ⊆ superoptimal
    pairs profile` ([blutner-2000] p. 12) is proved coinductively in the
    substrate at `Phonology/Constraint/Superoptimal.lean` via
    `isStrongOptimal_imp_mem_superoptimalSet` (Set-valued, against mathlib's
    `OrderHom.gfp`) and `strongOptimal_subset_superoptimal` (Finset
    corollary using the bridge theorem). The applications below are one-line
    discharges of the convergence hypothesis via `by decide`. -/

/-- Substrate's strong ⊂ weak applied to the Horn example. -/
theorem strong_subset_weak_horn :
    strongOptimal hornPairs hornProfile ⊆
    superoptimal hornPairs hornProfile :=
  strongOptimal_subset_superoptimal hornPairs hornProfile (by decide)

/-- Strict inclusion in the Horn example: weak admits the marked-pair
    that strong eliminates. -/
theorem strong_strict_subset_weak_horn :
    (strongOptimal hornPairs hornProfile).card <
    (superoptimal hornPairs hornProfile).card :=
  weak_strictly_larger

/-- Substrate's strong ⊂ weak applied to total blocking. -/
theorem strong_subset_weak_totalBlock :
    strongOptimal totalBlockPairs totalBlockProfile ⊆
    superoptimal totalBlockPairs totalBlockProfile :=
  strongOptimal_subset_superoptimal totalBlockPairs totalBlockProfile
    (by decide)

end Pragmatics.Bidirectional
