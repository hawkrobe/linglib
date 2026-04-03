import Linglib.Core.Logic.ConstraintEvaluation

/-!
# Bidirectional Optimality Theory

@cite{blutner-2000} @cite{horn-1984} @cite{atlas-levinson-1981}

Bidirectional OT integrates production and comprehension optimality into
a single framework. The key insight is that the Gricean maxims decompose
into two opposing optimization pressures:

- **Q-principle** (production optimality): for a given meaning τ, the
  optimal form A is the one that produces ⟨A, τ⟩ most harmonically.
  Blocking mechanism: suppresses interpretations that can be expressed
  more economically by an alternative form. Corresponds to the first
  part of Grice's Quantity maxim ("be as informative as required") and
  the force of diversification / auditor's economy
  (@cite{atlas-levinson-1981}, @cite{horn-1984}).

- **I-principle** (comprehension optimality): for a given form A, the
  optimal meaning τ is the one that produces ⟨A, τ⟩ most harmonically.
  Interpretation mechanism: selects the most coherent/stereotypical
  reading. Corresponds to the second part of Grice's Quantity maxim
  ("do not make your contribution more informative than required"),
  Relation, Manner, and the force of unification / speaker's economy
  (@cite{atlas-levinson-1981}, @cite{horn-1984}'s R-principle).

These correspond to the speaker/hearer optimization layers in RSA
(@cite{frank-goodman-2012}) and IBR (@cite{franke-2011}).

## Strong vs Weak BiOT

@cite{blutner-2000} defines two versions:

- **Strong** (eq. 9): Q and I are independent — ⟨A, τ⟩ is optimal iff
  it survives BOTH Q and I evaluated against the full candidate set.
  Solution concept: Nash Equilibrium.

- **Weak** (eq. 14): Q and I mutually constrain each other — competition
  under Q is restricted to I-surviving pairs, and vice versa.
  Solution concept: greatest fixed point of the blocking operator.

The weak version derives @cite{horn-1984}'s **division of pragmatic
labour**: unmarked forms pair with unmarked (stereotypical) meanings,
and marked forms pair with marked (non-stereotypical) meanings.
The strong version incorrectly predicts that marked forms are blocked
in ALL their interpretations.

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

namespace Theories.Pragmatics.Bidirectional

open Core.ConstraintEvaluation

-- ============================================================================
-- § 1: Q-Principle and I-Principle as Predicates
-- ============================================================================

/-- **Q-principle** (production optimality, @cite{blutner-2000} eq. 9(Q)):
    ⟨A, τ⟩ satisfies Q iff no other pair with the same meaning τ
    but a different form A' is strictly more harmonic.

    Operationally: the speaker chose A because it is the best way
    to express τ. If a better form A' existed, A would be blocked.
    This is the blocking mechanism — it suppresses interpretations
    that can be triggered more economically by an alternative form
    (@cite{horn-1984}'s Q-based implicature). -/
def satisfiesQ {F M : Type} [BEq F] [BEq M]
    (gen : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) : Bool :=
  !gen.any (fun q => !(q.1 == p.1) && q.2 == p.2 && lexLT (profile q) (profile p))

/-- **I-principle** (comprehension optimality, @cite{blutner-2000} eq. 9(I)):
    ⟨A, τ⟩ satisfies I iff no other pair with the same form A
    but a different meaning τ' is strictly more harmonic.

    Operationally: the hearer chose τ because it is the best
    interpretation of A. If a better meaning τ' existed, τ would
    be dispreferred. This is the interpretation mechanism — it
    selects the most coherent/stereotypical reading
    (@cite{horn-1984}'s R-based inference). -/
def satisfiesI {F M : Type} [BEq F] [BEq M]
    (gen : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) : Bool :=
  !gen.any (fun q => q.1 == p.1 && !(q.2 == p.2) && lexLT (profile q) (profile p))

/-- Strong-optimal = satisfies BOTH Q and I against the full candidate set.
    This is equivalent to `strongOptimal` in `ConstraintEvaluation`. -/
theorem strongOptimal_eq_both {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat) :
    strongOptimal pairs profile =
    pairs.filter (fun p => satisfiesQ pairs profile p && satisfiesI pairs profile p) := by
  simp only [strongOptimal, satisfiesQ, satisfiesI]

-- ============================================================================
-- § 2: Horn's Division of Pragmatic Labour
-- ============================================================================

/-! @cite{horn-1984}'s division of pragmatic labour: "unmarked forms tend
    to be used for unmarked situations and marked forms for marked
    situations." This emerges naturally from weak BiOT but NOT from
    strong BiOT. The example below formalizes @cite{blutner-2000}'s
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
def hornPairs : List (HornForm × HornMeaning) :=
  [(.unmarked, .stereotypical), (.unmarked, .nonStereotypical),
   (.marked, .stereotypical),   (.marked, .nonStereotypical)]

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
      [(.unmarked, .stereotypical), (.marked, .nonStereotypical)] := by
  native_decide

/-- **Strong BiOT** blocks the marked form entirely — only the
    unmarked pair survives. This is empirically wrong: marked forms
    DO get used (for marked meanings). -/
theorem horn_strong_biot :
    strongOptimal hornPairs hornProfile =
      [(.unmarked, .stereotypical)] := by
  native_decide

/-- The weak version admits strictly MORE pairs than the strong version
    for this case. This is the key empirical argument for weak BiOT. -/
theorem weak_strictly_larger :
    (superoptimal hornPairs hornProfile).length >
    (strongOptimal hornPairs hornProfile).length := by
  native_decide

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
def totalBlockPairs : List (LexForm × LexMeaning) :=
  [(.listed, .specialized),
   (.derived, .specialized), (.derived, .general)]

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
      [(.listed, .specialized), (.derived, .general)] := by
  native_decide

/-- Strong BiOT over-blocks: the derived form loses ALL interpretations
    because (.derived, .specialized) is I-better than (.derived, .general)
    under the same form. This makes strong BiOT too aggressive for
    partial blocking — only the listed form survives. -/
theorem total_blocking_strong :
    strongOptimal totalBlockPairs totalBlockProfile =
      [(.listed, .specialized)] := by
  native_decide

/-- Weak BiOT correctly handles partial blocking — the derived form
    keeps the general meaning because its I-competitor (.derived, .specialized)
    was removed by Q-blocking from (.listed, .specialized). -/
theorem total_blocking_weak_vs_strong :
    (superoptimal totalBlockPairs totalBlockProfile).length >
    (strongOptimal totalBlockPairs totalBlockProfile).length := by
  native_decide

-- ============================================================================
-- § 4: Properties
-- ============================================================================

/-- Every strong-optimal pair satisfies Q against the full set. -/
theorem strongOptimal_satisfies_Q {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) (hp : p ∈ strongOptimal pairs profile) :
    satisfiesQ pairs profile p = true := by
  simp only [strongOptimal, List.mem_filter] at hp
  simp only [satisfiesQ]
  exact Bool.and_eq_true_iff.mp hp.2 |>.1

/-- Every strong-optimal pair satisfies I against the full set. -/
theorem strongOptimal_satisfies_I {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) (hp : p ∈ strongOptimal pairs profile) :
    satisfiesI pairs profile p = true := by
  simp only [strongOptimal, List.mem_filter] at hp
  simp only [satisfiesI]
  exact Bool.and_eq_true_iff.mp hp.2 |>.2

/-- `strongOptimal` membership implies not blocked by the full pair set.
    This is the key step: the two independent checks in `strongOptimal`
    (no Q-blocker, no I-blocker) together cover the disjunction checked
    by `blocked` (Q-blocker ∨ I-blocker). -/
private theorem blocked_false_of_strongOptimal_aux {F M : Type} [BEq F] [BEq M]
    (profile : F × M → List Nat) (p : F × M)
    : (l : List (F × M)) →
    l.any (fun q => !(q.1 == p.1) && q.2 == p.2 && lexLT (profile q) (profile p)) = false →
    l.any (fun q => q.1 == p.1 && !(q.2 == p.2) && lexLT (profile q) (profile p)) = false →
    l.any (fun q => ((q.1 == p.1 && !(q.2 == p.2)) || (!(q.1 == p.1) && q.2 == p.2)) &&
      lexLT (profile q) (profile p)) = false
  | [], _, _ => rfl
  | q :: qs, hQ, hI => by
    simp only [List.any_cons] at *
    cases h1 : (q.1 == p.1) <;> cases h2 : (q.2 == p.2) <;>
      simp_all [blocked_false_of_strongOptimal_aux profile p qs]

theorem strongOptimal_not_blocked {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) (hp : p ∈ strongOptimal pairs profile) :
    blocked profile pairs p = false := by
  simp only [strongOptimal, List.mem_filter] at hp
  obtain ⟨_, hp2⟩ := hp
  have ⟨hQ, hI⟩ := Bool.and_eq_true_iff.mp hp2
  rw [Bool.not_eq_true'] at hQ hI
  exact blocked_false_of_strongOptimal_aux profile p pairs hQ hI

/-- @cite{blutner-2000} p. 12: "It is simple to prove that a pair which
    is optimal (strong bidirection), is super-optimal (weak bidirection)
    as well." Strong-optimal is a subset of super-optimal. -/
theorem strong_subset_weak {F M : Type} [BEq F] [BEq M]
    (pairs : List (F × M)) (profile : F × M → List Nat)
    (p : F × M) (hp : p ∈ strongOptimal pairs profile) :
    p ∈ superoptimal pairs profile := by
  have hm : p ∈ pairs := (List.mem_filter.mp hp).1
  have hnb := strongOptimal_not_blocked pairs profile p hp
  exact superoptimal_of_unblocked pairs profile p hm hnb

/-- Horn's division demonstrates strong ⊂ weak (strict inclusion):
    the marked pair survives weak but not strong BiOT. -/
theorem strong_strict_subset_weak_horn :
    (strongOptimal hornPairs hornProfile).length <
    (superoptimal hornPairs hornProfile).length := by
  native_decide

/-- The iterative-removal algorithm (`iterativeSuperoptimal`) agrees with
    strong BiOT for Horn's division. This shows that iterative removal
    over-removes: it behaves like the strong version (eq. 9), not
    the weak version (eq. 14). -/
theorem iterative_eq_strong_horn :
    iterativeSuperoptimal hornPairs hornProfile =
    strongOptimal hornPairs hornProfile := by
  native_decide

/-- The iterative-removal algorithm agrees with strong BiOT for
    total blocking as well. -/
theorem iterative_eq_strong_totalBlock :
    iterativeSuperoptimal totalBlockPairs totalBlockProfile =
    strongOptimal totalBlockPairs totalBlockProfile := by
  native_decide

end Theories.Pragmatics.Bidirectional
