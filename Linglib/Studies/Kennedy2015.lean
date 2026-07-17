import Linglib.Semantics.Quantification.Numerals.Basic
import Linglib.Semantics.Entailment.AsymStronger
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# [kennedy-2015]: De-Fregean numerals — neo-Gricean derivation
[kennedy-2015] [sauerland-2004] [nouwen-2010]
[geurts-nouwen-2007] [frank-goodman-2012] [franke-2011]

[kennedy-2015] replaces the Horn scale `⟨1, 2, 3, …⟩` with a single
**lexically-grouped alternative set** containing the bare numeral together
with all of its surface modifications:

```
  ALT(n) = {bare n, more than n, fewer than n, at least n, at most n}
```

The point is **anti-Horn-scale**: there is no fixed scale direction. The
asymmetric-entailment filter of [sauerland-2004]'s primary-implicature
operator does the work that a pre-categorized "lower" or "upper" scale
would otherwise do. Asserting "at least n" makes only the lower-direction
alternatives (bare n, more than n) asymmetrically stronger; the
upper-direction alternatives (fewer than n, at most n) are not — they're
disjoint or overlapping but not subsets — so they don't trigger primary
implicatures. The Class A / Class B distinction (labels from
[nouwen-2010], which [kennedy-2015] *contests* by replacing
Nouwen's lexical bifurcation with one denotation + asymmetric entailment)
falls out as a structural property of the modifier's relation:

- **Class B (`≥`, `≤`)** — the bare numeral is asymmetrically stronger
  than the asserted form (and so is the strict modifier on the same
  side); two primary implicatures, hence ignorance.
- **Class A (`>`, `<`)** — *no* alternative in the full set is
  asymmetrically stronger than the asserted form; no primary implicature.

We formalize both routes:

- §2 derives the predictions **symbolically** via `asymStrongerOn`
  (the polymorphic primitive from
  `Semantics/Entailment/AsymStronger.lean`).
- §3 derives the same direction probabilistically through RSA L1.

§3 is our own integration contribution, not Kennedy's — Kennedy's paper
discusses [franke-2011]'s IBR as the probabilistic counterpart, not
[frank-goodman-2012]-style RSA. The two routes are theoretically
distinct: §2 follows Kennedy directly; §3 shows the same qualitative
predictions emerge from a soft-max listener over the same alternative set
and bare-numeral semantics.

The formalization consumes `Numeral.Entry.denoteUnder` from
`Semantics/Numerals/Basic.lean` directly — there is no separate
"Kennedy meaning" function (Kennedy's alternative set is *which* numeral
words to consider, not *what they mean*).

Domain: cardinality 0–5 (`Fin 6`, wide enough that Class A "more than 3"
needs `w = 4` to be non-trivial).
-/

namespace Kennedy2015

open Semantics.Numerals
open Entailment (asymStrongerOn)

-- ============================================================================
-- §1: Cardinality worlds and Kennedy's single alternative set
-- ============================================================================

/-- Cardinality worlds 0–5. We use `Fin 6` directly: `decide` runs over
    the type-class-derived `Fintype`, and the six-element domain is wide
    enough that Class A "more than 3" needs `w = 4` to be non-trivial. -/
abbrev KCard : Type := Fin 6

/-- Kennedy's alternative set members for `n = 3`. One enum unifying
    bare and all four modifications — Class A vs Class B is read off
    asymmetric-entailment, not from membership in a pre-split sublist.
    The RSA analysis lives in `Kennedy2015PMF`. -/
inductive KUtt where
  | bare3 | moreThan3 | fewerThan3 | atLeast3 | atMost3
  deriving DecidableEq, Repr, Fintype

/-- The numeral word (`Numeral.Entry`) a Kennedy alternative is — all at
    argument 3, with their surface forms. -/
def KUtt.entry : KUtt → Numeral.Entry
  | .bare3      => ⟨"three", .eq, 3⟩
  | .moreThan3  => ⟨"more than three", .gt, 3⟩
  | .fewerThan3 => ⟨"fewer than three", .lt, 3⟩
  | .atLeast3   => ⟨"at least three", .ge, 3⟩
  | .atMost3    => ⟨"at most three", .le, 3⟩

/-- Prop-valued meaning of any Kennedy alternative under bilateral (exact) bare
    semantics — `Numeral.Entry.denoteUnder` with `bare := bareMeaning`. -/
def kMean (u : KUtt) (w : KCard) : Prop :=
  u.entry.denoteUnder bareMeaning w.val

noncomputable instance (u : KUtt) : DecidablePred (kMean u) :=
  fun w => inferInstanceAs (Decidable (u.entry.denoteUnder bareMeaning w.val))

-- ============================================================================
-- §2: Symbolic neo-Gricean derivation ([sauerland-2004] on Kennedy's alts)
-- ============================================================================

/-! Sauerland's primary-implicature schema applied to Kennedy's single
alternative set distinguishes Class A from Class B with no probability:

For asserted φ and alternative set ALT, the primary implicatures are
`{¬Kψ | ψ ∈ ALT, ψ asymmetrically entails φ over the speaker's worlds}`.

Over the six-world domain, the meanings at `n = 3` are:

| Expr             | True at        |
|------------------|----------------|
| `bare 3`         | `{3}`          |
| `more than 3`    | `{4, 5}`       |
| `fewer than 3`   | `{0, 1, 2}`    |
| `at least 3`     | `{3, 4, 5}`    |
| `at most 3`      | `{0, 1, 2, 3}` |

Asserting "at least 3": `bare 3 ⊊ at least 3` and `more than 3 ⊊
at least 3` — both asymmetrically stronger. The upper-direction
alternatives `fewer than 3` and `at most 3` are not subsets (the former
is disjoint, the latter overlaps but extends below). So 2 primary
implicatures fire.

Asserting "more than 3": `bare 3` is *disjoint* (rules out subset
relation in either direction); `at least 3` is a *weaker* alternative
(superset, not subset); `at most 3` and `fewer than 3` are also not
subsets. So 0 primary implicatures fire — exactly Kennedy's Class A
prediction.

The alternative set is `Finset.univ : Finset KUtt` (all 5 KUtt
constructors); the world domain is `Finset.univ : Finset KCard` (Fin 6
via Fintype). -/

/-- **Class B (lower-bound) triggers two primary implicatures**.
    Asserting "at least 3" makes both "bare 3" and "more than 3"
    asymmetrically stronger over the six-world domain; the
    upper-direction alternatives are not. -/
theorem classB_atLeast3_two_primary :
    (Finset.univ.filter
      (fun u : KUtt => asymStrongerOn Finset.univ (kMean u) (kMean .atLeast3))).card
      = 2 := by
  decide

/-- **Class A (lower-bound) triggers no primary implicatures**.
    Asserting "more than 3" makes *no* alternative in Kennedy's full
    set — neither bare-direction nor cross-direction — asymmetrically
    stronger. -/
theorem classA_moreThan3_no_primary :
    (Finset.univ.filter
      (fun u : KUtt => asymStrongerOn Finset.univ (kMean u) (kMean .moreThan3))).card
      = 0 := by
  decide

/-- Mirror image: **Class B (upper-bound) triggers two primary implicatures**. -/
theorem classB_atMost3_two_primary :
    (Finset.univ.filter
      (fun u : KUtt => asymStrongerOn Finset.univ (kMean u) (kMean .atMost3))).card
      = 2 := by
  decide

/-- Mirror image: **Class A (upper-bound) triggers no primary implicatures**. -/
theorem classA_fewerThan3_no_primary :
    (Finset.univ.filter
      (fun u : KUtt => asymStrongerOn Finset.univ (kMean u) (kMean .fewerThan3))).card
      = 0 := by
  decide

end Kennedy2015
