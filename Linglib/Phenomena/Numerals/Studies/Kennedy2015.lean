import Linglib.Theories.Semantics.Numerals.Basic
import Linglib.Theories.Pragmatics.RSA.Basic
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.Implicature.EpistemicBlocking
import Linglib.Theories.Semantics.Entailment.AsymStronger
import Mathlib.Data.Rat.Defs

/-!
# @cite{kennedy-2015}: De-Fregean numerals — neo-Gricean derivation
@cite{kennedy-2015} @cite{sauerland-2004} @cite{nouwen-2010}
@cite{geurts-nouwen-2007} @cite{frank-goodman-2012} @cite{franke-2011}

@cite{kennedy-2015} replaces the Horn scale `⟨1, 2, 3, …⟩` with a single
**lexically-grouped alternative set** containing the bare numeral together
with all of its surface modifications:

```
  ALT(n) = {bare n, more than n, fewer than n, at least n, at most n}
```

The point is **anti-Horn-scale**: there is no fixed scale direction. The
asymmetric-entailment filter of @cite{sauerland-2004}'s primary-implicature
operator does the work that a pre-categorized "lower" or "upper" scale
would otherwise do. Asserting "at least n" makes only the lower-direction
alternatives (bare n, more than n) asymmetrically stronger; the
upper-direction alternatives (fewer than n, at most n) are not — they're
disjoint or overlapping but not subsets — so they don't trigger primary
implicatures. The Class A / Class B distinction (labels from
@cite{nouwen-2010}, which @cite{kennedy-2015} *contests* by replacing
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
  `Theories/Semantics/Entailment/AsymStronger.lean`).
- §3 derives the same direction probabilistically through RSA L1.

§3 is our own integration contribution, not Kennedy's — Kennedy's paper
discusses @cite{franke-2011}'s IBR as the probabilistic counterpart, not
@cite{frank-goodman-2012}-style RSA. The two routes are theoretically
distinct: §2 follows Kennedy directly; §3 shows the same qualitative
predictions emerge from a soft-max listener over the same alternative set
and bare-numeral semantics.

The formalization consumes `NumeralExpr.meaning` from
`Theories/Semantics/Numerals/Basic.lean` directly — there is no separate
"Kennedy meaning" function (Kennedy's alternative set is *which*
`NumeralExpr` values to consider, not *what they mean*).

Domain: cardinality 0–5 (`Fin 6`, wide enough that Class A "more than 3"
needs `w = 4` to be non-trivial).
-/

namespace Kennedy2015

open Semantics.Numerals
open Semantics.Entailment (asymStrongerOn)

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
    The pattern-match `expr` keeps `rsa_predict` reflection cheap. -/
inductive KUtt where
  | bare3 | moreThan3 | fewerThan3 | atLeast3 | atMost3
  deriving DecidableEq, Repr, Fintype

/-- Embed a Kennedy alternative into the unified `NumeralExpr`. -/
def KUtt.expr : KUtt → NumeralExpr
  | .bare3      => .bare 3
  | .moreThan3  => .moreThan 3
  | .fewerThan3 => .fewerThan 3
  | .atLeast3   => .atLeast 3
  | .atMost3    => .atMost 3

/-- Prop-valued meaning of any Kennedy alternative under bilateral
    (exact) bare semantics — derived from `NumeralExpr.meaning bareMeaning`. -/
def kMean (u : KUtt) (w : KCard) : Prop :=
  u.expr.meaning bareMeaning w.val

noncomputable instance (u : KUtt) : DecidablePred (kMean u) :=
  fun w => inferInstanceAs (Decidable (u.expr.meaning bareMeaning w.val))

-- ============================================================================
-- §2: Symbolic neo-Gricean derivation (@cite{sauerland-2004} on Kennedy's alts)
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

-- ============================================================================
-- §3: RSA L1 implementation of the same neo-Gricean predictions
-- ============================================================================

/-! Our own integration contribution (Kennedy uses @cite{franke-2011}'s
IBR, not RSA). A rational L1 listener — assuming the speaker chose the
most informative true alternative — shifts probability mass *away* from
worlds where a stronger alternative would have been chosen. Class B's
at-boundary world is the world a Class B speaker would compete against
the bare alternative for, so probability mass shifts above the boundary;
Class A's asserted form admits no asymmetrically-stronger alternative,
so no competition arises. -/

open RSA Real in
/-- Kennedy's RSA configuration over the single alt-set. One config
    handles both Class A and Class B utterances — the qualitative
    predictions are read off `L1` probabilities on different `KUtt`
    arguments, not from a separate config per direction. -/
noncomputable def kennedyCfg : RSAConfig KUtt KCard where
  Latent := Unit
  meaning _ _ u w := if kMean u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg l0 α _ _ u hl0 _ := rpow_nonneg (hl0 u _) α
  α := 1
  α_pos := one_pos
  worldPrior_nonneg _ := by positivity
  latentPrior_nonneg _ _ := by positivity

/-- Class B competition at the boundary: "bare 3" beats "at least 3" at
    `w = 3`. A speaker who knew exactly 3 would have used the more
    informative "bare 3", so a listener hearing "at least 3" infers
    `w ≥ 4` is more likely. -/
theorem classB_competition_at_boundary :
    kennedyCfg.L1 .bare3 ⟨3, by decide⟩ > kennedyCfg.L1 .atLeast3 ⟨3, by decide⟩ := by
  rsa_predict

/-- Class A excludes the boundary semantically: "more than 3" is false
    at `w = 3`, so `L1(w=4 | "more than 3") > L1(w=3 | "more than 3")`. -/
theorem classA_no_competition_at_boundary :
    kennedyCfg.L1 .moreThan3 ⟨4, by decide⟩ > kennedyCfg.L1 .moreThan3 ⟨3, by decide⟩ := by
  rsa_predict

/-- Bare numeral is peaked under exact semantics:
    `L1("bare 3", w = 3) > L1("bare 3", w = 4)`. -/
theorem bare_peaked_with_kennedy_alternatives :
    kennedyCfg.L1 .bare3 ⟨3, by decide⟩ > kennedyCfg.L1 .bare3 ⟨4, by decide⟩ := by
  rsa_predict

/-- Class B strengthened above bare: hearing "at least 3" pushes
    probability above the boundary. -/
theorem classB_strengthened_above_bare :
    kennedyCfg.L1 .atLeast3 ⟨4, by decide⟩ > kennedyCfg.L1 .atLeast3 ⟨3, by decide⟩ := by
  rsa_predict

/-- Upper Class B competition at the boundary. -/
theorem upper_classB_competition :
    kennedyCfg.L1 .bare3 ⟨3, by decide⟩ > kennedyCfg.L1 .atMost3 ⟨3, by decide⟩ := by
  rsa_predict

/-- Upper Class A excludes the boundary: "fewer than 3" is false at `w = 3`. -/
theorem upper_classA_no_competition :
    kennedyCfg.L1 .fewerThan3 ⟨2, by decide⟩ > kennedyCfg.L1 .fewerThan3 ⟨3, by decide⟩ := by
  rsa_predict

/-- Upper Class B strengthened below bare: hearing "at most 3" pushes
    probability below the boundary (mirror of `classB_strengthened_above_bare`). -/
theorem upper_classB_strengthened_below_bare :
    kennedyCfg.L1 .atMost3 ⟨2, by decide⟩ > kennedyCfg.L1 .atMost3 ⟨3, by decide⟩ := by
  rsa_predict

end Kennedy2015
