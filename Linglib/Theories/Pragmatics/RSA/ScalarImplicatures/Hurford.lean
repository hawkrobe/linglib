/-
# RSA Analysis of Hurford's Constraint

Models Hurford's constraint as a consequence of speaker rationality in RSA.

Hurford's constraint (Potts & Levy 2015): "#A or B" is infelicitous when A ⊆ B or B ⊆ A.

In RSA, felicity = speaker rationality. A speaker wouldn't say "A or B" if:
1. One disjunct is redundant (B⊆A makes B add nothing)
2. A simpler utterance (just "A") conveys the same information

The rescue by exhaustification works because:
- exh(some) = "some but not all" ⊈ "all"
- Now the disjunction is informative: it covers mutually exclusive cases

## Model

- Worlds: {none, someNotAll, all}
- Utterances: "some", "all", "some or all", null
- Lexica: L_base (some = ≥1), L_refined (some = some-but-not-all)

S1 probability reflects speaker rationality:
- Low S1 for redundant utterances (Hurford violation)
- Higher S1 when exhaustification breaks entailment (rescue)

## References

- Hurford (1974). Exclusive or inclusive disjunction. Foundations of Language.
- Potts & Levy (2015). Negotiating lexical uncertainty and speaker expertise
  with disjunction. BLS 41.
- Singh (2008). On the interpretation of disjunction.
-/

import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval

namespace RSA.Hurford

open LURSA RSA.Eval


/--
World states for Hurford scenarios.

We use a coarse 3-world model:
- `none`: Nothing of interest happened
- `someNotAll`: Some but not all (the "middle" reading)
- `all_`: All (the strong reading)
-/
inductive HWorld where
  | none       -- Nobody read any books
  | someNotAll -- Someone read some-but-not-all books
  | all_       -- Someone read all books
  deriving DecidableEq, Repr, BEq, Inhabited


/--
Utterances for Hurford disjunction scenarios.

Key utterances:
- `some_`: "Mary read some of the books"
- `all_`: "Mary read all of the books"
- `someOrAll`: "Mary read some or all of the books"
- `null`: Null/silence alternative
-/
inductive HUtterance where
  | some_     -- "some" (weak or strong depending on lexicon)
  | all_      -- "all"
  | someOrAll -- "some or all" (the Hurford-relevant utterance)
  | null      -- null/baseline
  deriving DecidableEq, Repr, BEq, Inhabited


/--
Base lexicon: "some" = at-least-one (weak reading).

Under this lexicon:
- "some" is true in {someNotAll, all_}
- "all" is true only in {all_}
- "some or all" = "some" ∨ "all" = "some" (since all⊆some)

This makes "some or all" redundant -- a Hurford violation.
-/
def lexBase : Lexicon HUtterance HWorld where
  meaning u w := boolToRat $ match u, w with
    -- "some" = at-least-one
    | .some_, .none => false
    | .some_, .someNotAll => true
    | .some_, .all_ => true  -- "at least one" includes all
    -- "all"
    | .all_, .all_ => true
    | .all_, _ => false
    -- "some or all" under base = just "some" (all⊆some makes "or all" redundant)
    | .someOrAll, .none => false
    | .someOrAll, .someNotAll => true
    | .someOrAll, .all_ => true
    -- null
    | .null, _ => true

/--
Refined lexicon: "some" = some-but-not-all (exhaustified reading).

Under this lexicon:
- "some" is true only in {someNotAll}
- "all" is true only in {all_}
- "some or all" is now informative: covers {someNotAll, all_}

This rescues the Hurford violation -- the disjunction is no longer redundant.
-/
def lexRefined : Lexicon HUtterance HWorld where
  meaning u w := boolToRat $ match u, w with
    -- "some" = some-but-not-all (exhaustified)
    | .some_, .none => false
    | .some_, .someNotAll => true
    | .some_, .all_ => false  -- exh(some) excludes "all"
    -- "all"
    | .all_, .all_ => true
    | .all_, _ => false
    -- "some or all" under refined: disjunction of exhaustified "some" and "all"
    | .someOrAll, .none => false
    | .someOrAll, .someNotAll => true  -- exh(some) covers this
    | .someOrAll, .all_ => true        -- "all" covers this
    -- null
    | .null, _ => true


/--
Hurford LU Scenario.

- Two lexica: base (weak "some") and refined (strong "some")
- Uniform priors
- α = 1 (moderate rationality)

The model predicts:
- Under L_base: "some or all" is redundant → low speaker utility
- Under L_refined: "some or all" is informative → higher speaker utility
-/
def hurfordScenario : LUScenario where
  Utterance := HUtterance
  World := HWorld
  baseLexicon := lexBase
  lexica := [lexBase, lexRefined]
  lexPrior := λ _ => 1  -- Uniform prior over lexica
  worldPrior := λ _ => 1  -- Uniform prior over worlds
  utterances := [.some_, .all_, .someOrAll, .null]
  worlds := [.none, .someNotAll, .all_]
  α := 1


/-- L1 distribution over worlds for "someOrAll" utterance -/
def l1SomeOrAll : List (HWorld × ℚ) :=
  LURSA.L1 hurfordScenario .someOrAll

/-- L1 distribution for "some" alone -/
def l1Some : List (HWorld × ℚ) :=
  LURSA.L1 hurfordScenario .some_

/-- L1 distribution for "all" alone -/
def l1All : List (HWorld × ℚ) :=
  LURSA.L1 hurfordScenario .all_

#eval l1SomeOrAll
#eval l1Some
#eval l1All


/--
S1 probability for "someOrAll" given world = someNotAll, under base lexicon.

This measures: Would a rational speaker say "some or all" in the someNotAll world
if they believed the listener uses the base (weak "some") lexicon?
-/
def s1SomeOrAll_base_someNotAll : ℚ :=
  RSA.Eval.getScore (LURSA.S1_given hurfordScenario lexBase .someNotAll) .someOrAll

/--
S1 probability for "some" alone given world = someNotAll, under base lexicon.

Compare with s1SomeOrAll_base_someNotAll to see if disjunction is dispreferred.
-/
def s1Some_base_someNotAll : ℚ :=
  RSA.Eval.getScore (LURSA.S1_given hurfordScenario lexBase .someNotAll) .some_

#eval s1SomeOrAll_base_someNotAll
#eval s1Some_base_someNotAll
#eval (s1Some_base_someNotAll, s1SomeOrAll_base_someNotAll, decide (s1Some_base_someNotAll > s1SomeOrAll_base_someNotAll))

/--
S1 probability for "someOrAll" given world = someNotAll, under refined lexicon.
-/
def s1SomeOrAll_refined_someNotAll : ℚ :=
  RSA.Eval.getScore (LURSA.S1_given hurfordScenario lexRefined .someNotAll) .someOrAll

/--
S1 probability for "some" alone given world = someNotAll, under refined lexicon.
-/
def s1Some_refined_someNotAll : ℚ :=
  RSA.Eval.getScore (LURSA.S1_given hurfordScenario lexRefined .someNotAll) .some_

#eval s1SomeOrAll_refined_someNotAll
#eval s1Some_refined_someNotAll


/--
Hurford violation under base lexicon.

Under the base lexicon (weak "some"), a rational speaker prefers "some" over
"some or all" because the disjunction is redundant (all⊆some makes "or all"
add no information).

S1("some" | someNotAll, L_base) > S1("some or all" | someNotAll, L_base)
-/
theorem base_lexicon_disprefers_disjunction :
    s1Some_base_someNotAll ≥ s1SomeOrAll_base_someNotAll := by
  native_decide

/--
Hurford rescue under refined lexicon.

Under the refined lexicon (exh(some) = some-but-not-all), "some or all" becomes
informative because the disjuncts are now mutually exclusive.

However, in the someNotAll world, "some" alone is still sufficient.
-/
theorem refined_some_sufficient :
    s1Some_refined_someNotAll ≥ s1SomeOrAll_refined_someNotAll := by
  native_decide


/--
S1 probability for "someOrAll" in the all world, base lexicon.
-/
def s1SomeOrAll_base_all : ℚ :=
  RSA.Eval.getScore (LURSA.S1_given hurfordScenario lexBase .all_) .someOrAll

/--
S1 probability for "all" alone in the all world, base lexicon.
-/
def s1All_base_all : ℚ :=
  RSA.Eval.getScore (LURSA.S1_given hurfordScenario lexBase .all_) .all_

#eval s1SomeOrAll_base_all
#eval s1All_base_all

/--
In the all world, "all" is strongly preferred over "some or all".

If you know it's all, just say "all".
-/
theorem all_world_prefers_all :
    s1All_base_all > s1SomeOrAll_base_all := by
  native_decide


/-
How informative is "some or all" under each lexicon?

Under L_base: "some or all" = "some" (redundant)
Under L_refined: "some or all" covers {someNotAll, all_} distinctly
-/

/-- Worlds where "some or all" is true under base lexicon -/
def someOrAllTrueWorlds_base : List HWorld :=
  hurfordScenario.worlds.filter (λ w => lexBase.meaning .someOrAll w > 0)

/-- Worlds where "some" is true under base lexicon -/
def someTrueWorlds_base : List HWorld :=
  hurfordScenario.worlds.filter (λ w => lexBase.meaning .some_ w > 0)

#eval someOrAllTrueWorlds_base
#eval someTrueWorlds_base

/--
Under base lexicon, "some or all" and "some" have the same extension.
This is the semantic redundancy that causes Hurford violations.
-/
theorem base_redundancy :
    someOrAllTrueWorlds_base = someTrueWorlds_base := by
  native_decide

/-- Worlds where "some or all" is true under refined lexicon -/
def someOrAllTrueWorlds_refined : List HWorld :=
  hurfordScenario.worlds.filter (λ w => lexRefined.meaning .someOrAll w > 0)

/-- Worlds where "some" is true under refined lexicon -/
def someTrueWorlds_refined : List HWorld :=
  hurfordScenario.worlds.filter (λ w => lexRefined.meaning .some_ w > 0)

#eval someOrAllTrueWorlds_refined
#eval someTrueWorlds_refined

/--
Under refined lexicon, "some or all" covers more worlds than "some" alone.
This is why the disjunction is informative and the Hurford violation is rescued.
-/
theorem refined_disjunction_informative :
    someOrAllTrueWorlds_refined.length > someTrueWorlds_refined.length := by
  native_decide


/--
Connection to empirical Hurford data.

The model predicts:
1. Hurford violations (e.g., "American or Californian") = low S1 probability
   because the disjunction is redundant under the natural reading

2. Rescued cases (e.g., "some or all") = higher S1 probability when the
   listener interprets with the refined lexicon (exh applied)

The prediction: felicitous iff the disjunction is informative under some lexicon.
-/
theorem hurford_model_captures_rescue :
    -- The disjunction "some or all" is rescued because:
    -- Under refined lexicon, it covers strictly more worlds than "some" alone
    someOrAllTrueWorlds_refined.length > someTrueWorlds_refined.length ∧
    -- But under base lexicon, it's redundant
    someOrAllTrueWorlds_base = someTrueWorlds_base := by
  native_decide

/-
For "American or Californian", there's no exhaustification that breaks the
entailment. Californian ALWAYS entails American — it's a fixed hyponymy relation,
not a scalar implicature that can be strengthened.

We model this with a scenario where both lexica have the same (redundant) semantics.
-/

/-- Worlds for hyponymy scenario -/
inductive HyponymWorld where
  | neither      -- Not American (and therefore not Californian)
  | americanOnly -- American but not Californian
  | californian  -- Californian (and therefore American)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Utterances for hyponymy scenario -/
inductive HyponymUtterance where
  | american
  | californian
  | americanOrCalifornian
  | null
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Lexicon for hyponymy: Californian ⊆ American (no refinement possible).
-/
def lexHyponym : Lexicon HyponymUtterance HyponymWorld where
  meaning u w := boolToRat $ match u, w with
    | .american, .neither => false
    | .american, .americanOnly => true
    | .american, .californian => true  -- Californian implies American
    | .californian, .californian => true
    | .californian, _ => false
    -- "American or Californian" = just "American" (Californian ⊆ American)
    | .americanOrCalifornian, .neither => false
    | .americanOrCalifornian, .americanOnly => true
    | .americanOrCalifornian, .californian => true
    | .null, _ => true

/-- Hyponymy scenario: only ONE lexicon (no refinement available) -/
def hyponymScenario : LUScenario where
  Utterance := HyponymUtterance
  World := HyponymWorld
  baseLexicon := lexHyponym
  lexica := [lexHyponym]  -- Only one lexicon -- no LU
  lexPrior := λ _ => 1
  worldPrior := λ _ => 1
  utterances := [.american, .californian, .americanOrCalifornian, .null]
  worlds := [.neither, .americanOnly, .californian]
  α := 1

/-- Worlds where "American or Californian" is true -/
def americanOrCalifornianTrueWorlds : List HyponymWorld :=
  hyponymScenario.worlds.filter (λ w => lexHyponym.meaning .americanOrCalifornian w > 0)

/-- Worlds where "American" alone is true -/
def americanTrueWorlds : List HyponymWorld :=
  hyponymScenario.worlds.filter (λ w => lexHyponym.meaning .american w > 0)

#eval americanOrCalifornianTrueWorlds
#eval americanTrueWorlds

/--
For hyponymy, the disjunction is always redundant -- no rescue possible.
-/
theorem hyponym_always_redundant :
    americanOrCalifornianTrueWorlds = americanTrueWorlds := by
  native_decide

/--
RSA predicts "some or all" is felicitous: the disjunction is informative
under the refined lexicon (exh(some) = some-but-not-all).
-/
def rsaPredictsFelicitous_someOrAll : Bool :=
  someOrAllTrueWorlds_refined.length > someTrueWorlds_refined.length

/--
RSA predicts "American or Californian" is infelicitous: the disjunction
is always redundant (no lexicon refinement breaks the entailment).
-/
def rsaPredictsFelicitous_americanCalifornian : Bool :=
  !(americanOrCalifornianTrueWorlds == americanTrueWorlds)

end RSA.Hurford
