import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic

/-!
# RSA Analysis of Hurford's Constraint

Models Hurford's constraint as a consequence of speaker rationality in RSA.

Hurford's constraint (Potts & Levy 2015): "#A or B" is infelicitous when A ⊆ B or B ⊆ A.

In RSA, felicity = speaker rationality. A speaker wouldn't say "A or B" if:
1. One disjunct is redundant (B⊆A makes B add nothing)
2. A simpler utterance (just "A") conveys the same information

The rescue by exhaustification works because:
- exh(some) = "some but not all" ⊈ "all"
- Now the disjunction is informative: it covers mutually exclusive cases

## Status

The ℚ-based RSA evaluation infrastructure (RSA.Eval, boolToRat, LURSA) has been
removed. Type definitions and semantic characterizations of redundancy are preserved.
RSA computations (L1, S1) need to be re-implemented using the new RSAConfig framework.

## Model

- Worlds: {none, someNotAll, all}
- Utterances: "some", "all", "some or all", null
- Lexica: L_base (some = ≥1), L_refined (some = some-but-not-all)

## References

- Hurford (1974). Exclusive or inclusive disjunction. Foundations of Language.
- Potts & Levy (2015). Negotiating lexical uncertainty and speaker expertise
  with disjunction. BLS 41.
- Singh (2008). On the interpretation of disjunction.
-/

namespace RSA.Hurford


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
def lexBaseMeaning : HUtterance → HWorld → Bool
  | .some_, .none => false
  | .some_, .someNotAll => true
  | .some_, .all_ => true  -- "at least one" includes all
  | .all_, .all_ => true
  | .all_, _ => false
  | .someOrAll, .none => false
  | .someOrAll, .someNotAll => true
  | .someOrAll, .all_ => true
  | .null, _ => true

/--
Refined lexicon: "some" = some-but-not-all (exhaustified reading).

Under this lexicon:
- "some" is true only in {someNotAll}
- "all" is true only in {all_}
- "some or all" is now informative: covers {someNotAll, all_}

This rescues the Hurford violation -- the disjunction is no longer redundant.
-/
def lexRefinedMeaning : HUtterance → HWorld → Bool
  | .some_, .none => false
  | .some_, .someNotAll => true
  | .some_, .all_ => false  -- exh(some) excludes "all"
  | .all_, .all_ => true
  | .all_, _ => false
  | .someOrAll, .none => false
  | .someOrAll, .someNotAll => true  -- exh(some) covers this
  | .someOrAll, .all_ => true        -- "all" covers this
  | .null, _ => true

-- Semantic redundancy characterization

/-- Worlds where "some or all" is true under base lexicon -/
def someOrAllTrueWorlds_base : List HWorld :=
  [HWorld.none, HWorld.someNotAll, HWorld.all_].filter (λ w => lexBaseMeaning .someOrAll w)

/-- Worlds where "some" is true under base lexicon -/
def someTrueWorlds_base : List HWorld :=
  [HWorld.none, HWorld.someNotAll, HWorld.all_].filter (λ w => lexBaseMeaning .some_ w)

/--
Under base lexicon, "some or all" and "some" have the same extension.
This is the semantic redundancy that causes Hurford violations.
-/
theorem base_redundancy :
    someOrAllTrueWorlds_base = someTrueWorlds_base := by
  native_decide

/-- Worlds where "some or all" is true under refined lexicon -/
def someOrAllTrueWorlds_refined : List HWorld :=
  [HWorld.none, HWorld.someNotAll, HWorld.all_].filter (λ w => lexRefinedMeaning .someOrAll w)

/-- Worlds where "some" is true under refined lexicon -/
def someTrueWorlds_refined : List HWorld :=
  [HWorld.none, HWorld.someNotAll, HWorld.all_].filter (λ w => lexRefinedMeaning .some_ w)

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
  exact ⟨refined_disjunction_informative, base_redundancy⟩

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
def lexHyponymMeaning : HyponymUtterance → HyponymWorld → Bool
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

/-- Worlds where "American or Californian" is true -/
def americanOrCalifornianTrueWorlds : List HyponymWorld :=
  [HyponymWorld.neither, HyponymWorld.americanOnly, HyponymWorld.californian].filter
    (λ w => lexHyponymMeaning .americanOrCalifornian w)

/-- Worlds where "American" alone is true -/
def americanTrueWorlds : List HyponymWorld :=
  [HyponymWorld.neither, HyponymWorld.americanOnly, HyponymWorld.californian].filter
    (λ w => lexHyponymMeaning .american w)

/--
For hyponymy, the disjunction is always redundant -- no rescue possible.
-/
theorem hyponym_always_redundant :
    americanOrCalifornianTrueWorlds = americanTrueWorlds := by
  native_decide

end RSA.Hurford
