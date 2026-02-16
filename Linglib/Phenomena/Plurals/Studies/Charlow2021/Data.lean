import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Charlow 2021: Empirical Data

Finite witnessing models for the cumulative reading puzzle.

**Sentence**: "Exactly three boys saw exactly five movies."

**Scenario A** (Figure 1): 3 boys, 5 movies. Each boy saw some movies;
collectively all 5 movies were seen by some boy. Both cumulative and
pseudo-cumulative readings are true.

**Scenario B**: 4 boys, 6 movies. Four boys collectively saw 6 movies,
but a 3-boy subgroup saw exactly 5.
- Cumulative reading (= global counting): FALSE (4 boys total participated,
  not 3; 6 movies total, not 5)
- Pseudo-cumulative reading (= ∃ subset): TRUE ({b1,b2,b3} saw 5 movies)

The key empirical observation: native speakers judge the sentence FALSE
in Scenario B, matching the cumulative reading.

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
  Figure 1, §1.
-/

namespace Phenomena.Plurals.Studies.Charlow2021.Data

-- ════════════════════════════════════════════════════
-- § Scenario A: 3 boys, 5 movies
-- ════════════════════════════════════════════════════

inductive Boy3 where | b1 | b2 | b3
  deriving DecidableEq, Repr, BEq

instance : Fintype Boy3 where
  elems := {.b1, .b2, .b3}
  complete x := by cases x <;> decide

inductive Movie5 where | m1 | m2 | m3 | m4 | m5
  deriving DecidableEq, Repr, BEq

instance : Fintype Movie5 where
  elems := {.m1, .m2, .m3, .m4, .m5}
  complete x := by cases x <;> decide

/-- Scenario A seeing relation (bipartite graph):
    b1 saw m1, m2; b2 saw m3, m4; b3 saw m5.
    Collectively: 3 boys saw 5 movies. -/
def scenarioA_saw : Boy3 → Movie5 → Bool
  | .b1, .m1 => true | .b1, .m2 => true
  | .b2, .m3 => true | .b2, .m4 => true
  | .b3, .m5 => true
  | _, _ => false

-- ════════════════════════════════════════════════════
-- § Scenario B: 4 boys, 6 movies (the overgeneration case)
-- ════════════════════════════════════════════════════

inductive Boy4 where | b1 | b2 | b3 | b4
  deriving DecidableEq, Repr, BEq

instance : Fintype Boy4 where
  elems := {.b1, .b2, .b3, .b4}
  complete x := by cases x <;> decide

inductive Movie6 where | m1 | m2 | m3 | m4 | m5 | m6
  deriving DecidableEq, Repr, BEq

instance : Fintype Movie6 where
  elems := {.m1, .m2, .m3, .m4, .m5, .m6}
  complete x := by cases x <;> decide

/-- Scenario B seeing relation:
    b1 saw m1, m2; b2 saw m3, m4; b3 saw m5; b4 saw m6.
    Four boys participated, seeing 6 distinct movies total. -/
def scenarioB_saw : Boy4 → Movie6 → Bool
  | .b1, .m1 => true | .b1, .m2 => true
  | .b2, .m3 => true | .b2, .m4 => true
  | .b3, .m5 => true
  | .b4, .m6 => true
  | _, _ => false

-- ════════════════════════════════════════════════════
-- § Reading Definitions (Theory-neutral, Bool-computable)
-- ════════════════════════════════════════════════════

/-- Cumulative reading: the total number of boys who saw any movie = n_boys,
    AND the total number of movies seen by any boy = n_movies.
    This is the "global count" interpretation. -/
def cumulativeReading {B M : Type*} [BEq B] [BEq M]
    (saw : B → M → Bool) (allBoys : List B) (allMovies : List M)
    (n_boys : Nat) (n_movies : Nat) : Bool :=
  let activeBoys := allBoys.filter λ b => allMovies.any λ m => saw b m
  let seenMovies := allMovies.filter λ m => allBoys.any λ b => saw b m
  activeBoys.length == n_boys && seenMovies.length == n_movies

/-- Pseudo-cumulative reading: ∃ a subset of n_boys boys such that
    the movies they collectively saw number exactly n_movies.
    (Does NOT require the subset to be the maximal group.) -/
def pseudoCumulativeReading {B M : Type*} [BEq M]
    (saw : B → M → Bool) (allBoys : List B) (allMovies : List M)
    (n_boys : Nat) (n_movies : Nat) : Bool :=
  allBoys.sublists.any λ bs =>
    bs.length == n_boys &&
    (allMovies.filter λ m => bs.any λ b => saw b m).length == n_movies

-- Concrete enumerations for native_decide
def allBoys3 : List Boy3 := [.b1, .b2, .b3]
def allMovies5 : List Movie5 := [.m1, .m2, .m3, .m4, .m5]
def allBoys4 : List Boy4 := [.b1, .b2, .b3, .b4]
def allMovies6 : List Movie6 := [.m1, .m2, .m3, .m4, .m5, .m6]

-- ════════════════════════════════════════════════════
-- § Empirical Observations
-- ════════════════════════════════════════════════════

/-- Scenario A: cumulative reading is TRUE.
    3 boys participated in seeing, and 5 movies were seen. -/
theorem scenarioA_cumulative_true :
    cumulativeReading scenarioA_saw allBoys3 allMovies5 3 5 = true := by native_decide

/-- Scenario A: pseudo-cumulative reading is also TRUE. -/
theorem scenarioA_pseudo_true :
    pseudoCumulativeReading scenarioA_saw allBoys3 allMovies5 3 5 = true := by native_decide

/-- Scenario B: cumulative reading is FALSE.
    4 boys participated (not 3), and 6 movies were seen (not 5). -/
theorem scenarioB_cumulative_false :
    cumulativeReading scenarioB_saw allBoys4 allMovies6 3 5 = false := by native_decide

/-- Scenario B: pseudo-cumulative reading is TRUE (the overgeneration).
    {b1,b2,b3} is a 3-element subset that collectively saw 5 movies. -/
theorem scenarioB_pseudo_true :
    pseudoCumulativeReading scenarioB_saw allBoys4 allMovies6 3 5 = true := by native_decide

end Phenomena.Plurals.Studies.Charlow2021.Data
