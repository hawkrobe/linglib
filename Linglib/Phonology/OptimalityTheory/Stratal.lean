import Linglib.Phonology.Constraints.Defs


/-!
# Stratal Optimality Theory
[kiparsky-2000]

Stratal OT is a theory of the phonology–morphology interface where
phonological computation is **cyclic**: it applies at multiple levels
(strata) of morphological structure (Stem → Word → Phrase), with the output
of each stratum feeding the next as input. The crucial property is
**constraint reranking**: the same constraint can occupy different positions
in different strata's rankings, capturing level-ordering effects without ad
hoc rules or extrinsic ordering.

Per-stratum evaluation uses `OptimalityTheory.Tableau.ofRanking` / `Tableau.optimal`
in the consuming study file (e.g. the Telugu weak alternation, [aitha-2026]).
This module provides the cross-stratal vocabulary: a `StratalDerivation`
record of the per-stratum outputs, and the reranking predicates. The latter
are *cross-stratum* because strata typically score different candidate types
— the constraint inventory is shared by *name*, not by candidate type.

## Main definitions

* `StratalDerivation` — the per-stratum input/output record.
* `findRank` — the rank (0 = highest) of a constraint by name in a ranking.
* `isPromotedAcross` / `isDemotedAcross` — cross-stratum reranking predicates.
-/

namespace OptimalityTheory.Stratal


open Constraints

/-! ### Stratal derivation record -/

/-- The full derivational history across all three strata, recording the
    input and output at each level. Candidate types differ across strata
    because GEN produces different representations at each level (e.g.
    metrical parses at the Stem level, segmental modifications at the Word
    level). -/
structure StratalDerivation (S W P : Type*) where
  /-- Underlying representation (input to the Stem stratum). -/
  underlyingForm : S
  /-- Optimal output of the Stem stratum. -/
  stemOutput : S
  /-- Optimal output of the Word stratum. -/
  wordOutput : W
  /-- Optimal output of the Phrase stratum (= surface form). -/
  phraseOutput : P

/-! ### Constraint reranking -/

variable {L : Type*} [DecidableEq L] {C C₁ C₂ : Type*}

/-- The rank (position) of the constraint labeled `l` in a ranking: `0` is the highest
    rank; `none` if the constraint is not active at this stratum. -/
def findRank (l : L) (ranking : List (L × Constraint C)) : Option ℕ :=
  ranking.findIdx? (·.1 == l)

/-- Cross-stratum promotion: `l` is ranked higher (closer to `0`) in `r₁` than in `r₂`.
    Different candidate types between strata are permitted — the constraint inventory is
    shared by *label*, not by candidate type (e.g. ONSET is promoted from Word to Phrase
    level in Telugu, [aitha-2026] §5.3). -/
def IsPromotedAcross (l : L) (r₁ : List (L × Constraint C₁))
    (r₂ : List (L × Constraint C₂)) : Prop :=
  match findRank l r₁, findRank l r₂ with
  | some p₁, some p₂ => p₁ < p₂
  | _, _ => False

instance (l : L) (r₁ : List (L × Constraint C₁)) (r₂ : List (L × Constraint C₂)) :
    Decidable (IsPromotedAcross l r₁ r₂) := by
  unfold IsPromotedAcross; split <;> infer_instance

/-- Cross-stratum demotion. Dual of `IsPromotedAcross` (e.g. `*DIST-0` is demoted from
    Word to Phrase level in Telugu, [aitha-2026] §5.3). -/
def IsDemotedAcross (l : L) (r₁ : List (L × Constraint C₁))
    (r₂ : List (L × Constraint C₂)) : Prop :=
  IsPromotedAcross l r₂ r₁

instance (l : L) (r₁ : List (L × Constraint C₁)) (r₂ : List (L × Constraint C₂)) :
    Decidable (IsDemotedAcross l r₁ r₂) := by
  unfold IsDemotedAcross; infer_instance

end OptimalityTheory.Stratal
