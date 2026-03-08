import Linglib.Core.Logic.RankingFunction

/-!
# System Z: Constructing Rankings from Default Rules

@cite{goldszmidt-pearl-1996}

System Z constructs the unique minimal ranking function from a knowledge
base of default rules. Given defaults like "birds fly" and "penguins
don't fly", the Z-ordering stratifies rules by *tolerance* — which can
be satisfied without violating the others — and κ^z assigns each world
the lowest possible rank consistent with all constraints.

## Key definitions

- `DefaultRule W`: a default rule φ → ψ (Bool predicates on worlds)
- `KnowledgeBase W`: a list of default rules
- `tolerated`: a rule is tolerated by Δ iff ∃ω verifying it + all
  material counterparts (Def. 3)
- `admissible`: κ satisfies all rules' ranking constraints (Def. 2)
- `zRankValue`: κ^z(ω) from Z-prioritized rules (Def. 12, Eq. 10)
- `zRanking`: wrap as `RankingFunction`
- `rankEntails`: consequence via a ranking (Def. 7)

## Connection to RankingFunction

`zRanking` produces a `RankingFunction W`, connecting to all downstream
infrastructure: `toPlausibilityOrder`, `toPreferential`,
`ranking_rationalMonotonicity`, and the 95+ consumers of `NormalityOrder`.

## Architecture

```
Default rules Δ = {φᵢ → ψᵢ}
    ↓ Consistency-Test (tolerance stripping)
Z-priority ordering on rules
    ↓ Definition 12
κ^z : RankingFunction W (minimal admissible ranking)
    ↓ toPlausibilityOrder
PlausibilityOrder → PreferentialConsequence (System P)
```
-/

namespace Core.Logic.SystemZ

open Core.Logic.Ranking (RankingFunction)

-- ══════════════════════════════════════════════════════════════════════
-- § 1. Default Rules and Knowledge Bases
-- ══════════════════════════════════════════════════════════════════════

/-- A default rule "if φ then normally ψ", where φ and ψ are decidable
    predicates on worlds.

    @cite{goldszmidt-pearl-1996}: rules are the basic unit of defeasible
    knowledge. The rule φ → ψ expresses that ψ is normally the case
    in the domain φ, admitting exceptions. -/
structure DefaultRule (W : Type*) where
  /-- Antecedent (domain of the default) -/
  ante : W → Bool
  /-- Consequent (what normally holds) -/
  cons : W → Bool

/-- A knowledge base: a list of default rules. -/
abbrev KnowledgeBase (W : Type*) := List (DefaultRule W)

variable {W : Type*}

/-- A world **verifies** a rule: satisfies the material counterpart φ ⊃ ψ.
    Equivalently, either the antecedent is false or the consequent holds. -/
def DefaultRule.verified (r : DefaultRule W) (w : W) : Bool :=
  !r.ante w || r.cons w

/-- A world **falsifies** a rule: satisfies φ ∧ ¬ψ.
    This is the world that violates the default expectation. -/
def DefaultRule.falsified (r : DefaultRule W) (w : W) : Bool :=
  r.ante w && !r.cons w

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Tolerance and Admissibility
-- ══════════════════════════════════════════════════════════════════════

/-- @cite{goldszmidt-pearl-1996}, Definition 3 (Eq. 8). A rule α → β
    is **tolerated** by a knowledge base Δ iff there exists a world ω
    satisfying α ∧ β and the material counterpart of every rule in Δ.

    Tolerance is the key to stratification: rules that can be satisfied
    without violating others are the least surprising (lowest Z-priority). -/
def tolerated (r : DefaultRule W) (Δ : KnowledgeBase W) : Prop :=
  ∃ w : W, r.ante w = true ∧ r.cons w = true ∧
    (Δ.all fun r' => r'.verified w) = true

/-- @cite{goldszmidt-pearl-1996}, Definition 2 (Eq. 7). A ranking κ is
    **admissible** relative to Δ iff for each rule φᵢ → ψᵢ, every world
    falsifying the rule is outranked by some world satisfying it.

    Equivalently: κ(φᵢ ∧ ψᵢ) < κ(φᵢ ∧ ¬ψᵢ) — the most normal world
    satisfying the rule has strictly lower rank than the most normal
    world violating it. -/
def admissible (κ : RankingFunction W) (Δ : KnowledgeBase W) : Prop :=
  Δ.Forall fun r =>
    ∀ w : W, r.falsified w = true →
      ∃ v : W, (r.ante v && r.cons v) = true ∧ κ.rank v < κ.rank w

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Minimal Ranking κ^z
-- ══════════════════════════════════════════════════════════════════════

/-- The κ^z value at a world, given Z-prioritized rules.

    @cite{goldszmidt-pearl-1996}, Definition 12 (Eq. 10):
    - κ^z(ω) = 0 if ω does not falsify any rule in Δ
    - κ^z(ω) = max{Z(rᵢ) | ω falsifies rᵢ} + 1 otherwise

    Each rule is paired with its Z-priority (computed by the
    Consistency-Test procedure, verified concretely in study files). -/
def zRankValue (rules : List (DefaultRule W × ℕ)) (w : W) : ℕ :=
  match maxFalsifiedPriority rules w with
  | none => 0
  | some z => z + 1
where
  /-- Find the maximum Z-priority among rules falsified by world `w`. -/
  maxFalsifiedPriority : List (DefaultRule W × ℕ) → W → Option ℕ
    | [], _ => none
    | (r, z) :: rest, w =>
      let acc := maxFalsifiedPriority rest w
      match r.falsified w with
      | true => some (match acc with | none => z | some z' => max z z')
      | false => acc

/-- Build a `RankingFunction` from Z-prioritized rules.

    The normalization proof ensures some world has rank 0, i.e., some
    world verifies all rules simultaneously. This world exists whenever
    the knowledge base is consistent. -/
def zRanking (rules : List (DefaultRule W × ℕ))
    (hnorm : ∃ w : W, zRankValue rules w = 0) : RankingFunction W where
  rank := zRankValue rules
  normalized := hnorm

-- ══════════════════════════════════════════════════════════════════════
-- § 4. Consequence Relations
-- ══════════════════════════════════════════════════════════════════════

/-- @cite{goldszmidt-pearl-1996}, Definition 7 (Eq. 9). The consequence
    relation induced by a ranking κ: φ ⊨_κ σ iff the most normal
    world satisfying φ ∧ σ has strictly lower rank than the most normal
    world satisfying φ ∧ ¬σ.

    Equivalently: every world satisfying φ ∧ ¬σ is outranked by some
    world satisfying φ ∧ σ. -/
def rankEntails (κ : RankingFunction W) (φ σ : W → Bool) : Prop :=
  ∀ w : W, (φ w && !σ w) = true →
    ∃ v : W, (φ v && σ v) = true ∧ κ.rank v < κ.rank w

end Core.Logic.SystemZ
