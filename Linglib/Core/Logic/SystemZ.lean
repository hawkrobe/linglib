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

/-- @cite{goldszmidt-pearl-1996}, Definition 8 (p. 66). σ is
    **p-entailed** by φ given Δ iff φ ⊨_κ σ holds in every consequence
    relation ⊨_κ induced by an admissible ranking κ.

    p-entailment is conservative: it only draws conclusions that are
    safe across ALL admissible rankings. z-entailment (Definition 13)
    is bolder, using only the unique minimal ranking κ^z. Every
    p-entailed conclusion is z-entailed but not vice versa (Table 2). -/
def pEntails (Δ : KnowledgeBase W) (φ σ : W → Bool) : Prop :=
  ∀ κ : RankingFunction W, admissible κ Δ → rankEntails κ φ σ

/-- p-entailment implies z-entailment: if φ ⊨_p σ then φ ⊨_{κ^z} σ,
    since κ^z is one particular admissible ranking. -/
theorem pEntails_implies_rankEntails {Δ : KnowledgeBase W}
    {κ : RankingFunction W} (hadm : admissible κ Δ)
    {φ σ : W → Bool} (h : pEntails Δ φ σ) : rankEntails κ φ σ :=
  h κ hadm

-- ══════════════════════════════════════════════════════════════════════
-- § 5. Computable Consistency-Test (Fig. 2)
-- ══════════════════════════════════════════════════════════════════════

/-- Decidable tolerance check. Inlines the `tolerated` definition for
    `Decidable` instance synthesis on finite types. -/
def toleratedBool [Fintype W] (r : DefaultRule W) (Δ : KnowledgeBase W) : Bool :=
  decide (∃ w : W, r.ante w = true ∧ r.cons w = true ∧
    (Δ.all fun r' => r'.verified w) = true)

/-- Iterative tolerance stripping (Consistency-Test, Fig. 2).
    At each level, peels off tolerated rules and assigns them the
    current stratum number. `fuel` bounds iterations. -/
def zPrioritiesAux [Fintype W]
    (remaining : KnowledgeBase W) (level : ℕ) (fuel : ℕ) :
    List (DefaultRule W × ℕ) :=
  match fuel, remaining with
  | _, [] => []
  | 0, _ => remaining.map (·, level)
  | fuel' + 1, _ =>
    let (tol, rest) := remaining.partition (fun r => toleratedBool r remaining)
    if tol.isEmpty then remaining.map (·, level)
    else tol.map (·, level) ++ zPrioritiesAux rest (level + 1) fuel'

/-- Compute Z-priorities for all rules via the Consistency-Test (Fig. 2).
    Each rule is assigned its stratum number. -/
def zPriorities [Fintype W] (Δ : KnowledgeBase W) :
    List (DefaultRule W × ℕ) :=
  zPrioritiesAux Δ 0 Δ.length

-- ══════════════════════════════════════════════════════════════════════
-- § 6. System Z⁺: Variable-Strength Defaults
-- ══════════════════════════════════════════════════════════════════════

/-- A default rule with strength parameter δ.
    @cite{goldszmidt-pearl-1996}, Definition 18: higher δ demands a wider
    gap between verifying and falsifying worlds. -/
structure StrengthRule (W : Type*) extends DefaultRule W where
  /-- Strength parameter (δ ≥ 0) -/
  strength : ℕ

/-- A knowledge base of variable-strength default rules. -/
abbrev StrengthKB (W : Type*) := List (StrengthRule W)

/-- Strip strength parameters to get the underlying `KnowledgeBase`. -/
def StrengthKB.flat {W : Type*} (Δ : StrengthKB W) : KnowledgeBase W :=
  Δ.map (·.toDefaultRule)

/-- @cite{goldszmidt-pearl-1996}, Definition 18 (corrected).
    A ranking κ is **δ-admissible** relative to strength rules iff
    for each rule (φᵢ → ψᵢ, δᵢ), every falsifying world is outranked
    by at least δᵢ + 1 by some verifying world:
      κ(v) + δᵢ < κ(w) for some verifying v.

    Note: Eq. 14 as printed has δ on the wrong side; the "equivalently
    κ(¬ψ|φ) > δ" clause and Fig. 3 confirm this corrected form. -/
def strengthAdmissible (κ : RankingFunction W) (Δ : StrengthKB W) : Prop :=
  Δ.Forall fun sr =>
    ∀ w : W, sr.falsified w = true →
      ∃ v : W, (sr.ante v && sr.cons v) = true ∧ κ.rank v + sr.strength < κ.rank w

/-- `toleratedBool` computes `tolerated`: the Bool decision procedure
    agrees with the Prop definition on finite types. -/
theorem toleratedBool_iff [Fintype W] (r : DefaultRule W) (Δ : KnowledgeBase W) :
    toleratedBool r Δ = true ↔ tolerated r Δ := by
  simp [toleratedBool, tolerated, decide_eq_true_eq]

/-- Any element's strength is bounded by the foldr-max over the list. -/
private theorem strength_le_foldr_max (Δ : StrengthKB W)
    (sr : StrengthRule W) (hsr : sr ∈ Δ) :
    sr.strength ≤ Δ.foldr (fun sr n => max sr.strength n) 0 := by
  induction Δ with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldr]
    rcases List.mem_cons.mp hsr with rfl | htl
    · exact le_max_left _ _
    · exact le_trans (ih htl) (le_max_right _ _)

/-- @cite{goldszmidt-pearl-1996}, Theorem 19: a strength knowledge base
    is δ-consistent (admits a δ-admissible ranking) iff its flat
    projection (ignoring strengths) is consistent (admits an ordinary
    admissible ranking).

    (→) Drop strength terms: κ(v) + δ < κ(w) implies κ(v) < κ(w).
    (←) Scale the ranking by M = 1 + max{δᵢ}: the gap κ(v) < κ(w)
    becomes κ(v)·M + δ < (κ(v)+1)·M ≤ κ(w)·M for any δ < M. -/
theorem strength_consistent_iff_flat [Fintype W] (Δ : StrengthKB W) :
    (∃ κ : RankingFunction W, strengthAdmissible κ Δ) ↔
    (∃ κ : RankingFunction W, admissible κ Δ.flat) := by
  constructor
  · -- (→) δ-admissible → admissible (weaken constraints)
    rintro ⟨κ, hadm⟩
    refine ⟨κ, ?_⟩
    rw [strengthAdmissible, List.forall_iff_forall_mem] at hadm
    rw [admissible, StrengthKB.flat, List.forall_iff_forall_mem]
    intro r hr w hw
    obtain ⟨sr, hsr, rfl⟩ := List.mem_map.mp hr
    obtain ⟨v, hv, hlt⟩ := hadm sr hsr w hw
    exact ⟨v, hv, by omega⟩
  · -- (←) admissible → ∃ δ-admissible (scale by 1 + max δ)
    rintro ⟨κ, hadm⟩
    set M := 1 + Δ.foldr (fun sr n => max sr.strength n) 0 with hM_def
    refine ⟨⟨fun w => κ.rank w * M, ?_⟩, ?_⟩
    · obtain ⟨w, hw⟩ := κ.normalized; exact ⟨w, by simp [hw]⟩
    · rw [strengthAdmissible, List.forall_iff_forall_mem]
      intro sr hsr w hw
      rw [admissible, StrengthKB.flat, List.forall_iff_forall_mem] at hadm
      obtain ⟨v, hv, hlt⟩ := hadm sr.toDefaultRule (List.mem_map.mpr ⟨sr, hsr, rfl⟩) w hw
      refine ⟨v, hv, ?_⟩
      have hδ : sr.strength < M := by
        have := strength_le_foldr_max Δ sr hsr; omega
      show κ.rank v * M + sr.strength < κ.rank w * M
      have h := Nat.mul_le_mul_right M (show κ.rank v + 1 ≤ κ.rank w by omega)
      rw [Nat.succ_mul] at h; omega

end Core.Logic.SystemZ
