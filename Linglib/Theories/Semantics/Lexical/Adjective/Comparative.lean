import Linglib.Core.Scale
import Linglib.Theories.Semantics.Lexical.Adjective.Theory

/-!
# Comparative Semantics and Ambidirectionality

Degree comparatives analyzed through Rett's (2026) order-sensitive MAX
framework. The comparative morpheme selects MAX on a directional scale;
antonymy is scale reversal; and **ambidirectionality** — the property
that negating the standard of comparison is truth-conditionally vacuous —
explains why comparatives license expletive negation cross-linguistically.

## Key Results

1. **Comparative morpheme** (§2): Schwarzschild (2008) / Rett (2026) eq. 47 —
   "A is taller than B" iff MAX of A's degrees >_dir MAX of B's degrees.

2. **MAX–direct bridge** (§2): For singletons, MAX is trivial
   (`maxOnScale_singleton`), so the MAX-based formulation reduces to
   direct comparison μ(a) > μ(b). Proved in `comparativeSem_eq_MAX`.

3. **Antonymy as scale reversal** (§3): "A taller than B ↔ B shorter than A"
   follows from MAX on reversed scales.

4. **Ambidirectionality of comparatives** (§4): When the standard B forms a
   closed interval, negating B doesn't change truth conditions because B and
   ¬B share the informative degree bound. This is why *than*-clauses license
   EN (Rett 2026, §4).

5. **NPI licensing** (§5): The *than*-clause is DE because it involves
   universal quantification over degrees, which is anti-monotone in the domain
   (Hoeksema 1983, von Stechow 1984).

6. **Manner implicature** (§6): EN in comparatives or *before*-clauses
   triggers evaluativity (Cépeda 2018, Napoli & Nespor 1976, Krifka 2010b).

## References

- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
- Schwarzschild, R. (2008). The semantics of comparatives.
- Kennedy, C. & McNally, L. (2005). Scale structure, degree modification.
- Hoeksema, J. (1983). Negative polarity and the comparative.
- von Stechow, A. (1984). Comparing semantic theories of comparison.
- Cépeda, P. (2018). Expletive negation and evaluativity in Spanish comparatives.
- Napoli, D. J. & Nespor, M. (1976). Negatives in comparatives.
- Krifka, M. (2010b). *Before* and *after* without coercion. *NLLT* 28.
-/

namespace Semantics.Lexical.Adjective.Comparative

open Core.Scale (Boundedness maxOnScale maxOnScale_singleton isAmbidirectional)

-- ════════════════════════════════════════════════════
-- § 1. Scale Direction
-- ════════════════════════════════════════════════════

/-- Which pole of a degree scale the comparative targets.
    `positive`: "taller" — MAX picks the highest degrees.
    `negative`: "shorter" — MAX picks the lowest degrees. -/
inductive ScaleDirection where
  | positive  -- MAX on (· > ·): higher is better
  | negative  -- MAX on (· < ·): lower is better
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Comparative Morpheme
-- ════════════════════════════════════════════════════

/-! ### The comparative as MAX-comparison

Schwarzschild (2008) / Rett (2026, eq. 47): the comparative morpheme
compares the MAX of two degree sets. "A is taller than B" is true iff
the maximum of A's heights exceeds the maximum of B's heights.

For a measure function μ : Entity → α:
  ⟦A -er than B⟧ = MAX_dir({μ(a)}) >_dir MAX_dir({μ(b)})

Since MAX on a singleton is that singleton (`maxOnScale_singleton`),
this reduces to μ(a) > μ(b) for positive comparatives. The bridge
theorem `comparativeSem_eq_MAX` makes this explicit. -/

variable {Entity : Type*} {α : Type*} [LinearOrder α]

/-- Comparative semantics (Rett 2026 / Schwarzschild 2008):
    "A is Adj-er than B" iff μ(a) exceeds μ(b) on the directed scale. -/
def comparativeSem (μ : Entity → α) (a b : Entity) (dir : ScaleDirection) : Prop :=
  match dir with
  | .positive => μ a > μ b
  | .negative => μ a < μ b

/-- Equative semantics: "A is as Adj as B" iff μ(a) ≥ μ(b) on the
    directed scale. -/
def equativeSem (μ : Entity → α) (a b : Entity) (dir : ScaleDirection) : Prop :=
  match dir with
  | .positive => μ a ≥ μ b
  | .negative => μ a ≤ μ b

/-- **MAX–direct bridge**: the direct comparison `μ(a) > μ(b)` is
    equivalent to the MAX-based formulation. This makes explicit that
    `comparativeSem` is a simplification of the general MAX-comparison,
    justified by `maxOnScale_singleton`. -/
theorem comparativeSem_eq_MAX (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔
      ∃ m ∈ maxOnScale (· > ·) ({μ b} : Set α), μ a > m := by
  simp [comparativeSem, maxOnScale_singleton]

-- ════════════════════════════════════════════════════
-- § 3. Antonymy as Scale Reversal
-- ════════════════════════════════════════════════════

/-! ### Antonymy = direction flip

"A is taller than B" on the positive scale ↔ "B is shorter than A" on
the negative scale. This follows directly from the definition: positive
compares μ(a) > μ(b), negative compares μ(a) < μ(b), and the swap of
arguments reverses the inequality. -/

/-- "A taller than B" ↔ "B shorter than A" — antonymy is argument swap
    plus direction reversal. -/
theorem taller_shorter_antonymy (μ : Entity → α) (a b : Entity) :
    comparativeSem μ a b .positive ↔ comparativeSem μ b a .negative := by
  simp [comparativeSem]

/-- Equative antonymy: "A as tall as B" ↔ "B as short as A". -/
theorem equative_antonymy (μ : Entity → α) (a b : Entity) :
    equativeSem μ a b .positive ↔ equativeSem μ b a .negative := by
  simp [equativeSem]

-- ════════════════════════════════════════════════════
-- § 4. Ambidirectionality of Comparatives
-- ════════════════════════════════════════════════════

/-! ### Degree relatives and expletive negation

Rett (2026, §4): When the standard of comparison B is a **degree
relative** (e.g., "than Bill is tall"), B denotes a closed interval
of degrees [0, μ(b)]. Its complement ¬B = (μ(b), ∞) shares the
informative bound μ(b). So MAX₍>₎(B) = μ(b) = inf(MAX₍>₎(¬B)),
making the comparative ambidirectional.

This explains why *than*-clauses license EN in Italian, Spanish,
French, and other Romance languages (Napoli & Nespor 1976; Cépeda 2018).

**Prediction (Rett 2026, fn. on Kennedy & McNally 2005)**:
- Relative adjectives (open scales: tall, expensive) → license EN in comparatives
- Absolute adjectives (closed scales: full, dry) → do NOT license EN
  because the degree set is already bounded, and negation targets the
  wrong bound. -/

/-- The comparative is ambidirectional on degree sets: when B is the
    "at most" set {d | d ≤ μ(b)} (the degree relative denotation),
    MAX₍>₎(B) and MAX₍>₎(Bᶜ) share the boundary μ(b), so
    "A taller than B" ↔ "A taller than ¬B".

    TODO: Full proof requires showing that for B = {d | d ≤ μ(b)},
    MAX₍>₎(B) = {μ(b)} and inf(MAX₍>₎(Bᶜ)) = μ(b), then
    the comparative truth conditions depend only on this shared bound.
    The proof is analogous to `maxOnScale_atLeast_singleton`. -/
theorem comparative_ambidirectional {α : Type*} [LinearOrder α]
    (μ_a : α) (μ_b : α) (B : Set α) (hB : B = { d | d ≤ μ_b }) :
    isAmbidirectional (λ X => ∃ m ∈ maxOnScale (· > ·) X, μ_a > m) B := by
  sorry

/-- Equatives are also ambidirectional (Rett 2026, §4.3.1):
    "A as tall as B" ↔ "A as tall as ¬B" when B is a degree relative. -/
theorem equative_ambidirectional {α : Type*} [LinearOrder α]
    (μ_a : α) (μ_b : α) (B : Set α) (hB : B = { d | d ≤ μ_b }) :
    isAmbidirectional (λ X => ∃ m ∈ maxOnScale (· > ·) X, μ_a ≥ m) B := by
  sorry

-- ════════════════════════════════════════════════════
-- § 5. NPI Licensing in Comparatives
-- ════════════════════════════════════════════════════

/-! ### Downward entailingness of *than*-clauses

Hoeksema (1983), von Stechow (1984): the *than*-clause creates a DE
environment. The key insight is that comparatives involve **universal
quantification** over the degree set in the standard: "taller than
every student" ≡ ∀x ∈ students, μ(a) > μ(x). Universal quantification
over a domain is anti-monotone in the domain: if D₁ ⊆ D₂, then
(∀d ∈ D₂, P d) → (∀d ∈ D₁, P d). This is the source of DE-ness. -/

/-- The *than*-clause argument of a comparative is DE: universal
    quantification over a domain is anti-monotone in the domain.
    If D₁ ⊆ D₂ and the comparative holds against all of D₂,
    it holds against all of D₁. -/
theorem comparative_than_DE {α : Type*} (R : α → α → Prop)
    (μ_a : α) (D₁ D₂ : Set α) (h_sub : D₁ ⊆ D₂)
    (h : ∀ d ∈ D₂, R μ_a d) : ∀ d ∈ D₁, R μ_a d :=
  fun d hd => h d (h_sub hd)

-- ════════════════════════════════════════════════════
-- § 6. Manner Implicature
-- ════════════════════════════════════════════════════

/-! ### EN triggers evaluativity

Cépeda (2018), Krifka (2010b): expletive negation in ambidirectional
constructions triggers a **manner implicature** — the use of the marked
(negated) form signals that the comparison/temporal relation is
noteworthy, yielding an evaluative reading:
- "A is much taller than B" (Italian comparative + *non*)
- "A arrived well before B" (French *avant que* + *ne* expletif)

Napoli & Nespor (1976): Italian comparative + EN → evaluativity.
This is the same mechanism across both temporal and degree domains. -/

/-- Manner implicature triggered by EN in an ambidirectional construction.
    `evaluative`: the relation is noteworthy (large gap / early timing).
    `atypical`: the EN form is pragmatically marked (optional, stylistic). -/
structure MannerEffect where
  /-- Does EN trigger an evaluative reading? -/
  evaluative : Bool
  /-- Is the EN form pragmatically marked (optional, stylistic)? -/
  atypical : Bool
  deriving DecidableEq, BEq, Repr

/-- EN in ambidirectional constructions (comparatives, *before*-clauses)
    triggers evaluativity but is not atypical — it's a productive pattern
    cross-linguistically (Cépeda 2018, Krifka 2010b). -/
def enEvaluativeEffect : MannerEffect :=
  { evaluative := true, atypical := false }

end Semantics.Lexical.Adjective.Comparative
