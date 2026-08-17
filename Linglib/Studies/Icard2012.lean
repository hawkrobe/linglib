/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Logic.Natural.Completeness

/-!
# [icard-2012]: Inclusion and Exclusion in Natural Language

Table verifications for [icard-2012]'s relation algebra against the
substrate implementations in `Logic/Natural/Basic.lean`: the join table
(Lemma 1.5, p. 710 — the printed cells, independently certified against
the non-strict `Holds` reading by `Relation.Holds.join` and tight by
`Relation.isLeast_join`), the
projectivity tables (Lemma 2.4, p. 715), the composition table
(Lemma 2.7, p. 716) with its signature order (§2.2), the polarity
coarsening, the classification of *not* as the anti-morphism (p. 713),
and path computations illustrating the §2.4 context-projectivity
mechanism. The tables' semantic soundness is certified once and for all
in `Logic/Natural/Soundness.lean`; this file checks the implementations
cell-by-cell against the paper's printed entries.

The final sections formalize the ground fragment of the paper's
projectivity calculus 𝒞 (§3.1) with its soundness theorem
(Theorem 3.1), and the §3.2 worked fragment: the assumption set Γ, the
derivation that *no* ⊑ *not every* is not an extra postulate, and a
concrete model witnessing Γ's satisfiability.
-/

namespace Icard2012

open NaturalLogic NaturalLogic.Relation NaturalLogic.Signature

/-! ### The join table (Lemma 1.5, p. 710) -/

example : join .forward .forward = .forward := rfl       -- ⊑ ⋈ ⊑ = ⊑
example : join .negation .negation = .equiv := rfl       -- ^ ⋈ ^ = ≡
example : join .alternation .negation = .forward := rfl  -- | ⋈ ^ = ⊑
example : join .negation .forward = .cover := rfl        -- ^ ⋈ ⊑ = ⌣
example : join .forward .negation = .alternation := rfl  -- ⊑ ⋈ ^ = |
example : join .cover .negation = .reverse := rfl        -- ⌣ ⋈ ^ = ⊒

-- Printed below the table: ≡ ⋈ R = R = R ⋈ ≡ and # ⋈ R = # = R ⋈ #.
example : ∀ R : Relation, 1 * R = R ∧ R * 1 = R := by decide
example : ∀ R : Relation, ⊤ * R = ⊤ ∧ R * ⊤ = ⊤ := by decide

-- Lemma 1.5 is an equality: each printed cell is the *least* sound relation.
example : IsLeast {T : Relation | ∀ x y z : Finset (Fin 3),
    Relation.Holds .forward x y → Relation.Holds .negation y z → T.Holds x z}
    .alternation := Relation.isLeast_join .forward .negation

/-! ### The refinement order (§2.2) -/

example : ¬ ((Signature.all : Signature) ≤ .mono) := by decide
example : (Signature.mono : Signature) ≤ .all := by decide
example : (Signature.anti : Signature) ≤ .all := by decide
example : (Signature.addMult : Signature) ≤ .additive := by decide
example : (Signature.antiAddMult : Signature) ≤ .anti := by decide
example : ¬ ((Signature.mono : Signature) ≤ .additive) := by decide
example : ¬ ((Signature.additive : Signature) ≤ .mult) := by decide

/-! ### The projectivity tables (Lemma 2.4, p. 715)

Forward entailment (*dog* ⊑ *animal*), negation, alternation
(*cat* | *dog*), and cover (*animal* ⌣ *nondog*) pushed through each
signature class. -/

example : project .forward .mono = .forward := rfl        -- + : f(dog) ⊑ f(animal)
example : project .forward .anti = .reverse := rfl        -- − : f(dog) ⊒ f(animal)
example : project .forward .additive = .forward := rfl    -- ⊕ : as mono for ⊑
example : project .forward .antiAddMult = .reverse := rfl -- ◇⊟ : as anti for ⊑
example : project .negation .mono = .independent := rfl   -- + : ^ weakens to #
example : project .negation .anti = .independent := rfl   -- − : ^ weakens to #
example : project .negation .additive = .cover := rfl     -- ⊕ : x∨y=1 ⟹ f(x)∨f(y)=1
example : project .negation .mult = .alternation := rfl   -- ⊞ : x∧y=0 ⟹ f(x)∧f(y)=0
example : project .negation .antiAddMult = .negation := rfl -- ◇⊟ : ^ preserved
example : project .alternation .mono = .independent := rfl  -- + : can't track |
example : project .alternation .mult = .alternation := rfl  -- ⊞ : | preserved
example : project .alternation .additive = .independent := rfl -- ⊕ : | lost
example : project .alternation .antiMult = .cover := rfl    -- ⊟ : | flips to ∼
example : project .alternation .antiAddMult = .cover := rfl -- ◇⊟ : | flips to ∼
example : project .cover .additive = .cover := rfl          -- ⊕ : ∼ preserved
example : project .cover .mult = .independent := rfl        -- ⊞ : ∼ lost
example : project .cover .antiAdd = .alternation := rfl     -- ◇ : ∼ flips to |
example : project .cover .antiAddMult = .alternation := rfl -- ◇⊟ : ∼ flips to |

/-! ### The composition table (Lemma 2.7, p. 716) -/

example : compose .anti .anti = .mono := rfl                   -- − ∘ − = +
example : compose .antiAddMult .antiAddMult = .addMult := rfl  -- ◇⊟ ∘ ◇⊟ = ⊕⊞
example : compose .additive .additive = .additive := rfl       -- ⊕ ∘ ⊕ = ⊕
example : compose .antiAdd .additive = .antiAdd := rfl         -- ◇ ∘ ⊕ = ◇
example : compose .addMult .anti = .anti := rfl                -- ⊕⊞ ∘ − = −
example : compose .mult .antiAdd = .antiAdd := rfl             -- ⊞ ∘ ◇ = ◇
example : compose .additive .antiMult = .antiMult := rfl       -- ⊕ ∘ ⊟ = ⊟
example : compose .antiMult .antiAdd = .additive := rfl        -- ⊟ ∘ ◇ = ⊕
example : compose .mult .mult = .mult := rfl                   -- ⊞ ∘ ⊞ = ⊞
example : compose .additive .antiAdd = .anti := rfl            -- ⊕ ∘ ◇ = −
example : compose .all .mono = .all := rfl                     -- • absorbing
example : compose .anti .all = .all := rfl                     -- • absorbing

/-! ### The polarity coarsening -/

example : toContextPolarity .all = .nonMonotonic := rfl
example : toContextPolarity .mono = .upward := rfl
example : toContextPolarity .additive = .upward := rfl
example : toContextPolarity .mult = .upward := rfl
example : toContextPolarity .addMult = .upward := rfl
example : toContextPolarity .anti = .downward := rfl
example : toContextPolarity .antiAdd = .downward := rfl
example : toContextPolarity .antiMult = .downward := rfl
example : toContextPolarity .antiAddMult = .downward := rfl

example : ContextPolarity.compose .upward .downward = .downward := rfl
example : ContextPolarity.compose .downward .downward = .upward := rfl
example : ContextPolarity.compose .downward .upward = .downward := rfl

/-! ### Path computations (§2.4)

A position's signature is the monoid product along the path from root
to target (his `pro(s(u)) = top(s) ∘ pro(u)`); the sentences are
illustrations of the mechanism, not the paper's own examples. -/

-- "animal" in *Every animal runs*: path = [◇] (every-restrictor)
example : contextProjectivity [.antiAdd] = .antiAdd := rfl
-- "runs" in *Every animal runs*: path = [⊞] (every-scope)
example : contextProjectivity [.mult] = .mult := rfl
-- "cat" in *No big cat runs*: path = [◇, ⊕⊞] — a morphism leaves ◇ intact
example : contextProjectivity [.antiAdd, .addMult] = .antiAdd := rfl
-- "runs" in *It's not the case that every animal runs*: [◇⊟, ⊞] = ⊟
example : contextProjectivity [.antiAddMult, .mult] = .antiMult := rfl
-- Double negation is a morphism …
example : contextProjectivity [.antiAddMult, .antiAddMult] = .addMult := rfl
-- … and hence an upward context
example : toContextPolarity (contextProjectivity [.antiAddMult, .antiAddMult]) =
    .upward := rfl

/-! ### The negation signature

*Not* is anti-additive and anti-multiplicative (p. 713); ⊖ is its own
inverse — the only non-identity signature with one (p. 716). -/

example : toContextPolarity negationSignature = .downward := rfl
example : negationSignature * negationSignature = .addMult := rfl
example : negationSignature ^ 2 = .addMult := rfl
-- ◇⊟ is its own inverse up to the monoid identity on non-• signatures
example : negationSignature * negationSignature * negationSignature = negationSignature := rfl
example : negationSignature * .mult = .antiMult := rfl
-- not(not(every …))-scope: ⊟ ∘ ◇⊟ ∘ ◇⊟ = ⊟
example : .antiMult * negationSignature * negationSignature = .antiMult := rfl

/-! ### The calculus 𝒞 of relations (§3.1)

The ground fragment of the projectivity calculus: Reflexivity, the
four Symmetry rules, Absurdity, and Composition, over an assumption
set of relational statements. The Substitution rule needs the
signature-typed term language and is not yet formalized; neither is
the paper's closing observation that 𝒞 is incomplete (terms of
additive and anti-additive type always alternate, underivably from
`∅`) — completeness is left open there. -/

section Calculus

variable {ι : Type*}

/-- The ground fragment of the projectivity calculus 𝒞
([icard-2012] §3.1, p. 719), deriving relational statements between
terms `ι` from an assumption set `Γ`. -/
inductive Derives (Γ : ι → Relation → ι → Prop) : ι → Relation → ι → Prop
  | ax {t R t'} : Γ t R t' → Derives Γ t R t'
  | refl (t : ι) : Derives Γ t .forward t
  | symm_forward {t t'} : Derives Γ t .forward t' → Derives Γ t' .reverse t
  | symm_reverse {t t'} : Derives Γ t .reverse t' → Derives Γ t' .forward t
  | symm_alternation {t t'} :
      Derives Γ t .alternation t' → Derives Γ t' .alternation t
  | symm_cover {t t'} : Derives Γ t .cover t' → Derives Γ t' .cover t
  | absurd {t s s'} (R : Relation) :
      Derives Γ t .alternation t → Derives Γ s R s'
  | comp {t u v R S} :
      Derives Γ t R u → Derives Γ u S v → Derives Γ t (R * S) v

/-- [icard-2012]'s Theorem 3.1 for the ground fragment: a derivable
statement holds in every `⊥`-free model of the assumptions.
Composition is sound by `Relation.Holds.join`; Absurdity is the one
rule needing nonvacuity, since `t | t` forces `⟦t⟧ = ⊥`. -/
theorem Derives.sound {β : Type*} [DistribLattice β] [BoundedOrder β]
    {Γ : ι → Relation → ι → Prop} {v : ι → β}
    (hΓ : ∀ {t R t'}, Γ t R t' → R.Holds (v t) (v t'))
    (hv : ∀ i, v i ≠ ⊥) {t R t'} (h : Derives Γ t R t') :
    R.Holds (v t) (v t') := by
  induction h with
  | ax h => exact hΓ h
  | refl t => exact le_refl _
  | symm_forward _ ih => exact ih
  | symm_reverse _ ih => exact ih
  | symm_alternation _ ih => exact ih.symm
  | symm_cover _ ih => exact ih.symm
  | absurd _ _ ih => exact (hv _ (disjoint_self.mp ih)).elim
  | comp _ _ ih₁ ih₂ => exact ih₁.join ih₂

end Calculus

/-! ### The worked fragment (§3.2)

The paper's mini-lexicon and its assumption set Γ; the derivation that
*no* ⊑ *not every* needs no extra postulate; and a concrete model over
the three-atom Boolean algebra witnessing that Γ is satisfiable. -/

/-- The constants of the §3.2 fragment that Γ relates. -/
inductive Item where
  | every | some | no | notEvery | safe | dangerous | giantSquid | cephalopod
  deriving DecidableEq, Fintype, Repr

/-- The §3.2 assumption set Γ: *every* ^ *not every*, *some* ^ *no*,
*no* | *every*, *safe* | *dangerous*, *giant squid* ⊑ *cephalopod*. -/
inductive Assumption : Item → Relation → Item → Prop
  | everyNegNotEvery : Assumption .every .negation .notEvery
  | someNegNo : Assumption .some .negation .no
  | noAltEvery : Assumption .no .alternation .every
  | safeAltDangerous : Assumption .safe .alternation .dangerous
  | squidLeCephalopod : Assumption .giantSquid .forward .cephalopod

/-- §3.2: *no* ⊑ *not every* is derivable, not postulated —
Composition on *no* | *every* and *every* ^ *not every*, with
`| ⋈ ^ = ⊑`. -/
theorem derives_no_forward_notEvery :
    Derives Assumption .no .forward .notEvery :=
  .comp (.ax Assumption.noAltEvery) (.ax Assumption.everyNegNotEvery)

/-- A model of the §3.2 assumptions over the three-atom Boolean
algebra. -/
def squidModel : Item → Finset (Fin 3)
  | .every => {0}
  | .notEvery => {1, 2}
  | .some => {0, 2}
  | .no => {1}
  | .safe => {2}
  | .dangerous => {0, 1}
  | .giantSquid => {0}
  | .cephalopod => {0, 1}

theorem squidModel_models {t R t'} (h : Assumption t R t') :
    R.Holds (squidModel t) (squidModel t') := by
  cases h <;> decide

theorem squidModel_ne_bot : ∀ i, squidModel i ≠ ⊥ := by decide

-- Soundness applied: the derived statement holds in the model.
example : squidModel .no ≤ squidModel .notEvery :=
  derives_no_forward_notEvery.sound (λ h => squidModel_models h)
    squidModel_ne_bot

end Icard2012
