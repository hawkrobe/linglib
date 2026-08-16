/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Logic.Natural.Basic

/-!
# [icard-2012]: Inclusion and Exclusion in Natural Language

Table verifications for [icard-2012]'s relation algebra against the
substrate implementations in `Logic/Natural/Basic.lean`: the join table
(Lemma 1.5, p. 710 — the printed cells, independently certified against
the non-strict `Holds` reading by `NLRelation.Holds.join`), the
projectivity tables (Lemma 2.4, p. 715), the composition table
(Lemma 2.7, p. 716) with its signature order (§2.2), the polarity
coarsening, the classification of *not* as the anti-morphism (p. 713),
and path computations illustrating the §2.4 context-projectivity
mechanism. The tables' semantic soundness is certified once and for all
in `Logic/Natural/Soundness.lean`; this file checks the implementations
cell-by-cell against the paper's printed entries.
-/

namespace Icard2012

open NaturalLogic NaturalLogic.NLRelation NaturalLogic.EntailmentSig

/-! ### The join table (Lemma 1.5, p. 710) -/

example : join .forward .forward = .forward := rfl       -- ⊑ ⋈ ⊑ = ⊑
example : join .negation .negation = .equiv := rfl       -- ^ ⋈ ^ = ≡
example : join .alternation .negation = .forward := rfl  -- | ⋈ ^ = ⊑
example : join .negation .forward = .cover := rfl        -- ^ ⋈ ⊑ = ⌣
example : join .forward .negation = .alternation := rfl  -- ⊑ ⋈ ^ = |
example : join .cover .negation = .reverse := rfl        -- ⌣ ⋈ ^ = ⊒

/-! ### The refinement order (§2.2) -/

example : ¬ ((EntailmentSig.all : EntailmentSig) ≤ .mono) := by decide
example : (EntailmentSig.mono : EntailmentSig) ≤ .all := by decide
example : (EntailmentSig.anti : EntailmentSig) ≤ .all := by decide
example : (EntailmentSig.addMult : EntailmentSig) ≤ .additive := by decide
example : (EntailmentSig.antiAddMult : EntailmentSig) ≤ .anti := by decide
example : ¬ ((EntailmentSig.mono : EntailmentSig) ≤ .additive) := by decide
example : ¬ ((EntailmentSig.additive : EntailmentSig) ≤ .mult) := by decide

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

example : toContextPolarity negationSig = .downward := rfl
example : negationSig * negationSig = .addMult := rfl
example : negationSig ^ 2 = .addMult := rfl
-- ◇⊟ is its own inverse up to the monoid identity on non-• signatures
example : negationSig * negationSig * negationSig = negationSig := rfl
example : negationSig * .mult = .antiMult := rfl
-- not(not(every …))-scope: ⊟ ∘ ◇⊟ ∘ ◇⊟ = ⊟
example : .antiMult * negationSig * negationSig = .antiMult := rfl

end Icard2012
