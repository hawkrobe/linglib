import Linglib.Core.InformationTheory
import Linglib.Theories.Syntax.ConstructionGrammar.Basic
import Linglib.Theories.Pragmatics.RSA.Extensions.LexicalUncertainty.Basic

/-!
# Grammar as Distribution

@cite{dunn-2025} @cite{bergen-levy-goodman-2016}

A grammar is a frequency profile over constructions. This
generalizes lexical uncertainty: where LU varies meaning
assignments, grammar uncertainty varies both meaning AND production frequency.

## Architecture

Two types capture the individual–population hierarchy from @cite{dunn-2025}
variationist CxG:

- `GrammarDist C` — frequency profile over constructions (individual grammar)
- `Grammar C W` — frequency + interpretation (connects to RSA `Lexicon`)

@cite{dunn-2025} measures variation across three dimensions — individuals,
populations (dialects), and contexts (registers) — using Shannon entropy for
constructional diversity and Jensen-Shannon divergence for grammar similarity.
-/

namespace ConstructionGrammar

open Core.InformationTheory

-- ============================================================================
-- §1. Core Types
-- ============================================================================

/-- A non-negative frequency profile over constructions.

An individual's grammar is a frequency-weighted profile over constructions —
not a binary set (in/out) but a weighting reflecting how often each
construction is used. Note: this does not enforce normalization (Σ freq = 1);
the weights are relative frequencies, not probabilities. -/
structure GrammarDist (C : Type) where
  freq : C → ℚ
  freq_nonneg : ∀ c, 0 ≤ freq c

/-- A full grammar: frequency profile + interpretation function.

Extends `GrammarDist` with a meaning function mapping each construction
to a graded truth function over worlds. This connects grammar distributions
to RSA's literal semantics and to @cite{bergen-levy-goodman-2016}'s
`Lexicon` type. -/
structure Grammar (C W : Type) extends GrammarDist C where
  meaning : C → W → ℚ

-- ============================================================================
-- §2. Entropy and Similarity
-- ============================================================================

section EntropyAndSimilarity
variable {C : Type} [BEq C]

/-- Constructional diversity: Shannon entropy of the frequency profile.

Higher entropy = more diverse construction usage. @cite{dunn-2025} uses
grammar entropy to compare registers, dialects, and individual variation
within L1 populations. -/
def GrammarDist.entropyOver (g : GrammarDist C) (inventory : List C) : ℚ :=
  entropy (inventory.map fun c => (c, g.freq c))

/-- Jensen-Shannon divergence between two grammars over a shared inventory.

Symmetric, bounded, and a metric (after sqrt). Used by @cite{dunn-2025} to
measure register distance, dialect boundaries, and L1-L2 differences. -/
def GrammarDist.jsd (p q : GrammarDist C) (inventory : List C) : ℚ :=
  jsdOf inventory p.freq q.freq

end EntropyAndSimilarity

-- ============================================================================
-- §3. Connection to Lexicon (@cite{bergen-levy-goodman-2016})
-- ============================================================================

section LexiconConnection
variable {C W U : Type}

/-- Project a grammar to a lexicon by forgetting frequency.

A `Lexicon` is a meaning assignment `C → W → ℚ`.
A `Grammar` is a meaning assignment PLUS a frequency profile. The
projection forgets frequency, retaining only interpretation. -/
def Grammar.toLexicon (g : Grammar C W) : Lexicon C W where
  meaning := g.meaning

/-- Embed a lexicon as a grammar with uniform frequency.

This is the key structural claim: lexical uncertainty
is the special case of grammar uncertainty where only meaning varies and
production frequency is uniform across constructions.

Standard LU uses a flat prior over lexicons; grammar uncertainty extends
this by additionally varying production frequency. -/
def grammarOfLexicon (L : Lexicon U W) : Grammar U W where
  freq := fun _ => 1
  freq_nonneg := fun _ => by norm_num
  meaning := L.meaning

/-- Round-trip: Lexicon → Grammar → Lexicon preserves meaning.

The meaning function is unchanged by embedding into Grammar and projecting
back. This makes `toLexicon ∘ grammarOfLexicon` the identity on meaning. -/
theorem toLexicon_grammarOfLexicon_meaning (L : Lexicon U W) (u : U) (w : W) :
    (grammarOfLexicon L).toLexicon.meaning u w = L.meaning u w := rfl

/-- Lexical uncertainty embeds into grammar uncertainty (meaning preserved).

Every `Lexicon` embeds as a `Grammar` with uniform frequency, preserving
the meaning function. The embedding is meaning-preserving: `toLexicon`
after `grammarOfLexicon` recovers the original meaning. Grammar uncertainty
extends LU by additionally varying production frequency. -/
theorem grammar_subsumes_lexical_uncertainty (L : Lexicon U W) :
    (grammarOfLexicon L).toLexicon.meaning = L.meaning := rfl

end LexiconConnection

-- ============================================================================
-- §4. Grammar as RSA Cost
-- ============================================================================

section RSACost
variable {C : Type}

/-- Production cost derived from frequency: -log₂(freq).

Frequent constructions are cheap; rare ones are expensive. This connects
@cite{dunn-2025}'s frequency-based grammar to RSA's utterance cost: setting
`cost(u) = -log₂(freq(u))` in S1's action-based scoring rule grounds
utterance cost in production frequency rather than stipulating it. -/
def GrammarDist.cost (g : GrammarDist C) (c : C) : ℚ :=
  if g.freq c ≤ 0 then 10
  else -log2Approx (g.freq c)

end RSACost

end ConstructionGrammar
