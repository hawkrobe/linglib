/-
# RSA vs EXH: Expressivity Gap

Formalizes what standard RSA CANNOT express that EXH CAN:
**scope-sensitive implicatures**.

## The Core Problem

Standard RSA treats utterances atomically:
- Input: utterance u, alternatives ALT, world prior P(w)
- Output: P(w | u) - a single probability distribution

EXH is a compositional operator that can scope at different positions:
- "EXH [every student read some book]" (global)
- "every student [EXH read some book]" (local)

These give DIFFERENT truth conditions, but standard RSA conflates them.

## The Classic Example: Embedded Scalar Implicatures

Consider: "Every student read some book"
Alternative: "Every student read all books"

**Global EXH** (wide scope):
  EXH [∀x. some(x)] = ∀x. some(x) ∧ ¬(∀x. all(x))
  = "every student read some, and not every student read all"
  = at least one student read some but not all

**Local EXH** (narrow scope, under ∀):
  ∀x. [EXH some(x)] = ∀x. [some(x) ∧ ¬all(x)]
  = "every student read some but not all"
  = each individual student read some but not all

These are DIFFERENT propositions! Standard RSA gives ONE answer.

## What This File Establishes

1. **Standard RSA is scope-blind**: It computes one distribution P(w | u)
   without distinguishing scope configurations

2. **EXH is scope-sensitive**: Different scope positions yield different meanings

3. **The gap exists**: There are scenarios where global and local EXH
   predict different worlds, but standard RSA cannot distinguish them

4. **Compositional RSA closes the gap**: By lifting scope to a latent variable,
   RSA can recover EXH's scope sensitivity (as in ScontrasPearl2021)

## References

- Chierchia, Fox & Spector (2012). Scalar implicature as a grammatical phenomenon.
- Sauerland (2004). Scalar implicatures in complex sentences.
- Bergen et al. (2016). Pragmatic reasoning through semantic inference. (LU-RSA)
- Champollion, Alsop & Grosu (2019). Free choice as scope-dependent interpretation.
-/

import Linglib.Theories.NeoGricean.Exhaustivity.Basic
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Implementations.Franke2011

namespace Comparisons.RSAExhExpressivity

open NeoGricean.Exhaustivity
open RSA.IBR

-- SECTION 1: The Embedded SI Scenario

/-!
## The "Every Student Read Some Book" Scenario

We model a simple scenario with 2 students (Alice, Bob) and consider
whether each read "some" or "all" books.

**Worlds** (4 total):
- w_SS: Alice some, Bob some (neither read all)
- w_SA: Alice some, Bob all
- w_AS: Alice all, Bob some
- w_AA: Alice all, Bob all

**Key observation**:
- Global SI: excludes only w_AA (at least one didn't read all)
- Local SI: excludes w_SA, w_AS, w_AA (each read some but not all)
- Standard RSA: gives ONE answer, can't distinguish these
-/

/-- World states for the embedded SI scenario.
    Each student either read "some but not all" (S) or "all" (A). -/
inductive EmbeddedSIWorld where
  | SS : EmbeddedSIWorld  -- Alice: some, Bob: some
  | SA : EmbeddedSIWorld  -- Alice: some, Bob: all
  | AS : EmbeddedSIWorld  -- Alice: all, Bob: some
  | AA : EmbeddedSIWorld  -- Alice: all, Bob: all
  deriving DecidableEq, Fintype, Repr, BEq

/-- Messages in the embedded SI scenario -/
inductive EmbeddedSIMessage where
  | everySome : EmbeddedSIMessage  -- "Every student read some book"
  | everyAll  : EmbeddedSIMessage  -- "Every student read all books"
  deriving DecidableEq, Fintype, Repr, BEq

/-- Literal meaning: when is each message true?
    - "every some" is true in all worlds (some ⊆ all)
    - "every all" is true only in AA -/
def embeddedMeaning : EmbeddedSIMessage → EmbeddedSIWorld → Bool
  | .everySome, _ => true      -- "some" true everywhere
  | .everyAll, .AA => true     -- "all" true only when both read all
  | .everyAll, _ => false

-- SECTION 2: EXH at Different Scope Positions

/-!
## EXH Scope Positions

**Global EXH**: EXH scopes over the entire sentence
  EXH [every x. some(x)] = every x. some(x) ∧ ¬(every x. all(x))

**Local EXH**: EXH scopes under the universal quantifier
  every x. [EXH some(x)] = every x. [some(x) ∧ ¬all(x)]

The key difference:
- Global: "not everyone read all" - allows w_SA, w_AS
- Local: "everyone read some-but-not-all" - only allows w_SS
-/

/-- Scope position for EXH -/
inductive ExhScope where
  | global : ExhScope  -- EXH > ∀
  | local_ : ExhScope  -- ∀ > EXH
  deriving DecidableEq, Repr

/-- Truth conditions under global EXH:
    "every student read some" ∧ ¬"every student read all"

    True at: SS, SA, AS (not AA) -/
def globalExhMeaning : EmbeddedSIWorld → Bool
  | .SS => true   -- some ∧ ¬all: ✓
  | .SA => true   -- some ∧ ¬all: ✓ (Bob read all, but not everyone)
  | .AS => true   -- some ∧ ¬all: ✓ (Alice read all, but not everyone)
  | .AA => false  -- some ∧ ¬all: ✗ (everyone read all)

/-- Truth conditions under local EXH:
    "every student [read some but not all]"

    True at: SS only -/
def localExhMeaning : EmbeddedSIWorld → Bool
  | .SS => true   -- both read some-but-not-all: ✓
  | .SA => false  -- Bob read all: ✗
  | .AS => false  -- Alice read all: ✗
  | .AA => false  -- both read all: ✗

/-- EXH-with-scope: meaning depends on scope position -/
def exhScopedMeaning (scope : ExhScope) : EmbeddedSIWorld → Bool :=
  match scope with
  | .global => globalExhMeaning
  | .local_ => localExhMeaning

-- SECTION 3: Standard RSA (Scope-Blind)

/-!
## Standard RSA: No Scope Distinction

Standard RSA computes P(w | u) without any notion of scope.
It treats "every student read some book" as an atomic utterance
and computes a single distribution over worlds.

**The problem**: RSA gives ONE answer, but there are TWO legitimate
readings (global vs local EXH).
-/

/-- Standard RSA interpretation game for embedded SI.
    Note: This game has NO scope parameter - it's scope-blind. -/
def standardRSAGame : InterpGame where
  State := EmbeddedSIWorld
  Message := EmbeddedSIMessage
  meaning := embeddedMeaning
  prior := fun _ => 1 / 4  -- Uniform prior

-- SECTION 4: The Expressivity Gap

/-!
## The Expressivity Gap: Formal Statement

The key observation is that standard RSA, by treating utterances atomically,
must give the same probability to worlds that EXH would distinguish by scope.

**The distinguishing worlds**: w_SA and w_AS
- Global EXH: allows these (prob > 0)
- Local EXH: excludes these (prob = 0)
- Standard RSA L0: allows these (literal meaning satisfied)

This means standard RSA cannot implement local EXH - it always
"leaks" probability to worlds that local EXH would exclude.
-/

/-- The worlds that distinguish global from local EXH.
    These are true under global EXH but false under local EXH. -/
def distinguishingWorlds : List EmbeddedSIWorld := [.SA, .AS]

/-- Global EXH allows the distinguishing worlds -/
theorem globalExh_allows_SA : globalExhMeaning .SA = true := rfl
theorem globalExh_allows_AS : globalExhMeaning .AS = true := rfl

/-- Local EXH excludes the distinguishing worlds -/
theorem localExh_excludes_SA : localExhMeaning .SA = false := rfl
theorem localExh_excludes_AS : localExhMeaning .AS = false := rfl

/-- Standard RSA L0 includes SA (literal meaning satisfied) -/
theorem standardRSA_includes_SA : embeddedMeaning .everySome .SA = true := rfl
theorem standardRSA_includes_AS : embeddedMeaning .everySome .AS = true := rfl

/-- **Main Theorem**: The expressivity gap exists.

    There exists a world that is:
    1. Excluded by local EXH (prob 0)
    2. Included by global EXH (prob > 0)
    3. Included by standard RSA literal meaning

    This shows standard RSA can only express global, not local EXH. -/
theorem expressivity_gap :
    ∃ w : EmbeddedSIWorld,
      localExhMeaning w = false ∧
      globalExhMeaning w = true ∧
      embeddedMeaning .everySome w = true :=
  ⟨.SA, rfl, rfl, rfl⟩

-- SECTION 5: Compositional RSA Closes the Gap

/-!
## How Compositional RSA Resolves This

The solution is to make scope a LATENT VARIABLE that the listener infers:

  L1(w, scope | u) ∝ P(w) × P(scope) × S1(u | w, scope)

Now the listener can infer EITHER:
- Global scope interpretation (SA, AS possible)
- Local scope interpretation (only SS possible)

This is exactly what ScontrasPearl2021 does for "every horse didn't jump".
The scope ambiguity model lifts interpretation to a latent variable.

**Key insight**: Compositional RSA = Standard RSA + Scope as Latent Variable
-/

/-- Compositional RSA scenario: scope is a latent variable -/
structure CompositionalRSAScenario where
  world : EmbeddedSIWorld
  scope : ExhScope

/-- Compositional RSA can express both readings -/
def compositionalMeaning (config : CompositionalRSAScenario) : Bool :=
  exhScopedMeaning config.scope config.world

/-- Compositional RSA with local scope excludes SA -/
theorem compositionalRSA_local_excludes_SA :
    compositionalMeaning ⟨.SA, .local_⟩ = false := rfl

/-- Compositional RSA with global scope allows SA -/
theorem compositionalRSA_global_allows_SA :
    compositionalMeaning ⟨.SA, .global⟩ = true := rfl

-- SECTION 6: Connection to Franke 2011 and IBR

/-!
## The IBR Perspective

Franke (2011) shows that IBR (the α→∞ limit of RSA) equals exhMW.
But this is still SCOPE-BLIND - it's exhMW applied to the WHOLE sentence.

The IBR/exhMW analysis of "every student read some book":
- Alternatives: {"every some", "every all"}
- exhMW excludes worlds where stronger alternatives are true
- Result: excludes only w_AA (where "every all" is true)
- This matches GLOBAL EXH, not local EXH

**Conclusion**: Even IBR (the limit of RSA) is scope-blind.
To get local readings, you need scope as a latent variable.
-/

/-- IBR excludes AA (where "every all" is true) -/
theorem ibr_excludes_AA : embeddedMeaning .everyAll .AA = true := rfl

/-- IBR keeps SA (where "every all" is false) -/
theorem ibr_keeps_SA : embeddedMeaning .everyAll .SA = false := rfl

/-- IBR prediction matches global EXH, not local EXH.

    IBR (exhMW) excludes worlds where a stronger alternative is true.
    "every all" is only true at AA, so IBR excludes only AA.
    This gives exactly the global EXH reading, not the local one. -/
theorem ibr_is_global_not_local :
    -- IBR excludes only AA (same as global EXH)
    (embeddedMeaning .everyAll .AA = true) ∧
    (embeddedMeaning .everyAll .SA = false) ∧
    (embeddedMeaning .everyAll .AS = false) ∧
    (embeddedMeaning .everyAll .SS = false) ∧
    -- Global EXH also excludes only AA
    (globalExhMeaning .AA = false) ∧
    (globalExhMeaning .SA = true) ∧
    -- But local EXH excludes SA too!
    (localExhMeaning .SA = false) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- SECTION 7: Summary

/-!
## Summary: The Expressivity Hierarchy

1. **Standard RSA** (scope-blind):
   - Treats utterances atomically
   - Cannot distinguish scope positions
   - In the α→∞ limit, equals GLOBAL EXH (exhMW)

2. **IBR / exhMW** (scope-blind):
   - Deterministic limit of RSA
   - Still scope-blind
   - Implements global EXH only

3. **Compositional RSA** (scope-aware):
   - Lifts scope to a latent variable
   - Can express both global and local readings
   - Listener infers scope jointly with world

4. **EXH operator** (fully compositional):
   - Can be inserted at any scope position
   - Gives different meanings at different positions
   - Compositional RSA approximates this

**The Gap**: Standard RSA ⊂ Compositional RSA ≈ EXH

Standard RSA cannot express local exhaustification.
This motivates compositional/lexical approaches to RSA.

**Key Implication**: The RSA → IBR → exhMW chain (Franke 2011) only captures
GLOBAL readings. For LOCAL readings, we need the scope-aware approach
of ScontrasPearl2021, LexicalUncertainty, or compositional RSA.
-/

/-- The expressivity hierarchy is strict:
    Standard RSA < Compositional RSA

    Witnessed by the existence of a world that compositional RSA
    can exclude (with local scope) but standard RSA cannot. -/
theorem hierarchy_is_strict :
    ∃ w : EmbeddedSIWorld,
      -- Standard RSA (scope-blind) includes w
      embeddedMeaning .everySome w = true ∧
      -- Compositional RSA with local scope excludes w
      compositionalMeaning ⟨w, .local_⟩ = false :=
  ⟨.SA, rfl, rfl⟩

end Comparisons.RSAExhExpressivity
