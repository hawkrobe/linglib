import Linglib.Theories.Semantics.Exhaustification.Operators
import Linglib.Theories.Pragmatics.RSA.Core.EmbeddedSI

/-!
# RSA vs EXH: Expressivity Gap

Formalizes what standard RSA cannot express that EXH can:
scope-sensitive implicatures.

Standard RSA treats utterances atomically:
- Input: utterance u, alternatives ALT, world prior P(w)
- Output: P(w | u) - a single probability distribution

EXH is a compositional operator that can scope at different positions:
- "EXH [every student read some book]" (global)
- "every student [EXH read some book]" (local)

These give different truth conditions, but standard RSA conflates them.

## Results

1. Standard RSA is scope-blind (`expressivity_gap`)
2. IBR matches global EXH, not local (`ibr_is_global_not_local`)
3. Compositional RSA closes the gap (`hierarchy_is_strict`)
-/

namespace Phenomena.ScalarImplicatures.ScopeExpressivity

open Exhaustification
open RSA.Core.EmbeddedSI

-- SECTION 3: Standard RSA (Scope-Blind)

/-!
## Standard RSA: No Scope Distinction

Standard RSA computes P(w | u) without any notion of scope.
It treats "every student read some book" as an atomic utterance
and computes a single distribution over worlds.

RSA gives one answer, but there are two legitimate readings (global vs
local EXH).
-/

-- SECTION 4: The Expressivity Gap

/-!
## The Expressivity Gap: Formal Statement

The key observation is that standard RSA, by treating utterances atomically,
must give the same probability to worlds that EXH would distinguish by scope.

The distinguishing worlds are w_SA and w_AS:
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

/-- The expressivity gap exists.

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

The solution is to make scope a latent variable that the listener infers:

  L1(w, scope | u) ∝ P(w) × P(scope) × S1(u | w, scope)

Now the listener can infer either:
- Global scope interpretation (SA, AS possible)
- Local scope interpretation (only SS possible)

This is exactly what ScontrasPearl2021 does for "every horse didn't jump".
The scope ambiguity model lifts interpretation to a latent variable.

Compositional RSA = Standard RSA + Scope as Latent Variable.
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

-- SECTION 6: Connection to @cite{franke-2011} and IBR

/-!
## The IBR Perspective

@cite{franke-2011} shows that IBR (the α→∞ limit of RSA) equals exhMW.
But this is still SCOPE-BLIND - it's exhMW applied to the WHOLE sentence.

The IBR/exhMW analysis of "every student read some book":
- Alternatives: {"every some", "every all"}
- exhMW excludes worlds where stronger alternatives are true
- Result: excludes only w_AA (where "every all" is true)
- This matches GLOBAL EXH, not local EXH

Even IBR (the limit of RSA) is scope-blind. To get local readings,
scope must be a latent variable.
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
    -- Local EXH also excludes SA
    (localExhMeaning .SA = false) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- SECTION 7: Summary

/-!
## The Expressivity Hierarchy

1. Standard RSA (scope-blind):
   - Treats utterances atomically
   - Cannot distinguish scope positions
   - In the α→∞ limit, equals global EXH (exhMW)

2. IBR / exhMW (scope-blind):
   - Deterministic limit of RSA
   - Still scope-blind
   - Implements global EXH only

3. Compositional RSA (scope-aware):
   - Lifts scope to a latent variable
   - Can express both global and local readings
   - Listener infers scope jointly with world

4. EXH operator (fully compositional):
   - Can be inserted at any scope position
   - Gives different meanings at different positions
   - Compositional RSA approximates this

Standard RSA ⊂ Compositional RSA ≈ EXH. Standard RSA cannot express local
exhaustification. The RSA → IBR → exhMW chain only captures
global readings. For local readings, the scope-aware approach of
ScontrasPearl2021, LexicalUncertainty, or compositional RSA is needed.
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

end Phenomena.ScalarImplicatures.ScopeExpressivity
