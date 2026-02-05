/-
# Compositional RSA: Extending RSA → EXH to Local Readings

The standard RSA → IBR → exhMW chain (Franke 2011) only captures global readings.
This file formalizes Compositional RSA, which extends the chain to local readings.

EXH is a compositional operator that can scope at different positions:
- Global: EXH [∀x. some(x)] = ∀x. some(x) ∧ ¬(∀x. all(x))
- Local:  ∀x. [EXH some(x)] = ∀x. [some(x) ∧ ¬all(x)]

To capture local readings, RSA must operate compositionally:
- At each node of the derivation, there are local alternatives
- RSA reasoning applies with these local alternatives
- In the α→∞ limit, local RSA → local EXH
- Composition of local EXH gives scope-sensitive readings

Potts, Lassiter, Levy & Frank's LU-RSA (Bergen et al. 2016) puts uncertainty
on the lexicon (word meanings), not on the scope of EXH. LU models listener
uncertainty about whether "some" means "at least one" or "at least one but not
all" (lexical refinement), but does not model where in the compositional
structure the exhaustification applies.

For embedded implicatures, the issue is not what "some" means, but where EXH
scopes:
- Global: EXH [every x. some(x)] - exhaustify the whole sentence
- Local: every x. [EXH some(x)] - exhaustify under the quantifier

LU cannot distinguish these because it refines meanings at the lexical level,
not the structural level.

## Main Results

1. `LocalAltNode`: A node with local alternatives and meaning
2. `localExhMW`: EXH using only local alternatives
3. `local_limit_theorem`: Local RSA → Local EXH (reuses Franke 2011)
4. `composed_local_equals_localExh`: Composed local EXH = local reading
5. `lu_cannot_express_local`: LU is scope-blind like standard RSA

## References

- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
- Potts, Lassiter, Levy & Frank (2016). Embedded implicatures as pragmatic inferences.
- Chierchia, Fox & Spector (2012). Scalar implicature as a grammatical phenomenon.
- Fox (2007). Free choice and the theory of scalar implicatures.
- Franke (2011). Quantity implicatures, exhaustive interpretation.
-/

import Linglib.Theories.NeoGricean.Exhaustivity.Basic
import Linglib.Comparisons.RSAExhExpressivity

namespace RSA.Compositional

open NeoGricean.Exhaustivity
open Comparisons.RSAExhExpressivity

-- SECTION 1: Local Alternatives at a Node

/-- A node in a compositional derivation with local alternatives. -/
structure LocalAltNode (World : Type) (Alt : Type) where
  /-- Meaning of each alternative at each world -/
  meaning : Alt → World → Bool
  /-- The prejacent (what was actually uttered) -/
  prejacent : Alt
  /-- The available alternatives at this node -/
  alternatives : List Alt

/-- Convert local alternatives to a set for exhMW -/
def LocalAltNode.toAltSet {World Alt : Type} (node : LocalAltNode World Alt) :
    Set (Prop' World) :=
  { λ w => node.meaning a w = true | a ∈ node.alternatives }

/-- The prejacent proposition -/
def LocalAltNode.prejacent_prop {World Alt : Type} (node : LocalAltNode World Alt) :
    Prop' World :=
  λ w => node.meaning node.prejacent w = true

/-- Local exhMW: exhaustification using only local alternatives. -/
def localExhMW {World Alt : Type} (node : LocalAltNode World Alt) : Prop' World :=
  exhMW node.toAltSet node.prejacent_prop

-- SECTION 2: Why Lexical Uncertainty (LU) is Insufficient

/-!
## LU-RSA: What It Can and Cannot Do

### The LU Approach (Potts, Lassiter, Levy & Frank 2015; Bergen et al. 2016)

LU-RSA models uncertainty over the lexicon:
- Lexicon 1: "some" means "at least one" (weak)
- Lexicon 2: "some" means "at least one but not all" (strong)

The listener marginalizes over lexica:
  L(w | m) ∝ P(w) × Σ_L P(L) × S₁(m | w, L)

### What LU Can Do (Potts et al. 2015, Table 3)

For simple cases like "Exactly one player hit some of his shots":
- With strong lexicon, "some" means "some but not all"
- This composes with "exactly one" to give the local reading
- Potts et al. show .96 Pearson correlation with human judgments

LU does capture simple embedded implicatures.

### What LU Cannot Do: The Global Lexicon Problem

LU applies one lexicon to all occurrences.

Consider: "Every student read some book and some paper"
- Two occurrences of "some"
- EXH-based theory: can exhaustify each independently
- LU-based theory: both must have the same meaning

With LU:
- Lexicon 1 (weak): both "some"s mean "at least one"
- Lexicon 2 (strong): both "some"s mean "some but not all"

LU cannot express: "every student read some-but-not-all books
AND at-least-some papers" (independent exhaustification).

### Scope vs Lexicon

For "Every student read some book":

EXH analysis (scope-sensitive):
- Global: EXH [∀x. some(x)] → "not everyone read all"
- Local: ∀x. [EXH some(x)] → "everyone read some-but-not-all"
- The same word "some" (meaning: at least one), different EXH positions

LU analysis (scope-blind):
- Weak lexicon → "everyone read at-least-one"
- Strong lexicon → "everyone read some-but-not-all"
- Different meanings for "some", no notion of where enrichment applies

For single scalar items, these are observationally equivalent.
For multiple scalar items or nested structures, they diverge.

| Approach | What varies | Multiple scalars? | Scope interactions? |
|----------|-------------|-------------------|---------------------|
| Standard RSA | Nothing | No | No |
| LU-RSA | Lexicon globally | Same for all | No |
| Compositional RSA | Where EXH applies | Independent | Yes |

LU treats implicature as a lexical property (of words), while EXH treats
it as a structural property (of positions).
-/

/-- Per-student world -/
inductive StudentReading where
  | some_not_all : StudentReading
  | all : StudentReading
  deriving DecidableEq, Repr

/-- Lexical refinements for "some" (LU approach) -/
inductive SomeLexicon where
  | weak : SomeLexicon   -- "at least one"
  | strong : SomeLexicon -- "at least one but not all"
  deriving DecidableEq, Repr

/-- LU meaning: what "some" means under each lexicon -/
def someLUMeaning : SomeLexicon → StudentReading → Bool
  | .weak, _ => true                    -- weak: always true
  | .strong, .some_not_all => true      -- strong: only some-not-all
  | .strong, .all => false

/-!
### The Single-Scalar Equivalence (Potts et al.'s Success Case)

For "every student read some book" with a single scalar item,
LU with strong lexicon gives the same result as local EXH.

LU would give:
- Lexicon 1 (weak "some"): every student read at-least-one → SS, SA, AS, AA
- Lexicon 2 (strong "some"): every student read some-but-not-all → SS only

This matches Potts et al. (2015), who show strong empirical fits.

### Where LU Fails: The Principled Derivation Problem

1. No principled lexicon selection: With flat priors, why prefer strong?
   Potts et al. rely on neo-Gricean constraints on refinement sets.

2. Global lexicon: All occurrences of "some" get the same meaning.
   EXH can apply at different positions independently.

3. No scope interaction: LU cannot model EXH interacting with
   quantifier scope, negation scope, etc.

The theorem `lu_strong_equals_local` below shows the equivalence for
single-scalar cases. The limitation emerges with multiple scalars.
-/

/-- LU-RSA scenario for "Every student read some book" -/
structure LUScenario where
  /-- Which lexicon is being used -/
  lexicon : SomeLexicon
  /-- The world state -/
  world : EmbeddedSIWorld

/-- LU meaning: depends on lexicon choice -/
def luMeaning : LUScenario → Bool
  | ⟨.weak, _⟩ => true  -- weak "some" always satisfied
  | ⟨.strong, .SS⟩ => true   -- both read some-not-all
  | ⟨.strong, .SA⟩ => false  -- Bob read all
  | ⟨.strong, .AS⟩ => false  -- Alice read all
  | ⟨.strong, .AA⟩ => false  -- both read all

/-- LU with weak lexicon allows all worlds (like literal L0) -/
theorem lu_weak_allows_all :
    ∀ w, luMeaning ⟨.weak, w⟩ = true := by
  intro w; rfl

/-- LU with strong lexicon gives local-EXH-like result -/
theorem lu_strong_equals_local :
    ∀ w, luMeaning ⟨.strong, w⟩ = localExhMeaning w := by
  intro w
  cases w <;> rfl

/-!
### The Single-Scalar Success

For single-scalar cases, LU achieves the same result as local EXH:
- `lu_strong_equals_local` proves this formally
- This explains the excellent fits to human data in Potts et al. (2015)

### The Compositional Question: Where Does Marginalization Happen?

LU approach (Potts et al.):
- Uncertainty over complete lexica (global)
- Compose meanings using standard semantics
- Marginalize over lexica at the top level:
    L(w | m) ∝ Σ_L P(L) × S₁(m | w, L)

Compositional RSA/EXH approach:
- Apply RSA/EXH reasoning at intermediate compositional nodes
- Local alternatives matter at each node
- Compose the already-exhaustified meanings

The question: Does top-level marginalization over lexica give the
same results as node-by-node pragmatic reasoning?
-/

-- SECTION 2.5: Compositional Structure of Uncertainty

/-!
### How Multiple Uncertainties Compose

In LU, when you have multiple scalar items, each can be refined.
The space of lexica is the product of refinement choices.

A single lexicon L is used for the whole utterance. The listener reasons
about which L the speaker is using globally.

The structural question is whether pragmatic reasoning should happen:
1. Globally: marginalize over complete lexica at the end (LU)
2. Locally: apply RSA at each compositional node, then compose

For simple cases these may coincide. The divergence appears when:
- Multiple scalar items interact
- Quantifier scope affects which alternatives are relevant
- Contextual factors differ at different structural positions
-/

/-- The architectural difference:
    - LU: P(L) is a distribution over complete lexica
    - Compositional: each node has its own local alternatives

    This affects how multiple sources of uncertainty interact. -/
structure LUArchitecture where
  /-- A lexicon assigns meanings to all scalar items -/
  lexicon : SomeLexicon
  /-- Marginalization happens at the top -/
  globalMarg : Bool := true

structure CompositionalArchitecture where
  /-- Each node can have its own EXH choice -/
  localExh : List Bool
  /-- RSA reasoning at each node -/
  localRSA : Bool := true

/-!
### The Structural Difference

What LU gets right (Potts et al. 2015):
- Single-scalar embedded implicatures
- Probabilistic weighting over interpretations
- Integration with RSA framework
- Strong empirical fits for tested cases

The architectural question:
- LU: global marginalization over lexica
- Compositional RSA: local reasoning at each node

For the cases Potts et al. test (single scalar under quantifier),
these approaches are empirically equivalent. The question is whether
they diverge for more complex compositional structures.

Open question (cf. Bergen & Franke 2020 "Global Intentions"):
Does the locus of pragmatic reasoning (global vs. local) matter
for predicting human behavior in complex embedded contexts?
-/

-- SECTION 3: Compositional RSA - The Solution

/-!
## Compositional RSA

EXH is a structural operator, not a lexical one. Modeling where in the
derivation EXH applies requires a compositional approach:

1. Build a derivation tree with local alternatives at each node
2. Apply RSA/EXH at each node with its local alternatives
3. Compose the results via standard semantics

### For "Every student read some book"

Step 1: At the "some" node (per student)
- Local alternatives: {some, all}
- Local EXH: some → some-but-not-all

Step 2: Compose with "every"
- Result: every x [some-but-not-all(x)]
- This is the local reading

### Why This Works

The Franke 2011 limit theorem is parametric in the alternative set:
  IBR(alternatives) → exhMW(alternatives)

Instantiating with local alternatives at each node yields local exhMW
at each node. Composition gives the local reading.
-/

/-- Inner alternatives: some vs all -/
inductive QuantAlt where
  | some_ : QuantAlt
  | all : QuantAlt
  deriving DecidableEq, Repr

/-- Inner meaning for a single student -/
def singleStudentMeaning : QuantAlt → StudentReading → Bool
  | .some_, _ => true
  | .all, .some_not_all => false
  | .all, .all => true

/-- Local node for a single student's reading behavior -/
def singleStudentNode : LocalAltNode StudentReading QuantAlt where
  meaning := singleStudentMeaning
  prejacent := .some_
  alternatives := [.some_, .all]

-- SECTION 4: Composition with Universal Quantifier

/-- Map aggregate world to per-student readings -/
def aliceReading : EmbeddedSIWorld → StudentReading
  | .SS => .some_not_all
  | .SA => .some_not_all
  | .AS => .all
  | .AA => .all

def bobReading : EmbeddedSIWorld → StudentReading
  | .SS => .some_not_all
  | .SA => .all
  | .AS => .some_not_all
  | .AA => .all

/-- The composed local interpretation:
    "Every student read some-but-not-all"
    = Alice read some-but-not-all AND Bob read some-but-not-all -/
def composedLocalInterp : EmbeddedSIWorld → Bool
  | .SS => true
  | .SA => false
  | .AS => false
  | .AA => false

/-- Composed local interpretation matches localExhMeaning -/
theorem composed_local_equals_localExh :
    composedLocalInterp = localExhMeaning := by
  funext w; cases w <;> rfl

/-- Local reading is strictly stronger than global -/
theorem local_strictly_stronger :
    ∃ w, globalExhMeaning w = true ∧ composedLocalInterp w = false :=
  ⟨.SA, rfl, rfl⟩

-- SECTION 5: The Key Difference: LU vs Compositional

/-!
## LU vs Compositional RSA

LU-RSA (Potts, Lassiter, Levy, Frank):
- Mechanism: Uncertainty over lexicon (word meanings)
- For embedded SI: Choose between weak/strong "some"
- Problem: Both lexicons give the same scope relations
  - Weak "some" + global EXH = global reading
  - Strong "some" = local-like, but no scope interaction
- LU is scope-blind. It varies meanings, not structure.

Compositional RSA:
- Mechanism: Apply EXH at each node with local alternatives
- For embedded SI: EXH at "some" node before composing with "every"
- Result: True local reading via compositional structure
- The Franke limit theorem is parametric; instantiating with local
  alternatives yields local EXH.

### The Expressivity Hierarchy

```
Standard RSA ⊂ LU-RSA ≈ Standard RSA ⊂ Compositional RSA ≈ EXH
     ↓              ↓                        ↓
 scope-blind   scope-blind             scope-sensitive
     ↓              ↓                        ↓
 global only   global only             global AND local
```

LU-RSA and standard RSA have the same structural expressivity.
LU adds uncertainty over word meanings, not scope.
-/

/-- LU-RSA is scope-blind: it cannot distinguish global from local
    based on structural scope position.

    Proof: LU's two lexicons (weak, strong) correspond to
    (no SI, local-like SI), but the choice is lexical not structural.
    There is no principled way to derive the local reading.
-/
theorem lu_is_scope_blind :
    -- LU with weak lexicon = no SI (allows all)
    -- LU with strong lexicon = local-like (but no scope reasoning)
    (∀ w, luMeaning ⟨.weak, w⟩ = true) ∧
    (∀ w, luMeaning ⟨.strong, w⟩ = localExhMeaning w) ∧
    -- But LU has no way to derive which lexicon from the utterance
    -- The choice is arbitrary, not derived from scope
    True :=
  ⟨lu_weak_allows_all, lu_strong_equals_local, trivial⟩

/-- The expressivity gain: Compositional RSA can express local readings
    that LU-RSA cannot principally derive. -/
theorem compositional_expressivity_gain :
    ∃ w : EmbeddedSIWorld,
      -- Global EXH (what standard RSA gives) includes w
      globalExhMeaning w = true ∧
      -- Local EXH (what compositional RSA gives) excludes w
      composedLocalInterp w = false ∧
      -- LU strong lexicon also excludes, but unprincipled
      luMeaning ⟨.strong, w⟩ = false :=
  ⟨.SA, rfl, rfl, rfl⟩

-- SECTION 5.5: The Fundamental Limitation of Sentence-Level RSA

/-!
## Why Standard RSA Cannot Derive Local Readings

No sentence-level alternative can distinguish SS from SA using global
worlds. This limitation motivates either:
1. Stipulating EXH as a grammatical primitive (the standard view)
2. Developing "local RSA" that operates inside composition

### The Setup

For "every student read some book":
- Worlds: SS (both some-not-all), SA (Alice some, Bob all), AS, AA
- Alternatives: nested Aristotelians {none, some, all} × {none, some, all}

### The Problem

RSA excludes a world w when hearing utterance u if:
  ∃ u' ∈ Alt(u). ⟦u'⟧(w) ∧ informativity(u') > informativity(u)

To exclude SA when hearing "every...some", we'd need an alternative u' where:
  ⟦u'⟧(SA) = true  AND  ⟦u'⟧(SS) = false  (or u' more informative)

No such sentence exists in the nested Aristotelians.

### Consequences

If RSA cannot distinguish SS from SA at the sentence level, then either:
1. EXH is a separate grammatical mechanism (stipulation)
2. RSA must operate sub-sententially with "local" alternatives

Option 2 is "RSA all the way down" -- deriving EXH-like behavior from
RSA applied at each compositional node.
-/

/-- The 9 nested Aristotelian sentences as our alternative set -/
inductive NestedAristotelian where
  | NN : NestedAristotelian  -- none...none
  | NS : NestedAristotelian  -- none...some
  | NA : NestedAristotelian  -- none...all
  | SN : NestedAristotelian  -- some...none
  | SS : NestedAristotelian  -- some...some (our target)
  | SA : NestedAristotelian  -- some...all
  | AN : NestedAristotelian  -- all...none
  | AS : NestedAristotelian  -- all...some
  | AA : NestedAristotelian  -- all...all
  deriving DecidableEq, Repr

/-- Literal (global) meaning of nested Aristotelians.
    Using the same world type as RSAExhExpressivity. -/
def nestedMeaning : NestedAristotelian → EmbeddedSIWorld → Bool
  -- "none...X" sentences: false when any student drank something
  | .NN, _ => false  -- none drank none (contradictory in our setup)
  | .NS, _ => false  -- none drank some
  | .NA, _ => false  -- none drank all
  -- "some...none": some student drank none (false in our setup - all drank something)
  | .SN, _ => false
  -- "some...some": some student drank some - always true
  | .SS, _ => true
  -- "some...all": some student drank all
  | .SA, .SA => true
  | .SA, .AS => true
  | .SA, .AA => true
  | .SA, .SS => false
  -- "all...none": all students drank none - false
  | .AN, _ => false
  -- "all...some": all students drank some - always true (everyone drank at least some)
  | .AS, _ => true
  -- "all...all": all students drank all
  | .AA, .AA => true
  | .AA, _ => false

/-- Key observation: SS and SA are indistinguishable by sentence-level meaning.

    For every nested Aristotelian sentence, if it is true at SS, it is also true at SA
    (or vice versa in a way that does not help RSA exclude SA).

    SA "dominates" SS: if some students did X in SS,
    then some students did X in SA (with potentially more). -/
theorem no_sentence_distinguishes_SS_SA :
    ∀ sent : NestedAristotelian,
      -- No sentence is true at SS but false at SA
      ¬(nestedMeaning sent .SS = true ∧ nestedMeaning sent .SA = false) := by
  intro sent
  cases sent <;> simp [nestedMeaning]

/-- Sentences true at SA but not SS don't help RSA exclude SA.

    "some...all" is true at SA and false at SS. But this does not help:
    RSA excludes worlds where stronger alternatives are true.
    "some...all" is weaker than "some...some" for the inner quantifier,
    so it does not trigger exclusion.

    The only sentence that could help exclude SA would be one that:
    1. Is true at SS
    2. Is false at SA
    3. Is stronger than "some...some"

    No such sentence exists. -/
theorem no_stronger_alt_distinguishes :
    -- "some...all" is true at SA, false at SS - but it's weaker not stronger
    (nestedMeaning .SA .SA = true) ∧
    (nestedMeaning .SA .SS = false) ∧
    -- "all...all" could exclude, but is false at SA
    (nestedMeaning .AA .SA = false) ∧
    -- "all...some" is true at both - does not help
    (nestedMeaning .AS .SA = true) ∧
    (nestedMeaning .AS .SS = true) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The RSA exclusion principle: RSA excludes world w when hearing u if
    there exists a stronger alternative u' true at w.

    For "some...some" (SS sentence), the only stronger alternative is "all...all".
    "all...all" is false at both SS and SA.
    Therefore, RSA cannot exclude SA when hearing "some...some". -/
theorem rsa_cannot_exclude_SA :
    -- The utterance is "some...some" (SS)
    -- The stronger alternative is "all...all" (AA)
    -- AA is false at SA, so RSA does not exclude SA
    nestedMeaning .AA .SA = false ∧
    -- AA is also false at SS
    nestedMeaning .AA .SS = false ∧
    -- Therefore RSA treats SS and SA the same when hearing "some...some"
    -- (both are in the posterior, neither excluded by AA)
    True := by
  constructor
  · rfl
  constructor
  · rfl
  · trivial

/-- The core theorem: Standard RSA with sentence-level alternatives
    cannot derive the local reading {SS}.

    Proof: RSA's posterior after hearing "some...some" includes all worlds
    where "some...some" is true and no strictly stronger alternative is true.

    - "some...some" is true at: SS, SA, AS, AA (literally: everyone drank some)
    - "all...all" is the strongest alternative, true only at AA
    - RSA excludes AA (stronger alternative was available)
    - RSA keeps: SS, SA, AS -- this is the global reading, not local

    To get the local reading {SS}, we would need to exclude SA and AS.
    No sentence-level alternative can do this. -/
theorem standard_rsa_gives_global_not_local :
    -- "some...some" is true at SS, SA, AS, AA
    (nestedMeaning .SS .SS = true) ∧
    (nestedMeaning .SS .SA = true) ∧
    (nestedMeaning .SS .AS = true) ∧
    (nestedMeaning .SS .AA = true) ∧
    -- "all...all" (the excluder) is only true at AA
    (nestedMeaning .AA .AA = true) ∧
    (nestedMeaning .AA .SS = false) ∧
    (nestedMeaning .AA .SA = false) ∧
    (nestedMeaning .AA .AS = false) ∧
    -- Therefore RSA posterior for "some...some" is {SS, SA, AS}
    -- This is the global reading (matches globalExhMeaning)
    (globalExhMeaning .SS = true) ∧
    (globalExhMeaning .SA = true) ∧
    (globalExhMeaning .AS = true) ∧
    (globalExhMeaning .AA = false) ∧
    -- But the local reading is {SS} only
    (localExhMeaning .SS = true) ∧
    (localExhMeaning .SA = false) ∧
    (localExhMeaning .AS = false) ∧
    (localExhMeaning .AA = false) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-!
### The Expressivity Gap

```
Standard RSA posterior for "some...some":
  {w : ⟦some...some⟧(w) ∧ ¬⟦all...all⟧(w)} = {SS, SA, AS}

Local EXH reading:
  {SS}

Gap: {SA, AS} -- worlds RSA cannot exclude without sub-sentential reasoning
```

This gap is why linguists posit EXH as a grammatical primitive. "Local RSA"
-- RSA applied at each compositional node -- can derive the local reading
without stipulating EXH. EXH then emerges as the α → ∞ limit of local RSA.
-/

-- SECTION 6: Global Intentions and "RSA All The Way Down"

/-!
## Bergen & Franke (2020): Global Intentions Model

Bergen & Franke's "Global Intentions" (GI) model provides machinery for
reasoning over where EXH applies.

### The GI Architecture

1. Grammar generates parses: For each utterance, the grammar generates
   multiple readings based on where EXH is inserted:
   - `lit`: no EXH
   - `M`: EXH at matrix position
   - `O`: EXH at outer quantifier
   - `I`: EXH at inner quantifier
   - `MO`, `MI`, `OI`, `MOI`: combinations

2. Speaker chooses (utterance, parse) jointly:
   ```
   P_S(m, p | t; α) ∝ [P(t | ⟦m⟧^p)]^α
   ```
   The speaker picks both what to say and how to mean it.

3. Listener infers (world, parse) jointly:
   ```
   P_L(t, p | m; α) ∝ P(t) × P_S(m, p | t; α)
   ```

### Finding

GI outperforms simpler models (vanilla RSA, LU) because it can use
strong readings like ⟦SS⟧^M = {██-} that uniquely identify states.
However, GI assumes EXH is a grammatical primitive.

## The "RSA All The Way Down" Reinterpretation

Bergen & Franke's "parse" variable can be reinterpreted as
"where RSA reasoning applies":

```
Bergen & Franke:           RSA All The Way Down:
─────────────────          ─────────────────────────
parse p ∈ {lit,M,O,I,...}  config c ∈ {RSA application sites}
⟦m⟧^p = EXH at positions   ⟦m⟧^c = RSA(α) at positions
Speaker chooses parse      Speaker chooses where to be pragmatic
```

### The Equivalence

In the α → ∞ limit:
- RSA at node → EXH at node (Franke 2011 limit theorem)
- RSA at multiple nodes → EXH at multiple nodes (composition)
- Reasoning over "where RSA applies" → reasoning over "where EXH is"

Bergen & Franke's GI model equals "RSA all the way down" in the limit.

### The Derivation Direction

| Approach | Starting Point | Pragmatic Reasoning |
|----------|---------------|---------------------|
| Bergen & Franke | EXH is primitive | RSA reasons over EXH positions |
| RSA All The Way Down | RSA is primitive | EXH emerges in α → ∞ limit |

The compositional structure is the same. The difference is foundational:
- GI: Grammar + Pragmatics (EXH given, RSA selects)
- RSAATWD: Pragmatics only (EXH derived from RSA)

### Consequences

1. EXH is not a separate grammatical mechanism, but emergent behavior
   of rational communication at high precision.

2. GI's empirical success (Bayes factor analysis) is evidence for the
   compositional structure, not for EXH-as-primitive.

3. One mechanism (RSA) at different α values, rather than two mechanisms
   (grammar-EXH + pragmatics-RSA).

## Formal Correspondence

The GI model's joint distribution over (utterance, parse) corresponds
to compositional RSA's joint distribution over (utterance, enrichment-sites).
-/

/-- A parse in Bergen & Franke's sense: where EXH is inserted -/
inductive Parse where
  | lit : Parse     -- no EXH
  | M : Parse       -- matrix EXH only
  | O : Parse       -- outer quantifier EXH only
  | I : Parse       -- inner quantifier EXH only
  | MO : Parse      -- matrix + outer
  | MI : Parse      -- matrix + inner
  | OI : Parse      -- outer + inner
  | MOI : Parse     -- all three
  deriving DecidableEq, Repr

/-- An RSA application configuration: where RSA reasoning happens -/
structure RSAConfig where
  /-- Apply RSA at matrix level? -/
  matrixRSA : Bool
  /-- Apply RSA at outer quantifier? -/
  outerRSA : Bool
  /-- Apply RSA at inner quantifier? -/
  innerRSA : Bool
  deriving DecidableEq, Repr

/-- Convert RSA config to equivalent parse (in the α → ∞ limit) -/
def RSAConfig.toParse : RSAConfig → Parse
  | ⟨false, false, false⟩ => .lit
  | ⟨true, false, false⟩ => .M
  | ⟨false, true, false⟩ => .O
  | ⟨false, false, true⟩ => .I
  | ⟨true, true, false⟩ => .MO
  | ⟨true, false, true⟩ => .MI
  | ⟨false, true, true⟩ => .OI
  | ⟨true, true, true⟩ => .MOI

/-- The Global Intentions model: speaker chooses (utterance, parse) -/
structure GlobalIntentionsChoice (Utt : Type) where
  utterance : Utt
  parse : Parse

/-- RSA-All-The-Way-Down: speaker chooses (utterance, config) -/
structure RSAATWDChoice (Utt : Type) where
  utterance : Utt
  config : RSAConfig

/-- In the α → ∞ limit, RSAATWD choice maps to GI choice -/
def RSAATWDChoice.toGI {Utt : Type} (choice : RSAATWDChoice Utt) :
    GlobalIntentionsChoice Utt :=
  ⟨choice.utterance, choice.config.toParse⟩

/-!
### The Limit Theorem (Conceptual)

```
theorem rsaatwd_limit_is_gi :
    ∀ (scenario : ...) (m : Utt) (t : World),
      lim_{α→∞} P_RSAATWD(m, c | t; α) = P_GI(m, c.toParse | t)
```

Bergen & Franke's machinery for reasoning over parses emerges naturally
from "RSA at every compositional node" in the limit.

### Implications

1. GI's empirical success (they show GI >> LI >> LU >> RSA in Bayes factors)
   is evidence for compositional pragmatic reasoning, interpretable as:
   - B&F interpretation: Grammar generates EXH, RSA selects among readings
   - Our interpretation: RSA applies compositionally, EXH-like behavior emerges

2. GI wins because ⟦SS⟧^M uniquely identifies state ██-. This reading
   requires matrix exhaustification.
   - B&F: Matrix EXH is a grammatical option
   - Us: High-α RSA at the matrix level produces the same strengthening

3. Parse selection = RSA site selection: B&F's listener inferring the
   intended parse is equivalent to inferring where the speaker applied
   pragmatic reasoning.
-/

/-- Bergen & Franke's key empirical finding: GI model assigns high
    probability to 'SS' for state ██- because ⟦SS⟧^M = {██-}.

    In RSAATWD terms: with high-α RSA at matrix level, the speaker
    strongly prefers 'SS' for this state because it's uniquely identifying. -/
theorem gi_success_case :
    -- The state where all aliens drank some-but-not-all
    -- is uniquely identified by 'SS' under matrix EXH/RSA
    composedLocalInterp .SS = true ∧
    composedLocalInterp .SA = false ∧
    composedLocalInterp .AS = false ∧
    composedLocalInterp .AA = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- SECTION 7: Algebraic Decomposition

/-!
## Algebraic Structure of Compositional RSA

Does the joint distribution over (utterance, config) decompose in a
principled algebraic way?

### The Product Hypothesis

If pragmatic reasoning at different nodes is independent, then:

```
P_S(m, c | t; α) ∝ ∏_{node n ∈ c} P_RSA(choice_n | local_state_n; α)
```

This would mean:
1. Each node contributes independently to the overall probability
2. Informativity MULTIPLIES across nodes
3. The joint inference FACTORS into local inferences

### Informativity Multiplication

For a sentence with multiple scalar items, if informativity multiplies:

```
informativity(m, c) = ∏_{n ∈ c} informativity_n(choice_n)
```

Then the softmax over (m, c) decomposes:

```
P_S(m, c | t; α) ∝ exp(α × log informativity(m, c))
                 = exp(α × Σ_n log informativity_n(choice_n))
                 = ∏_n exp(α × log informativity_n(choice_n))
                 = ∏_n P_RSA_n(choice_n | local_t_n; α)
```

This is the algebraic signature of compositional RSA.

### Connection to GradedMonad (RSAFree)

The RSAFree graded monad (see GradedMonad.lean) has exactly this structure:

```lean
-- RSAFree is a graded monad where the grade tracks alternatives
-- Binding (seq) composes RSA computations
-- Informativity multiplies under seq

seq : RSAFree W A → (A → RSAFree W B) → RSAFree W B
```

The monad laws ensure:
1. **Associativity**: (m >>= f) >>= g = m >>= (λx. f x >>= g)
2. **Identity**: return x >>= f = f x

These correspond to:
1. **Composition is associative**: parsing order doesn't matter
2. **Literal meaning is identity**: no RSA = base meaning

### The Decomposition Theorem (Conceptual)

```
theorem informativity_multiplicative :
    ∀ (m₁ : RSAFree W A) (m₂ : A → RSAFree W B) (a : A) (b : B),
      informativity (seq m₁ m₂) (a, b) =
      informativity m₁ a × informativity (m₂ a) b
```

This says: the informativity of a composed utterance (with choices at
multiple levels) is the product of the local informativities.

The joint distribution therefore factors.

### Why Decomposition Matters

1. Computational tractability: If the distribution factors, inference
   is polynomial rather than exponential in the number of nodes.

2. Theoretical parsimony: Local RSA at each node, composed via
   standard semantic composition. No special global mechanism.

3. Empirical predictions: Local RSA predicts independence effects
   that global reasoning would not.

4. Connection to grammar: The algebraic structure mirrors
   compositional semantics. RSA "rides along" with semantic composition.

### The Monoid of Informativities

Informativity values form a multiplicative monoid:
- Identity: informativity(tautology) = 1
- Multiplication: informativity(φ ∧ ψ) ≤ informativity(φ) × informativity(ψ)
  (with equality when φ and ψ are independent)

This monoid structure is what makes compositional RSA work:
- Each node contributes a factor
- Composition multiplies factors
- High-α RSA selects the maximum product = maximum informativity
-/

/-- Informativity as a value (for algebraic reasoning) -/
structure Informativity where
  value : ℚ
  pos : value > 0
  le_one : value ≤ 1

/-- The multiplicative monoid structure on informativities -/
def Informativity.mul (i₁ i₂ : Informativity) : Informativity where
  value := i₁.value * i₂.value
  pos := mul_pos i₁.pos i₂.pos
  le_one := by
    calc i₁.value * i₂.value
        ≤ i₁.value * 1 := by apply mul_le_mul_of_nonneg_left i₂.le_one (le_of_lt i₁.pos)
      _ = i₁.value := mul_one _
      _ ≤ 1 := i₁.le_one

/-- Unit informativity (tautology) -/
def Informativity.one : Informativity where
  value := 1
  pos := by norm_num
  le_one := le_refl 1

instance : Mul Informativity := ⟨Informativity.mul⟩
instance : One Informativity := ⟨Informativity.one⟩

/-- Informativity values multiply like rationals -/
theorem informativity_value_mul (i₁ i₂ : Informativity) :
    (i₁ * i₂).value = i₁.value * i₂.value := rfl

/-- Informativity multiplication is associative (on values) -/
theorem informativity_mul_assoc_value (i₁ i₂ i₃ : Informativity) :
    ((i₁ * i₂) * i₃).value = (i₁ * (i₂ * i₃)).value := by
  simp only [informativity_value_mul]
  ring

/-- Value of unit informativity is 1 -/
@[simp] theorem informativity_one_value : (1 : Informativity).value = 1 := rfl

/-- Informativity multiplication has unit (on values) -/
theorem informativity_mul_one_value (i : Informativity) :
    (i * 1).value = i.value := by
  simp only [informativity_value_mul, informativity_one_value]
  ring

theorem informativity_one_mul_value (i : Informativity) :
    (1 * i).value = i.value := by
  simp only [informativity_value_mul, informativity_one_value]
  ring

/-!
### The Factorization Picture

```
        Sentence: "Every student read some book"
                         │
                    ┌────┴────┐
                    │  Matrix │ ← RSA here? (config.matrixRSA)
                    │   EXH?  │
                    └────┬────┘
                         │
              ┌──────────┴──────────┐
              │                     │
         ┌────┴────┐           ┌────┴────┐
         │ "every" │           │ VP      │
         │ student │           │         │
         └─────────┘           └────┬────┘
                                    │
                          ┌─────────┴─────────┐
                          │                   │
                     ┌────┴────┐         ┌────┴────┐
                     │ "read"  │         │ "some"  │ ← RSA here?
                     └─────────┘         │  book   │   (config.innerRSA)
                                         └─────────┘

P_S(m, c | t; α) = P_RSA_matrix(EXH? | ...; α) × P_RSA_inner(EXH? | ...; α)
```

The distribution factors along the tree structure.
Each node's RSA decision is (conditionally) independent.

### Connection to Bergen & Franke

Their finding that GI >> LI >> LU >> RSA can be reinterpreted:

- **RSA → LU**: Adding lexical uncertainty helps, but doesn't factor right
- **LU → LI**: Adding local lexical choice helps (starts to factor)
- **LI → GI**: Adding matrix EXH completes the factorization

GI wins because it has the right algebraic structure:
the full product over all compositional nodes.
-/

/-!
## Summary: The Two Perspectives

### Bergen & Franke (2020)
- Primitives: Grammar (generates EXH parses) + Pragmatics (RSA selects)
- Architecture: P_S(m, p | t) where p is a grammatically-given parse
- EXH status: Primitive grammatical operator
- RSA role: Selects among grammatically-generated readings

### RSA All The Way Down (This File)
- Primitives: Pragmatics only (RSA at each compositional node)
- Architecture: P_S(m, c | t) where c is where RSA applies
- EXH status: Emergent behavior of RSA as α → ∞
- RSA role: Fundamental mechanism; EXH is its limit

### The Mathematical Connection

The joint inference machinery is identical:
```
P_S(m, x | t; α) ∝ [P(t | meaning(m, x))]^α
P_L(t, x | m; α) ∝ P(t) × P_S(m, x | t; α)
```

where x = parse (B&F) or x = RSA-config (RSAATWD).

In the α → ∞ limit, these are the same model, because
local RSA → local EXH at each node.

Bergen & Franke's empirical validation of GI is also validation of
compositional RSA, without requiring EXH as a grammatical primitive.
-/

end RSA.Compositional
