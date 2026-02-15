# Sorry & Axiom Audit — Strategic Analysis

**Generated**: 2026-02-14
**Counts**: 278 sorry occurrences across 89 files; 21 axioms across 6 files

This document analyzes every `sorry` and `axiom` in linglib by *strategic role* —
what does each incomplete proof do for the project, and what would completing it
actually require? The goal is to prioritize work that maximizes credibility per
hour invested.

---

## Classification Framework

Each sorry/axiom falls into one of these roles:

| Role | Description | Priority |
|------|-------------|----------|
| **Showcase** | Proofs that demonstrate the formalization works — things you'd put in a paper/talk | High |
| **Load-bearing** | Axioms that downstream code imports and builds on | High |
| **Bridge** | Connect Fragment data to Theory predictions (the Phenomena test suite) | Medium |
| **Paper replication** | Needed to claim a specific paper is faithfully implemented | Medium |
| **Infrastructure** | Core/ utilities needed for downstream work | Medium |
| **Frontier** | Exploratory formalizations not yet connected to anything | Low |
| **Dead-end** | Sorrys in files nothing imports or builds on | Low |

Each sorry also gets a **difficulty** rating:

| Difficulty | Description |
|------------|-------------|
| **A** | Quick win — `native_decide`, `decide`, `omega`, or 1-2 tactic proof |
| **B** | Medium — needs structured proof, maybe 10-50 lines |
| **C** | Hard — real math (analysis, topology, combinatorics) |
| **D** | Blocked — needs upstream sorry resolved first, or new infrastructure |

---

## §1: Axioms (21 across 6 files)

Axioms are the most important to audit — they are *assumed truths* that could
silently make the entire system inconsistent if wrong.

### 1.1 RSA Convergence (5 axioms) — `Theories/RSA/Core/Convergence.lean`

These are the mathematical backbone of the RSA convergence proof (Zaslavsky et al. 2020).

| Axiom | Type | Role | Difficulty | Notes |
|-------|------|------|------------|-------|
| `kkt_sufficiency_for_concave_on_simplex` | KKT optimality on simplex | Load-bearing | C | Standard convex optimization result; provable with enough Mathlib |
| `kkt_sufficiency_for_concave_on_positive` | KKT on positive orthant | Load-bearing | C | Same, different domain |
| `rsa_speaker_maximizes_G_α` | Speaker update is optimal | Load-bearing | C | Follows from KKT + concavity of G_α |
| `rsa_listener_maximizes_G_α` | Listener update is optimal | Load-bearing | C | Same pattern |
| `G_α_bounded` | G_α has an upper bound | Load-bearing | B | Entropy is bounded by log|U|; should be provable |

**Assessment**: These 5 axioms are the *only* axioms needed for the RSA convergence
theorem (`G_α_monotone`, `RSA_converges`). The convergence proof itself is *fully
structured* — it chains speaker and listener optimality via `le_trans`. The axioms
encapsulate the hard real analysis. This is a *good* use of axioms: the proof
architecture is visible, and the assumed facts are standard results from convex
optimization.

**Action**: Keep as axioms with clear docstrings. Optionally attempt KKT proof
using Mathlib's `ConcaveOn` + `Finset.sum` API, but this is C-difficulty and
low ROI unless targeting a formal methods audience.

### 1.2 Attitude Semantics (2 axioms) — `Theories/IntensionalSemantics/Attitude/CDistributivity.lean`

| Axiom | Type | Role | Difficulty | Notes |
|-------|------|------|------------|-------|
| `c_distributivity` | C distributes over conjunction | Load-bearing | D | Deep philosophical axiom (Heim 1992) |
| `c_consistency` | C-modal base is consistent | Load-bearing | D | Needed for attitude logic |

**Assessment**: These encode Heim's (1992) C operator properties. They are
genuinely axiomatic — they *define* how the attitude system works rather than
being provable from deeper principles. Appropriate as axioms.

**Action**: Keep. These are theory-constitutive axioms, not proof gaps.

### 1.3 Quantifier Universals (5 axioms) — `Phenomena/Quantification/Universals.lean`

| Axiom | Type | Role | Difficulty | Notes |
|-------|------|------|------------|-------|
| `conservativity_universal` | All QuantityWords are conservative | Showcase | D | Blocked on `few`/`half` gqDenotations |
| `quantity_universal` | All QuantityWords satisfy QUANT | Showcase | D | Same blocker |
| `positive_strong_determiners_upward_monotone` | PosStrong → ScopeUpMono | Showcase | D | Same blocker |
| `strong_implies_monotone` | Strong dets are monotone | Bridge | A | Checkable over 6 QuantityWords! |
| `persistent_implies_weak_and_up` | Weak dets are monotone | Bridge | A | Checkable over 6 QuantityWords! |

**Assessment**: The first 3 are blocked on incomplete `gqDenotation` for `few`
and `half` — these QuantityWords have `sorry` in their GQ denotation in
`Fragments/English/Determiners.lean`. The last 2 could be proved by `native_decide`
if stated as `∀ q ∈ QuantityWord.toList, ...` (finite enumeration).

**Action**:
- `strong_implies_monotone` and `persistent_implies_weak_and_up`: Convert from
  axiom to theorem + `native_decide`. **Quick wins.**
- The other 3: Keep as axioms until `few`/`half` denotations are implemented.
  Add `[sorry: blocked on few/half gqDenotation]` tags.

### 1.4 Noun Categorization (6 axioms) — `Phenomena/Agreement/NounCategorization.lean`

| Axiom | Type | Role | Difficulty | Notes |
|-------|------|------|------------|-------|
| `noun_class_requires_agreement` | Noun class → agreement | Bridge | A | Could check against 5 attested systems |
| `numeral_classifier_no_agreement` | Classifiers lack agreement | Bridge | A | Same |
| `classifier_assignment_semantic` | Classifier assignment is semantic | Bridge | A | Same |
| `animacy_universal` | All systems mark animacy | Bridge | A | Same |
| `noun_class_small_inventory` | Noun class ≤ 20 classes | Bridge | A | Same |
| `classifier_semantic_hierarchy` | Animacy > Shape > Function | Bridge | B | Implicational, harder |

**Assessment**: These are stated as universals over `NounCategorizationSystem` but
could be *verified* against the 5 attested systems (French, Mandarin, Japanese,
Swahili, Dyirbal). The universal quantifier is appropriate (they're conjectures
about all languages), but we should at minimum have `native_decide` verification
that the 5 attested systems satisfy them.

**Action**: Add per-system verification theorems (like `french_satisfies_U1`,
`mandarin_satisfies_U2`, etc.) proved by `native_decide`. Keep the universally
quantified versions as axioms since they claim something about *all* possible
systems, not just our 5.

### 1.5 CCG (1 axiom) — `Theories/CCG/Formal/FormalLanguageTheory.lean`

| Axiom | Type | Role | Difficulty | Notes |
|-------|------|------|------------|-------|
| `ccg_mildly_context_sensitive` | CCG ⊆ TAG languages | Frontier | C | Major result (Vijay-Shanker & Weir 1994) |

**Assessment**: This is a well-known result in formal language theory. Proving it
formally would be a significant achievement but is far beyond current scope.

**Action**: Keep as axiom. Not a credibility concern — it's a cited result.

### 1.6 Minimalism (2 axioms) — `Theories/Minimalism/Formal/Amalgamation.lean`

| Axiom | Type | Role | Difficulty | Notes |
|-------|------|------|------------|-------|
| `merge_is_simplest_set_theoretic_operation` | Merge is simplest | Frontier | D | Philosophical claim |
| `amalgamation_preserves_coherence` | Amalgamation is coherent | Frontier | C | Needs proof |

**Assessment**: Exploratory formalization of Minimalist syntax. Low import count.

**Action**: Keep. Low priority.

---

## §2: High-Value Sorry Clusters

These are groups of sorrys where completing them would significantly boost
credibility.

### 2.1 English GQ Denotations (2 sorrys) — `Fragments/English/Determiners.lean`

| Sorry | What's missing | Difficulty | Downstream impact |
|-------|---------------|------------|-------------------|
| `few.gqDenotation` | `sorry` body | B | Blocks 3 Universals axioms |
| `half.gqDenotation` | `sorry` body | B | Same |

**Assessment**: These two sorrys are the *single biggest blocker* in the codebase.
Completing them would unblock `conservativity_universal`, `quantity_universal`,
and `positive_strong_determiners_upward_monotone` — converting 3 axioms to
theorems. "Few" needs a vagueness-sensitive denotation; "half" needs a
proportional denotation.

**Action**: HIGH PRIORITY. Define `few` as "less than half" or use a threshold,
and `half` as `|A∩B| ≥ |A|/2`. Even approximate denotations would unblock proofs.

### 2.2 RSA Core Model (9 sorrys) — `Theories/RSA/Core/Model.lean`

| Sorry | What's missing | Difficulty |
|-------|---------------|------------|
| `lexicon_nonneg` | ℚ→ℝ cast is nonneg | A |
| `prior_nonneg` | Same | A |
| `prior_pos` | Exists positive prior | B |
| 6 others | Various ℝ arithmetic | A-B |

**Assessment**: These are ℚ→ℝ coercion lemmas in `RSAScenario.toReal`. Most are
trivially true (`Nat.cast_nonneg`, `Rat.cast_nonneg`) but need the right Mathlib
API calls.

**Action**: Medium priority. These are A-difficulty but require Mathlib fluency.

### 2.3 Softmax & Max Entropy (10 sorrys) — `RSA/Core/Softmax/`

Two files with real-analysis proofs about softmax properties:
- `Limits.lean`: 2 sorrys (softmax limit as α→∞, α→0)
- `MaxEntropy.lean`: 8 sorrys (uniform distribution maximizes entropy, etc.)

**Assessment**: These are genuine real-analysis proofs. Completing them would make
the RSA convergence story airtight. But they require significant Mathlib fluency
(filters, limits, summation API).

**Action**: Low priority unless targeting formal methods audience. The *statements*
are correct and well-documented.

### 2.4 Question Semantics (50+ sorrys across 10 files)

The largest cluster. Key files:

| File | Sorrys | Character |
|------|--------|-----------|
| `GSVanRooyBridge.lean` | 14 | Bridge between G&S and van Rooij |
| `EntropyNPIs.lean` | 13 | Entropy-based NPI licensing |
| `Answerhood.lean` | 11 | ANS operator properties |
| `PolarQuestions.lean` (Comparisons) | 8 | Cross-theory comparison |
| `RelevanceTheories.lean` (Comparisons) | 10 | Cross-theory comparison |
| `PragmaticAnswerhood.lean` | 6 | Pragmatic answerhood |

**Assessment**: Question semantics is the most ambitious module — 18 files covering
Hamblin, partition, inquisitive, and probabilistic approaches. Many sorrys are
in *comparison* files that cross-reference multiple theories. These are structurally
interesting but hard to prove because they involve interactions between different
formalizations.

**Action**: Focus on `Answerhood.lean` — it has the most *provable* sorrys
(properties of the ANS operator over partitions). `GSVanRooyBridge` and comparison
files are lower priority.

### 2.5 Strawson Entailment (7 sorrys) — `Sentence/Entailment/StrawsonEntailment.lean`

Properties of Strawson entailment (von Fintel 1999): monotonicity respecting
presuppositions.

**Assessment**: Important for polarity theory. The proofs require careful handling
of partial functions (presupposition failure = undefined). Medium difficulty.

### 2.6 Temporal Connectives (6 sorrys) — `Sentence/Tense/TemporalConnectives.lean`

Properties of temporal operators (since, until, when).

**Assessment**: Infrastructure for tense semantics. Medium difficulty.

### 2.7 Polarity / NPI (7+13 sorrys)

| File | Sorrys | Character |
|------|--------|-----------|
| `VonFintel1999.lean` | 7 | NPI licensing in Strawson DE environments |
| `EntropyNPIs.lean` | 13 | Entropy-based NPI licensing |

**Assessment**: Two competing NPI theories. `VonFintel1999` is more classical
and the sorrys are more tractable. `EntropyNPIs` involves information-theoretic
concepts and is harder.

### 2.8 Dependency Grammar (10 sorrys across 4 files)

| File | Sorrys | Character |
|------|--------|-----------|
| `HarmonicOrder.lean` | 6 | Harmonic word order universals |
| `NonProjective.lean` | 2 | Non-projective dependency properties |
| `VPDivergence.lean` | 1 | VP divergence |
| `Catena.lean` | 1 | Catena properties |

**Assessment**: Formal dependency grammar. `HarmonicOrder` has the most interesting
sorrys — they encode Greenberg-style word order universals. These could potentially
be verified by `native_decide` over finite language samples.

### 2.9 Causative Semantics (15 sorrys across 6 files)

Spread across necessity, sufficiency, integration, builder, resultatives, and
production dependence. These encode causal reasoning (Nadathur & Lauer 2020,
Copley & Harley 2015) and are mostly medium-difficulty structured proofs.

---

## §3: Quick Wins (Category A)

These sorrys could likely be closed in under 5 minutes each:

| File | Sorry | Expected proof |
|------|-------|---------------|
| `Universals.lean` | `strong_implies_monotone` | Convert axiom → theorem + `native_decide` over QuantityWord.toList |
| `Universals.lean` | `persistent_implies_weak_and_up` | Same |
| `NounCategorization.lean` | 5 universals | Add per-system `native_decide` verification theorems |
| `Model.lean` | `lexicon_nonneg`, `prior_nonneg` | `Rat.cast_nonneg` or similar Mathlib lemma |
| `Coordination/Typology.lean` | 1 sorry | Already closed (trivial) |
| `Partition.lean` | 1 sorry | Probably `simp` + `omega` |
| `Mereology.lean` | 1 sorry | Likely `omega` or `simp` |
| `Roundness.lean` | 1 sorry | Likely `native_decide` |
| `Complementation/Typology.lean` | 1 sorry | Likely `native_decide` |
| `English/PolarityItems.lean` | 1 sorry | Likely `native_decide` |

**Estimated total**: ~15-20 quick wins, closable in a single session.

---

## §4: Strategic Recommendations

### What to do first (highest credibility/hour)

1. **Close the ~15 Category A sorrys** — immediate sorry count reduction
2. **Implement `few` and `half` gqDenotations** — unblocks 3 axiom→theorem conversions
3. **Add per-system verification theorems for NounCategorization** — shows the axioms aren't vacuous
4. **Close easy Answerhood.lean sorrys** — the ANS operator proofs are mostly partition reasoning

### What to defer

- RSA real-analysis proofs (Softmax, MaxEntropy, Convergence) — correct statements, hard proofs, niche audience
- Question semantics comparison files — ambitious but low external visibility
- CCG formal language theory — major theoretical result, not our core focus
- Minimalism axioms — exploratory

### What to reconsider

Some sorrys may represent *over-ambitious* theorem statements. Before closing a
sorry, ask: "Does linglib actually *need* this theorem?" If nothing imports it
and it doesn't demonstrate a key capability, consider deleting it rather than
proving it. Dead theorems are worse than no theorems — they suggest the
formalization is broader than it actually is.

---

## §5: Dependency Graph (What Blocks What)

```
few/half gqDenotation (Determiners.lean)
  └── conservativity_universal (Universals.lean)
  └── quantity_universal (Universals.lean)
  └── positive_strong_determiners_upward_monotone (Universals.lean)

KKT axioms (Convergence.lean)
  └── G_α_monotone (proved, uses axioms)
  └── RSA_converges (sorry, uses G_α_monotone + G_α_bounded)

GSQuestion properties (Partition.lean, Answerhood.lean)
  └── GSVanRooyBridge.lean (14 sorrys)
  └── PragmaticAnswerhood.lean (6 sorrys)
  └── EntropyNPIs.lean (13 sorrys)
```

---

## §6: Per-File Detail

*To be expanded as we work through each cluster. For now, the strategic
groupings above should guide prioritization.*
