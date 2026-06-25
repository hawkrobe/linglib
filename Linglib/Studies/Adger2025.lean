import Linglib.Studies.Ross1967
import Linglib.Syntax.SynGraph
import Linglib.Syntax.Minimalist.Merge.MinimalYield
import Linglib.Syntax.Minimalist.Defs

set_option autoImplicit false

/-!
# Mereological Syntax: Angular Locality and Islands
[adger-2025]

[adger-2025] (Linguistic Inquiry Monograph 90, MIT Press) develops a
mereological alternative to set-theoretic Bare Phrase Structure: syntactic
objects are *parts* of one another (rather than members of sets), and the
operation `Subjoin` makes one object a 1-part or 2-part of another. The
book derives a range of locality phenomena from **Angular Locality** (AL):
a structural condition on subjunction paths that fails when the path
crosses dimensions (mixed 1-part/2-part transitivity).

## Coverage of this file

This is a thin study layer that re-exports the AL substrate derivations
from `Syntax/SynGraph.lean` (§10) and frames cross-framework
engagement. The substrate covers:

- **Subject islands** (Ch 7 §7.7, book pp. 216–223): cross-dimensional path
  blocks sub-extraction; the subject DP itself, as T's direct 2-part, is
  reachable. *Caveat:* Adger's full §7.7 derivation depends on a [Fam]/[uFam]
  T feature triggering D-subjunction (which fills D's 2-part and produces
  the cross-dimensional path). The substrate models the blocked endpoint,
  not the [Fam] machinery that triggers it. Ch §7.8 emphasises that subject
  islands are "not consistent islands" — strength varies with definiteness/
  topicality of the subject.

- **Definite nominal islands** (Ch 6 §6.3.2, book pp. 153–157): when
  Det/Dem/Poss subjoins to D, D's 2-part is "used up", blocking extraction
  through D. Indefinite DPs (D with a free 2-part) are transparent.

- **Successive cyclicity** (Ch 4 §4.3): wh requires intermediate stops at
  embedded C edges to traverse the right dimension chain at each step.

- **Anti-locality, lowering, parallel merge, sideward subjunction** (Ch 4
  consequences (35a–e)): all blocked by AL.

## Out of scope

- **Wh-Islands** (entire Ch 5, book pp. 117–142), including the **WIRE
  Effect** (Wh-Island Re-Emergence, book p. 125) — Adger's most novel
  cross-linguistic prediction. Formalising WIRE as a graph-decidable
  predicate over Wh-pair clausemate configurations is the most natural
  empirical extension.
- **Adjunct islands beyond Ch 4 graph instantiation.** Adger explicitly
  admits at the start of Ch 8 (book p. 225): "I owe at least a sketch of
  how these islands might be tackled." The substrate's
  `adjunct_island_blocks` exhibits the Ch 4 cross-dimensional mechanism on
  an `AdvP` 2-part of `v`; the Ch 8 Mod-headed Geis/Haegeman analysis is
  not formalised here.
- **Concrete (§6.3.1) vs Relational (§6.3.2) nominal split.**
- **Articleless-language typology** for nominal islands (§6.4):
  Mandarin/Persian/Japanese contrasts predicted by D-Interpretation.
- **The [Fam]/[uFam] T-feature machinery** (Ch 7 §7.7) driving subject-
  island gradience — substrate models the structural endpoint only.

## Cross-framework engagement

§3 of this file articulates AL's relationship to one rival framework
([marcolli-chomsky-berwick-2025] §1.6 algebraic Merge): both reach
a `false` verdict on Sideward Merge from incompatible primitives.

The classification handles `adgerSubjectIslandSource` and
`adgerDefiniteNominalSources` are exposed for use by *later* paper-anchored
Studies files. Newer rivals make convergence/divergence claims against
Adger's classification:
- [cartner-et-al-2026] (`Studies/CartnerEtAl2026.lean`) converges with
  Adger on `IslandSource.syntactic` for subject islands, from cross-
  constructional invariance data.
- [shen-huang-2026] (`Studies/ShenHuang2026.lean`) diverges from
  Adger on definite-nominal sources, arguing for a `[.syntactic, .semantic]`
  composite from English VOC effects + Mandarin wh-in-situ data.

Phase Theory (`Syntax/Minimalist/Phase.lean`,
[chomsky-2000], [chomsky-2008]) is the immediate theoretical
rival — Adger's framing is to derive island effects "without stipulating
phases, barriers, or subjacency." No formal cross-translation is provided
here: AL operates on graph-theoretic parthood across dimensions; Phase
Theory on PIC over derivational phases. The frameworks share no
structural lemma; identifying a configuration where AL blocks but PIC
permits (or vice versa) is left as a future critical experiment.

-/

namespace Adger2025

-- §1. Substrate re-export

/-! Core AL derivations live in `Syntax/SynGraph.lean` (§10):

| Theorem | Phenomenon |
|---|---|
| `al_blocks_superlocal` | antilocality (35a) |
| `al_blocks_lowering` | no lowering (35b) |
| `al_blocks_sideward` | no sideward subjunction (35c) |
| `al_blocks_parallel` | no parallel merge (35d) |
| `al_blocks_cross_dim` / `al_allows_within_dim` | cross-dim transitivity (35e) |
| `al_allows_rollup_2part` / `al_allows_rollup_1part` | roll-up movement |
| `succ_cyc_blocked_cross_clause` | cross-clausal succ-cyc requires stops |
| `succ_cyc_wh_reaches_C1_after_stop` | with stops, succ-cyc allowed |
| `subject_island_blocks` / `subject_itself_can_extract` | subject islands |
| `adjunct_island_blocks` / `adjunct_itself_can_extract` | adjunct islands |
| `nominal_island_definite_blocks` / `nominal_island_indefinite_allows` | nominal islands |
| `antilocality_sub1` / `antilocality_sub12` | general antilocality |

The graphs `g_subject_island`, `g_adjunct_island`, `g_definite_island`,
`g_sideward` are also public for downstream consumers. -/

-- §2. AL blocks three island configurations from one mechanism

/-- The same `satisfiesAL` predicate fires `false` on three distinct
    configurations: subject (Ch 7 §7.7), adjunct (Ch 4 mechanism on AdvP),
    definite nominal (Ch 6 §6.3.2). The conjunction *composes* the
    substrate theorems rather than re-running `native_decide` on inlined
    copies of the same graphs.

    The "same mechanism" claim is internal to Adger's account — all three
    blockings route through cross-dimensional path failure on the AL
    substrate. It is *not* a unification claim across all of CED:
    - Adjunct islands receive only a Ch 8 sketch (book p. 225); the
      substrate graph instantiates the Ch 4 mechanism, not Ch 8's
      Mod-headed Geis/Haegeman analysis.
    - Subject islands themselves are non-uniform per §7.8 — strength
      varies with definiteness/topicality of the subject.
    - The definite-nominal case requires the Det-subjunction-fills-D
      machinery (book pp. 154–157), not just AL alone. -/
theorem al_blocks_three_island_configurations :
    g_subject_island.satisfiesAL ⟨8, by decide⟩ ⟨0, by decide⟩ = false ∧
    g_adjunct_island.satisfiesAL ⟨7, by decide⟩ ⟨0, by decide⟩ = false ∧
    g_definite_island.satisfiesAL ⟨9, by decide⟩ ⟨0, by decide⟩ = false :=
  ⟨subject_island_blocks, adjunct_island_blocks, nominal_island_definite_blocks⟩

-- §3. Per-phenomenon classifications

/-- Adger's AL classifies subject islands as syntactically sourced — they
    arise from the structural cross-dimensional path failure on a graph
    (`subject_island_blocks`), not from binding (semantic), memory load
    (processing), or information-structural backgroundedness (discourse).

    The classification is editorial in the sense that `IslandSource.syntactic`
    is the natural bin for any structural-configurational mechanism;
    `subject_island_blocks` is the structural fact this classification
    summarises. Exposed as a handle for cross-framework theorems in newer
    Studies files (e.g., `CartnerEtAl2026.subjectIslandSource`). -/
def adgerSubjectIslandSource : IslandSource := .syntactic

/-- Adger's AL classifies definite-nominal islands as single-source
    syntactic: the Det-subjunction-fills-D mechanism (Ch 6 §6.3.2) is
    itself structural — Det subjoins to D filling its 2-part, blocking
    extraction across the resulting cross-dimensional path
    (`nominal_island_definite_blocks`). No separate semantic mechanism
    is invoked.

    [shen-huang-2026] (`Studies/ShenHuang2026.lean`) argues from
    English VOC effects + Mandarin wh-in-situ data that this should be a
    `[.syntactic, .semantic]` composite — the divergence is recorded in
    that file's theorems. -/
def adgerDefiniteNominalSources : List IslandSource := [.syntactic]

-- §4. Cross-framework convergence: Adger AL ↔ MCB §1.6 on Sideward

/-! Both [adger-2025] (mereological Merge, this file) and
[marcolli-chomsky-berwick-2025] §1.6 (algebraic Merge) reach a
`false` verdict on Sideward Merge from incompatible structural primitives:

- **Adger**: Sideward subjunction (sibling subjoin) violates Angular
  Locality — the would-be mover and target are both 1-parts of the same
  parent vertex, so the candidate-α set is empty (no within-dimension
  chain reaches the target). See `al_blocks_sideward` in `SynGraph.lean`,
  on the canonical `g_sideward` configuration. The book's own (35c) lists
  this as "Sidewards subjunction (to a 2-part / 'specifier')," book p. 91
  (PDF p. 103); the substrate's `g_sideward` is a graph-level
  representation of (30) on book p. 91.

- **MCB**: Sideward operations 2(b), 3(a), 3(b) violate either
  `MinimalYieldWeak` (Δb₀ > 0 — workspace components increase) or
  `InducedMapNCL` (the canonical induced map decreases `leafCount`).
  See `Syntax/Minimalist/Merge/MinimalYield.lean` and
  `NoComplexityLoss.lean`.

The two frameworks share NO structural lemma. AL reasons about
graph-theoretic parthood across dimensions; MCB reasons about Hopf-
algebra coproduct counting and induced component maps. The shared
verdict is convergent evidence from incompatible foundations — exactly
the kind of theoretical cross-checking linglib is designed to make
visible (CLAUDE.md: "high interconnection density … incompatibilities
between theories … become visible across the codebase").

The bundled theorem below is *honestly* a verdict-comparison: a
conjunction of two unrelated propositions about different structural
objects, both true. A genuine reduction would require a translation
`SynGraph → Forest (Nonplanar …)` lifting `satisfiesAL ↔ MinimalYieldWeak`;
no such bridge is in scope here. -/

/-- Verdict comparison: the canonical Sideward configuration is rejected
    by both frameworks. Two propositions about different structural
    objects, conjoined to make the cross-framework agreement visible at
    the type level. The Adger conjunct does not depend on the MCB
    parameters `T_i Tnode T_iq`; the MCB conjunct does not reference the
    AL graph. The bundling is documentation, not a reduction. -/
theorem adger_and_mcb_both_reject_sideward
    (T_i Tnode T_iq : RootedTree.Nonplanar (Minimalist.LIToken ⊕ Unit)) :
    -- MCB: Sideward 3(a)-shape transformation violates MinimalYieldWeak
    (¬ Minimalist.Merge.MinimalYieldWeak
        ({T_i} : RootedTree.Forest (RootedTree.Nonplanar (Minimalist.LIToken ⊕ Unit)))
        ({Tnode, T_iq} : RootedTree.Forest (RootedTree.Nonplanar (Minimalist.LIToken ⊕ Unit))))
    ∧
    -- Adger: the canonical Sideward subjunction configuration fails AL
    (g_sideward.satisfiesAL ⟨2, by decide⟩ ⟨1, by decide⟩ = false) :=
  ⟨Minimalist.Merge.sideward_3a_violates_noDivergenceWeak T_i Tnode T_iq,
   al_blocks_sideward⟩

end Adger2025
