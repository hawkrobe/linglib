# Team-Semantic Logics — Architecture & Roadmap

Long-run shape for the team-semantic logic family. The family currently spans
three sibling directories under `Core/Logic/`:

- `Modal/` — the logics (BSML, QBSML, MDL, MIL, InqML) + the Kripke carrier.
- `Team/` — closure-property substrate (`splitsAs`, `IsFlat ↔ Order.IsIdeal`, convexity).
- `Bilateral/` — `IsBilateral` (the paraconsistent negation substrate, shared with non-modal bilateral logics too).

Grounding: Anttila 2025, *Not Nothing: Nonemptiness in Team Semantics* (ILLC
DS-2025-04). The dissertation's chapter structure **is** the target
architecture, and this roadmap is read off it.

---

## Organizing principle: two axes + one payoff relation

A team-semantic logic evaluates formulas against **teams** (`Finset W`, sets of
points). The family stratifies along two orthogonal axes, and each logic is
pinned to a cell by a theorem.

- **Signature axis** (Anttila treats all three as first-class — Ch 3 is
  "Convex *Propositional and Modal* Team Logics"; Ch 5 translates modal ML(⊆)
  into *first-order* inclusion logic): **propositional / modal / first-order**.
- **Closure-class axis** over team properties — *the spine* (Ch 3 is sequenced
  "Convex Properties" → "Convex and Union-closed Properties"):
  - empty-team (`∅ ∈ ·`)
  - downward-closed = persistency (`IsLowerSet`)
  - union-closed (`SupClosed`)
  - convex (`Set.OrdConnected`)
  - lattice law: **`DC = convex + empty`** (already proved in `Team/Closure.lean`).
- **Payoff — expressive completeness**: each logic *is exactly* the formulas
  denoting one cell. `⟦L⟧ = { P | closure conditions }` (+ invariance under
  bounded bisimulation in the modal case). **The cell is a theorem about a
  logic, not a directory** — stratify files by signature, *prove* the cell.

## Cell map

`⟦L⟧` = the class of team properties definable in `L`. ✓ = formalised under
`Modal/` today.

Status legend: **defs** = syntax + support formalised; **cell** = soundness
half (`⟦L⟧ ⊆ cell`) wired via the `Definability` bridge.

| logic | signature | cell | status |
|---|---|---|---|
| classical ML | modal | flat (= DC + UC + empty) | open |
| dependence logic (MDL) | modal | downward-closed + empty | defs + cell ✓ `Dependence.lean` |
| inquisitive (InqML) | modal | downward-closed + empty (≠ mechanism) | defs + cell ✓ `Inquisitive.lean` |
| ML(⊆) (MIL) | modal | union-closed + empty | defs + cell ✓ `Inclusion.lean` |
| **BSML** | modal | **convex + union-closed** | defs + cell ✓ `BSML/` |
| QBSML | first-order | NE-free fragment: flat | defs + cell ✓ (NE-free) `QBSML/` |
| BSML⊘ (BSMLEmpty) | modal | union-closed + empty | in `Studies/AloniAnttilaYang2024.lean` |
| BSML⫦ (BSMLOr, global ∨) | modal | all bisim-invariant (top) | in `Studies/AloniAnttilaYang2024.lean` |
| convex logics (◆) | prop / modal | all-convex | open |
| PL(⫦) | propositional | downward-closed + empty | open |

The closure-profile table in each logic's own module docstring records its cell;
this map is the union of those, plus the gaps.

## Target tree

Genus = team semantics (not "modal"); signature is the directory axis; the
closure cell is discharged per-logic by an expressive-completeness theorem.

```
Core/Logic/TeamSemantics/            namespace TeamSemantics
  Defs.lean              TeamProperty W := Set (Finset W); splitsAs (team partition)
  Closure.lean           lowerSet / supClosed / convex / empty on TeamProperty;
                         bridges (flat ↔ Order.IsIdeal, convex+empty ↔ DC)   [reuses Order/]
  Definability.lean      ⟦L⟧ = definable team properties (Set.Definable-style)   ← THE SPINE
  UniformDefinability.lean   uniform definability / uniform extension (Ch 3.4)   ← cross-logic glue
  Bilateral.lean         IsBilateral + incompatibility notions, bicompleteness (Ch 4)
  Modal/
    Kripke.lean          carrier
    Bisimulation.lean    (bounded) team bisimulation + invariance   ← the modal completeness invariant
    BSML/{Defs, ExpressiveCompleteness, Axiomatization, Enrichment}.lean
    BSMLEmpty/…   BSMLGlobal/…        (graduated out of Studies/)
    Inclusion/…   Dependence/…   Inquisitive/…   Might/…   (◆/▽ variants)
  Propositional/
    PL.lean   Dependence.lean   Inquisitive.lean   Convex.lean
    ProofTheory/GT.lean          sequent calculus, cut elimination (Ch 6)
  FirstOrder/
    QBSML/…   Inclusion.lean     FO inclusion (Ch 5 translation target)
```

## Substrate the long-run needs (and lacks today)

1. **`Definability`** — `⟦L⟧`, the class of team properties a logic defines.
   Every expressive-completeness theorem is a statement `⟦L⟧ = cell`. Keystone:
   nothing below composes without it. (Analogue: mathlib `ModelTheory/Definability.lean`.)
2. **Bisimulation as genus modal substrate** — bounded team bisimulation +
   invariance is the invariant *every* modal completeness theorem (BSML, BSML⊘,
   ML(⊆), BSMLOr) quantifies over. Currently trapped in `BSML/Bisimulation.lean`.
3. **Uniform definability** (Ch 3.4) — the dissertation's *own* cross-logic
   abstraction (the precise sense in which the convex logics extend
   dependence / inquisitive logic). It is a body of **lemmas, not a typeclass
   over logics**.
4. **Incompatibility / bicompleteness** (Ch 4) — the bilateral-negation
   cross-cut (□-incompatibility vs ground-incompatibility, Burgess theorems),
   sitting with `Bilateral.lean`.

## Per-logic structure

Each logic grows into the quadruple the dissertation uses per chapter (Ch 2, Ch 5):

```
Defs → ExpressiveCompleteness / NormalForms → Axiomatization → [ProofTheory]
```

Today's `Defs` + `Properties` split is the `Defs` half plus a sliver of
`ExpressiveCompleteness`.

## Build order — backward from the completeness theorems

Each phase names the consumer that justifies it, so no abstraction is designed
forward. A "soundness cell" below means `⟦L⟧ ⊆ cell` (the easy half, via
`Team/Definability.lean`'s `definableClass_subset`); the converse `cell ⊆ ⟦L⟧`
(full expressive completeness, via normal forms + bisimulation invariance) is
the harder half tracked in phase 5.

1. **`Definability` substrate.** ✅ **Done.** `Team/Definability.lean`:
   `TeamProperty α`, `definedBy`/`Definable`/`definableClass`, the cell classes,
   and the `definableClass_subset` bridge. Consumers wired: MIL
   (`Inclusion.soundFor_unionClosed_inter_empty`) and BSML
   (`BSML.soundFor_convex_inter_unionClosed`).
2. **Bisimulation substrate.** ✅ **Done.** Generic core lifted to
   `Modal/Bisimulation.lean` (`WorldBisim`/`StateBisim` + Lemma 3.7 transport,
   incl. `biUnionAccess`/`possWitness` for the single-relation ◇). BSML invariance
   re-anchored on it; `AloniAnttilaYang2024` kept zero-edit via `export`. Second
   consumer landed: **MDL** (`Dependence.bisim_invariant_eval`) — which is what
   licensed the lift.
3. **Close the BSML cell.** Soundness half ✅ **done**: `ordConnected_support`
   discharged (Anttila Prop 3.3.1, split-disjunction convexity via union
   closure), and `soundFor_convex_inter_unionClosed` wired. **Open:** the
   converse `convex ∧ union-closed ⊆ ⟦BSML⟧` (normal forms), where *uniform
   definability* emerges as lemmas.
4. **Stratify + rename.** Regroup as `TeamSemantics/{…}`, namespace
   `TeamSemantics.*` (shed `Core.Logic.`). *Gate:* only after 1–3 — it touches
   14+ consumers, so land it on a proven structure. (High churn; lowest urgency.)
5. **Fill the lattice.** Soundness cells ✅ **done for all five formalised
   logics**: MIL (`unionClosed ∩ empty`), BSML (`convex ∩ unionClosed`), MDL and
   InqML (`downwardClosed ∩ empty`, `soundFor_downwardClosed_inter_empty`), and
   QBSML — *fragment-relative*: the NE-free fragment is sound for `flat`
   (`soundFor_flat_neFree`, via the new `definableClassWhere` substrate), since
   NE is QBSML's only non-classical element so the full logic has no
   unconditional cell (@cite{aloni-vanormondt-2023} Prop 4.1 / Facts 1–2). BSML
   also carries the dual NE-free `flat` cell.
   **Open:** the converse / `ExpressiveCompleteness` + `Axiomatization` per logic;
   graduate BSMLOr and BSMLEmpty out of `Studies/`; add the open cells (classical
   ML = flat, convex ◆-logics, propositional PL + proof theory, FO inclusion).
6. **Proof theory + incompatibility.** Sequent calculus (Ch 6) and the Burgess /
   bicompleteness program for bilateral negation (Ch 4). Most research-y; lowest
   priority.

## Discipline

- **Backward from instances, not forward design.** The shared abstraction is the
  `Definability` + uniform-definability *lemma layer* (phases 1, 3), justified by
  the completeness theorems that consume it — **not** a bundled `TeamLogic` class.
  No closure law is shared across cells (even the empty-team property fails for
  NE-bearing BSML), so a class would carry data with no laws.
- **`IsBilateral` stays a `Prop`-bundle** (like mathlib `IsLUB`/`IsLeast`), and
  applies only to the bilateral logics (BSML, QBSML, MDL); unilateral logics
  (MIL, InqML) genuinely have no anti-support — do not force a `Bool`-polarity
  `eval` on them.
- **Closure lemmas are property-first** (mathlib convention: `supClosed_empty`,
  `isClosed_empty`, `isOpen_univ`): use `supClosed_support`, `isLowerSet_support`.
  `support_empty` correctly stays subject-first (it is a `∅ ∈ ·` *membership*
  assertion, cf. `Order.Ideal.bot_mem`). ✅ All five logics now use the
  property-first form uniformly (`supClosed_support`, `isLowerSet_support`); the
  former `Inclusion.support_supClosed` / `Inquisitive.support_isLowerSet`
  outliers were renamed.

## Status snapshot

Phases 1–2 done; soundness cells closed for all five formalised logics (MIL,
BSML, MDL, InqML, and QBSML's NE-free fragment), the `Definability` substrate
extended with fragment-relative `definableClassWhere`, and the closure-lemma
naming unified property-first. Carrier-level bisimulation lifted with two
invariance consumers (BSML, MDL). The converse (full expressive completeness
via normal forms) and the axiomatization / proof-theory program remain
unbuilt. **Next deep step:** a BSML normal-form / converse theorem (phase 3
open half) — where bisimulation invariance and `Definability` finally combine,
and *uniform definability* emerges. Beyond that: the QBSML / MDL / InqML
converses, then graduating BSMLOr / BSMLEmpty out of `Studies/`.
