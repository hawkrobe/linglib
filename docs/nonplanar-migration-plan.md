# Nonplanar SyntacticObject Migration Plan

**Goal**: Make nonplanar trees the primary representation of syntactic
objects, with planar order derived via a separate linearization theory
(LCA, head-directionality parameter, prosodic determinants).

## MCB Faithfulness (verified 2026-05-06 against the published 2025 book)

Nonplanarity is not a §1.7 detail — it's the foundation of MCB chapter 1.
Page-cited evidence:

| Page | Reference | Quote |
|------|-----------|-------|
| 22 | Def 1.1.1 | "SO is the free, non-associative, **commutative** magma over SO₀, **SO = Magma_{na,c}(SO₀, M)**, with M(α,β) = **{α,β}**" |
| 23 | Remark 1.1.2 | "By **nonplanar** we mean that we regard objects T ∈ 𝔗_{SO₀} as **abstract trees, without fixing a choice of a planar embedding**. ... word order is considered part of the **Externalization process**, not of the core computational mechanism of syntax given by Merge." |
| 23–24 | §1.1.3 | When MCB draws trees with α-β-γ, "the tree represented here is the same as" γ-β-α (explicit) |
| 27 | Def 1.2.1 | "Workspaces are nonempty finite (multi)sets of syntactic objects... binary **nonplanar** rooted trees" |
| 34 | Remark 1.2.9 | The coproduct Δ^c is "the restriction to **non-planar** binary rooted tree of the well-studied coproduct of the Connes-Kreimer Hopf algebra" |
| 35 | example | "this is a nonplanar tree, so {α, {β, γ}} = [α-β-γ] = [β-γ-α] = [α-γ-β]" (three planar drawings explicitly equated) |
| 37 | Lemma 1.2.10 proof | "associative and **commutative**, in the case of **nonplanar** trees and forests" |
| 77 | Def 1.7.1 | "two **nonplanar** binary rooted trees T₁, T₂ ∈ 𝔗_{SO₀}" |
| 78 | Lemma 1.7.2 proof | Case (3) match "as shown in Figure 1.6" — relies on `{T₂, T₃} = {T₃, T₂}` |
| 92 | Lemma 1.10.1 | SO is "the free, nonassociative, **commutative** magma" |
| 93 | Prop 1.10.2 | Planar embeddings appear as "multiplicities" only |

The §1.7 pre-Lie blocker is not an isolated mismatch — it's where a
*pervasive* design mismatch becomes visible. MCB's entire chapter is on
nonplanar trees; the current planar TraceTree formalization is at odds
with §1.1 Def 1.1.1 itself. We just hadn't hit a theorem that exposed
it until §1.7. Phase 4–5 substrate (dual Hopf primitive Lie,
countercyclic-to-EM/IM equivalence) would have hit exactly the same
wall.

## Mathlib Inventory

`Mathlib.Algebra.Group.Defs`:
- Defines **typeclasses** for `Magma`, `CommMagma`, `Semigroup`,
  `CommSemigroup`, `Monoid`, etc. — predicates over types with a
  binary operation, not type constructors.

`Mathlib.Algebra.Free`:
- Defines `FreeMagma α` = `inductive ... | of (a : α) | mul (l r : _)`.
  Same shape as planar TraceTree (modulo our `.trace` movement marker).
- Has `Magma.AssocQuotient` (quotient by associativity → Semigroup).
- **No `FreeCommMagma α`.** No `Magma.CommQuotient`.

So mathlib supplies `CommMagma` as a typeclass we can *satisfy* on
whatever nonplanar tree type we build, but doesn't supply the type
itself. We define it as a quotient of mathlib's `FreeMagma`:

```lean
def FreeCommMagma (α : Type*) := Quotient (FreeMagma.commSetoid α)
```

(Detailed construction in the "Type Choice" section below.)

**Side benefit**: contributing `FreeCommMagma α` upstream to mathlib
would be a natural completion of the `FreeMagma` API, with uses beyond
linglib (operad theory, Connes-Kreimer Hopf algebra).

## Motivation summary

- MCB explicitly says nonplanar from §1.1.1 onward (not just §1.7).
- Chomsky's Merge is set-theoretic: M(α,β) = {α,β}, unordered.
- Linearization (LCA, head-directionality, prosody) is a *separate
  theory* in linguistics — Externalization, in MCB's terms. The
  current planar-storage design conflates it with syntactic structure
  and makes parameter variation (head-final Japanese vs head-initial
  English) awkward.
- The §1.7 pre-Lie identity is provably false on planar TraceTree
  (Lean-verified at `scratch/test_preLie_planar.lean`). The planarity
  debt compounds with every additional algebraic identity formalized
  on the wrong carrier.

---

## Architectural Picture

```
SyntacticObject (nonplanar, primary)
   │
   ├── algebra: insertSum, ◇, lieBracketR, Hopf coproduct (strict equalities)
   │
   ├── Linearization (separate theory: LCA / head-directionality / prosody)
   │      │
   │      ▼
   │   List LIToken (PF output)
   │
   └── HeadMarking (which child is the head — needed for outerCat,
                    head projection, X-bar; also feeds Linearization)
```

Old picture (current):

```
SyntacticObject = TraceTree (planar, primary)
   │
   ├── algebra: insertSum, ◇, ... (false strict identities; pre-Lie sorry)
   │
   └── phonYield (left-to-right concat — "free" because planarity is baked in)
         ▼
       List LIToken
```

The "free" linearization in the current design is the bug, not the
feature. It papers over a real theory.

---

## Type Choice: `FreeCommMagma α` (mathlib-canonical)

**Decision**: use mathlib's existing `FreeMagma α` (planar binary tree
with leaf labels) and quotient by the smallest commutativity congruence:

```lean
-- Already in mathlib (Mathlib/Algebra/Free.lean):
-- inductive FreeMagma (α : Type*) where
--   | of : α → FreeMagma α
--   | mul : FreeMagma α → FreeMagma α → FreeMagma α

-- New (this migration adds; eventually upstream):
inductive FreeMagma.CommRel : FreeMagma α → FreeMagma α → Prop
  | swap      : CommRel (a * b) (b * a)
  | mul_left  : CommRel x y → CommRel (x * z) (y * z)
  | mul_right : CommRel x y → CommRel (z * x) (z * y)

def FreeMagma.commSetoid (α : Type*) : Setoid (FreeMagma α) :=
  ⟨EqvGen FreeMagma.CommRel, EqvGen.is_equivalence _⟩

def FreeCommMagma (α : Type*) : Type _ :=
  Quotient (FreeMagma.commSetoid α)
```

**Single type parameter**: trace markers fold into leaves via `Sum`:

```lean
abbrev SyntacticObject : Type := FreeCommMagma (LIToken ⊕ Nat)
@[match_pattern] abbrev SyntacticObject.leaf (a : LIToken) : SyntacticObject :=
  FreeCommMagma.of (.inl a)
@[match_pattern] abbrev SyntacticObject.trace (n : Nat) : SyntacticObject :=
  FreeCommMagma.of (.inr n)
```

### Why this is mathlib-canonical

1. **Matches the `Free` + `CommX` pattern**: mathlib has `FreeMonoid` /
   `FreeCommMonoid`. The non-associative analog is `FreeMagma`; its
   commutative analog is `FreeCommMagma`. The naming slots in by analogy.
2. **Uses the existing `CommMagma` typeclass** from
   `Mathlib.Algebra.Group.Defs`. `FreeCommMagma α` is the free instance
   of that typeclass — the universal property writes itself.
3. **Single type parameter**: matches `FreeMagma α`, `FreeMonoid α`,
   `FreeGroup α`, `FreeCommMonoid α`. Mathlib prefers minimal
   parameters.
4. **Right home in mathlib**: `Mathlib/Algebra/Free.lean` already has
   `FreeMagma` and `Magma.AssocQuotient`. `FreeCommMagma` belongs in
   the same file or sibling. Upstream PR shape is obvious.
5. **No initialism, no negation**: tells you what it IS, not what it
   isn't.

### Hard prerequisite verified before Phase 0

The auditor verified that `inductive ... | node : Sym2 (...) → _` is
REJECTED by Lean's positivity check (`Sym2` is `Quot (Sym2.Rel α)`,
and Lean does not allow recursive occurrences under an arbitrary
`Quot`). This rules out a Sym2-based inductive entirely — must use a
quotient of an existing inductive.

The `Quotient FreeMagma`-based route compiles (auditor verified at
`/tmp/quot_route.lean`). Phase 0's first deliverable is a local
re-verification spike at `scratch/freecommmagma_spike.lean`.

### Mathlib precedents for this pattern

- `Multiset α := Quotient (List.isSetoid α)`
  (`Mathlib/Data/Multiset/Defs.lean`) — quotient an inductive carrier
  by an order-irrelevance setoid.
- `Sym2 α := Quot (Sym2.Rel α)` (`Mathlib/Data/Sym/Sym2.lean:100`) —
  quotient the planar pair by the swap relation.
- `FreeAbelianGroup α := Additive (Abelianization (FreeGroup α))`
  (`Mathlib/GroupTheory/FreeAbelianGroup.lean:96`) — closest analogue:
  take a free non-commutative thing, commutativize via quotient.

### Recursor / lift API mirrors `Sym2` line-for-line

Mathlib's `Sym2.ind`, `Sym2.lift`, `Sym2.lift₂` (lines 123–235 of
`Mathlib/Data/Sym/Sym2.lean`) are the API template. We define
`FreeCommMagma.ind`, `FreeCommMagma.recOn`, `FreeCommMagma.lift`,
`FreeCommMagma.lift₂`, all tagged `@[induction_eliminator,
elab_as_elim]`. The `Subtype`-shaped "respects swap" obligation
matches `Sym2.lift`'s line 202.

The "ergonomic cost" of `Quot.lift` (a common worry) is exactly what
mathlib accepts everywhere; the mitigation is the recursor API,
not avoidance of the quotient.

### Naming convention recap

- **`FreeCommMagma α`** — the underlying type. Single parameter.
  Mathlib-shaped, upstream-candidate.
- **No separate `FreeCommMagma` middle layer** — folding traces
  through `Sum` keeps everything in the single `FreeCommMagma α` shape.
- **`SyntacticObject : Type`** — the linglib-level abbrev,
  unchanged in name and concept; just retargeted from `TraceTree
  LIToken Nat` to `FreeCommMagma (LIToken ⊕ Nat)`.
- **`.leaf` / `.trace` constructors preserved** as
  `@[match_pattern]` shims at the `SyntacticObject` level (so existing
  pattern matches like `match so with | .leaf a => ... | .trace n => ...`
  continue to work, modulo Quotient lift obligations).

---

## Migration Phases

Each phase is independently buildable + commitable. **Deprecation
aliases ship from Phase 0 onward** (mathlib idiom: don't maintain
parallel substrate without deprecation pressure). The `SyntacticObject :=
FreeCommMagma` swap moves into Phase 1, not Phase 4 — mathlib
discourages long-lived parallel hierarchies.

### Phase 0: FreeCommMagma backbone + ergonomics (1–2 sessions)

**Deliverables:**
- `Linglib/Core/Algebra/Free/CommMagma.lean` (mathlib-shaped path):
  - Define `FreeMagma.CommRel` (3 constructors: swap, mul_left,
    mul_right) and `FreeMagma.commSetoid α`.
  - `def FreeCommMagma (α : Type*) : Type _ := Quotient (FreeMagma.commSetoid α)`
  - Constructor shims (matching mathlib's `FreeMagma` API):
    - `FreeCommMagma.of : α → FreeCommMagma α := Quotient.mk _ ∘ FreeMagma.of`
    - `FreeCommMagma.mul : FreeCommMagma α → FreeCommMagma α → FreeCommMagma α`
      (lifted from `FreeMagma.mul` via `Quotient.lift₂` with `swap_respects` proof)
    - `instance : Mul (FreeCommMagma α)` and `instance : CommMagma (FreeCommMagma α)`
  - Recursors mirroring `Sym2`'s API verbatim:
    - `@[induction_eliminator, elab_as_elim] def FreeCommMagma.ind`
    - `FreeCommMagma.recOn`, `FreeCommMagma.lift`, `FreeCommMagma.lift₂`
      with the `Subtype`-shaped "respects swap" obligation per
      `Sym2.lift` line 202
  - Basic API: `size`, `length` — each defined via `lift` over a
    swap-respecting underlying function
  - `DecidableEq` via canonicalization to a lex-min representative
    (mathlib doesn't have a generic "DecidableEq for Quot" idiom for
    this shape; we hand-write canonicalization)
  - `Repr` instance via the same canonical form
  - Universal property: `lift : (α →ₙ* β) ≃ (FreeCommMagma α →ₙ* β)`
    when `β` carries a `CommMagma` instance — mirrors `FreeMagma.lift`
    (line ~110 of `Mathlib/Algebra/Free.lean`)

**Build invariant:** TraceTree code untouched but a one-way coercion
`TraceTree.toFreeCommMagma : TraceTree α β → FreeCommMagma (α ⊕ β)`
lands in `Decorated.lean` (forgets order; uses `.inl` for leaves and
`.inr` for traces).

**Exit criteria:**
- `lake build Linglib.Core.Algebra.Free.CommMagma` clean
- `FreeCommMagma.mul a b = FreeCommMagma.mul b a` provable via
  `Quotient.sound (FreeMagma.CommRel.swap.eqvGen)`
- `decide` works on small `FreeCommMagma`-equality goals (test on
  `FreeCommMagma Nat` with concrete trees)
- Build-time delta measured (not estimated): record clean build
  before/after Phase 0 in CHANGELOG entry.

### Phase 1: SyntacticObject swap + Pre-Lie + Hopf algebra (4–6 sessions)

**1.0 — `SyntacticObject := FreeCommMagma (LIToken ⊕ Nat)` swap (1 session, FIRST)**
- Change `Linglib/Theories/Syntax/Minimalist/Basic.lean:158`:
  `abbrev SyntacticObject := FreeCommMagma (LIToken ⊕ Nat)`
- Provide `@[match_pattern]` shims for the `.leaf` / `.trace`
  constructor distinction at SyntacticObject level:
  ```lean
  @[match_pattern] abbrev SyntacticObject.leaf (a : LIToken) : SyntacticObject :=
    FreeCommMagma.of (.inl a)
  @[match_pattern] abbrev SyntacticObject.trace (n : Nat) : SyntacticObject :=
    FreeCommMagma.of (.inr n)
  ```
  Existing `match so with | .leaf a => ... | .trace n => ...` continues
  to work, modulo the `.mul`-respect-swap obligations on the result.
- Add `@[deprecated (since := "2026-05-06")] alias` for every
  `TraceTree`-pattern operation that has a one-line `FreeCommMagma`
  equivalent (so all downstream consumers see warnings immediately).
- Update construction sites: `.node a b` becomes `FreeCommMagma.mul a b`
  (the swap-equivalent now provable, not a definitional bug).
- Pattern-match sites: cascade through ~26 files. Some breakages
  expected; either fix in this session (preferred) or land deprecation
  aliases that smooth the transition.
- Build invariant after 1.0: full repo builds. PF / linearization /
  head projection all temporarily use a "trivial canonical
  linearization" — this is the substrate Phase 2 replaces with real
  linearization theory.

This is the cascade mathlib would insist on; deferring it (as the
original plan did, putting the swap in Phase 4) produces months of
parallel-substrate maintenance with no migration pressure on
consumers. We pay the cost up front instead.

**Sub-phases (after 1.0):**

**1a — Insertion substrate (1 session)**
- `Linglib/Core/Combinatorics/RootedTree/Insertion.lean` — refactor
  in place; the file's existing namespace stays
  - Port `insertSum`, `insertAt`, `Edge`, `edges` to FreeCommMagma
  - Each MCB-edge is now genuinely 1 insertion (not 2 planar variants)
  - Port §9.1 `Edge.classifyEquiv` (much simpler — no `newEprime`
    asymmetry; the new sibling pair is intrinsically unordered)
  - Port §9.2 `edges_insertAt_eq_classification`
  - Port §9.3 `insertAt_commute_diff`
  - Port `insertAt_lift_eq_nested` (Step 1 substrate from current work)

**1b — Pre-Lie identity (1 session)**
- Define `insertSumZ`, `lieBracketR`, `insertSumLift` (◇) on FreeCommMagma
- **Prove `insertSumLift_right_preLie` as a strict equality** —
  this is the headline. The (c) `newEprime` discrepancy disappears
  because `Quot.mk _ (.mul T₂ T₃) = Quot.mk _ (.mul T₃ T₂)` via
  `.swap`.
- Derive Jacobi for `⁅·,·⁆` lifted bilinearly

**1c — Hopf algebra carrier (2 sessions)**
- Refactor `Linglib/Core/Algebra/ConnesKreimer/Defs.lean`:
  `Hc R α := (FreeCommMagma α) →₀ R`
- Port `Bialgebra`, `Coproduct`, `AdmissibleCut`, `AugmentedCut`,
  `LhsBridge`, `LhsEquiv`, `LhsIndex`, `DoubleCut` to the nonplanar
  carrier. The cuts and quotients work cleanly because they were
  already using `Multiset` for unordered cut-sets.
- **Sanity theorem**: bridge from planar `Hc R α` (legacy) to
  nonplanar by summing over planar embeddings of each nonplanar tree
  (witnesses MCB's "multiplicity" reading of §1.10). Marks the
  planar `Hc` `@[deprecated]` once the bridge is in place.

**1d — pre-Lie ↔ Hopf primitive Lie identification (1 session)**
- MCB Lemma 1.7.3 (book p. 78): the insertion Lie algebra is the
  primitive-element Lie algebra of `H^∨` (dual Hopf algebra). This
  was deferred as Phase 4 in the original §1.7 roadmap; it lands
  cleanly on nonplanar substrate.

**Build invariant:** Pre-Lie identity in §1.7 is sorry-free. All
previously sorry-free theorems remain sorry-free. The §6 `sorry` is
removed (the theorem is now true on the new carrier and provable).

**Exit criteria:** `insertSumLift_right_preLie` is sorry-free on
FreeCommMagma; old TraceTree-based equivalent (kept as legacy under
deprecation alias) gets removed in Phase 4 cleanup.

### Phase 2: Linearization theory (2–3 sessions)

**Deliverables:**
- `Linglib/Theories/Syntax/Minimalist/Linearization/HeadDirectionality.lean`
  - `HeadMarking` — picks the head child at each `.mul` node
  - `HeadDirectionality := HeadInitial | HeadFinal` parameter
  - `linearize_param : FreeCommMagma → HeadMarking → HeadDirectionality → List LIToken`
- `Linglib/Theories/Syntax/Minimalist/Linearization/LCA.lean`
  (already exists as a stub; flesh out)
  - LCA derivation from asymmetric c-command (Kayne 1994)
  - Theorem: LCA + head marking → consistent linearization
- `Linglib/Theories/Syntax/Minimalist/Linearization/PFOutput.lean`
  - `phonYield : FreeCommMagma → Linearization → List String`
  - `linearize : FreeCommMagma → Linearization → List LIToken`
  - Phase 1.0's "trivial canonical linearization" is replaced by
    real linearization theory; the trivial one becomes a derived
    `defaultLinearization` instance

**Sanity tests:**
- Japanese head-final example: same FreeCommMagma, head-final
  linearization → SOV order
- English head-initial example: same FreeCommMagma, head-initial → SVO
- Show one syntactic object can have multiple PF realizations

### Phase 3: Per-phenomenon followups + study-file migration (3–5 sessions)

After Phase 1.0's cascade through ~26 files, some study files and
specific Theory files may have planar-tree assumptions that survived
the swap (e.g., specific `decide`-checked equalities that depend on
storage order). Phase 3 audits and fixes these.

**Files to audit (post-Phase 1.0):**
- `Theories/Syntax/Minimalist/{Selection,Labeling,Agree,SmallClause}.lean`
- `Theories/Syntax/Minimalist/HeadFunction.lean` —
  `PlanarMarking` → `HeadMarking` (a head-marking on a
  FreeCommMagma; the "planar" framing was the bug)
- `Phenomena/Possession/Studies/AissenPolian2025.lean`,
  `Phenomena/Case/Studies/Pesetsky2013.lean`,
  `Phenomena/Islands/Studies/Adger2025.lean`,
  `Theories/Syntax/CCG/Formal/Equivalence.lean`

**Build invariant:** Each migrated file passes its own build. The
deprecation aliases from Phase 0/1.0 give the warnings; Phase 3
silences them per-file.

### Phase 4: TraceTree retirement decision (1 session)

After Phases 0–3, decide:
- **Keep TraceTree** as a separate planar tree type for diagnostic /
  presentation purposes (e.g., printing example trees in studies)
- **Remove TraceTree entirely**, with FreeCommMagma handling all storage and
  PF being just `List LIToken`

This decision can be deferred until Phase 4 lands and we see how often
TraceTree is actually still useful.

---

## Substrate Invariants Preserved Through Migration

1. **Sorry counts**: monotonically non-increasing through phases.
   Phase 1b *removes* the §6 pre-Lie sorry (against the new FreeCommMagma
   version); existing sorries elsewhere stay sorries.
2. **Build time**: should not regress. Adding parallel substrate may
   add 10–20% to clean build time during Phase 1; Phase 4 retirement
   compensates.
3. **API stability**: every Phenomena/Studies file should keep building
   without code changes through Phases 0–2; Phase 3 introduces
   per-file changes.
4. **Theorem statements**: existing strict-equality theorems on
   TraceTree remain. New theorems on FreeCommMagma are additional.

---

## Risk Assessment + Mitigation

### Risk: `DecidableEq (FreeCommMagma α)` requires canonicalization

Mathlib does not have a generic "DecidableEq for `Quot`" idiom for the
free-commutative-magma shape; `Sym2`'s `decEq` works because `Sym2.Rel`
is the simple swap relation with explicit pairs. The full congruence
`EqvGen FreeMagma.CommRel` (the equivalence closure of swap-at-any-depth
plus mul-congruence) is *not* obviously decidable on syntax-tree-shaped
data without normalizing.

**Mitigation:** Define a canonicalization function
`FreeMagma.normalize : FreeMagma α → FreeMagma α`
(for `[LinearOrder α]`) that produces a lex-min representative (sort
the `.mul` arguments at each node by some total order — `.of` leaves
first, then by leaf label, then recursively). Prove
`normalize_respects_commRel` and `commEquiv_iff_normalize_eq`. Then
`DecidableEq (FreeCommMagma α)` follows from `DecidableEq (FreeMagma α)`
via the canonical form. Same canonicalization underlies the `Repr`
instance. (For `α` without `LinearOrder`, fall back to `noncomputable`
DecidableEq via classical logic — acceptable for proof-only contexts.)

### Risk: `Quot.lift` definitional unfolding

Mathlib has been bitten by `Quot.lift` not reducing the way you want
(`Quot.lift f h (Quot.mk r x) = f x` is a propositional equality, not
definitional, in some configurations). Operations defined via
`FreeCommMagma.lift` won't reduce in `decide` / `rfl` proofs the way
direct inductive matches would.

**Mitigation:** Establish a clean `simp` API per operation:
`@[simp] theorem size_leaf`, `size_trace`, `size_mul` — the user-facing
lemmas, defined to unfold cleanly. Inside proofs, prefer `simp only
[size_*]` over relying on `rfl`. Test in Phase 0 that `decide` works
on small decidable goals.

### Risk: Hopf algebra refactor cost

`DoubleCut.lean` is 1627 lines, `Coproduct.lean` is 549, `LhsEquiv` is
502. These have ~250 .node-pattern lines combined.

**Mitigation:** Phase 1.0's deprecation aliases keep the planar API
working briefly; refactor in Phase 1c is a focused rewrite of those
specific files. If 1c blows up, deprecation aliases let us pause
mid-refactor without breaking other consumers. Verify estimated cost
by porting one mid-sized file (`LhsEquiv.lean`, ~76 .node patterns)
first as a calibration spike.

### Risk: Per-language planar choices break

Some studies depend on a specific planar order (e.g., Japanese
head-final examples encoded as `.node Spec (.node V Obj)`). After
migration, these need an explicit head marking.

**Mitigation:** Provide `defaultLeftHeaded` linearization in Phase 1.0
that matches the current implicit convention. Phase 2 fleshes out the
real LCA / head-directionality theory. Phase 3 study migration becomes
"add `headMarking := defaultLeftHeaded` annotation" plus targeted fixes.

### Risk: Pre-Lie proof on FreeCommMagma turns out hard

The headline of Phase 1b is sorry-free pre-Lie. If the proof is harder
than expected (e.g., `Quot.lift` issues with the §9 substrate), the
whole migration's main motivation is undermined.

**Mitigation:** First sub-deliverable of Phase 1b is
`insertSumLift_zero_*` + `insertSum_swap` (sanity that the substrate
respects the swap relation). If those take >1 session, abort to Path 3
(planarKernel modulo) with the Phase 0 substrate as foundation for a
future retry. The §9.1–§9.4 substrate already landed (`classifyEquiv`,
edge decomposition, commute-diff, lifted-equals-nested) is reusable
on either carrier.

### Risk: Bus factor / mid-migration interruption

The migration spans many sessions. If interrupted mid-phase, the repo
may be in an inconsistent state.

**Mitigation:** Each phase is independently mergeable. Land Phase 0
before starting Phase 1; land Phase 1.0 (the cascade) atomically — do
not commit a partial-cascade state. Phases 2/3 are naturally per-file.

### Risk: Downstream consumers we missed

`grep -ln TraceTree` finds 26 files; some may have non-obvious
dependencies on planar order (e.g., a `decide`-checked equality in a
study file's tests).

**Mitigation:** Pre-cascade audit in Phase 0 produces a complete
inventory + per-file estimate. Phase 1.0's atomic cascade either
succeeds (all files build) or fails fast (catastrophic, requires
revert) — no in-between. Lake's incremental rebuild surfaces missed
consumers immediately.

### Risk: Universe polymorphism issues

`FreeCommMagma α` has a single type parameter `α : Type u`; `Quotient`
lives in the universe of its argument. The `Sum` fold (`α ⊕ β`) for
SyntacticObject keeps both `α : Type u` and `β : Type v` accessible
but may pin us to `Type (max u v)`.

**Mitigation:** Phase 0 spike validates with `α : Type u` explicit
universe parameter. Test `Hc R α := (FreeCommMagma α) →₀ R` for
`R : Type w`, `α : Type u` with both universes distinct. For
SyntacticObject's `Sum` fold, the canonical use case is
`LIToken : Type` and `Nat : Type`, both `Type 0`, so universe
constraints don't bite at the linguistic level. If we ever need to
go polymorphic, `ULift` resolves it.

---

## Concrete Phase 0 First Session Deliverables

1. **Positivity-check spike** at `scratch/freecommmagma_spike.lean`:
   verify `def FreeCommMagma α := Quotient (FreeMagma.commSetoid α)`
   compiles in linglib's mathlib version. Auditor verified at
   `/tmp/quot_route.lean`; we re-verify locally.
2. **Land `Linglib/Core/Algebra/Free/CommMagma.lean`** with:
   - `inductive FreeMagma.CommRel` (3 constructors: swap, mul_left,
     mul_right)
   - `def FreeMagma.commSetoid α : Setoid (FreeMagma α)`
   - `def FreeCommMagma α := Quotient (FreeMagma.commSetoid α)`
   - Constructor shims: `FreeCommMagma.of`, `FreeCommMagma.mul`
   - Recursors: `ind`, `recOn`, `lift`, `lift₂` per `Sym2.lift` pattern
     (lines 123–235 of `Mathlib/Data/Sym/Sym2.lean`)
   - Basic operations: `size`, `length`
   - Typeclass instances: `Mul`, `CommMagma`
   - Decidable equality (via canonicalization, requires `[LinearOrder α]`)
   - `Repr` instance via canonical form
   - Universal property: `lift : (α →ₙ* β) ≃ (FreeCommMagma α →ₙ* β)`
     when `β` is `CommMagma`
3. **Add `TraceTree.toFreeCommMagma` coercion** in
   `Linglib/Core/Combinatorics/RootedTree/Decorated.lean` —
   `TraceTree α β → FreeCommMagma (α ⊕ β)`, one-way bridge for the
   migration window.
4. **Update §6 sorry's docstring** in `Insertion.lean` to point at the
   incoming FreeCommMagma-based replacement (Phase 1b deliverable).

**Estimated total effort**: 8–12 focused sessions over 2–4 weeks of
calendar time, depending on session frequency.

---

## What This Plan Does NOT Cover (Explicit Out-of-Scope)

- **Migrating non-Minimalist tree types**: CCG trees, dependency
  grammar, HPSG feature structures all have their own carriers and
  are not affected.
- **Phenomena/Studies migration beyond syntax**: Semantics studies,
  pragmatics, phonology — only affected if they import SyntacticObject
  directly.
- **Backwards-compatibility for downstream-of-linglib users**: linglib
  has no external users; SyntacticObject API change is acceptable.
- **Performance**: `Quotient` lift may add a small overhead vs raw
  inductive pattern matching. Not optimizing in this migration.

---

## User-Approved Decisions (2026-05-06)

1. **Type choice**: Option C1 (`Quotient FreeMagma`) — Option C2
   (Sym2-based inductive) does not compile (auditor-verified
   positivity rejection).
2. **Naming**: `FreeCommMagma α` (single type parameter).
   Trace markers fold into leaves via `Sum`. No separate
   `SyntacticTree` middle type; `SyntacticObject := FreeCommMagma
   (LIToken ⊕ Nat)` direct.
3. **Phase ordering**: SyntacticObject swap moves to Phase 1.0 (FIRST,
   before pre-Lie / Hopf algebra refactor) — mathlib idiom: don't
   maintain parallel substrate without deprecation pressure.
4. **Phase 1d (Lemma 1.7.3 dual Hopf)**: bundled into the migration
   since it's the natural completion of the §1.7 substrate.
5. **TraceTree retirement (Phase 4)**: decision deferred until Phase 3
   completes — informed by whether TraceTree is still useful for
   diagnostic / presentation purposes.
