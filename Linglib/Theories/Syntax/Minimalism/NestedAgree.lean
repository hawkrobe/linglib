import Linglib.Theories.Syntax.Minimalism.Probe

/-!
# Nested Agree @cite{amato-2025}

A configuration on a Minimalist `SyntacticObject`: a single head bears
two (or more) ordered probes that share a goal-head, and each
post-initial probe's search domain is restricted to the daughters of
the shared goal. The matryoshka structure is *derived* from
`cCommandsIn` (the Minimalist substrate), not stipulated.

## Configuration

A `NestedAgreeConfig` packages:

1. `stack : OrderedProbeStack` — ordered probes; head of list = first.
2. `root : SyntacticObject` — the tree under consideration.
3. `probingHead : SyntacticObject` — the head bearing the probes.
4. `goalHead : SyntacticObject` — the shared goal targeted under MME.
5. `phiActive : SyntacticObject → Bool` — *lexical* primitive: which
   subtrees carry active φ-features. Defective v of unaccusatives
   gets `false`; this is what blocks π-Agree in @cite{amato-2025}'s
   §3.4.2 unaccusative analysis.

`initialDomain`, `daughters`, `searchDomain` are *derived* via
`cCommandsIn` and reflexive containment, filtered by `phiActive`. The
matryoshka claim — post-initial domains restricted to the goal's
daughters — is structural, not axiomatic. Consequently
`IsNestedAgreeConfig` is non-vacuous: it requires `goalHead` to be
both c-commanded by `probingHead` in `root` *and* phi-active.

## Cross-domain applications

Italian aux selection (§3) is formalized at
`Phenomena/AuxiliaryVerbs/Studies/Amato2025.lean`. Other Amato 2025 §4
case studies (Icelandic DAT-NOM, Lak perfective, Spanish VOS,
Bulgarian wh, ditransitives) are deferred — their consumers will
construct `SyntacticObject` trees and `phiActive` predicates the
same way.

## Architecture

Sits at Layer 2 (compositional Agree pattern), built on the Layer-1
substrate (`SyntacticObject`, `cCommandsIn`, `containsOrEq`,
`subtrees`) imported transitively via `Probe`. Predicates are `Prop`
with `[Decidable]` instances; `runStack` returns
`Option SyntacticObject`.

## Sibling mechanisms in `Theories/Syntax/Minimalism/`

`Theories/Syntax/Minimalism/CyclicAgree.lean` (@cite{bejar-rezac-2009})
and `LongDistanceAgree.lean` (@cite{szabolcsi-2009}) are sibling
Layer-2 patterns. All three address "what does a probe do beyond its
first operation," but the answers differ:

- **Nested Agree** (this file): *multiple ordered probes* on a single
  head, all forced to target the *same* goal under maximized matching;
  each subsequent probe operates on a *truncated* search domain
  restricted to the prior goal's daughters.
- **Cyclic Agree** (`CyclicAgree.lean`): a *single articulated probe*
  with multiple feature segments; cycle I targets the IA, cycle II
  targets the EA via the *expanded* residue domain. Subsequent
  cycles see *more* (residue + EA), not less.
- **Long-Distance Agree** (`LongDistanceAgree.lean`): a *single probe*
  in the matrix relaxes locality across a non-defective C, reaching
  an embedded goal.

The three are conceptually orthogonal mechanisms for serial probing.
A unified theory of probe behavior would treat them as alternatives
in the design space; we keep them as independent Layer-2 patterns
that consumers select by phenomenon.
-/

namespace Minimalism.NestedAgree

-- ============================================================================
-- § 1: Probe stack
-- ============================================================================

/-- An ordered list of probes on a single head. The list order encodes
    the feature-checking order: head of list = first probe. -/
abbrev OrderedProbeStack : Type := List ProbeProfile

-- ============================================================================
-- § 2: Configuration
-- ============================================================================

/-- A Nested Agree configuration on a Minimalist `SyntacticObject`. -/
structure NestedAgreeConfig where
  /-- Ordered probes on the probing head. -/
  stack : OrderedProbeStack
  /-- The root tree under consideration. -/
  root : SyntacticObject
  /-- The head bearing the probes (e.g. Perf in Italian aux selection). -/
  probingHead : SyntacticObject
  /-- The shared goal head every probe targets under maximized matching
      (e.g. v in Italian aux selection). -/
  goalHead : SyntacticObject
  /-- Lexical primitive: which subtrees carry active φ-features.
      Defective v of unaccusatives gets `false`. Distinct from any
      derivational fact about whether Agree succeeded. -/
  phiActive : SyntacticObject → Bool

namespace NestedAgreeConfig

/-- Number of probes in the stack. -/
def length (c : NestedAgreeConfig) : Nat := c.stack.length

/-- Probe 0's c-command domain, filtered by phi-activity. Derived
    from `cCommandsIn` (Minimalist c-command on `SyntacticObject`). -/
def initialDomain (c : NestedAgreeConfig) : List SyntacticObject :=
  c.root.subtrees.filter (fun y =>
    decide (cCommandsIn c.root c.probingHead y) && c.phiActive y)

/-- The shared goal's daughters: the goal itself plus everything it
    c-commands, filtered by phi-activity. The reflexive inclusion of
    `goalHead` is required by maximized matching — every post-initial
    probe must be able to find the goal again. -/
def daughters (c : NestedAgreeConfig) : List SyntacticObject :=
  c.root.subtrees.filter (fun y =>
    (y == c.goalHead || decide (cCommandsIn c.root c.goalHead y)) &&
      c.phiActive y)

/-- Search domain at probe `i`: derived from the structural
    primitives. The matryoshka claim is encoded definitionally —
    `searchDomain (i+1) = daughters` for all `i ≥ 0`. -/
def searchDomain (c : NestedAgreeConfig) : Nat → List SyntacticObject
  | 0     => c.initialDomain
  | _ + 1 => c.daughters

end NestedAgreeConfig

-- ============================================================================
-- § 3: Well-formedness
-- ============================================================================

/-- A *bona fide* Nested Agree configuration: the shared goal lies in
    probe 0's c-command domain and is phi-active. Non-vacuous: derives
    a structural claim about `root` (via `cCommandsIn`) plus the
    lexical primitive (`phiActive`). When phi-Agree fails (unaccusative
    v has `phiActive = false`), this predicate is correctly false —
    the formal expression of @cite{amato-2025}'s "the chain breaks
    down at π-Agree." -/
def IsNestedAgreeConfig (c : NestedAgreeConfig) : Prop :=
  c.goalHead ∈ c.initialDomain

instance (c : NestedAgreeConfig) : Decidable (IsNestedAgreeConfig c) := by
  unfold IsNestedAgreeConfig; exact inferInstance

-- ============================================================================
-- § 4: Running the stack
-- ============================================================================

/-- Run probe `i` against its derived search domain. Returns the
    shared goal when visible at index `i`, else `none`. -/
def runStack (c : NestedAgreeConfig) (i : Nat) : Option SyntacticObject :=
  if i < c.length ∧ c.goalHead ∈ c.searchDomain i then
    some c.goalHead
  else
    none

theorem runStack_some_iff (c : NestedAgreeConfig) (i : Nat) :
    (runStack c i).isSome = true ↔
      i < c.length ∧ c.goalHead ∈ c.searchDomain i := by
  unfold runStack
  by_cases h : i < c.length ∧ c.goalHead ∈ c.searchDomain i
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]; exact iff_of_false (by simp) h

-- ============================================================================
-- § 5: Truncation
-- ============================================================================

/-- Post-initial search domains equal `daughters` by definition. -/
@[simp]
theorem searchDomain_succ (c : NestedAgreeConfig) (i : Nat) :
    c.searchDomain (i + 1) = c.daughters := rfl

/-- A well-formed configuration's goal lies in its own daughters
    (reflexive inclusion + phi-active). Used in the apparent-minimality
    theorem. -/
theorem goalHead_mem_daughters (c : NestedAgreeConfig)
    (h : IsNestedAgreeConfig c) :
    c.goalHead ∈ c.daughters := by
  unfold IsNestedAgreeConfig at h
  rw [NestedAgreeConfig.initialDomain, List.mem_filter] at h
  rw [NestedAgreeConfig.daughters, List.mem_filter]
  refine ⟨h.1, ?_⟩
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨?_, h.2.2⟩
  rw [Bool.or_eq_true]
  exact Or.inl (beq_self_eq_true _)

-- ============================================================================
-- § 6: Apparent vs actual minimality
-- ============================================================================

/-- A subtree visible to probe 0 but outside `daughters` is excluded
    from every post-initial probe's search domain. Strict-truncation
    content in the conclusion's `∈ ∧ ∉` shape. -/
theorem apparent_intervener_excluded
    (c : NestedAgreeConfig) (i : Nat) (δ : SyntacticObject)
    (hVisible : δ ∈ c.initialDomain)
    (hOut : δ ∉ c.daughters) :
    δ ∈ c.searchDomain 0 ∧ δ ∉ c.searchDomain (i + 1) :=
  ⟨hVisible, hOut⟩

/-- A subtree outside the goal's daughters cannot be returned by any
    post-initial probe — `runStack` only ever produces the (well-
    formedness-guaranteed) `goalHead`, which by `goalHead_mem_daughters`
    is *inside* its own daughters. -/
theorem apparent_minimality_not_actual
    (c : NestedAgreeConfig) (h : IsNestedAgreeConfig c)
    (i : Nat) (δ : SyntacticObject)
    (hOut : δ ∉ c.daughters) :
    runStack c (i + 1) ≠ some δ := by
  intro hEq
  unfold runStack at hEq
  split_ifs at hEq
  have hδEq : c.goalHead = δ := Option.some.inj hEq
  exact hOut (hδEq ▸ goalHead_mem_daughters c h)

-- ============================================================================
-- § 7: Worked Italian-style example
-- ============================================================================

/-! ### A 2-probe stack on a Perf+vP `SyntacticObject`

Tree: `Perf [DPsubj [v DPobj]]`. Probe 0 (Infl-Agree) targets v;
probe 1 (π-Agree) is restricted by Nested Agree to v's c-command
domain (reflexively including v). The apparent intervener DPsubj is
in Perf's c-command but not in v's, so it is structurally excluded
from probe 1 — encoding @cite{amato-2025}'s resolution of the
apparent minimality violation.

`phiActive` is `true` everywhere here (transitive case); the
unaccusative case (`phiActive (.leaf aV) = false`) is the one tested
in `Phenomena/AuxiliaryVerbs/Studies/Amato2025.lean`. -/

private def aT : LIToken := ⟨LexicalItem.simple .T [], 0⟩
private def aV : LIToken := ⟨LexicalItem.simple .V [], 1⟩
private def aDPsubj : LIToken := ⟨LexicalItem.simple .D [], 2⟩
private def aDPobj : LIToken := ⟨LexicalItem.simple .D [], 3⟩

/-- The structural tree for the worked example. -/
private def perfTree : SyntacticObject :=
  .node (.leaf aT)
    (.node (.leaf aDPsubj)
      (.node (.leaf aV) (.leaf aDPobj)))

/-- Both probes sit on Perf with horizon C. Identical `ProbeProfile`
    data; the list ordering is what distinguishes them. -/
private def perfProbe : ProbeProfile := ⟨.T, some .C⟩

def italianAuxExample : NestedAgreeConfig where
  stack := [perfProbe, perfProbe]
  root := perfTree
  probingHead := .leaf aT
  goalHead := .leaf aV
  phiActive := fun _ => true

theorem italianAuxExample_is_nested :
    IsNestedAgreeConfig italianAuxExample := by decide

theorem italianAuxExample_runStack_0 :
    runStack italianAuxExample 0 = some (.leaf aV) := by decide

theorem italianAuxExample_runStack_1 :
    runStack italianAuxExample 1 = some (.leaf aV) := by decide

/-- DPsubj is in probe 0's c-command (Perf c-commands DPsubj) but
    not in probe 1's truncated domain (v doesn't c-command DPsubj).
    Real strict-truncation content from the Minimalist c-command
    primitive. -/
theorem italianAuxExample_excludes_apparent_intervener :
    SyntacticObject.leaf aDPsubj ∈ italianAuxExample.searchDomain 0 ∧
    SyntacticObject.leaf aDPsubj ∉ italianAuxExample.searchDomain 1 :=
  apparent_intervener_excluded italianAuxExample 0 (.leaf aDPsubj)
    (by decide) (by decide)

end Minimalism.NestedAgree
