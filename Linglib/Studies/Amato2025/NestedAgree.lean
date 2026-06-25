import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm
import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Nested Agree [amato-2025]

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
5. `validGoal : SyntacticObject → Bool` — *lexical* primitive: which
   subtrees carry active φ-features. Defective v of unaccusatives
   gets `false`; this is what blocks π-Agree in [amato-2025]'s
   §3.4.2 unaccusative analysis.

`initialDomain`, `daughters`, `searchDomain` are *derived* via
`cCommandsIn` and reflexive containment, filtered by `validGoal`. The
matryoshka claim — post-initial domains restricted to the goal's
daughters — is structural, not axiomatic. Consequently
`IsNestedAgreeConfig` is non-vacuous: it requires `goalHead` to be
both c-commanded by `probingHead` in `root` *and* phi-active.

## Cross-domain applications

Italian aux selection (§3) is formalized at
`Studies/Amato2025.lean`. Other Amato 2025 §4
case studies (Icelandic DAT-NOM, Lak perfective, Spanish VOS,
Bulgarian wh, ditransitives) are deferred — their consumers will
construct `SyntacticObject` trees and `validGoal` predicates the
same way.

## Architecture

Sits at Layer 2 (compositional Agree pattern), built on the Layer-1
substrate (`SyntacticObject`, `cCommandsIn`, `containsOrEq`,
`subtrees`) imported transitively via `Probe`. Predicates are `Prop`
with `[Decidable]` instances; `runStack` returns
`Option SyntacticObject`.

## Sibling mechanisms in `Syntax/Minimalism/`

`Syntax/Minimalism/CyclicAgree.lean` ([bejar-rezac-2009])
and Long-Distance Agree ([szabolcsi-2009], `Studies/Allotey2021.lean`)
are sibling Layer-2 patterns. All three address "what does a probe do
beyond its first operation," but the answers differ:

- **Nested Agree** (this file): *multiple ordered probes* on a single
  head, all forced to target the *same* goal under maximized matching;
  each subsequent probe operates on a *truncated* search domain
  restricted to the prior goal's daughters.
- **Cyclic Agree** (`CyclicAgree.lean`): a *single articulated probe*
  with multiple feature segments; cycle I targets the IA, cycle II
  targets the EA via the *expanded* residue domain. Subsequent
  cycles see *more* (residue + EA), not less.
- **Long-Distance Agree** (`Studies/Allotey2021.lean`): a *single probe*
  in the matrix relaxes locality across a non-defective C, reaching
  an embedded goal.

The three are conceptually orthogonal mechanisms for serial probing.
A unified theory of probe behavior would treat them as alternatives
in the design space; we keep them as independent Layer-2 patterns
that consumers select by phenomenon.
-/

namespace Amato2025.NestedAgree

open Minimalist

-- ============================================================================
-- § 1: Probe stack
-- ============================================================================

/-- An ordered list of probes on a single head. The list order encodes
    the feature-checking order: head of list = first probe. -/
abbrev OrderedProbeStack : Type := List Probe.Profile

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
  validGoal : SyntacticObject → Bool

namespace NestedAgreeConfig

/-- Number of probes in the stack. -/
def length (c : NestedAgreeConfig) : Nat := c.stack.length

/-- Probe 0's c-command domain, filtered by phi-activity. Derived
    from `cCommandsIn` (Minimalist c-command on `SyntacticObject`).

    `subtrees` returns `Multiset` (post-Phase-1.0; MCB-faithful per
    Def 1.2.2), so the filtered domain is also `Multiset`. Membership
    checks (`goalHead ∈ initialDomain`) work identically to the prior
    `List` flavor. -/
def initialDomain (c : NestedAgreeConfig) : Multiset SyntacticObject :=
  c.root.subtrees.filter (fun y =>
    decide (SO.cCommandsIn c.root c.probingHead y) && c.validGoal y)

/-- The shared goal's daughters: the goal itself plus everything it
    c-commands, filtered by phi-activity. The reflexive inclusion of
    `goalHead` is required by maximized matching — every post-initial
    probe must be able to find the goal again. -/
def daughters (c : NestedAgreeConfig) : Multiset SyntacticObject :=
  c.root.subtrees.filter (fun y =>
    (y == c.goalHead || decide (SO.cCommandsIn c.root c.goalHead y)) &&
      c.validGoal y)

/-- Search domain at probe `i`: derived from the structural
    primitives. The matryoshka claim is encoded definitionally —
    `searchDomain (i+1) = daughters` for all `i ≥ 0`. -/
def searchDomain (c : NestedAgreeConfig) : Nat → Multiset SyntacticObject
  | 0     => c.initialDomain
  | _ + 1 => c.daughters

end NestedAgreeConfig

-- ============================================================================
-- § 3: Well-formedness
-- ============================================================================

/-- A *bona fide* Nested Agree configuration: the shared goal lies in
    probe 0's c-command domain and is phi-active. Non-vacuous: derives
    a structural claim about `root` (via `cCommandsIn`) plus the
    lexical primitive (`validGoal`). When phi-Agree fails (unaccusative
    v has `validGoal = false`), this predicate is correctly false —
    the formal expression of [amato-2025]'s "the chain breaks
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
-- § 4b: Grounding in `Probe.search`
-- ============================================================================

/-- The goal-seeking probe: visible exactly at the shared goal. Nested
    Agree's locality lives in `searchDomain`; the probe itself just seeks
    the goal. -/
def NestedAgreeConfig.goalProbe (c : NestedAgreeConfig) : Probe SyntacticObject :=
  Probe.ofVis (fun y => decide (y = c.goalHead))

private theorem find?_decideEq (L : List SyntacticObject) (g : SyntacticObject) :
    L.find? (fun y => decide (y = g)) = if g ∈ L then some g else none := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x = g
    · subst hx; rw [List.find?_cons_of_pos (by simp)]; simp
    · rw [List.find?_cons_of_neg (by simp [hx]), ih]
      have hgx : ¬ g = x := fun h => hx h.symm
      simp [List.mem_cons, hgx]

/-- `runStack` factors through the canonical `Probe.search`: running
    probe `i` is the goal-seeking probe searching probe `i`'s derived
    domain (when probe `i` exists). The bespoke membership test *is*
    `Probe.search` over `searchDomain i`, bringing Nested Agree onto the
    one probe engine (cf. `CyclicAgree.eaIsLicensed_iff_segment_licensed`).
    The whole-stack composition is `findSome?`/`Probe.cascade` over the
    indices; the per-probe truncated domains are why each step is a
    `search` over its own `searchDomain`, not a `cascade` over one list. -/
theorem runStack_eq_search (c : NestedAgreeConfig) (i : Nat) :
    runStack c i =
      if i < c.length then c.goalProbe.search (c.searchDomain i).toList
      else none := by
  have hsearch : c.goalProbe.search (c.searchDomain i).toList
      = if c.goalHead ∈ c.searchDomain i then some c.goalHead else none := by
    simp only [NestedAgreeConfig.goalProbe, Probe.search, Probe.ofVis]
    rw [find?_decideEq]
    simp only [Multiset.mem_toList]
  rw [runStack]
  by_cases hi : i < c.length
  · rw [if_pos hi, hsearch]
    by_cases hg : c.goalHead ∈ c.searchDomain i
    · rw [if_pos ⟨hi, hg⟩, if_pos hg]
    · rw [if_neg (fun h => hg h.2), if_neg hg]
  · rw [if_neg hi, if_neg (fun h => hi h.1)]

/-- The Nested-Agree licensing fact in the licensing API: probe `i`
    licenses the shared goal iff the goal is in probe `i`'s domain. -/
theorem goalProbe_licensed_iff (c : NestedAgreeConfig) (i : Nat) :
    c.goalProbe.Licensed (c.searchDomain i).toList c.goalHead ↔
      c.goalHead ∈ c.searchDomain i := by
  unfold Probe.Licensed
  simp only [NestedAgreeConfig.goalProbe, Probe.search, Probe.ofVis]
  rw [find?_decideEq]
  simp only [Multiset.mem_toList]
  by_cases hg : c.goalHead ∈ c.searchDomain i <;> simp [hg]

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
  rw [NestedAgreeConfig.initialDomain, Multiset.mem_filter] at h
  rw [NestedAgreeConfig.daughters, Multiset.mem_filter]
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
-- § 7: Consumer builder API
-- ============================================================================

/-! ### Standard linear-Spec configuration builder

The four landed Amato 2025 case studies (Italian aux, Icelandic
DAT-NOM, Lak perfective, Bulgarian wh) all share a structural
template: a 4-leaf binary tree `[probe-head [intervener [mid goal]]]`
with a 2-probe stack on the head. The builder below extracts this
template so consumers don't repeat it.

Consumers vary in:
- LIToken category labels (T / C / Asp; DPsubj / DPdat / Erg / WhSbj;
  V; DPobj / DPnom / Abs / WhObj)
- Which leaf is the chosen goal (typically `midNode` in Italian/Lak,
  `terminal` in Icelandic/Bulgarian)
- The `validGoal` predicate

The common shape — a single Probe.Profile used twice, a 4-leaf linear
tree, the 2-probe stack — is captured by `standardConfig`. -/

/-- Standard 4-leaf linear-Spec tree:
    `[probeHd [intervener [midNode terminal]]]`.
    Shared template across the landed Amato 2025 case studies. -/
def standardLinearTree (probeHd intervener midNode terminal : LIToken) :
    SyntacticObject :=
  SO.ofPlanar (SO.nodeP (SO.leafP probeHd)
    (SO.nodeP (SO.leafP intervener)
      (SO.nodeP (SO.leafP midNode) (SO.leafP terminal))))

/-- A `NestedAgreeConfig` over the standard linear tree, with a
    2-probe stack on `probeHd`. The `goalHd` selects which leaf
    serves as the shared goal under maximized matching. -/
def standardConfig (probeProfile : Probe.Profile)
    (probeHd intervener midNode terminal : LIToken)
    (goalHd : LIToken) (vg : SyntacticObject → Bool) :
    NestedAgreeConfig where
  stack := [probeProfile, probeProfile]
  root := standardLinearTree probeHd intervener midNode terminal
  probingHead := SO.lexLeaf probeHd
  goalHead := SO.lexLeaf goalHd
  validGoal := vg

-- ============================================================================
-- § 8: Worked Italian-style example
-- ============================================================================

/-! ### A 2-probe stack on a Perf+vP `SyntacticObject`

Tree: `Perf [DPsubj [v DPobj]]`. Probe 0 (Infl-Agree) targets v;
probe 1 (π-Agree) is restricted by Nested Agree to v's c-command
domain (reflexively including v). The apparent intervener DPsubj is
in Perf's c-command but not in v's, so it is structurally excluded
from probe 1 — encoding [amato-2025]'s resolution of the
apparent minimality violation.

`validGoal` is `true` everywhere here (transitive case); the
unaccusative case (`validGoal (SO.lexLeaf aV) = false`) is the one tested
in `Studies/Amato2025.lean`. -/

private def aT : LIToken := ⟨LexicalItem.simple .T [], 0⟩
private def aV : LIToken := ⟨LexicalItem.simple .V [], 1⟩
private def aDPsubj : LIToken := ⟨LexicalItem.simple .D [], 2⟩
private def aDPobj : LIToken := ⟨LexicalItem.simple .D [], 3⟩

private def perfProbe : Probe.Profile := ⟨.T, some .C⟩

/-- Italian-style 2-probe configuration constructed via `standardConfig`. -/
def italianAuxExample : NestedAgreeConfig :=
  standardConfig perfProbe aT aDPsubj aV aDPobj aV (fun _ => true)

theorem italianAuxExample_is_nested :
    IsNestedAgreeConfig italianAuxExample := by decide

theorem italianAuxExample_runStack_0 :
    runStack italianAuxExample 0 = some (SO.lexLeaf aV) := by decide

theorem italianAuxExample_runStack_1 :
    runStack italianAuxExample 1 = some (SO.lexLeaf aV) := by decide

/-- DPsubj is in probe 0's c-command (Perf c-commands DPsubj) but
    not in probe 1's truncated domain (v doesn't c-command DPsubj).
    Real strict-truncation content from the Minimalist c-command
    primitive. -/
theorem italianAuxExample_excludes_apparent_intervener :
    SO.lexLeaf aDPsubj ∈ italianAuxExample.searchDomain 0 ∧
    SO.lexLeaf aDPsubj ∉ italianAuxExample.searchDomain 1 :=
  apparent_intervener_excluded italianAuxExample 0 (SO.lexLeaf aDPsubj)
    (by decide) (by decide)

end Amato2025.NestedAgree
