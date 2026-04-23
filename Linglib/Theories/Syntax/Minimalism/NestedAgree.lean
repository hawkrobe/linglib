import Linglib.Theories.Syntax.Minimalism.Probe
import Linglib.Theories.Syntax.Minimalism.Agree
import Linglib.Theories.Syntax.Minimalism.Features

/-!
# Nested Agree @cite{amato-2025}

A general syntactic configuration: a single head bears two (or more)
*ordered* probes, and the second probe is required to target the same
goal as the first. The downstream consequence is that prior Agree
operations *truncate* the search domain available to later ones —
because the first probe's choice of goal restricts where the second
probe is allowed to look.

The puzzle Nested Agree solves is *apparent minimality violations*: a
configuration where the lower of two candidate goals controls Agree,
even though minimality would normally pick the higher one. Under
Nested Agree the higher candidate is excluded from the second probe's
search domain *by construction* (because it lay outside the first
probe's chosen-goal subtree). Minimality is satisfied; the violation is
only apparent.

## Configuration

A `NestedAgreeConfig` packages four ingredients:

1. `stack : List ProbeProfile` — ordered probes; head of list is checked
   first. (No bundled wrapper — *thin* wrapper structures around `List`
   are anti-pattern unless they carry a load-bearing invariant.)
2. `goalLabel : Token` — the goal every probe targets (under MME).
3. `daughters : Token → List Token` — abstract subtree-of relation.
   Reflexive on reachable goals (`goalLabel ∈ daughters goalLabel` for
   well-formed configurations).
4. `initialDomain : List Token` — probe 0's c-command domain.

The matryoshka structure (`searchDomain (i+1) ⊆ daughters goalLabel`) is
encoded **definitionally**: `searchDomain` is a derived function rather
than a stipulated field, so post-initial truncation holds by `rfl`.

## Cross-domain applications (advertised, not all formalized here)

Amato 2025 (NLLT) advances Nested Agree as a unifying account across at
least six phenomena:

- Italian auxiliary selection (§3) — formalized at
  `Phenomena/AuxiliaryVerbs/Studies/Amato2025.lean`.
- Case + agreement alignments in ditransitives (§4.1.1).
- Dative intervention in Icelandic biclausal sentences (§4.1.2).
- Person agreement in Lak perfective (§4.2.1).
- Subject φ-agreement in Spanish VOS (§4.2.2).
- Multiple wh-fronting in Bulgarian via Merge features (§4.2.3).

Two domains the paper *excludes*: anti-local agreement in Hindi-Urdu
(§4.3.1) and Italian past participle agreement (§4.3.2; Edge Features,
not Nested Agree). Cross-domain applications may refine `Token` with
richer structure (case features, Merge features) — kept minimal here.

## Architecture

Imports `Probe`, `Agree`, `Features` only. No `Phase` — phase-bounding
is a consumer concern. Predicates are `Prop` with `[Decidable]` instances
(mathlib style); `runStack` returns `Option Token` (data, not Bool).
-/

namespace Minimalism.NestedAgree

-- ============================================================================
-- § 1: Tokens and probe stacks
-- ============================================================================

/-- Tokens are abstract goal identifiers. We use `Nat` for decidable
    equality, finite enumerations, and trivial `Repr`; the Italian aux
    slot does not need richer structure. Cross-domain applications
    (Bulgarian wh, Icelandic dative) may refine this — see the module
    docstring. -/
abbrev Token : Type := Nat

/-- An ordered stack of probes on a single head. The list order encodes
    the feature-checking order: head of list is the first probe.

    No bundled wrapper around `List`: `feedback_no_thin_bundled_struct`
    rules. If nonemptiness or other invariants become load-bearing,
    introduce `List.Nonempty` then. -/
abbrev OrderedProbeStack : Type := List ProbeProfile

-- ============================================================================
-- § 2: Nested Agree configuration
-- ============================================================================

/-- A Nested Agree configuration on a single head — *pure data*.

    - `stack`: the ordered probes that share this head.
    - `goalLabel`: the goal token all probes must target (under MME).
    - `daughters t`: abstract subtree-of relation. Reflexive on the
      shared goal (`goalLabel ∈ daughters goalLabel` for well-formed
      configurations). Designed to come from a structural primitive in
      the consumer (a tree, or a φ-feature-presence predicate as in
      @cite{amato-2025}'s defective-v cases) — *not* from the answer
      we're trying to prove.
    - `initialDomain`: probe 0's c-command domain.

    The matryoshka structure is captured *definitionally* by the
    derived `searchDomain` function below: `searchDomain (i+1) =
    daughters goalLabel` by `rfl`. No separate coherence axiom needed. -/
structure NestedAgreeConfig where
  stack : OrderedProbeStack
  goalLabel : Token
  daughters : Token → List Token
  initialDomain : List Token

namespace NestedAgreeConfig

/-- Number of probes in this configuration. -/
def length (c : NestedAgreeConfig) : Nat := c.stack.length

/-- Search domain at probe index `i`. **Derived**, not stipulated:

    - `i = 0`: `initialDomain` (probe 0's full c-command).
    - `i ≥ 1`: `daughters goalLabel` (under MME, every post-initial
      probe targets the same goal, so the matryoshka collapses to
      "daughters of the shared goal" after the initial step).

    The matryoshka claim — post-initial domains are restricted to the
    daughters of the shared goal — is now true *by definition* of this
    function, not by a coherence axiom on a stipulated field. -/
def searchDomain (c : NestedAgreeConfig) : Nat → List Token
  | 0     => c.initialDomain
  | _ + 1 => c.daughters c.goalLabel

end NestedAgreeConfig

-- ============================================================================
-- § 3: Well-formedness predicate
-- ============================================================================

/-- A *bona fide* Nested Agree configuration. Two conjuncts:

    - **(A) Initial visibility.** The shared goal lies in probe 0's
      c-command domain.
    - **(B) Goal reflexivity.** The shared goal lies in its own
      daughters — equivalently, `goalLabel ∈ searchDomain (i+1)` for
      every post-initial probe (since `searchDomain (i+1) = daughters
      goalLabel`). When (B) fails, the configuration represents a
      *failed-Agree* derivation at the second probe — exactly what
      @cite{amato-2025}'s unaccusative analysis means by "the chain
      breaks down at π-Agree." -/
def IsNestedAgreeConfig (c : NestedAgreeConfig) : Prop :=
  c.goalLabel ∈ c.initialDomain ∧
  c.goalLabel ∈ c.daughters c.goalLabel

instance (c : NestedAgreeConfig) : Decidable (IsNestedAgreeConfig c) := by
  unfold IsNestedAgreeConfig; exact inferInstance

-- ============================================================================
-- § 4: Running the stack
-- ============================================================================

/-- Run probe `i` against its search domain and return its hit, if any.
    The hit is the *first* token in `searchDomain i` matching `goalLabel`
    — by maximized matching, that's `goalLabel` itself, but the function
    is total in `i` (returns `none` when the probe index is out of range
    or the goal is absent from the search domain).

    Returning `Option Token` rather than `Bool` keeps this a *data*
    function (the value of the hit), separate from the proposition that
    the hit succeeded. -/
def runStack (c : NestedAgreeConfig) (i : Nat) : Option Token :=
  if i < c.length ∧ c.goalLabel ∈ c.searchDomain i then
    some c.goalLabel
  else
    none

theorem runStack_some_iff (c : NestedAgreeConfig) (i : Nat) :
    (runStack c i).isSome = true ↔
      i < c.length ∧ c.goalLabel ∈ c.searchDomain i := by
  unfold runStack
  by_cases h : i < c.length ∧ c.goalLabel ∈ c.searchDomain i
  · rw [if_pos h]; exact iff_of_true rfl h
  · rw [if_neg h]; exact iff_of_false (by simp) h

-- (Removed: `MaximizedMatching` and `nested_implies_mme`.
--  The previous stub had the trivial direction — `runStack` returns
--  `goalLabel` by definition, so `nested_implies_mme` was rfl-trivial
--  per the CLAUDE.md anti-pattern. The genuine MME ⇏ NestedAgree
--  counterexample direction requires structural reading of feature
--  ordering beyond what this file exposes; deferred to a follow-up
--  with `OrderedProbes.lean` or the Amato §Appendix construction.)

-- ============================================================================
-- § 5: Truncation — by definition
-- ============================================================================

/-- **The matryoshka, by `rfl`.** Post-initial search domains *equal*
    the daughters of the shared goal — by the definition of
    `searchDomain`, not by an axiom on a stipulated field. Truncation
    is encoded in the abstraction itself. -/
theorem searchDomain_succ_eq_daughters (c : NestedAgreeConfig) (i : Nat) :
    c.searchDomain (i + 1) = c.daughters c.goalLabel := rfl

-- ============================================================================
-- § 6: Apparent vs. actual minimality
-- ============================================================================

/-- **Apparent intervener excluded — strict-truncation form.** A token
    `δ` visible to probe 0 but outside the daughters of the shared goal
    belongs to `searchDomain 0` and is *not* in any post-initial
    `searchDomain`. The strict-truncation claim is encoded in the
    conclusion's `∈ ∧ ∉` shape: probe 0 sees `δ`, post-initial probes
    do not. Both hypotheses are load-bearing — `hVisible` carries the
    "was-in-initial-domain" content, `hAbove` carries the "excluded by
    daughters-restriction" content.

    This is @cite{amato-2025}'s mechanism for resolving an apparent
    minimality violation: the structurally-higher candidate `δ` (e.g.,
    the EA in an unaccusative configuration) is in Perf's c-command
    domain (probe 0) but excluded from π-Agree's truncated domain
    (probe 1). -/
theorem apparent_intervener_excluded
    (c : NestedAgreeConfig) (i : Nat) (δ : Token)
    (hVisible : δ ∈ c.searchDomain 0)
    (hAbove : δ ∉ c.daughters c.goalLabel) :
    δ ∈ c.searchDomain 0 ∧ δ ∉ c.searchDomain (i + 1) := by
  refine ⟨hVisible, ?_⟩
  rw [searchDomain_succ_eq_daughters]
  exact hAbove

/-- **Apparent minimality is not actual minimality.** A token outside
    the daughters of the shared goal cannot be returned by any
    post-initial probe — `runStack` only produces the (well-formedness-
    guaranteed) `goalLabel`, which by hypothesis is *inside* its own
    daughters. -/
theorem apparent_minimality_not_actual
    (c : NestedAgreeConfig) (h : IsNestedAgreeConfig c)
    (i : Nat) (δ : Token)
    (hAbove : δ ∉ c.daughters c.goalLabel) :
    runStack c (i + 1) ≠ some δ := by
  intro hEq
  unfold runStack at hEq
  split_ifs at hEq
  have hδEq : c.goalLabel = δ := Option.some.inj hEq
  exact hAbove (hδEq ▸ h.2)

-- ============================================================================
-- § 7: Worked abstract Italian-style example
-- ============================================================================

/-! ### A 2-probe stack on a 3-token domain

The Italian Perf head bears `[*Infl:perf*] ≻ [*π:_*]`: Infl-Agree first,
then π-Agree. Token alphabet `{0, 1, 2}`: 0 = DPsubj, 1 = v (the shared
goal under MME), 2 = DPobj. Probe 0's c-command is the full set
`[0, 1, 2]`; `daughters 1 = [1, 2]` is v's subtree, excluding the
apparent intervener 0.

`searchDomain` is now derived: `searchDomain 0 = initialDomain = [0,1,2]`;
`searchDomain (i+1) = daughters 1 = [1, 2]` by `rfl`. -/

/-- Both probes of the example sit on Perf with horizon C. They are the
    *same* probe-profile data; the ordering on the stack is what
    distinguishes them — there is no per-probe distinguishing data in
    `ProbeProfile`. -/
private def perfProbe : ProbeProfile := ⟨.T, some .C⟩

/-- Italian-style 2-probe configuration. -/
def italianAuxExample : NestedAgreeConfig where
  stack := [perfProbe, perfProbe]
  goalLabel := 1
  daughters
    | 1 => [1, 2]
    | _ => []
  initialDomain := [0, 1, 2]

theorem italianAuxExample_is_nested :
    IsNestedAgreeConfig italianAuxExample := by decide

theorem italianAuxExample_runStack_0 :
    runStack italianAuxExample 0 = some 1 := by decide

theorem italianAuxExample_runStack_1 :
    runStack italianAuxExample 1 = some 1 := by decide

/-- The apparent intervener `0` (the EA) is visible to probe 0 but
    excluded from probe 1's truncated domain — encoding @cite{amato-2025}'s
    resolution of the apparent minimality violation in Italian unaccusative
    auxiliary selection. Strict-truncation content: probe 0 sees `0`,
    probe 1 does not. -/
theorem italianAuxExample_excludes_apparent_intervener :
    (0 : Token) ∈ italianAuxExample.searchDomain 0 ∧
    (0 : Token) ∉ italianAuxExample.searchDomain 1 :=
  apparent_intervener_excluded italianAuxExample 0 0 (by decide) (by decide)

end Minimalism.NestedAgree
