import Linglib.Theories.Semantics.Conditionals.Iatridou
import Linglib.Theories.Semantics.Reference.Kaplan
import Linglib.Theories.Semantics.Tense.ConditionalShift

/-!
# Anderson Conditionals: Crosslinguistic Marking Strategies
@cite{anderson-1951} @cite{mizuno-2024} @cite{schlenker-2004} @cite{condoravdi-2002} @cite{von-fintel-iatridou-2023}

## Anderson Conditionals

Anderson conditionals (@cite{anderson-1951}) are conditionals in which the
antecedent is an explanans for observed facts described in the consequent:

> "If Jones had taken arsenic, he would show exactly the symptoms
> he is *actually* showing. So, it looks like he did take arsenic."

The speaker believes the antecedent is true and uses the conditional to
argue from observed evidence to that conclusion. Despite using
counterfactual morphology (in English), Anderson conditionals are
epistemically indicative — the follow-up "So it looks like he did" is
felicitous.

## The Triviality Problem

The consequent of an Anderson conditional describes an observed fact — it
holds at every world in the live domain D. Under standard conditional
semantics (universal quantification over D), this makes the conditional
trivially true regardless of the antecedent. Both crosslinguistic
strategies avoid triviality by expanding the domain:

### X-marking (English)

Counterfactual morphology (fake past) expands the domain from D to D⁺ ⊃ D,
including worlds where the consequent may fail. The conditional becomes
non-trivial. "Actually" in the consequent recovers the actual world via
Kaplanian origin access, since X-marking shifts the evaluation world away.

### O-marking with Historical Present (Japanese)

Non-Past morphology in the consequent triggers a perspectival shift
analogous to the Historical Present. Following @cite{schlenker-2004}'s
bicontextual analysis, this shifts the Context of Utterance v backward in
time (to v' with TIME(v') < TIME(v)) while preserving the Context of
Thought θ at the utterance time. In the ContextTower, θ = `origin` and
v = `innermost` after the shift.

Under branching time (@cite{condoravdi-2002}), this backward shift expands
the domain: D_{w,t'} ⊃ D_{w,t} because more futures branch from earlier
times. The conditional becomes non-trivial without counterfactual morphology.
Temporal indexicals like *sakuya* 'last night' evaluate against θ (origin),
not v, paralleling HP in narrative contexts.

## FLV Correlation

@cite{mizuno-2024}: the availability of X-marking for Anderson conditionals
and for Future Less Vivid conditionals seem to stand or fall together
across languages (English has both; Japanese and Mandarin have neither).
This correlation is captured empirically in the study file, not derived
from the marking strategy type.

-/

namespace Semantics.Conditionals.Anderson

open Core.Context (KContext ContextTower ContextShift RichContext
  hpShift xMarkingShift DomainExpanding)
open Semantics.Conditionals.Iatridou (ExclF ExclDimension)
open Semantics.Reference.Kaplan (opActually_access opActually_shift_invariant)
open Semantics.Mood (subjShift)
open Semantics.Tense.ConditionalShift (domainRestrictedConditional
  trivialConsequent nonTrivialConsequent
  trivial_domainRestricted expansion_resolves_triviality
  nontrivial_conditional_excludes)

-- ════════════════════════════════════════════════════════════════
-- § Marking Strategy Typology
-- ════════════════════════════════════════════════════════════════

/-- The two crosslinguistic strategies for Anderson conditionals.

@cite{von-fintel-iatridou-2023} introduce the O-marking/X-marking
distinction as a general typological label for grammatical means of
distinguishing live from non-live possibilities.
@cite{mizuno-2024}: languages differ in whether they use X-marking
(counterfactual morphology) or O-marking (non-past) to express Anderson
conditionals. Both strategies achieve domain expansion — and thus avoid
triviality — via different mechanisms. -/
inductive MarkingStrategy where
  /-- X-marking: counterfactual morphology expands the domain from D to D⁺.
      "Actually" in the consequent recovers the actual world via Kaplanian
      origin access.
      English: "If Jones *had taken* arsenic, he *would have shown* exactly
      the symptoms he is *actually* showing." -/
  | xMarking
  /-- O-marking: Non-Past morphology triggers a perspectival shift analogous
      to the Historical Present (@cite{schlenker-2004}). The backward time
      shift expands the domain under branching time, avoiding triviality
      without counterfactual morphology. The actual world is directly
      accessible (no world shift, so no need for "actually").
      Japanese: "Jones-si-ga... nom-*eba*,... mise-*ru* (hazuda)." -/
  | oMarking
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § Strategy Properties
-- ════════════════════════════════════════════════════════════════

/-- X-marking strategy uses counterfactual morphology; O-marking does not.

    This is the single primitive property of marking strategies. All other
    properties (ExclF production, "actually" requirement) are derived from
    it — they are `abbrev`s equal to `hasXMarking`, with docstrings
    explaining *why* the correlation holds. -/
def MarkingStrategy.hasXMarking : MarkingStrategy → Bool
  | .xMarking => true
  | .oMarking => false

/-- X-marking produces ExclF; O-marking does not.

    X-marking is counterfactual morphology: `subjShift` changes the evaluation
    world, creating modal ExclF (origin.world ≠ innermost.world). O-marking
    leaves the tower at the root, so no ExclF arises.

    Definitionally equal to `hasXMarking` — the correlation holds because
    ExclF is the *mechanism* of X-marking. -/
abbrev MarkingStrategy.producesExclF (s : MarkingStrategy) : Bool := s.hasXMarking

/-- X-marking requires "actually" to recover the actual world; O-marking
    does not.

    When X-marking produces ExclF, the actual world is excluded from the
    shifted evaluation. "Actually" (Kaplanian origin access) is needed to
    reach back through the shift. With O-marking, the evaluation world IS
    the actual world, so no recovery operator is needed.

    Definitionally equal to `hasXMarking` — the "actually" requirement is
    a direct consequence of ExclF. -/
abbrev MarkingStrategy.requiresActuallyOperator (s : MarkingStrategy) : Bool := s.hasXMarking

-- ════════════════════════════════════════════════════════════════
-- § ExclDimension / Deal Bridge
-- ════════════════════════════════════════════════════════════════

/-- Map marking strategies to Iatridou's ExclDimension.

    X-marking produces modal ExclF (world exclusion); O-marking produces
    no ExclF — it expands the domain via HP backward time shift, not via
    counterfactual world shift. -/
def MarkingStrategy.exclDimension : MarkingStrategy → Option ExclDimension
  | .xMarking => some .modal
  | .oMarking => none

/-- Map marking strategies to Deal's PastMorphologyUse.

    X-marking corresponds to counterfactual tense (past morphology
    encoding modal remoteness, not temporal precedence).
    O-marking corresponds to temporal tense (Non-Past / HP). -/
def MarkingStrategy.toDealUse : MarkingStrategy → Semantics.Tense.CounterfactualTense.PastMorphologyUse
  | .xMarking => .counterfactual
  | .oMarking => .temporal

/-- X-marking maps to modal ExclDimension. -/
theorem xMarking_exclDimension :
    MarkingStrategy.xMarking.exclDimension = some .modal := rfl

/-- O-marking has no ExclDimension — no world shift occurs. -/
theorem oMarking_no_exclDimension :
    MarkingStrategy.oMarking.exclDimension = none := rfl

/-- X-marking is Deal's counterfactual use of past morphology:
    the past morpheme encodes modal remoteness, not temporal precedence.

    Connects to `ExclDimension.toDealUse` from Iatridou.lean:
    `ExclDimension.modal.toDealUse = .counterfactual`. -/
theorem xMarking_is_deal_counterfactual :
    MarkingStrategy.xMarking.toDealUse = .counterfactual := rfl

/-- O-marking is Deal's temporal use: Non-Past morphology performs its
    ordinary temporal function (Historical Present). -/
theorem oMarking_is_deal_temporal :
    MarkingStrategy.oMarking.toDealUse = .temporal := rfl

/-- Consistency: X-marking's ExclDimension maps to the same Deal use
    as X-marking's direct toDealUse. -/
theorem xMarking_excl_deal_consistent :
    (MarkingStrategy.xMarking.exclDimension.map ExclDimension.toDealUse) =
    some MarkingStrategy.xMarking.toDealUse := rfl

-- ════════════════════════════════════════════════════════════════
-- § Tower-Level Theorems
-- ════════════════════════════════════════════════════════════════

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- X-marking produces modal ExclF: subjunctive shift changes the world,
    creating world exclusion (origin.world ≠ innermost.world).

    This is why English Anderson conditionals use CF morphology:
    the X-marking shifts the evaluation world away from the actual world,
    setting up the need for "actually" to recover it.

    Wraps `Iatridou.subjShift_produces_modal_exclF`. -/
theorem xMarking_produces_exclF (c : KContext W E P T) (w' : W) (t' : T)
    (h : w' ≠ c.world) :
    ExclF .modal ((ContextTower.root c).push (subjShift w' t')) :=
  Iatridou.subjShift_produces_modal_exclF c w' t' h

/-- "Actually" recovers the origin world even after X-marking shift.

    In an Anderson conditional with X-marking, the CF morphology pushes
    the tower (shifting the evaluation world). But "actually" — being a
    Kaplanian indexical with `depth = .origin` — resolves to the speech-act
    world regardless. This is what makes Anderson conditionals felicitous
    despite the counterfactual morphology: "actually" reaches through the
    CF layer to access the actual world.

    Wraps `Kaplan.opActually_shift_invariant`. -/
theorem actually_recovers_origin_after_shift
    (t : ContextTower (KContext W E P T)) (σ : ContextShift (KContext W E P T)) :
    opActually_access.resolve (t.push σ) = opActually_access.resolve t :=
  opActually_shift_invariant t σ

/-- O-marking has no modal ExclF: without CF morphology, the tower stays
    at the root, and origin.world = innermost.world.

    This is why Japanese Anderson conditionals use O-marking: no world shift
    means the actual world is directly accessible without "actually".

    Wraps `Iatridou.root_no_modal_exclF`. -/
theorem oMarking_no_exclF (c : KContext W E P T) :
    ¬ ExclF .modal (ContextTower.root c) :=
  Iatridou.root_no_modal_exclF c

-- ════════════════════════════════════════════════════════════════
-- § Domain Expansion Bridge
-- ════════════════════════════════════════════════════════════════

/-- X-marking shift produces modal ExclF on RichContext towers.

The `xMarkingShift` (from Rich.lean) changes both world and time. When
the counterfactual world differs from the origin, the resulting tower
has modal ExclF. -/
theorem xMarking_produces_modal_exclF
    (rc : RichContext W E P T)
    (pastTime : T) (cfWorld : W) (expandedDomain : Set W)
    (h : cfWorld ≠ rc.base.world) :
    ((xMarkingShift (E := E) (P := P) pastTime cfWorld expandedDomain).apply rc
      ).base.world ≠ rc.base.world :=
  h

/-- Both strategies avoid triviality by expanding the domain. This theorem
    witnesses the general pattern: if a domain expansion produces a world
    where the consequent fails, the conditional is non-trivial.

    - X-marking achieves this via `xMarkingShift` (CF morphology → D⁺)
    - O-marking achieves this via `hpShift` (HP → backward time → D⁺)

    Wraps `ConditionalShift.expansion_resolves_triviality`. -/
theorem domain_expansion_avoids_triviality
    (smallDomain expandedDomain : Set W)
    (consequent : W → Prop)
    (h_subset : smallDomain ⊆ expandedDomain)
    (h_trivial : trivialConsequent smallDomain consequent)
    (w : W) (hw : w ∈ expandedDomain) (hw_fails : ¬ consequent w) :
    nonTrivialConsequent expandedDomain consequent :=
  expansion_resolves_triviality smallDomain expandedDomain consequent
    h_subset h_trivial w hw hw_fails

/-- End-to-end O-marking domain expansion: backwards-closed history +
    backward time shift → the HP-shifted domain contains the original.

    This connects the three layers:
    1. `BranchingTime.WorldHistory.backwardsClosed` (semantic property)
    2. `ConditionalShift.history_monotone_set` (set-level monotonicity)
    3. `hpShift` installs the expanded domain

    For any RichContext whose domain is contained in `history s₀`, the
    HP shift to an earlier time `t'` installs `history ⟨s₀.world, t'⟩`
    as the new domain, which is a superset of the original. -/
theorem oMarking_hpShift_expanding
    {W : Type*} {T : Type*} [Preorder T]
    (history : Semantics.Tense.BranchingTime.WorldHistory W T)
    (h_bc : history.backwardsClosed)
    (w₀ : W) (t₀ t' : T) (h_earlier : t' ≤ t₀)
    (D : Set W) (h_domain : D ⊆ history ⟨w₀, t₀⟩) :
    D ⊆ history ⟨w₀, t'⟩ :=
  Set.Subset.trans h_domain
    (Semantics.Tense.ConditionalShift.history_monotone_set
      history h_bc ⟨w₀, t₀⟩ t' h_earlier)

/-- The O-marking triviality problem: without domain expansion, the
    Anderson conditional is vacuously true. The `domainRestrictedConditional`
    over the non-expanded domain D is trivially satisfied because the
    consequent (an observed fact) holds at every world in D.

    This is why English O-marked Anderson conditionals (ex. 2 in
    @cite{mizuno-2024}) are infelicitous. -/
theorem oMarking_trivial
    (domain : Set W)
    (antecedent consequent : W → Prop)
    (h_trivial : trivialConsequent domain consequent) :
    domainRestrictedConditional domain antecedent consequent :=
  trivial_domainRestricted domain antecedent consequent h_trivial

/-- The X-marking / O-marking payoff: when domain expansion makes the
    consequent non-trivial, the antecedent of a true conditional must
    exclude at least one world in D⁺. The conditional is informative —
    the antecedent restriction partitions D⁺ into consequent-satisfying
    worlds (selected by the conditional) and consequent-failing worlds
    (excluded by the antecedent).

    This is why domain expansion resolves the triviality problem:
    the Anderson conditional "If Jones took arsenic, he would show these
    symptoms" is non-trivially true because the expanded domain includes
    worlds where Jones shows different symptoms, and the antecedent
    excludes those worlds. -/
theorem expanded_conditional_informative
    (expandedDomain : Set W)
    (antecedent consequent : W → Prop)
    (h_nontrivial : nonTrivialConsequent expandedDomain consequent)
    (h_cond : domainRestrictedConditional expandedDomain antecedent consequent) :
    ∃ w ∈ expandedDomain, ¬ antecedent w :=
  nontrivial_conditional_excludes expandedDomain antecedent consequent
    h_nontrivial h_cond

-- ════════════════════════════════════════════════════════════════
-- § Bicontextual Semantics (@cite{schlenker-2004})
-- ════════════════════════════════════════════════════════════════

/-!
### ContextTower as Bicontextual Semantics

@cite{schlenker-2004} distinguishes two evaluation contexts:

- **Context of Thought θ**: temporal coordinate identical to utterance time.
  Temporal indexicals (*seventy-eight years ago*, *sakuya* 'last night')
  evaluate against θ.
- **Context of Utterance v**: temporal coordinate can be shifted by HP.
  Tense morphology evaluates against v.

The `ContextTower` implements this distinction:

- `tower.origin` = θ (speech-act context, stable under shifts)
- `tower.innermost` = v (after HP or subjunctive shift)

In a root tower (no shifts), θ = v. An HP shift pushes the tower,
creating v' with TIME(v') < TIME(θ) while `origin` remains θ.
An X-marking shift pushes the tower, creating v' with
WORLD(v') ≠ WORLD(θ) — which is exactly modal ExclF.

This structural correspondence means the `origin_stable` theorem
(`AccessPattern.origin_stable`) directly captures Schlenker's claim
that indexicals anchored to θ are unaffected by HP or CF shifts.
-/

/-- In O-marking (HP) strategy, temporal indexicals still evaluate against
    the speech-act context (θ = origin), not the shifted context (v = innermost).

    This explains why Japanese *sakuya* 'last night' in the antecedent
    of (4a) evaluates against the utterance time, paralleling the behavior
    of *seventy-eight years ago* in Schlenker's HP example (5). -/
theorem oMarking_indexicals_at_origin
    (ap : Core.Context.AccessPattern (KContext W E P T) W)
    (hd : ap.depth = .origin)
    (t : ContextTower (KContext W E P T)) (σ : ContextShift (KContext W E P T)) :
    ap.resolve (t.push σ) = ap.resolve t :=
  Core.Context.AccessPattern.origin_stable ap hd t σ

end Semantics.Conditionals.Anderson
