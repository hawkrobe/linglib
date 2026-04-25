import Linglib.Theories.Discourse.DiscourseRef

/-!
# Dynamic Context — Effect-Functor-Parameterized Interface

@cite{groenendijk-stokhof-1991} @cite{muskens-1996} @cite{heim-1982}
@cite{charlow-2019} @cite{hofmann-2025} @cite{grove-white-2025b}

A typeclass interface for dynamic-semantics contexts, parameterized on
the **effect functor `M`** that wraps each variable's value at a world.
The unifying frame across deterministic, nondeterministic, and
probabilistic dynamic semantics — at the **fibered-lookup signature**.

## Mathlib-style discipline

Where structure is shared, expose it via a typeclass. `HasFiberedLookup`
gives every family the same `iLookup : Ctx → V → W → M E` interface, so
cross-family predicates are by-construction comparable. `HasIndivDrefs`
extends it, adding the Hofmann-specific `iVarUp` update relation.
`HasJointState` extends it the *other* direction, marking frameworks
whose underlying state is natively joint over (world, assignment) pairs
— a strictly richer commitment than the fibered signature exposes.

Bridge maps between families are explicit named natural transformations
of `M`, following the mathlib pattern (`Function`/`Set.Image`/
`MeasurableFunction`/`PMF`/`Measure` as a family of related-but-not-
unified abstractions).

## Honest scope: the lookup is *fibered*

The lookup signature `Ctx → V → W → M E` is fibered by construction —
every state, joint or not, can answer "what is the `M`-distribution of
`v`'s value at world `w`?". For Charlow's joint `Set (W × Assignment E)`,
this requires marginalizing out the world-assignment correlation; for
ICDRT it's a direct lookup; for fibered-Bayesian (`W → PMF (Assignment E)`)
it's projection. The renamed class `HasFiberedLookup` (was
`HasIndivLookupM`) makes this explicit — what is unified is the
*fibered projection*, not the underlying state shape.

## Six 2026 seams

What this interface *does not* paper over: six places where dynamic
theories deliberately diverge in 2026. Each is named, locatable
(`grep "## SEAM"`), and committed at the per-family file level —
visible structure, not hidden disagreement.

### Seam 1 — Falsifier convention

What does "no referent for `v` at `w`" mean?

| Family | Falsifier | Source |
|---|---|---|
| ICDRT | `Entity.star` (bivalent distinguished value) | @cite{hofmann-2025} |
| Charlow | `∅` (empty alternative-set; no value-level falsifier) | @cite{charlow-2019} |
| Bayesian | zero-mass (PMF assigns probability 0; no value-level falsifier) | @cite{grove-white-2025b} |
| FCS | `Dom`-partiality (FCP undefined; no value-level falsifier at all) | @cite{heim-1982} |

Charlow's argument: bivalence undermines compositional negation.
Hofmann's argument: alternative-sets underdetermine anaphora projection.
Heim's argument: partiality models presupposition-as-definedness directly.
The seam stays open.

### Seam 2 — State shape (joint vs fibered)

Does the underlying state remember world–assignment correlation?

| Family | State shape | Class |
|---|---|---|
| ICDRT | fibered (`indiv : IVar → W → Entity E`) | `HasFiberedLookup` only |
| Charlow | joint (`Set (W × Assignment E)`) | `HasFiberedLookup` + `HasJointState` |
| Bayesian (PDS) | joint (`PMF (W × Assignment E)`, per @cite{grove-white-2025b}) | `HasFiberedLookup` + `HasJointState` |
| Bayesian (fibered) | fibered (`W → PMF (Assignment E)`) | `HasFiberedLookup` only |
| FCS | joint (`Sat ⊆ World × Assignment`) | `HasFiberedLookup` + `HasJointState` |

The lookup *signature* is fibered for every family — this is what
`HasFiberedLookup` unifies. The *underlying state* may carry strictly
more structure: `HasJointState` marks frameworks where it does. The
fibered projection of a joint state is **lossy** — world-assignment
correlations beyond what a single `(v, w)` query probes are discarded.

### Seam 3 — Update mechanism

What does "extend the discourse" mean operationally?

| Family | Update primitive |
|---|---|
| ICDRT | assignment update (`updateIndiv g v e`) |
| Charlow | alternative filtering / set-builder |
| Bayesian | conditioning (Bayes update / `PMF.bind`) |
| FCS | partial functional update (definedness-tracking) |

These genuinely don't unify — Charlow's bind is non-commutative (his
"scope of alternatives" thesis); PMF's bind is commutative under
independence; Hofmann's update is sequential; Heim's is partial. The
interface deliberately omits a master `Update` typeclass.

### Seam 4 — Definedness predicate

"`v` has a definite referent at `w` in `i`."

| Family | Predicate shape |
|---|---|
| ICDRT | `iLookup i v w ≠ Entity.star` |
| Charlow | `iLookup i v w` is a singleton set |
| Bayesian | `iLookup i v w` is a Dirac/point-mass |
| FCS | `v ∈ Dom(F)` (definedness is metadata, not value-level) |

All four express "the M-fiber is determinate." Mathlib has
`Set.Subsingleton` and `PMF.IsDeterministic` for the second/third;
FCS's `Dom`-tracking is structurally distinct (it's a property of the
*state*, not the *fiber*). We ship parallel-named predicates
(`isDeterminateAt` per family) without yet abstracting; the seam stays
visible until a study needs to quantify over it.

### Seam 5 — Effect commutativity

Does the order in which effects are introduced matter?

| Family | Commutativity |
|---|---|
| ICDRT | trivially yes (sequential update) |
| Charlow | NO — "scope of alternatives" thesis |
| Bayesian | yes under independence; no in general |

Not visible in lookup; surfaces in *composition* (multiple lookups
combining). Out of scope for this interface; lives in each family's
own composition operators.

### Seam 6 — Anaphora resolution mechanism

Where does pronoun resolution come from?

| Family | Mechanism |
|---|---|
| Heim/Kamp | dref binding via assignment update |
| E-type / situation | NP reconstruction (Elbourne, Heim 1990) |
| Charlow | alternatives in the continuation |
| Hofmann (ICDRT) | propositional drefs as local contexts |
| Bayesian | posterior conditioning on observed reference |

The deepest seam — not in the lookup signature, but in how lookups get
used by `Phenomena/.../Studies/`. Each Studies file commits in its own
resolution semantics. (Karttunen 1976 introduced *the idea* of drefs
without the assignment-update formalization, so the binding row is
attributed to Heim/Kamp.)

## Key Types

| Class | Carries |
|---|---|
| `HasFiberedLookup M Ctx V W E` | Fibered lookup signature `Ctx → V → W → M E` |
| `HasJointState M Ctx V W E` | Extends `HasFiberedLookup`; native joint state `Ctx → M (W × (V → E))` |
| `HasIndivDrefs Ctx V W E` | Extends `HasFiberedLookup Entity` + Hofmann `iVarUp` law |
| `HasPropDrefs Ctx P W` | Propositional drefs `P` to sets of worlds |
| `HasDiscourseCommitment Ctx P` | Distinguished commitment-set var (single speaker) |
| `HasMultiDC Ctx P Speaker` | Per-speaker commitment-set vars (dialogue) |
-/

namespace Semantics.Dynamic.Context

open Semantics.Dynamic.Core

universe u v w x w₁ w₂

-- ════════════════════════════════════════════════════════════════
-- § 1. Fibered effect-functor lookup — the shared scaffolding
-- ════════════════════════════════════════════════════════════════

/-- **Fibered effect-functor lookup** — the unifying frame across
deterministic, nondeterministic, and probabilistic dynamic semantics.

`iLookup i v w : M E` returns a *family* of values structured by an
effect functor `M` at a particular world:

- `M = Entity` (deterministic; ICDRT)
- `M = Set` (nondeterministic; Charlow's marginal at world `w`)
- `M = PMF` (probabilistic; Bayesian per-world fiber)
- `M = Id` (extensional baselines: DPL, CDRT, DRT — `W = PUnit`)

`M` is `outParam`: each `Ctx` carries exactly one effect functor.
`Functor M` is enough — no `Monad M` requirement, since `Set` lacks a
clean `Monad` instance in Lean. Bridge maps between families are
**explicit named natural transformations** of `M`, not monad lifts.

## SEAM (Seam 2): The signature is *fibered* by construction. Joint-state
families (Charlow, FCS, PDS Bayesian) provide an `iLookup` by
marginalizing their joint state — see `HasJointState` for the explicit
joint-vs-fibered distinction, and individual instance files for the
per-family marginalization implementation.

## SEAM (Seam 1): Per-family `iLookup` instances commit to a falsifier
convention — `.star` (Entity), `∅` (Set), zero-mass (PMF), `Dom`-partiality
(FCS metadata-level). -/
class HasFiberedLookup (M : outParam (Type u → Type u)) [Functor M]
    (Ctx : Type v) (V : outParam (Type w))
    (W : outParam (Type x)) (E : outParam (Type u)) where
  /-- Look up the M-family of values for variable `v` at world `w`. -/
  iLookup : Ctx → V → W → M E

/-- **Joint-state interface** — frameworks whose underlying state is a
single `M`-distribution / structure over (world, assignment) pairs,
rather than a fiber `W → M (Assignment E)`. Per Seam 2.

Joint states *automatically* provide `HasFiberedLookup` (it is an
`extends` parent), but the fibered projection of a joint state is
**lossy**: world-assignment correlations beyond what a single `(v, w)`
query probes are discarded by marginalization.

The marginalization itself is per-family because it requires more than
`Functor M` — Charlow needs filtering (set-builder), PDS needs
conditioning (`PMF.cond` machinery). Each `HasJointState` instance
provides its own `iLookup` implementation that agrees with marginalizing
its `joint`; the agreement is a per-family proof obligation, not a
typeclass field.

Frameworks committing to this typeclass: Charlow 2019
(`State W E := Set (W × Assignment E)`), FCS (`HeimFile` with
`Sat ⊆ World × Assignment`), PDS Bayesian per @cite{grove-white-2025b}
(`PMF (W × Assignment E)`). Frameworks that deliberately do *not*
declare it: ICDRT, fibered-Bayesian.

The `joint` field exposes the native joint object as
`M (W × (V → E))` — assignments rendered as functions `V → E`. This
constrains `V`/`W`/`E` to share the universe `u` of `M`'s domain.

## SEAM (Seam 2): Declaring this typeclass commits empirically to having
joint structure to lose. The mere existence of `HasFiberedLookup` says
nothing about the underlying state; `HasJointState` does. -/
class HasJointState (M : outParam (Type u → Type u)) [Functor M]
    (Ctx : Type v) (V : outParam (Type u))
    (W : outParam (Type u)) (E : outParam (Type u))
    extends HasFiberedLookup M Ctx V W E where
  /-- The native joint object — the `M`-structure over
  (world, assignment) pairs that the framework natively carries.
  Assignments are rendered as functions `V → E`. -/
  joint : Ctx → M (W × (V → E))

-- ════════════════════════════════════════════════════════════════
-- § 1.5. Trivial extensional baseline — `M = Id`, `W = PUnit`
-- ════════════════════════════════════════════════════════════════

/-- Assignments themselves serve as the *extensional* dynamic-semantic
context, with `M = Id` (no effect) and `W = PUnit` (no world parameter).
This is the trivial baseline shared by @cite{groenendijk-stokhof-1991}
DPL, @cite{muskens-1996} CDRT, and @cite{kamp-reyle-1993} DRT —
their state types are all definitionally `Nat → E = Assignment E`, so
this single instance covers all three.

Lookup is just function application, world-independent. The
"indefinite-persistence" pattern that recurs across these three
extensional theories — pronouns can pick up whatever an indefinite
introduced — is captured at the typeclass level by sharing the same
`HasFiberedLookup Id` interface. Per-paper theorems can be stated
abstractly over `[HasFiberedLookup Id Ctx V W E]` and instantiated to
each theory.

## SEAM (Seam 1): The extensional baseline has *no falsifier* — every
variable always has a value. This is the empirically wrong commitment
that motivated the move to Hofmann's `.star`, Charlow's `∅`, and
Heim's `Dom` — but it is also the cleanest baseline against which the
other three falsifier conventions are minimal extensions. -/
instance instAssignmentHasFiberedLookup (E : Type u) :
    HasFiberedLookup Id (Assignment E) Nat PUnit.{u + 1} E where
  iLookup g v _ := g v

-- ════════════════════════════════════════════════════════════════
-- § 2. ICDRT-specific extensions
-- ════════════════════════════════════════════════════════════════

/-- Hofmann-style **deterministic** context: `HasFiberedLookup Entity`
plus the `iVarUp` update relation.

Extends the abstract effect-functor lookup with the Hofmann update law:
two contexts that "differ at most in `v`" agree on every other variable.
The Entity-specific extension; for non-bivalent families the analogous
update relations are family-specific (Seam 3). -/
class HasIndivDrefs (Ctx : Type v) (V : outParam (Type w))
    (W : outParam (Type x)) (E : outParam (Type u))
    extends HasFiberedLookup Entity Ctx V W E where
  /-- "j differs from i at most in v" — relation form. -/
  iVarUp : V → Ctx → Ctx → Prop
  /-- Equality of lookups outside the updated variable. -/
  iVarUp_other : ∀ v i j (u : V),
    iVarUp v i j → u ≠ v → iLookup j u = iLookup i u

-- ════════════════════════════════════════════════════════════════
-- § 3. Propositional drefs and discourse commitments
-- ════════════════════════════════════════════════════════════════

/-- Contexts carrying propositional drefs (sets of worlds). -/
class HasPropDrefs (Ctx : Type v) (P : outParam (Type w)) (W : outParam (Type x)) where
  /-- Look up the worlds-set associated with propositional variable `p`. -/
  pLookup : Ctx → P → Set W
  /-- "j differs from i at most in p" — relation form. -/
  pVarUp : P → Ctx → Ctx → Prop
  /-- Equality of lookups outside the updated variable. -/
  pVarUp_other : ∀ p i j (q : P), pVarUp p i j → q ≠ p → pLookup j q = pLookup i q

/-- Contexts with a single distinguished commitment-set propositional var. -/
class HasDiscourseCommitment (Ctx : Type v) (P : outParam (Type w)) where
  /-- The propositional variable naming the speaker's commitment set. -/
  commitVar : P

/-- Contexts with per-speaker commitment-set vars. `Speaker` is NOT
outParam: the same context type may carry different speaker indexings. -/
class HasMultiDC (Ctx : Type v) (P : outParam (Type w)) (Speaker : Type x) where
  /-- Map from interlocutor identifier to her commitment-set var. -/
  commitVarOf : Speaker → P

/-- Single-speaker is the trivial multi-speaker case with `Speaker = PUnit`. -/
instance instMultiDC_of_single {Ctx : Type v} {P : Type w}
    [HasDiscourseCommitment Ctx P] :
    HasMultiDC Ctx P PUnit where
  commitVarOf _ := HasDiscourseCommitment.commitVar (Ctx := Ctx)

-- ════════════════════════════════════════════════════════════════
-- § 4. Abstract Predicates (Hofmann/Entity-specific)
-- ════════════════════════════════════════════════════════════════

/-! These predicates use the `Entity.star` falsifier and so are
ICDRT-specific. Charlow / Bayesian analogs (`uniquelyDeterminedAt`,
PMF determinism) live in their respective family files (Seam 4). -/

section Predicates
variable {Ctx : Type v} {V : Type w₁} {P : Type w₂} {W : Type x} {E : Type u}
variable [HasIndivDrefs Ctx V W E] [HasPropDrefs Ctx P W]

/-- Local contextual entailment: `v` defined throughout `φ(i)`.
A precondition for anaphora to `v` resolved in local context `φ`. -/
def localEntailment (φ : P) (v : V) (i : Ctx) : Prop :=
  ∀ w ∈ HasPropDrefs.pLookup (W := W) i φ,
    HasFiberedLookup.iLookup i v w ≠ Entity.star

/-- Veridicality of an individual dref relative to a commitment set. -/
def veridicalIndiv (φ_DC : P) (v : V) (i : Ctx) : Prop :=
  ∀ w ∈ HasPropDrefs.pLookup (W := W) i φ_DC,
    HasFiberedLookup.iLookup i v w ≠ Entity.star

/-- Counterfactuality: `v` maps to ⋆ in all `φ_DC`-worlds. -/
def counterfactualIndiv (φ_DC : P) (v : V) (i : Ctx) : Prop :=
  ∀ w ∈ HasPropDrefs.pLookup (W := W) i φ_DC,
    HasFiberedLookup.iLookup i v w = Entity.star

/-- Subset requirement: `φ_anaphor(i) ⊆ φ_antecedent(i)`. -/
def subsetReq (φ_anaphor φ_antecedent : P) (i : Ctx) : Prop :=
  HasPropDrefs.pLookup (W := W) i φ_anaphor ⊆ HasPropDrefs.pLookup i φ_antecedent

/-- DEC condition: `φ_DC(j) ⊆ φ(j)`. -/
def decCondition (φ_DC φ : P) (i : Ctx) : Prop :=
  HasPropDrefs.pLookup (W := W) i φ_DC ⊆ HasPropDrefs.pLookup i φ

/-- Discourse consistency: commitment set is nonempty. -/
def consistentAt (φ_DC : P) (i : Ctx) : Prop :=
  (HasPropDrefs.pLookup (W := W) i φ_DC).Nonempty

/-- Accessibility = local entailment ∧ consistency. -/
def accessible (φ_anaphor : P) (v : V) (φ_DC : P) (i : Ctx) : Prop :=
  localEntailment (W := W) φ_anaphor v i ∧ consistentAt (W := W) φ_DC i

/-- Worlds where `v` has a non-⋆ referent in context `i`. -/
def definedAt (v : V) (i : Ctx) : Set W :=
  { w | HasFiberedLookup.iLookup i v w ≠ Entity.star }

/-- Generic relative-variable update: differ at most in `v`, and the
propositional dref `φ(j)` tracks exactly `v`'s definedness pattern in
`j`. This is Hofmann's cross-field operation expressed without a new
typeclass — pure combination of `iVarUp` and `pLookup`. -/
def relVarUp (φ : P) (v : V) (i j : Ctx) : Prop :=
  HasIndivDrefs.iVarUp v i j ∧
  HasPropDrefs.pLookup (W := W) j φ = definedAt (E := E) v j

end Predicates

-- ════════════════════════════════════════════════════════════════
-- § 5. Multi-Speaker Predicates
-- ════════════════════════════════════════════════════════════════

/-- Pull the commitment var out of `HasMultiDC` with explicit type
arguments — wrapping avoids field-projection ambiguities from the
non-outParam `Speaker` parameter. -/
def commitVarFor {Ctx : Type v} (P : Type w) {Speaker : Type x}
    [HasMultiDC Ctx P Speaker] (s : Speaker) : P :=
  @HasMultiDC.commitVarOf Ctx P Speaker _ s

/-- Multi-agent discourse consistency: every speaker's commitment set is
nonempty in `i`. -/
def multiConsistentAt {Ctx : Type v} {P : Type w₁} {W : Type w₂} {Speaker : Type x}
    [HasPropDrefs Ctx P W] [HasMultiDC Ctx P Speaker]
    (speakers : Set Speaker) (i : Ctx) : Prop :=
  ∀ s ∈ speakers,
    (HasPropDrefs.pLookup (W := W) i (commitVarFor (Ctx := Ctx) P s)).Nonempty

/-- Per-speaker accessibility — local entailment plus multi-agent consistency. -/
def multiAccessible {Ctx : Type v} {P : Type w} {V : Type w₁} {W : Type w₂}
    {E : Type u} {Speaker : Type x}
    [HasIndivDrefs Ctx V W E] [HasPropDrefs Ctx P W]
    [HasMultiDC Ctx P Speaker]
    (φ_anaphor : P) (vr : V) (speakers : Set Speaker) (i : Ctx) : Prop :=
  localEntailment (W := W) φ_anaphor vr i ∧
  multiConsistentAt (W := W) speakers i

-- ════════════════════════════════════════════════════════════════
-- § 6. Abstract Theorems
-- ════════════════════════════════════════════════════════════════

/-- **Counterfactual antecedent blocks veridical anaphor** (abstract).

In any `Ctx` with prop drefs, if we extend `i` to `j` keeping `φ_DC` and
`φ_neg` lookups fixed, and the antecedent provides counterfactuality
(`φ_DC(i) ∩ φ_neg(i) = ∅`), then satisfying both DEC
(`φ_DC(j) ⊆ φ_anaphor(j)`) and the subset requirement
(`φ_anaphor(j) ⊆ φ_neg(j)`) forces `φ_DC(j) = ∅`, i.e. discourse
inconsistency.

This is the typeclass-only version of @cite{hofmann-2025}'s bathroom-
sentence theorem: "There isn't a bathroom. #It is upstairs."

## SEAM 6 (Anaphora resolution): The theorem only needs `HasPropDrefs`
— individual drefs and the Entity/Set/PMF effect functor play no role.
Charlow's `State W E` carries no propositional-dref structure, so this
theorem **does not transfer** to Charlow contexts. The same empirical
phenomenon under Charlow's framework is solved by alternative-set
filtering, not by propositional-dref disjointness — different
resolution mechanism, different theorem. -/
theorem counterfactual_blocks_veridical
    {Ctx : Type v} {P : Type w} {W : Type x}
    [HasPropDrefs Ctx P W]
    (i j : Ctx) (φ_DC φ_anaphor φ_neg : P)
    (h_extends_DC :
      HasPropDrefs.pLookup (W := W) j φ_DC = HasPropDrefs.pLookup i φ_DC)
    (h_extends_neg :
      HasPropDrefs.pLookup (W := W) j φ_neg = HasPropDrefs.pLookup i φ_neg)
    (h_DC_disjoint_neg :
      HasPropDrefs.pLookup (W := W) i φ_DC ∩
        HasPropDrefs.pLookup (W := W) i φ_neg = ∅)
    (h_dec : decCondition (W := W) φ_DC φ_anaphor j)
    (h_subset : subsetReq (W := W) φ_anaphor φ_neg j) :
    ¬ consistentAt (W := W) φ_DC j := by
  intro ⟨w, hw⟩
  have hw' : w ∈ HasPropDrefs.pLookup (W := W) i φ_DC := by
    rw [← h_extends_DC]; exact hw
  have hw_neg' : w ∈ HasPropDrefs.pLookup (W := W) i φ_neg := by
    rw [← h_extends_neg]; exact h_subset (h_dec hw)
  have hmem :
      w ∈ HasPropDrefs.pLookup (W := W) i φ_DC ∩
            HasPropDrefs.pLookup (W := W) i φ_neg := ⟨hw', hw_neg'⟩
  rw [h_DC_disjoint_neg] at hmem; exact hmem

/-- Multi-speaker generalization: blocks veridical anaphor for ANY
speaker whose commitment set is disjoint from the negative prejacent. -/
theorem multi_counterfactual_blocks_veridical
    {Ctx : Type v} {P : Type w} {W : Type w₂} {Speaker : Type x}
    [HasPropDrefs Ctx P W]
    [HasMultiDC Ctx P Speaker]
    (i j : Ctx) (φ_anaphor φ_neg : P)
    (speakers : Set Speaker) (s : Speaker) (hs : s ∈ speakers)
    (h_extends_DC :
      HasPropDrefs.pLookup (W := W) j (commitVarFor (Ctx := Ctx) P s) =
        HasPropDrefs.pLookup i (commitVarFor (Ctx := Ctx) P s))
    (h_extends_neg :
      HasPropDrefs.pLookup (W := W) j φ_neg = HasPropDrefs.pLookup i φ_neg)
    (h_DC_disjoint_neg :
      HasPropDrefs.pLookup (W := W) i (commitVarFor (Ctx := Ctx) P s) ∩
        HasPropDrefs.pLookup (W := W) i φ_neg = ∅)
    (h_dec :
      decCondition (W := W) (commitVarFor (Ctx := Ctx) P s) φ_anaphor j)
    (h_subset : subsetReq (W := W) φ_anaphor φ_neg j) :
    ¬ multiConsistentAt (W := W) speakers j := by
  intro hcons
  exact counterfactual_blocks_veridical
    i j (commitVarFor (Ctx := Ctx) P s) φ_anaphor φ_neg
    h_extends_DC h_extends_neg h_DC_disjoint_neg h_dec h_subset (hcons s hs)

end Semantics.Dynamic.Context
