import Linglib.Theories.Semantics.Dynamic.Core.DiscourseRef

/-!
# Dynamic Context — Effect-Functor-Parameterized Interface

@cite{groenendijk-stokhof-1991} @cite{muskens-1996} @cite{hofmann-2025}

A typeclass interface for dynamic-semantics contexts, parameterized on
the **effect functor `M`** that wraps each variable's value at a world.
The unifying frame across deterministic, nondeterministic, and
probabilistic dynamic semantics.

## Mathlib-style discipline

Where structure is shared, expose it via a typeclass — `HasIndivLookupM`
gives every family the same `iLookup` interface, so cross-family
predicates are by-construction comparable. `HasIndivDrefs` extends it,
adding the Hofmann-specific `iVarUp` update relation. Bridge maps
between families are explicit named natural transformations of `M`,
following the mathlib pattern (Function/Set.Image/MeasurableFunction/
PMF/Measure as a family of related-but-not-unified abstractions).

## Six 2026 seams

What this interface *does not* paper over: six places where dynamic
theories deliberately diverge in 2026. Each is named, locatable
(`grep "## SEAM"`), and committed at the per-family file level —
visible structure, not hidden disagreement.

### Seam 1 — Falsifier convention

What does "no referent for `v` at `w`" mean?

| Family | Falsifier |
|---|---|
| ICDRT | `Entity.star` (bivalent distinguished value) |
| Charlow | `∅` (empty alternative-set; no value-level falsifier) |
| Bayesian | zero-mass (PMF assigns probability 0; no value-level falsifier) |

Charlow's argument: bivalence undermines compositional negation.
Hofmann's argument: alternative-sets underdetermine anaphora projection.
The seam stays open.

### Seam 2 — State shape (joint vs fibered)

Does the state remember world–assignment correlation?

| Family | Shape |
|---|---|
| ICDRT | fibered (`indiv : IVar → W → Entity E`) |
| Charlow | joint (`State W E := Set (W × Assignment E)`) |
| Bayesian | fibered (`BayesianState W E := W → PMF (Assignment E)`) |

The joint form admits world–assignment dependencies (e.g., counterfactual
worlds where reference also changes); the fibered form rules them out.
Charlow ↔ fibered-Charlow correspondence is recoverable but not
identity (joint Charlow strictly more expressive).

### Seam 3 — Update mechanism

What does "extend the discourse" mean operationally?

| Family | Update primitive |
|---|---|
| ICDRT | assignment update (`updateIndiv g v e`) |
| Charlow | alternative filtering / set-builder |
| Bayesian | conditioning (Bayes update / `PMF.bind`) |

These genuinely don't unify — Charlow's bind is non-commutative (his
"scope of alternatives" thesis); PMF's bind is commutative under
independence; Hofmann's update is sequential. The interface deliberately
omits a master `Update` typeclass.

### Seam 4 — Definedness predicate

"`v` has a definite referent at `w` in `i`."

| Family | Predicate shape |
|---|---|
| ICDRT | `iLookup i v w ≠ Entity.star` |
| Charlow | `iLookup i v w` is a singleton set |
| Bayesian | `iLookup i v w` is a Dirac/point-mass |

All three express "the M-fiber is determinate." Mathlib has
`Set.Subsingleton` and `PMF.IsDeterministic` for the latter two. We
ship parallel-named predicates (`isDeterminateAt` per family) without
yet abstracting; the seam stays visible until a study needs to
quantify over it.

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
| Karttunen / Heim | dref binding via assignment update |
| Charlow | alternatives in the continuation |
| Hofmann (ICDRT) | propositional drefs as local contexts |
| Bayesian | posterior conditioning on observed reference |

The deepest seam — not in the lookup signature, but in how lookups get
used by `Phenomena/.../Studies/`. Each Studies file commits in its own
resolution semantics.

## Key Types

| Class | Carries |
|---|---|
| `HasIndivLookupM M Ctx V W E` | Effect-functor lookup `Ctx → V → W → M E` |
| `HasIndivDrefs Ctx V W E` | `HasIndivLookupM Entity` + Hofmann `iVarUp` law |
| `HasPropDrefs Ctx P W` | Propositional drefs `P` to sets of worlds |
| `HasDiscourseCommitment Ctx P` | Distinguished commitment-set var (single speaker) |
| `HasMultiDC Ctx P Speaker` | Per-speaker commitment-set vars (dialogue) |
-/

namespace Semantics.Dynamic.Context

open Semantics.Dynamic.Core

-- ════════════════════════════════════════════════════════════════
-- § 1. Effect-functor lookup — the shared scaffolding
-- ════════════════════════════════════════════════════════════════

/-- **Effect-functor-parameterized lookup** — the unifying frame across
deterministic, nondeterministic, and probabilistic dynamic semantics.

`iLookup i v w : M E` returns a *family* of values structured by an
effect functor `M`:

- `M = Entity` (deterministic; ICDRT)
- `M = Set` (nondeterministic; Charlow)
- `M = PMF` (probabilistic; Bayesian)

`M` is `outParam`: each `Ctx` carries exactly one effect functor.
`Functor M` is enough — no `Monad M` requirement, since `Set` lacks a
clean `Monad` instance in Lean. Bridge maps between families are
**explicit named natural transformations** of `M`, not monad lifts.

## SEAM: per-family `iLookup` instances commit to a falsifier
convention (Seam 1) — `.star` (Entity), `∅` (Set), zero-mass (PMF). -/
class HasIndivLookupM (M : outParam (Type* → Type*)) [Functor M]
    (Ctx : Type*) (V : outParam Type*)
    (W : outParam Type*) (E : outParam Type*) where
  /-- Look up the M-family of values for variable `v` at world `w`. -/
  iLookup : Ctx → V → W → M E

-- ════════════════════════════════════════════════════════════════
-- § 2. ICDRT-specific extensions
-- ════════════════════════════════════════════════════════════════

/-- Hofmann-style **deterministic** context: `HasIndivLookupM Entity`
plus the `iVarUp` update relation.

Extends the abstract effect-functor lookup with the Hofmann update law:
two contexts that "differ at most in `v`" agree on every other variable.
The Entity-specific extension; for non-bivalent families the analogous
update relations are family-specific (Seam 3). -/
class HasIndivDrefs (Ctx : Type u) (V : outParam (Type u))
    (W : outParam (Type u)) (E : outParam (Type u))
    extends HasIndivLookupM Entity Ctx V W E where
  /-- "j differs from i at most in v" — relation form. -/
  iVarUp : V → Ctx → Ctx → Prop
  /-- Equality of lookups outside the updated variable. -/
  iVarUp_other : ∀ v i j (u : V),
    iVarUp v i j → u ≠ v → iLookup j u = iLookup i u

-- ════════════════════════════════════════════════════════════════
-- § 3. Propositional drefs and discourse commitments
-- ════════════════════════════════════════════════════════════════

/-- Contexts carrying propositional drefs (sets of worlds). -/
class HasPropDrefs (Ctx : Type u) (P : outParam (Type u)) (W : outParam (Type u)) where
  /-- Look up the worlds-set associated with propositional variable `p`. -/
  pLookup : Ctx → P → Set W
  /-- "j differs from i at most in p" — relation form. -/
  pVarUp : P → Ctx → Ctx → Prop
  /-- Equality of lookups outside the updated variable. -/
  pVarUp_other : ∀ p i j (q : P), pVarUp p i j → q ≠ p → pLookup j q = pLookup i q

/-- Contexts with a single distinguished commitment-set propositional var. -/
class HasDiscourseCommitment (Ctx : Type u) (P : outParam (Type u)) where
  /-- The propositional variable naming the speaker's commitment set. -/
  commitVar : P

/-- Contexts with per-speaker commitment-set vars. `Speaker` is NOT
outParam: the same context type may carry different speaker indexings. -/
class HasMultiDC (Ctx : Type u) (P : outParam (Type u)) (Speaker : Type u) where
  /-- Map from interlocutor identifier to her commitment-set var. -/
  commitVarOf : Speaker → P

/-- Single-speaker is the trivial multi-speaker case with `Speaker = Unit`. -/
instance instMultiDC_of_single {Ctx P : Type} [HasDiscourseCommitment Ctx P] :
    HasMultiDC Ctx P Unit where
  commitVarOf _ := HasDiscourseCommitment.commitVar (Ctx := Ctx)

-- ════════════════════════════════════════════════════════════════
-- § 4. Abstract Predicates (Hofmann/Entity-specific)
-- ════════════════════════════════════════════════════════════════

/-! These predicates use the `Entity.star` falsifier and so are
ICDRT-specific. Charlow / Bayesian analogs (`uniquelyDeterminedAt`,
PMF determinism) live in their respective family files (Seam 4). -/

section Predicates
variable {Ctx V P W E : Type}
variable [HasIndivDrefs Ctx V W E] [HasPropDrefs Ctx P W]

/-- Local contextual entailment: `v` defined throughout `φ(i)`.
A precondition for anaphora to `v` resolved in local context `φ`. -/
def localEntailment (φ : P) (v : V) (i : Ctx) : Prop :=
  ∀ w ∈ HasPropDrefs.pLookup (W := W) i φ,
    HasIndivLookupM.iLookup i v w ≠ Entity.star

/-- Veridicality of an individual dref relative to a commitment set. -/
def veridicalIndiv (φ_DC : P) (v : V) (i : Ctx) : Prop :=
  ∀ w ∈ HasPropDrefs.pLookup (W := W) i φ_DC,
    HasIndivLookupM.iLookup i v w ≠ Entity.star

/-- Counterfactuality: `v` maps to ⋆ in all `φ_DC`-worlds. -/
def counterfactualIndiv (φ_DC : P) (v : V) (i : Ctx) : Prop :=
  ∀ w ∈ HasPropDrefs.pLookup (W := W) i φ_DC,
    HasIndivLookupM.iLookup i v w = Entity.star

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
  { w | HasIndivLookupM.iLookup i v w ≠ Entity.star }

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
def commitVarFor {Ctx : Type} (P : Type) {Speaker : Type}
    [HasMultiDC Ctx P Speaker] (x : Speaker) : P :=
  @HasMultiDC.commitVarOf Ctx P Speaker _ x

/-- Multi-agent discourse consistency: every speaker's commitment set is
nonempty in `i`. -/
def multiConsistentAt {Ctx P W Speaker : Type}
    [HasPropDrefs Ctx P W] [HasMultiDC Ctx P Speaker]
    (speakers : Set Speaker) (i : Ctx) : Prop :=
  ∀ x ∈ speakers,
    (HasPropDrefs.pLookup (W := W) i (commitVarFor (Ctx := Ctx) P x)).Nonempty

/-- Per-speaker accessibility — local entailment plus multi-agent consistency. -/
def multiAccessible {Ctx P V W E Speaker : Type}
    [HasIndivDrefs Ctx V W E] [HasPropDrefs Ctx P W]
    [HasMultiDC Ctx P Speaker]
    (φ_anaphor : P) (v : V) (speakers : Set Speaker) (i : Ctx) : Prop :=
  localEntailment (W := W) φ_anaphor v i ∧
  multiConsistentAt (W := W) speakers i

-- ════════════════════════════════════════════════════════════════
-- § 6. Abstract Theorems
-- ════════════════════════════════════════════════════════════════

/-- **Counterfactual antecedent blocks veridical anaphor** (abstract).

In any `Ctx` with indiv and prop drefs, if we extend `i` to `j` keeping
`φ_DC` and `φ_neg` lookups fixed, and the antecedent provides
counterfactuality (`φ_DC(i) ∩ φ_neg(i) = ∅`), then satisfying both DEC
(`φ_DC(j) ⊆ φ_anaphor(j)`) and the subset requirement
(`φ_anaphor(j) ⊆ φ_neg(j)`) forces `φ_DC(j) = ∅`, i.e. discourse
inconsistency.

This is the typeclass-only version of @cite{hofmann-2025}'s bathroom-
sentence theorem (§3.4): "There isn't a bathroom. #It is upstairs." -/
theorem counterfactual_blocks_veridical
    {Ctx P V W E : Type}
    [HasIndivDrefs Ctx V W E] [HasPropDrefs Ctx P W]
    (i j : Ctx) (φ_DC φ_anaphor φ_neg : P) (_v : V)
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
    {Ctx P V W E Speaker : Type}
    [HasIndivDrefs Ctx V W E] [HasPropDrefs Ctx P W]
    [HasMultiDC Ctx P Speaker]
    (i j : Ctx) (φ_anaphor φ_neg : P) (v : V)
    (speakers : Set Speaker) (x : Speaker) (hx : x ∈ speakers)
    (h_extends_DC :
      HasPropDrefs.pLookup (W := W) j (commitVarFor (Ctx := Ctx) P x) =
        HasPropDrefs.pLookup i (commitVarFor (Ctx := Ctx) P x))
    (h_extends_neg :
      HasPropDrefs.pLookup (W := W) j φ_neg = HasPropDrefs.pLookup i φ_neg)
    (h_DC_disjoint_neg :
      HasPropDrefs.pLookup (W := W) i (commitVarFor (Ctx := Ctx) P x) ∩
        HasPropDrefs.pLookup (W := W) i φ_neg = ∅)
    (h_dec :
      decCondition (W := W) (commitVarFor (Ctx := Ctx) P x) φ_anaphor j)
    (h_subset : subsetReq (W := W) φ_anaphor φ_neg j) :
    ¬ multiConsistentAt (W := W) speakers j := by
  intro hcons
  exact counterfactual_blocks_veridical
    i j (commitVarFor (Ctx := Ctx) P x) φ_anaphor φ_neg v
    h_extends_DC h_extends_neg h_DC_disjoint_neg h_dec h_subset (hcons x hx)

end Semantics.Dynamic.Context
