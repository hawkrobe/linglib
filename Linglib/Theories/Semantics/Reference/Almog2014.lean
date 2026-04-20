import Linglib.Theories.Semantics.Reference.Basic
import Linglib.Theories.Semantics.Reference.Kaplan
import Linglib.Theories.Semantics.Reference.Donnellan
import Linglib.Theories.Semantics.Reference.KaplanLD
import Linglib.Theories.Semantics.Reference.Kripke
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Core.Conjectures

/-!
# @cite{almog-2014}: Referential Mechanics — Synthesis

The central thesis of @cite{almog-2014}: the three mechanisms of direct reference
— designation, singular propositions, and referential use — are logically
independent. An expression can exhibit any subset of the three.

This module provides canonical referential profiles for each expression type,
proves pairwise independence of the three dimensions, chains the key
argumentation from across the Reference module, and bridges the reference
theory to the rest of Linglib.

## Canonical Profiles (from @cite{almog-2014})

| Expression         | Designation | Singular Prop | Referential Use |
|--------------------|-------------|---------------|-----------------|
| True demonstrative | ✓           | ✓             | ✓               |
| Proper name        | ✓           | ✓             | ✗               |
| dthat[the φ]       | ✓           | ✗             | ✗               |
| "The φ" (ref.)     | ✗           | ✗             | ✓               |
| "The φ" (attr.)    | ✗           | ✗             | ✗               |

The ⟨F,T,F⟩ combination (singularity without designation) is witnessed by
de re scope: a description taking wide scope over a modal contributes a
singular proposition without itself being rigid. This is not an "expression
type" per se but a scope configuration that demonstrates the logical
independence of designation from singularity.

## Independence

The three dimensions are pairwise independent:
- Designation ⊥ singularProp: name [T,T] vs dthat [T,F] vs deReScope [F,T] vs attrDesc [F,F]
- Designation ⊥ referentialUse: demo [T,T] vs name [T,F] vs refDesc [F,T] vs attrDesc [F,F]
- SingularProp ⊥ referentialUse: demo [T,T] vs name [T,F] vs refDesc [F,T] vs attrDesc [F,F]

## End-to-End Argumentation

The central chain from @cite{almog-2014} Ch 1–2:
1. dthat is rigid (KaplanLD.dthatW_isRigid)
2. dthat is scope-inert (Kripke.rigid_iff_scope_invariant, forward direction)
3. But dthat does NOT produce singular propositions (dthat_not_singular)
4. Therefore designation ≠ singularity (designation_indep_singularProp)
5. Singular propositions solve the Frege puzzle (frege_puzzle)
6. So dthat alone cannot solve the Frege puzzle

-/

namespace Semantics.Reference.Almog2014

open Semantics.Reference.Basic (ReferentialProfile ReferringExpression properName
  isDirectlyReferential)
open Semantics.Reference.Kaplan (SingularProposition indexical)
open Semantics.Reference.Donnellan (UseMode referentialExpression)
open Semantics.Reference.KaplanLD (dthatW dthatW_isRigid)
open Semantics.Reference.Kripke (rigid_iff_scope_invariant deRe deDicto)
open Core (Intension)
open Core.Intension (rigid IsRigid rigid_isRigid evalAt rigid_section
  rigid_evalAt_lossy)

/-! ## Canonical Referential Profiles -/

/-- Proper name: designation + singularity, no referential use.

"Aristotle" rigidly designates an individual (@cite{kripke-1980}) and expresses a
singular proposition ⟨Aristotle, property⟩ (@cite{kaplan-1989}), but does not require
the speaker to have a cognitive fix on any particular occasion. -/
def nameProfile : ReferentialProfile := ⟨true, true, false⟩

/-- dthat[the φ]: designation only.

sharpest separation (Ch 1): `dthat[the tallest spy]` rigidly
designates whoever is actually the tallest spy (`dthatW_isRigid`), but its
content is a general proposition (a rigid intension), NOT a structured
⟨individual, property⟩ pair. This distinguishes rigidity from direct
referentiality in Kaplan's sense. -/
def dthatProfile : ReferentialProfile := ⟨true, false, false⟩

/-- Referentially-used description: referential use only.

"The man drinking a martini" used referentially — the speaker has Jones in
mind, using the description to identify him. Per Ch 3
§§2.2–2.12, this is a cognitive mechanism: the speaker's mind is already
"loaded" with the referent. The description itself is non-rigid
(designation = false), and per reading of Donnellan
(§2.12), the propositional content is NOT singular — Donnellan gives a
"proposition-free account, rather de re (de object coming in) in its
form." Only the cognitive fix is present. -/
def refDescProfile : ReferentialProfile := ⟨false, false, true⟩

/-- Attributively-used description: no mechanism of direct reference.

"The man drinking a martini" used attributively — "whoever uniquely satisfies
the description." No rigidity, no singular proposition, no cognitive fix. -/
def attrDescProfile : ReferentialProfile := ⟨false, false, false⟩

/-- True demonstrative: all three mechanisms.

"That [pointing]" — rigid designation (the demonstrated object is fixed),
singular propositional content (⟨demonstrated object, property⟩), and
referential use (the speaker has the object in mind via the demonstration).
The demonstrative is the paradigm case where all three of
mechanisms converge. -/
def demoProfile : ReferentialProfile := ⟨true, true, true⟩

/-- De re scope reading: singularity without designation.

"Lois believes [the man at the door]₁ is tall" (de re) — the description
takes wide scope, contributing a singular proposition about the actual man
at the door. But the description itself is not rigid (at different worlds,
different people might be at the door).

Note: this is a *scope configuration*, not an expression type per se. We
include it to witness the logical independence of designation from
singularity — all four combinations of (designation, singularProp) must be
attested for independence, and this is the only natural witness for ⟨F,T,F⟩. -/
def deReScopeProfile : ReferentialProfile := ⟨false, true, false⟩

/-! ## Pairwise Independence

For each pair of dimensions (X, Y), we exhibit profiles demonstrating that
X can vary independently of Y: both (X=T, Y=T) and (X=T, Y=F) are attested,
as are (X=F, Y=T) and (X=F, Y=F). -/

/-- Designation is independent of singular propositional content.

All four combinations of (designation, singularProp) are attested:
name [T,T], dthat [T,F], deReScope [F,T], attrDesc [F,F]. -/
theorem designation_indep_singularProp :
    nameProfile.designation = true ∧ nameProfile.singularProp = true ∧
    dthatProfile.designation = true ∧ dthatProfile.singularProp = false ∧
    deReScopeProfile.designation = false ∧ deReScopeProfile.singularProp = true ∧
    attrDescProfile.designation = false ∧ attrDescProfile.singularProp = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Designation is independent of referential use.

All four combinations of (designation, referentialUse) are attested:
demo [T,T], name [T,F], refDesc [F,T], attrDesc [F,F]. -/
theorem designation_indep_referentialUse :
    demoProfile.designation = true ∧ demoProfile.referentialUse = true ∧
    nameProfile.designation = true ∧ nameProfile.referentialUse = false ∧
    refDescProfile.designation = false ∧ refDescProfile.referentialUse = true ∧
    attrDescProfile.designation = false ∧ attrDescProfile.referentialUse = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Singular propositional content is independent of referential use.

All four combinations of (singularProp, referentialUse) are attested:
demo [T,T], name [T,F], refDesc [F,T], attrDesc [F,F]. -/
theorem singularProp_indep_referentialUse :
    demoProfile.singularProp = true ∧ demoProfile.referentialUse = true ∧
    nameProfile.singularProp = true ∧ nameProfile.referentialUse = false ∧
    refDescProfile.singularProp = false ∧ refDescProfile.referentialUse = true ∧
    attrDescProfile.singularProp = false ∧ attrDescProfile.referentialUse = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Dthat: Designation Without Singularity

central argument against conflating rigidity with direct
referentiality. `dthat[the φ]` is rigid by mechanism — `KaplanLD.dthatW_isRigid`
proves this — but its content is not a structured ⟨individual, property⟩ pair.
It is a general proposition that happens to be world-invariant. -/

/-- A dthat-expression as a `ReferringExpression`: rigid character, profile
records designation without singularity or referential use. -/
def dthatExpression {C W E : Type*} (desc : Intension W E) (cW : W) :
    ReferringExpression C W E :=
  { character := λ _ => dthatW desc cW
  , profile := dthatProfile }

/-- dthat-expressions are de jure rigid: their character produces rigid
content and their profile records the designation mechanism. -/
theorem dthat_deJureRigid {C W E : Type*} (desc : Intension W E) (cW : W) :
    Semantics.Reference.Basic.IsDeJureRigid
      (dthatExpression (C := C) desc cW) :=
  ⟨rfl, λ _ => dthatW_isRigid desc cW⟩

/-- dthat-expressions do NOT have singular propositional content.
This is the formal content of separation thesis. -/
theorem dthat_not_singular {C W E : Type*} (desc : Intension W E) (cW : W) :
    (dthatExpression (C := C) desc cW).profile.singularProp = false := rfl

/-! ## End-to-End Argumentation Chain

central argument in formal steps:

1. dthat rigidifies descriptions → `dthatW_isRigid`
2. Rigid designators are scope-inert → `rigid_iff_scope_invariant` (fwd)
3. But dthat does NOT produce singular propositions → `dthat_not_singular`
4. Singular propositions solve Frege puzzles → `frege_puzzle`
5. Therefore dthat CANNOT solve the Frege puzzle — rigidity alone is
   insufficient; we need singularity (structured content) to distinguish
   ⟨Hesperus, bright⟩ from ⟨Phosphorus, bright⟩.

This is the formal core of argument that designation
and singularity are independent mechanisms with different explanatory roles. -/

/-- Step 1–2: dthat is scope-inert. Since dthat is rigid (dthatW_isRigid),
scope invariance follows from `rigid_iff_scope_invariant`. -/
theorem dthat_scope_inert {W E : Type*} (desc : Intension W E) (cW w₀ : W) :
    ∀ (P : E → W → Prop) (w : W),
      deRe P (dthatW desc cW) w₀ w ↔ deDicto P (dthatW desc cW) w :=
  (rigid_iff_scope_invariant (dthatW desc cW) w₀).mp (dthatW_isRigid desc cW)

/-- Step 3–5: dthat cannot solve the Frege puzzle.

Given two descriptions that happen to co-denote at the actual world,
dthat rigidifies both to the same individual. Their dthat-contents are
identical (same rigid intension). But the *structured* singular
propositions would distinguish them — except dthat doesn't produce
structured content at all. So dthat eliminates scope ambiguity (step 2)
but cannot explain informativeness. -/
theorem dthat_insufficient_for_frege {W E : Type*}
    (desc₁ desc₂ : Intension W E) (cW : W)
    (hCo : desc₁ cW = desc₂ cW) :
    -- dthat makes them the same intension...
    dthatW desc₁ cW = dthatW desc₂ cW := by
  simp only [dthatW, hCo]

/-! ## The Frege Puzzle (Cross-Module Bridge) -/

/-- The Frege puzzle: unstructured propositions conflate what structured
propositions distinguish.

Given two proper names for distinct individuals that happen to satisfy
the same property at every world, their unstructured propositions are
identical but their singular propositions are distinct.

Bridge to `Kaplan.SingularProposition.structured_distinguishes_unstructured`. -/
theorem frege_puzzle {W E : Type*} (a b : E) (P : E → W → Prop) (hab : a ≠ b)
    (hflat : (SingularProposition.mk a P).flatten =
             (SingularProposition.mk b P).flatten) :
    -- Same unstructured content...
    (SingularProposition.mk a P).flatten = (SingularProposition.mk b P).flatten ∧
    -- ...but different structured content
    (SingularProposition.mk a P) ≠ (SingularProposition.mk b P) :=
  ⟨hflat, SingularProposition.structured_distinguishes_unstructured a b P hab hflat⟩

/-! ## The "No Entailments" Thesis (Ch 2, §2.1)

central metatheoretic claim: direct reference theory
proper — whether via designation, singular propositions, or referential use —
produces NO entailments about either modal or attitudinal questions.

"The simple logical point is this: *There are no entailments from direct
reference theory proper regarding either modal or attitudinal questions.*"

The theory assigns the same proposition to "Cicero = Cicero" and
"Cicero = Tully." But that is all. Whether that proposition is *necessary*
requires the independent metaphysical doctrine of modal haecceitism.
Whether an agent *believes* it requires an independent theory of attitude
verb semantics. The reference theory is silent on both. -/

/-- Direct reference theory is silent on opacity.

Distinct individuals produce distinct singular propositions — this is a
structural fact about ⟨individual, property⟩ pairs, not an explanation of
attitude opacity. Per (Ch 2, §2.1), no doctrine regarding
modal or cognitive matters follows from direct reference theory proper.
Substitution failure in attitude reports requires an independent theory
of attitudinal verb semantics (see `Attitudes.Doxastic.substitutionMayFail`
for the formal framework). -/
theorem structured_content_distinguishes {W E : Type*} :
    ∀ (a b : E) (P : E → W → Prop), a ≠ b →
    SingularProposition.mk a P ≠ SingularProposition.mk b P := by
  intro a b P hab heq
  have := congrArg SingularProposition.individual heq
  simp at this
  exact hab this

/-! ## Cross-Module Bridges -/

/-- Proper names are directly referential: bridges the `Reference/Basic.lean`
proper name definition through `IsDeJureRigid` to the broader system.

This is the formal content of @cite{kripke-1980}'s thesis as formalized
via designation mechanism. -/
theorem properName_deJure {C W E : Type*} (e : E) :
    isDirectlyReferential (properName (C := C) (W := W) e).character :=
  λ _ => rigid_isRigid e

/-! ## Bridge: PLA and the Frege Puzzle

@cite{dekker-2012}'s cover-relative belief framework (`Semantics.Dynamic.PLA`) gives a
formal mechanism for Frege puzzles: two concepts can co-refer at the actual
world but diverge in belief-accessible worlds. This is exactly the scenario
where proper names have the same referent but different cognitive significance.

The bridge is informal: PLA uses cover-relative assignment functions while
framework uses mechanism-based analysis. A formal
connection would require unifying "mode of presentation" across both. -/

/-! ## KDthat: Outside-In Reference (Ch 3, §2.13)

alternative to Kaplan's `dthat`. In KDthat, the reference
is already fixed by an incoming signal (outside-in) before any linguistic
expression is deployed. The description in parentheses serves only as a
communicative guide — it helps the audience identify the referent the speaker
already has in mind, but does not determine it.

Contrast with `dthatW`, which rigidifies *by evaluating* the description
at the actual world (inside-out).

KDthat encodes the three-stage model of referential use (Ch 3, §1.2):
1. Object-contact (outside-in): `loaded` — the object that came to mind
2. Predicative characterization: the speaker forms (possibly false) beliefs
3. Communication: `guide` — the linguistic device deployed to direct the audience -/

/-- KDthat: a point-demonstrative whose reference is fixed outside-in.
`loaded` is the individual from stage 1 (object-contact). `guide` is the
description used to communicate (stage 3). The guide plays no role in
determining reference. -/
def kdthat {W E : Type*} (loaded : E) (_guide : E → W → Prop) : Intension W E :=
  rigid loaded

/-- KDthat is rigid (trivially — reference was already fixed). -/
theorem kdthat_isRigid {W E : Type*} (loaded : E) (guide : E → W → Prop) :
    IsRigid (kdthat loaded guide) :=
  rigid_isRigid loaded

/-- Changing the communicative guide does not change the referent.
This is the formal content of outside-in thesis:
reference is fixed at object-contact (stage 1), not at communication
(stage 3). -/
theorem kdthat_guide_irrelevant {W E : Type*}
    (loaded : E) (guide₁ guide₂ : E → W → Prop) :
    kdthat loaded guide₁ = kdthat loaded guide₂ :=
  rfl

/-- KDthat vs Dthat diverge when the description misfits.
KDthat: "that [pointing at Jones] — the man with the martini" → Jones.
Dthat: "dthat[the man with the martini]" → whoever actually satisfies it.
When Jones is drinking water, these pick out different individuals.

This is the formal core of argument that Donnellan's
referential use is a genuinely different mechanism from Kaplan's
rigidification-by-description. -/
theorem kdthat_dthat_diverge {W E : Type*}
    (loaded : E) (guide : E → W → Prop)
    (desc : Intension W E) (cW : W)
    (hMisfit : desc cW ≠ loaded) :
    kdthat loaded guide ≠ dthatW desc cW := by
  intro heq
  exact hMisfit (congrFun heq cW).symm

/-- A KDthat-expression as a `ReferringExpression`: referential use only.

The profile is `refDescProfile` ⟨F, F, T⟩ because in's
framework, the expression (description) is not de jure rigid — the rigidity
comes from the speaker's cognitive fix on the loaded referent, not from
the expression's linguistic type. Per §2.12, Donnellan gives a
"proposition-free account" (no singular proposition content).

Contrast with `dthatExpression`, which has `dthatProfile` ⟨T, F, F⟩:
dthat is de jure rigid by linguistic mechanism, without referential use. -/
def kdthatExpression {C W E : Type*} (loaded : E) (guide : E → W → Prop) :
    ReferringExpression C W E :=
  { character := λ _ => kdthat loaded guide
  , profile := refDescProfile }

/-- KDthat-expressions are de facto rigid: their content is rigid (because
the loaded referent is fixed), but the designation mechanism is not what
secures rigidity — the cognitive fix does.

Contrast with `dthat_deJureRigid`: dthat is de jure rigid (rigid by
linguistic mechanism + designation=true). KDthat is de facto rigid
(rigid content + designation=false). This formalizes the core of
distinction between designation and referential use
as independent sources of world-invariance. -/
theorem kdthat_deFactoRigid {C W E : Type*} (loaded : E) (guide : E → W → Prop)
    (c : C) :
    Semantics.Reference.Basic.IsDeFactoRigid
      (kdthatExpression (C := C) loaded guide) c :=
  ⟨rigid_isRigid loaded, rfl⟩

/-! ## Informativeness Is Not Semantic (Ch 4, §2)

dissolution of the Frege puzzle. The informativeness of
"Cicero = Tully" is NOT a semantic fact — it is a cognitive/relational fact,
depending on the thinker's partial information database. Semantically, the
two names contribute identical content (proven below). Any difference in
cognitive significance must be extra-semantic: relative to the thinker's
historically incomplete knowledge of which loaded names track back to
which objects. -/

/-- Co-referential rigid designators have identical content.
Since rigid intensions are constant functions, co-reference at any one
world entails identity everywhere. The informativeness of "Hesperus =
Phosphorus" cannot come from the *semantics* (the contents are the same);
it must come from the *cognitive* relation between the thinker and the
two names. -/
theorem informativeness_not_semantic {W E : Type*}
    (t₁ t₂ : Intension W E)
    (hRig₁ : IsRigid t₁) (hRig₂ : IsRigid t₂)
    (w : W) (hCoref : t₁ w = t₂ w) :
    t₁ = t₂ := by
  ext w'
  exact (hRig₁ w' w).trans (hCoref.trans (hRig₂ w w'))

/-- Direct reference assigns the same proposition to "P(a)" and "P(b)"
when a and b are co-referential rigid designators.

This is the "full stop" of what direct reference theory delivers
(Ch 2, §2.1). Whether the proposition is *necessary*
requires the independent metaphysical doctrine of modal haecceitism.
Whether an agent *believes* it requires an independent theory of attitude
verb semantics. The reference theory is silent on both. -/
theorem dr_same_proposition {W E : Type*}
    (t₁ t₂ : Intension W E) (P : E → W → Bool)
    (hRig₁ : IsRigid t₁) (hRig₂ : IsRigid t₂)
    (w : W) (hCoref : t₁ w = t₂ w) :
    (λ w' => P (t₁ w') w') = (λ w' => P (t₂ w') w') := by
  rw [informativeness_not_semantic t₁ t₂ hRig₁ hRig₂ w hCoref]

/-! ## The Dual Semantic Function of Nominals (Ch 4, §4.1)

extends @cite{donnellan-1966}'s referential/attributive
distinction beyond definite descriptions to ALL nominals. Every nominal
— proper name, bare plural, Det+CN phrase — has two potential semantic
functions: pre-nominal (reference already established) and nominal (the
noun originates the reference). The duality is *semantic*, not pragmatic
— it is "written into the very conventional rules governing these phrases"
(). -/

/-- The dual semantic function of nominals.
- `preNominal`: Reference preceded the nominal. The speaker already has
  the referent in mind; the noun merely expresses/conveys the link.
  "Bono" (when I've already seen him at the cheese section).
- `nominal`: The nominal originates the reference. It is essential to
  establishing the subject for subsequent predication.
  "A musician I met at Whole Foods" (introducing a new subject). -/
inductive NominalFunction where
  | preNominal
  | nominal
  deriving DecidableEq, Repr

/-- Donnellan's `UseMode` maps into the broader `NominalFunction`.
Referential use = pre-nominal (reference already established by
object-contact). Attributive use = nominal (the description originates
the reference). -/
def nominalFunctionOf : UseMode → NominalFunction
  | .referential => .preNominal
  | .attributive => .nominal

/-- KDthat encodes pre-nominal function: the `loaded` parameter records
that the referent was fixed before any nominal was deployed. -/
theorem kdthat_is_preNominal :
    nominalFunctionOf .referential = .preNominal :=
  rfl

/-! ## The Orthogonality of Mechanism and Content

deepest structural claim: the *mechanism* by which
reference is secured (designation, cognitive fix, etc.) and the *content*
that results (the intension, the proposition expressed) are orthogonal.
Same content can arise from different mechanisms; same mechanism can
produce different content.

Categorically, this is a commutativity diagram. Both `dthat` and `kdthat`
factor through `rigid : E → Intension W E`:

```
                      eval
    Desc × World ——————————→ E
         |                   |
         | dthat             | rigid
         |                   |
         v                   v
      Content ════════════ Content
         ^                   ^
         | kdthat            | rigid
         |                   |
    E × Guide ———— π₁ ————→ E
```

Both squares commute by construction (`dthat_factors`, `kdthat_factors`).
The outer rectangle commutes when `eval(desc, cW) = π₁(loaded, guide)`,
i.e., when `desc cW = loaded` — the `hMatch` hypothesis.

The content projection is a coequalizer of the two mechanism paths.
But the diagram does NOT lift to `ReferringExpression` (which carries
the profile): the profile projection distinguishes what the content
projection conflates. This non-liftability is `mechanism_content_orthogonality`. -/

/-- Dthat factors through `rigid`: `dthat = rigid ∘ eval`.

This is the top square of the commutativity diagram. The inside-out
mechanism first *evaluates* the description at the actual world to
obtain an entity, then *rigidifies* that entity. -/
theorem dthat_factors {W E : Type*} (desc : Intension W E) (cW : W) :
    dthatW desc cW = rigid (desc cW) :=
  rfl

/-- KDthat factors through `rigid`: `kdthat = rigid ∘ π₁`.

This is the bottom square of the commutativity diagram. The outside-in
mechanism *projects* the loaded entity (ignoring the guide), then
*rigidifies*. The factorization is trivial because `kdthat` is defined
as `rigid loaded`. -/
theorem kdthat_factors {W E : Type*} (loaded : E) (guide : E → W → Prop) :
    kdthat loaded guide = rigid loaded :=
  rfl

/-- **The Separation Theorem.** The content square commutes but the
profile square does not — mechanism and content are orthogonal.

When the inside-out evaluation (`desc cW`) and the outside-in cognitive
fix (`loaded`) converge on the same entity, both paths through `rigid`
produce the same content. But the referential profiles — which record
*how* reference was secured — differ: dthat has `⟨T, F, F⟩` (designation),
KDthat has `⟨F, F, T⟩` (referential use).

Categorically: the forgetful functor `π_content : ReferringExpression → Content`
is a coequalizer of the two mechanism paths, but the projection
`π_profile : ReferringExpression → ReferentialProfile` is NOT — it
distinguishes the two paths. The profile is genuinely new information
not recoverable from the content. -/
theorem mechanism_content_orthogonality {C W E : Type*}
    (loaded : E) (desc : Intension W E) (guide : E → W → Prop) (cW : W)
    (hMatch : desc cW = loaded) :
    -- Content square commutes (same intension)...
    (dthatExpression (C := C) desc cW).character =
      (kdthatExpression (C := C) loaded guide).character ∧
    -- ...but profile square does not (different mechanism)
    (dthatExpression (C := C) desc cW).profile ≠
      (kdthatExpression (C := C) loaded guide).profile := by
  constructor
  · -- Commutativity: both paths through `rigid` agree
    ext _ w
    simp only [dthatExpression, kdthatExpression, dthatW, kdthat, rigid, hMatch]
  · -- Non-commutativity: profiles distinguish the paths
    intro heq
    have : (dthatExpression (C := C) desc cW).profile.designation =
           (kdthatExpression (C := C) loaded guide).profile.designation :=
      congrArg ReferentialProfile.designation heq
    simp [dthatExpression, kdthatExpression, dthatProfile, refDescProfile] at this

/-! ## The Flow Diagram Reversal (Ch 1, §2.3)

recurring structural observation: in all four founding
fathers' work, the classical Fregean direction of semantic determination is
*reversed*. Classically, meaning (intension) determines denotation (extension)
— symbol → satisfaction → object. In the historical/referential account,
the object determines the reference — object → signal → loaded symbol.

The mathematical content of this reversal is a **section-retraction pair**:
`rigid : E → Intension W E` is a section (right inverse) of world-evaluation
`evalAt · w : Intension W E → E`.

- `evalAt w ∘ rigid = id` (`rigid_section`): The historical chain
  (object → loaded name → evaluation) is lossless.
- `rigid ∘ evalAt w ≠ id` on non-rigid intensions (`rigid_evalAt_lossy`):
  The Fregean direction (intension → evaluate → re-embed) is lossy —
  it discards world-variation.

This makes `E` a **retract** of `Intension W E`. The image of `rigid` —
the rigid intensions — is isomorphic to `E`. Non-rigid intensions (descriptions)
live in the ambient space but collapse under the retraction.

Consequences already formalized in this module:
- `dthat_factors` / `kdthat_factors`: Both paths factor through the section `rigid`
- `informativeness_not_semantic`: The retraction annihilates modal information,
  so informativeness cannot be a semantic property of the retracted content
- `mechanism_content_orthogonality`: The retraction coequalizes the two mechanism
  paths, but the profile is not in the retracted image -/

/-- The flow diagram reversal as a retraction: `evalAt w ∘ rigid = id`.

Ch 1, §2.3: "this reversal of the flow diagram is a
pattern that recurs in all four founding fathers' works on direct reference."
Kripke's reversal for names (Ch 1), Donnellan's for descriptions (Ch 3),
Kaplan's for demonstratives (Ch 2), Putnam's for common nouns (Ch 4). -/
theorem flowDiagramReversal {W E : Type*} (w : W) :
    (fun (x : E) => evalAt (rigid (W := W) x) w) = id :=
  rigid_section w

/-- The Fregean direction is lossy: non-rigid intensions (descriptions)
cannot survive the round-trip through entity.

This is the mathematical content of "no entailments"
thesis: once you project to the retracted image (rigid intensions / entities),
the modal information that lived in the ambient intension space is gone.
"The man drinking a martini" varies across worlds; `rigid (desc w)` does not.
The retraction annihilates the very information that would distinguish
de re from de dicto readings. -/
theorem fregeDirectionLossy {W E : Type*}
    (desc : Intension W E) (w : W) (hVaries : ¬ IsRigid desc) :
    rigid (desc w) ≠ desc :=
  rigid_evalAt_lossy desc w hVaries

/-! ## The Russell-Partee-Kaplan Challenge (Ch 4, §3)

formulation of the RPK impossibility: three natural
desiderata for a global semantics of nominals cannot all be satisfied
simultaneously. Each of the three historical waves of logical reformers
sacrifices exactly one.

The three desiderata:
1. **Syntactic faithfulness**: Preserve the visible subject-predicate grammar.
   "John is wise" and "Every philosopher is wise" have the same form.
2. **Semantic faithfulness**: Subject terms *refer* to entities (type `E`),
   not to constructed denotations (sets-of-properties, GQs, etc.).
3. **Uniform composition**: The same compositional mechanism handles all
   subject-predicate constructions.

The impossibility arises because referential subjects (type `E`) and
quantificational subjects (type `(E → Prop) → Prop`) have incompatible
types. Uniform composition requires a single subject type; semantic
faithfulness requires it to be `E`; but quantifiers cannot be entities.

The three waves each sacrifice one desideratum:
- Russell 1905: Drops syntactic faithfulness (invisible logical form)
- Montague 1970: Drops semantic faithfulness (type-lifts `E` to GQ)
- Direct reference (Almog): Drops uniform composition (dual semantic function) -/

/-- The three desiderata of the Russell-Partee-Kaplan challenge. -/
inductive RPKDesideratum where
  /-- Preserve visible subject-predicate grammar -/
  | syntacticFaith
  /-- Subject terms refer to entities (not constructed denotations) -/
  | semanticFaith
  /-- Same composition for all subject-predicate structures -/
  | uniformComp
  deriving DecidableEq, Repr

/-- A semantic approach: satisfies some subset of the three desiderata. -/
structure RPKApproach where
  satisfies : RPKDesideratum → Bool

/-- Russell 1905: Drop visible grammar, keep referential semantics +
uniform composition. "Every philosopher is wise" gets invisible logical
form `∀x(P(x) → W(x))`. -/
def russell : RPKApproach :=
  { satisfies := fun
    | .syntacticFaith => false
    | .semanticFaith => true
    | .uniformComp => true }

/-- Montague 1970: Keep visible grammar + uniform composition, sacrifice
referential semantics. "John" is type-lifted from `E` to `(E → Prop) → Prop`
via the Montague lift (= `TypeShifting.lift`). -/
def montague : RPKApproach :=
  { satisfies := fun
    | .syntacticFaith => true
    | .semanticFaith => false
    | .uniformComp => true }

/-- Direct reference (): Keep visible grammar + referential
semantics, sacrifice uniform composition. "John" and "every philosopher"
have different semantic functions (pre-nominal vs nominal). -/
def directRef : RPKApproach :=
  { satisfies := fun
    | .syntacticFaith => true
    | .semanticFaith => true
    | .uniformComp => false }

/-- Each of the three historical approaches sacrifices exactly one
desideratum. No approach satisfies all three. -/
theorem rpk_each_sacrifices_one :
    russell.satisfies .syntacticFaith = false ∧
    montague.satisfies .semanticFaith = false ∧
    directRef.satisfies .uniformComp = false :=
  ⟨rfl, rfl, rfl⟩

/-- Each approach satisfies the other two desiderata. -/
theorem rpk_each_keeps_two :
    russell.satisfies .semanticFaith = true ∧ russell.satisfies .uniformComp = true ∧
    montague.satisfies .syntacticFaith = true ∧ montague.satisfies .uniformComp = true ∧
    directRef.satisfies .syntacticFaith = true ∧ directRef.satisfies .semanticFaith = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The type-theoretic content of the RPK impossibility: referential subjects
have type `E`, quantificational subjects have type `(E → Prop) → Prop`.
The Montague lift `fun e P => P e` embeds the former into the latter, but
it is injective-not-surjective: not every GQ arises from an entity.

This means the lift is a genuine sacrifice — "John" is no longer type `E`
but a constructed object of type `(E → Prop) → Prop`.

Bridge to `TypeShifting.lift`: this is the same operation as Partee's
type-raising `lift(j) = λP. P(j)`. -/
def rpkLift {E : Type*} (e : E) : (E → Prop) → Prop := fun P => P e

/-- The RPK lift is injective: distinct entities give distinct GQs. -/
theorem rpkLift_injective {E : Type*} :
    Function.Injective (rpkLift (E := E)) := by
  intro a b hab
  have h : rpkLift b (· = a) := by rw [← hab]; exact rfl
  exact h.symm

/-- The RPK lift is NOT surjective in general: the universal quantifier
`fun P => ∀ x, P x` is a GQ that is not in the image of the lift
(assuming `E` has at least 2 elements).

This is the type-theoretic witness of the RPK impossibility: Montague's
uniform composition requires all subjects to be GQs, but not all GQs
are referential. The gap between `E` and `(E → Prop) → Prop` is real. -/
theorem rpkLift_not_surjective {E : Type*} (a b : E) (hab : a ≠ b) :
    ¬ ∃ e : E, rpkLift e = (fun P => ∀ x, P x) := by
  intro ⟨e, he⟩
  apply hab
  have h := congrFun he (fun x => x = e)
  dsimp [rpkLift] at h
  -- h : (e = e) = (∀ x, x = e)
  have hall : ∀ x, x = e := cast h rfl
  exact (hall a).trans (hall b).symm

/-- **The RPK Impossibility Theorem.** If:
(1) Subject terms denote entities (type `E`) — *semantic faithfulness*
(2) Composition is uniform: sentence meaning = `P(subject)` — *uniform composition*
then no entity can serve as the subject of "Every φ is ψ" — *syntactic
faithfulness* fails for quantificational sentences.

The proof: if the subject is `e : E` and composition is function application,
the sentence meaning is `fun P => P e`. But by `rpkLift_not_surjective`, the
universal quantifier `fun P => ∀ x, P x` is not in the image of this map
(assuming `E` has ≥ 2 elements). Therefore "Every philosopher is wise" cannot
be given a subject-predicate semantics in this framework.

This is the formal core of RPK challenge (Ch 4, §3):
all three desiderata cannot be satisfied simultaneously. -/
theorem rpk_impossibility {E : Type*} (a b : E) (hab : a ≠ b) :
    ¬ ∃ e : E, (fun P : E → Prop => P e) = (fun P => ∀ x, P x) :=
  rpkLift_not_surjective a b hab

end Semantics.Reference.Almog2014
