import Linglib.Fragments.ASL.Height
import Linglib.Theories.Semantics.Quantification.DomainRestriction

/-!
# @cite{davidson-gagne-2022}

Davidson, K. & Gagné, D. (2022). "More is up" for domain restriction in ASL.
*Semantics & Pragmatics* 15, Article 1: 1–52.

## Core Argument

In ASL, vertical height in signing space overtly marks the size of the
quantifier domain. When FS(ALL) is signed at neutral height, it quantifies
over the contextually supplied domain (e.g., friends who watched the movie).
When signed higher, it quantifies over a wider domain (e.g., everyone in
the world). This is not a gestural expression of surprise or emphasis —
it is a **grammatical** mechanism that enters through pronominal elements
(IX-arc) and composes with quantifiers via a partitive-like restrictor
structure.

## Key Claims Formalized

1. **Height = domain size** (§5.2): Vertical ordering on loci corresponds to
   mereological part-hood on domains. Formalized via `HeightDDRP` as a
   `NestedRestriction`, giving all monotonicity theorems free.

2. **Monotonicity contrast** (§4): ALL and NONE are ↓MON in the restrictor
   (smaller domain → easier to satisfy), SOME is ↑MON (larger domain →
   easier to satisfy). Height affects domain size uniformly, but truth
   conditions react differently depending on the quantifier's monotonicity.

3. **Height ≠ intensification** (§4, after ex. 36): If height were merely
   emphatic strengthening, then higher SOME should be *harder* to satisfy
   (stronger). But higher SOME is *easier* to satisfy (wider domain for
   the existential witness). This rules out the emphasis analysis.

4. **Only pronominal structures** (§3.3): Bare nouns cannot be height-marked
   because they lack a pronominal argument position. Height requires IX-arc
   (overt or incorporated).

5. **Structural parallel to cognitive DDRPs** (§5): ASL height (overt,
   modality-specific) and @cite{ritchie-schiller-2024}'s spatial heuristics
   (covert, modality-general) are both instances of `NestedRestriction` — the
   same abstract nesting structure produces the same formal predictions.

## Compositional Grounding

Truth conditions derive from `every_restricted` / `some_restricted` /
`no_restricted` (DomainRestriction.lean), which wrap `every_sem` / `some_sem`
/ `no_sem` (Quantifier.lean) with a height-indexed domain predicate. Nesting
theorems derive from `DDRP.every_nesting` / `DDRP.some_nesting` /
`DDRP.no_nesting`, connecting height ordering to restrictor monotonicity.

## Not formalized here

- **Directional verbs** (§3): verb height marking analyzed as pronominal
  incorporation. The semantic contribution is the same height-indexed domain
  restriction; the morphological incorporation mechanism is left to
  @cite{ahn-kocab-davidson-2026} (which postdates this paper and CAN
  reference it).
- **Comparison with *irgendein*** (§5.4): @cite{davidson-gagne-2022} argue
  that ASL height-based domain widening is structurally different from
  German *irgend-* (@cite{kratzer-shimoyama-2002}): height is on pronouns
  (not determiners), gradient (not binary), and restricted to pronominal
  structures. Documented here but not formalized as a cross-fragment theorem.
- **Cross-linguistic parallels** (§6.2): JSL (ex. 54: chest→cheek→forehead
  for class→school→prefecture) and Nicaraguan Sign Language (ex. 55:
  TODO-mid vs TODO-high for local vs national scope) show the same pattern.
  Placeholder theorems are `sorry`-marked for future fragment work.
-/

set_option autoImplicit false

namespace DavidsonGagne2022

open Core.IntensionalLogic (Frame)
open Semantics.Quantification.Quantifier (every_sem some_sem)
open Semantics.Quantification.DomainRestriction
open Fragments.ASL.Height

-- ============================================================================
-- §1. Domain Types: Vampire Scenario
-- ============================================================================

/-! The running example from @cite{davidson-gagne-2022} §1:

    Context: "Last night I watched a movie with my friends about vampires.
    Afterwards I went to bed and I dreamt that..."

    FS(ALL)-neutral BECOME VAMPIRE → 'All of my friends became vampires'
    FS(ALL)-high BECOME VAMPIRE → 'All of the people in the world became vampires'
-/

/-- Entities in the vampire scenario.
    - `f1`–`f4`: friends who watched the movie (contextual domain)
    - `p5`–`p6`: people in the wider world (outside contextual domain) -/
inductive Entity where
  | f1 | f2 | f3 | f4  -- friends
  | p5 | p6             -- wider world
  deriving DecidableEq, Repr, Inhabited

abbrev vampireModel : Frame := { Entity := Entity, Index := Unit }

instance : Fintype Entity where
  elems := {Entity.f1, .f2, .f3, .f4, .p5, .p6}
  complete := λ x => by cases x <;> simp

-- ============================================================================
-- §2. Height Assignment & DDRP
-- ============================================================================

/-- Height assignment: friends are in the neutral (default) domain,
    wider-world individuals require high signing. -/
def vampireZone : Entity → VerticalHeight
  | .f1 | .f2 | .f3 | .f4 => .neutral
  | .p5 | .p6 => .high

/-- DDRP for the vampire scenario, derived from the height assignment.
    neutral-domain = {f1, f2, f3, f4}, high-domain = everyone. -/
abbrev vampireDDRP : HeightDDRP Entity := heightToDDRP vampireZone

-- ============================================================================
-- §3. World States
-- ============================================================================

/-- World states: who became vampires in the dream.
    - `friendsOnly`: only friends (f1–f4) became vampires
    - `allVampires`: everyone became vampires -/
inductive World where
  | friendsOnly
  | allVampires
  deriving DecidableEq, Repr, Inhabited

instance : Fintype World where
  elems := ({World.friendsOnly, World.allVampires} : Finset World)
  complete := λ x => by cases x <;> simp

def becameVampire : World → Entity → Bool
  | .allVampires, _ => true
  | .friendsOnly, .f1 | .friendsOnly, .f2 => true
  | .friendsOnly, .f3 | .friendsOnly, .f4 => true
  | .friendsOnly, _ => false

-- ============================================================================
-- §4. Truth Tables: "FS(ALL) BECOME VAMPIRE" Under Height
-- ============================================================================

/-- Truth of "all [of them] became vampires" under a height-indexed domain.
    Uses `vampireZone e ≤ h` directly (definitionally equal to
    `e ∈ vampireDDRP.region h`) for `Decidable` transparency. -/
abbrev fsAllBecomeVampire (h : VerticalHeight) (w : World) : Prop :=
  ∀ e : Entity, vampireZone e ≤ h → becameVampire w e = true

-- Neutral height: quantifies over friends only.
theorem all_neutral_friendsOnly : fsAllBecomeVampire .neutral .friendsOnly := by
  decide
theorem all_neutral_allVampires : fsAllBecomeVampire .neutral .allVampires := by
  decide

-- High height: quantifies over everyone.
theorem all_high_friendsOnly : ¬ fsAllBecomeVampire .high .friendsOnly := by
  decide
theorem all_high_allVampires : fsAllBecomeVampire .high .allVampires := by
  decide

/-- **D&G's core observation**: At neutral height, "all became vampires"
    is true when only friends became vampires (domain = friends). At high
    height, it is false — the domain includes everyone, and not everyone
    became a vampire. Same sentence, different height, different truth value. -/
theorem height_disambiguates :
    fsAllBecomeVampire .neutral .friendsOnly ∧
    ¬ fsAllBecomeVampire .high .friendsOnly :=
  ⟨all_neutral_friendsOnly, all_high_friendsOnly⟩

-- ============================================================================
-- §5. Existential Quantifier: "SOME BECOME VAMPIRE"
-- ============================================================================

/-- Truth of "some [of them] became vampires" under a height-indexed domain. -/
abbrev someBecomeVampire (h : VerticalHeight) (w : World) : Prop :=
  ∃ e : Entity, vampireZone e ≤ h ∧ becameVampire w e = true

-- SOME is true under both heights when friends are vampires.
theorem some_neutral_friendsOnly : someBecomeVampire .neutral .friendsOnly := by
  decide
theorem some_high_friendsOnly : someBecomeVampire .high .friendsOnly := by
  decide

-- ============================================================================
-- §5b. Negative Quantifier: "NONE BECOME VAMPIRE"
-- ============================================================================

/-! @cite{davidson-gagne-2022} §4 (ex. 33–35) discuss NONEsym, showing the
    same height-domain pattern. NONEsym-neutral = "none of my immediate
    family", NONEsym-high = "none of my entire family including ancestors,
    distant relations, etc." NONE is ↓MON in the restrictor, like ALL. -/

/-- Truth of "none [of them] became vampires" under a height-indexed domain. -/
abbrev noneBecomeVampire (h : VerticalHeight) (w : World) : Prop :=
  ∀ e : Entity, vampireZone e ≤ h → becameVampire w e = false

-- NONE-neutral in friendsOnly world: false (friends DID become vampires)
theorem none_neutral_friendsOnly : ¬ noneBecomeVampire .neutral .friendsOnly := by
  decide
-- NONE-neutral in allVampires world: false (friends became vampires)
theorem none_neutral_allVampires : ¬ noneBecomeVampire .neutral .allVampires := by
  decide
-- NONE-high in friendsOnly world: false (friends in domain, became vampires)
theorem none_high_friendsOnly : ¬ noneBecomeVampire .high .friendsOnly := by
  decide

-- ============================================================================
-- §6. Nesting from DDRP Structure (Zero New Proofs)
-- ============================================================================

/-- ⟦every⟧ nesting: truth under a higher height entails truth under any
    lower height. Smaller domain → fewer entities to check → universal easier.
    Direct application of `DDRP.every_nesting`. -/
theorem every_height_nesting {h₁ h₂ : VerticalHeight} (hle : h₁ ≤ h₂)
    (R S : vampireModel.Entity → Prop) :
    every_restricted vampireModel (vampireDDRP.region h₂) R S →
    every_restricted vampireModel (vampireDDRP.region h₁) R S :=
  DDRP.every_nesting (m := vampireModel) vampireDDRP R S hle

/-- ⟦some⟧ nesting: truth under a lower height entails truth under any
    higher height. Larger domain → more witnesses → existential easier.
    Direct application of `DDRP.some_nesting`. -/
theorem some_height_nesting {h₁ h₂ : VerticalHeight} (hle : h₁ ≤ h₂)
    (R S : vampireModel.Entity → Prop) :
    some_restricted vampireModel (vampireDDRP.region h₁) R S →
    some_restricted vampireModel (vampireDDRP.region h₂) R S :=
  DDRP.some_nesting (m := vampireModel) vampireDDRP R S hle

/-- ⟦no⟧ nesting: truth under a higher height entails truth under any
    lower height. Same direction as ⟦every⟧ (both ↓MON in the restrictor).
    Direct application of `DDRP.no_nesting`. -/
theorem no_height_nesting {h₁ h₂ : VerticalHeight} (hle : h₁ ≤ h₂)
    (R S : vampireModel.Entity → Prop) :
    no_restricted vampireModel (vampireDDRP.region h₂) R S →
    no_restricted vampireModel (vampireDDRP.region h₁) R S :=
  DDRP.no_nesting (m := vampireModel) vampireDDRP R S hle

/-- **Monotonicity contrast**: ALL and SOME react oppositely to height.
    In the friendsOnly world, ALL is true only under neutral height
    (↓MON: smaller domain helps), while SOME is true under both heights
    (↑MON: larger domain never hurts). -/
theorem monotonicity_contrast :
    fsAllBecomeVampire .neutral .friendsOnly ∧
    ¬ fsAllBecomeVampire .high .friendsOnly ∧
    someBecomeVampire .neutral .friendsOnly ∧
    someBecomeVampire .high .friendsOnly :=
  ⟨all_neutral_friendsOnly, all_high_friendsOnly,
   some_neutral_friendsOnly, some_high_friendsOnly⟩

-- ============================================================================
-- §7. Height ≠ Intensification
-- ============================================================================

/-! @cite{davidson-gagne-2022} §4 (after ex. 36) argue that height is not
    merely emphatic strengthening. The critical evidence comes from existential
    quantifiers: if height strengthened the utterance, higher SOME should impose
    *stronger* truth conditions (harder to satisfy). But higher SOME is *easier*
    to satisfy — a wider domain provides more potential witnesses.

    For universal and negative quantifiers, both strengthening and domain
    widening make the same prediction (wider domain → stronger statement).
    But for existentials, they diverge: strengthening predicts harder, domain
    widening predicts easier. The data favor domain widening. -/

/-- Height widens existential domain: SOME-high is at least as easy to
    satisfy as SOME-neutral. If height were intensification, the opposite
    would hold for existentials. This is the formal refutation. -/
theorem some_height_widens (R S : vampireModel.Entity → Prop) :
    some_restricted vampireModel (vampireDDRP.region .neutral) R S →
    some_restricted vampireModel (vampireDDRP.region .high) R S :=
  some_height_nesting (by decide : VerticalHeight.neutral ≤ .high) R S

-- ============================================================================
-- §8. Bare Nouns Cannot Be Height-Marked
-- ============================================================================

/-! @cite{davidson-gagne-2022} §3.3 (ex. 27): bare nouns like DOG cannot be
    signed higher to convey domain widening. This is predicted by the
    pronominal analysis: height modifies IX-arc (a pronoun), not the
    noun directly. Nouns lack an unsaturated pronominal argument position.

    Structurally: `HeightDDRP` is a parameter of the pronominal/quantifier
    denotation, not of the noun denotation. A bare noun `dog : Entity → Bool`
    has no slot for a `HeightDDRP` argument. Domain restriction enters only
    via the pronominal restrictor: FS-ALL-of-[IX-arc-height].

    This is a type-level observation: the type signature of the quantifier
    (`HeightDDRP Entity → VerticalHeight → ...`) vs. the bare noun
    (`Entity → Bool`) enforces the restriction structurally. No theorem
    is needed — the compiler rejects ill-typed compositions. -/

/-- A height-restricted quantifier: takes a HeightDDRP argument.
    The pronominal restrictor (IX-arc) provides the domain; the quantifier
    quantifies over it. Bare nouns (type `Entity → Bool`) cannot supply
    the `ddrp` or `h` arguments — height is enforced by the type system. -/
def heightRestrictedAll (ddrp : HeightDDRP Entity) (h : VerticalHeight)
    (S : Entity → Prop) : Prop :=
  ∀ e : Entity, (ddrp.region h) e → S e

-- ============================================================================
-- §9. Bridge: Height ≅ Spatial Scale (NestedRestriction Unification)
-- ============================================================================

/-! Both @cite{davidson-gagne-2022}'s height-based domain restriction and
    @cite{ritchie-schiller-2024}'s cognitive DDRP framework instantiate
    `Core.NestedRestriction`: a monotone family of predicates indexed by
    an ordered scale. The scale source differs — physical signing height
    (ASL, overt) vs. cognitive spatial proximity (spoken language, covert) —
    but the formal structure is identical.

    This means the monotonicity theorems proved once in `NestedRestriction`
    (`forall_nesting`, `exists_nesting`) give correct predictions for BOTH
    the cognitive heuristic theory (SpatialScale) and the ASL height theory
    (VerticalHeight) with zero duplication. -/

/-- Any entity in a height-DDRP region is also in the corresponding
    spatial-DDRP region when domains are aligned (i.e., the height zone
    maps into the spatial zone). This shows the two scale systems compose:
    an entity's signing-height visibility entails its spatial-region
    visibility whenever the modalities agree on the entity's position. -/
theorem height_spatial_compose
    {E : Type*}
    (heightDDRP : HeightDDRP E) (spatialDDRP : DDRP SpatialScale E)
    (align : ∀ e, e ∈ heightDDRP.region .neutral →
                   e ∈ spatialDDRP.region .peripersonal)
    {e : E} (h : e ∈ heightDDRP.region .neutral) :
    e ∈ spatialDDRP.region .peripersonal :=
  align e h

/-- The nesting property is uniform across all `NestedRestriction` instances:
    height-DDRP nesting and spatial-DDRP nesting are both instances of the
    same abstract monotonicity. This is the formal content of the claim
    that ASL height and cognitive spatial heuristics are "the same structure." -/
theorem uniform_nesting
    {E : Type*}
    (heightDDRP : HeightDDRP E)
    (spatialDDRP : DDRP SpatialScale E) :
    -- Height nesting: neutral ⊆ high
    (∀ e, e ∈ heightDDRP.region .neutral →
          e ∈ heightDDRP.region .high) ∧
    -- Spatial nesting: peripersonal ⊆ action
    (∀ e, e ∈ spatialDDRP.region .peripersonal →
          e ∈ spatialDDRP.region .action) :=
  ⟨λ e h => heightDDRP.monotone (by decide) e h,
   λ e h => spatialDDRP.monotone (by decide) e h⟩

-- ============================================================================
-- §10. Cross-Linguistic Support
-- ============================================================================

/-! @cite{davidson-gagne-2022} §6.2 reports parallel height-domain mappings
    in other sign languages:

    **JSL** (ex. 54): "There is/was nobody from a deaf family in my {class /
    school / (prefecture of) Wakayama}." Height levels @chest < @cheek <
    @forehead correspond to class ⊂ school ⊂ prefecture.

    **Nicaraguan Sign Language** (ex. 55): TODO-mid = "all [of us here]" vs
    TODO-high = "all [of Nicaragua]".

    These data suggest that the height-domain mapping may be a universal
    tendency in sign languages, possibly grounded in the MORE IS UP
    conceptual metaphor. Full formalization awaits dedicated JSL and
    LSN fragments. -/

-- ============================================================================
-- §11. Partitive Composition: Grounding Truth Tables (§5.3, eqs. 50–51)
-- ============================================================================

/-! @cite{davidson-gagne-2022} §5.3 derives quantifier truth conditions
    through the partitive type function ⟦of⟧ = λxλy. y ≤ x:

    1. IX-arc-h denotes discourse referent z with height presuppositions
    2. ⟦of⟧ z = `Set.Iic z` = {y | y ≤ z} — the parts of z
    3. FS-ALL(`Set.Iic z`)(Q) = ∀x ∈ Set.Iic z, Q x

    The theorems `partitive_neutral_subset` and `partitive_high_superset`
    (in `Height.lean`) show that the presuppositions encode exactly
    `Set.Iic z ⊆ C` (neutral) and `C ⊆ Set.Iic z` (high).

    The DDRP region `vampireDDRP.region h` serves as the computational
    implementation of `Set.Iic z_h` — see `partitive_ddrp_equiv`
    for the abstract alignment theorem. The theorems below close the
    grounding gap by showing that the stipulative truth tables
    (`fsAllBecomeVampire`, `someBecomeVampire`) agree with the composed
    meaning using `every_restricted` / `some_restricted` from the
    theory layer. -/

/-- FS-ALL composed through the theory-layer quantifier `every_restricted`.
    The DDRP region at height h serves as the domain restrictor C,
    matching the partitive path where `Set.Iic z` restricts the
    quantifier to parts of the discourse referent.

    After the Bool→Prop conversion, `fsAllBecomeVampire` and `fsAllComposed`
    are definitionally equivalent: both express `∀ e, e ∈ region h → ...`.
    The grounding theorem below witnesses this structural alignment. -/
def fsAllComposed (h : VerticalHeight) (w : World) : Prop :=
  every_restricted vampireModel (vampireDDRP.region h)
    (λ _ => True) (λ e => becameVampire w e = true)

/-- SOME composed through the theory-layer quantifier `some_restricted`. -/
def fsSomeComposed (h : VerticalHeight) (w : World) : Prop :=
  some_restricted vampireModel (vampireDDRP.region h)
    (λ _ => True) (λ e => becameVampire w e = true)

/-- **Grounding theorem**: `fsAllBecomeVampire` agrees with the
    compositionally-derived `fsAllComposed`. After the Bool→Prop conversion,
    both are `∀ e, e ∈ region h → becameVampire w e = true` (modulo
    a vacuous `True` restrictor), so the proof is structural. -/
theorem fsAll_grounding (h : VerticalHeight) (w : World) :
    fsAllBecomeVampire h w ↔ fsAllComposed h w := by
  simp only [fsAllBecomeVampire, fsAllComposed, every_restricted, every_sem]
  constructor
  · intro hall x ⟨hC, _⟩; exact hall x hC
  · intro hall x hC; exact hall x ⟨hC, trivial⟩

/-- **Grounding theorem for SOME**: `someBecomeVampire` agrees with
    `some_restricted` from the theory layer. -/
theorem fsSome_grounding (h : VerticalHeight) (w : World) :
    someBecomeVampire h w ↔ fsSomeComposed h w := by
  simp only [someBecomeVampire, fsSomeComposed, some_restricted, some_sem]
  constructor
  · intro ⟨e, hC, hS⟩; exact ⟨e, ⟨hC, trivial⟩, hS⟩
  · intro ⟨e, ⟨hC, _⟩, hS⟩; exact ⟨e, hC, hS⟩

end DavidsonGagne2022
