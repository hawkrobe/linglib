import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Bare NPs as properties
[krifka-2004] [krifka-2003]

Krifka's analysis of bare NPs ("Bare NPs: Kind-referring, Indefinites, Both, or
Neither?", SALT 13 / EISS 5). Bare NPs are basically **properties**; context-sensitive
type shifts coerce them to kind or indefinite readings — so, in the title's terms,
*neither* kind-referring nor indefinite, but shiftable to both.

Count nouns carry a natural-number argument: `den w n x` reads "in `w`, the individual
`x` consists of `n` instances", and a count noun is an *additive extensive measure
function* in that argument (`IsExtensiveMeasure`). Number morphology saturates the
argument: the singular fills it with `1`, the semantic plural binds it existentially
with **no** `> 1` restriction (so the bare plural is true of a single instance —
"Do you have dogs? — Yes, one"). A bare singular count noun is therefore the wrong
type to be an argument — number-indexed `⟨n,⟨e,t⟩⟩`, not a predicate `⟨e,t⟩` — which is
why `*Dog barks` is out. Kind reference reuses [chierchia-1998]'s ∩ operator
(`Semantics.Kinds.NMP.down`), which Krifka adopts (§4.3), and requires topic position;
the existential shift applies at the surface position, deriving the narrow scope of
bare plurals and their wide scope under scrambling.

## Main declarations
* `CountNounDen`, `MassNounDen` — count (number-indexed) vs mass denotations
* `IsExtensiveMeasure` — the count noun's uniqueness + additivity laws
* `singularize`, `pluralize` — number morphology (fill `1` / bind `∃ n`)
* `availableInterpretations`, `kind_requires_topic` — topic-gating of kind reference
* `krifkaDerivScrambled`, `krifkaDerivUnscrambled` — the surface-position ∃-shift (built
  on the shared closure `NMP.existsClose`) used for the Dutch/German scrambling contrast
* `scope_follows_position` — scrambled and unscrambled derivations diverge
-/

namespace Krifka2004

open Semantics.Kinds.NMP (Individual existsClose)

/-! ### Count and mass denotations

`Atom` is `Type` (not `Type*`) to align with `NMP.Individual`, the Link/Chierchia
individual lattice (`Set Atom`) that this file reuses for kind reference. -/

section Denotations

variable {World Atom : Type}

/-- Count noun denotation `⟨s,⟨n,⟨e,t⟩⟩⟩`: `den w n x` holds iff in world `w` the
individual `x` consists of `n` instances. -/
abbrev CountNounDen (World Atom : Type) := World → ℕ → Individual Atom → Prop

/-- Mass noun denotation `⟨s,⟨e,t⟩⟩`: no number argument. -/
abbrev MassNounDen (World Atom : Type) := World → Individual Atom → Prop

/-- The basic type of a bare NP: a property `⟨s,⟨e,t⟩⟩`. -/
abbrev Property (World Atom : Type) := World → Individual Atom → Prop

/-- Count nouns are *additive extensive measure functions* in their number argument:
the count of an individual is unique, and the counts of disjoint individuals add. -/
def IsExtensiveMeasure (den : CountNounDen World Atom) : Prop :=
  (∀ w n m x, den w n x → den w m x → n = m) ∧
  (∀ w n m x y, den w n x → den w m y → Disjoint x y → den w (n + m) (x ∪ y))

/-! ### Number morphology -/

/-- Singular morphology fills the number argument with `1`. -/
def singularize (den : CountNounDen World Atom) : Property World Atom :=
  fun w x => den w 1 x

/-- Semantic plural morphology binds the number argument existentially, with **no**
`> 1` restriction — the analysis Krifka adopts over the rejected `∃ n > 1` variant. -/
def pluralize (den : CountNounDen World Atom) : Property World Atom :=
  fun w x => ∃ n, den w n x

/-- The bare plural is true of a single instance ("Do you have dogs? — Yes, one"):
this is why the plural cannot mean `∃ n > 1`. -/
theorem pluralize_of_singular (den : CountNounDen World Atom) {w : World}
    {x : Individual Atom} (h : den w 1 x) : pluralize den w x :=
  ⟨1, h⟩

/-- The bare-singular block is a *type* fact, not a stipulation. The only routes from
a number-indexed `CountNounDen` to an argument-type `Property` are the morphological
saturations `singularize` (fill `1`) and `pluralize` (bind `∃ n`); a bare singular
saturates nothing, so `*Dog barks` has no argument-type parse. -/
theorem morphology_saturates (den : CountNounDen World Atom) (w : World)
    (x : Individual Atom) :
    singularize den w x = den w 1 x ∧ pluralize den w x = (∃ n, den w n x) :=
  ⟨rfl, rfl⟩

end Denotations

/-! ### Type shifts and information structure -/

/-- The type shifts available to a property-denoting bare NP. -/
inductive TypeShift where
  /-- `∃` shift: `P ↦ λQ. ∃x[P(x) ∧ Q(x)]`. -/
  | existsShift
  /-- `ι` shift: `P ↦ ιx.P(x)`. -/
  | iota
  /-- `∩` (down) shift: `P ↦` kind. This is [chierchia-1998]'s operator
      (`Semantics.Kinds.NMP.down`), which Krifka adopts (§4.3). -/
  | down
  deriving DecidableEq, Repr

/-- Information-structure position of the bare NP. -/
inductive InfoStructure where
  | topic
  | focus
  | neutral
  deriving DecidableEq, Repr

/-- Shifts available at each position. Kind reference (`∩`) requires topic position;
elsewhere only the existential shift applies. -/
def availableInterpretations : InfoStructure → List TypeShift
  | .topic => [.down, .existsShift]
  | .focus => [.existsShift]
  | .neutral => [.existsShift]

/-- Kind reference requires topic position: the `∩` (down) shift is available only
when the bare NP is a topic. -/
theorem kind_requires_topic {p : InfoStructure}
    (h : TypeShift.down ∈ availableInterpretations p) : p = .topic := by
  cases p <;> simp_all [availableInterpretations]

/-! ### Surface-position ∃-shift (scrambling)

Krifka's existential type shift is a *local type repair* applied "as late, or as locally,
as possible" (§4.2) at the bare NP's surface position, so scope follows position: a bare
plural under negation scopes narrow, one raised above negation scopes wide. Built on the
shared closure `NMP.existsClose`, so Krifka's narrow reading is *definitionally*
Chierchia's DKP derivation (`NMP.chierchiaDerivUnscrambled`); the accounts diverge only
on the scrambled reading (compared in `Studies/LeBruynDeSwart2022.lean`). -/

section Scrambling

variable {Entity : Type*}

/-- Unscrambled `[niet [BP V]]`: ∃-shift below negation — `¬ ∃ x ∈ dom, P x ∧ Q x`
(narrow scope). Definitionally `NMP.chierchiaDerivUnscrambled`. -/
def krifkaDerivUnscrambled (dom : List Entity) (P Q : Entity → Prop) : Prop :=
  ¬ existsClose dom P Q

/-- Scrambled `[BP [niet V]]`: ∃-shift above negation — `∃ x ∈ dom, P x ∧ ¬ Q x`
(wide scope over negation). -/
def krifkaDerivScrambled (dom : List Entity) (P Q : Entity → Prop) : Prop :=
  existsClose dom P (fun x => ¬ Q x)

/-- **Scope follows position**: the scrambled (wide) and unscrambled (narrow) derivations
diverge on some model — witnessed by a two-element domain where one element satisfies the
predicate and the other does not. -/
theorem scope_follows_position :
    ∃ (Entity : Type) (dom : List Entity) (P Q : Entity → Prop),
      krifkaDerivScrambled dom P Q ≠ krifkaDerivUnscrambled dom P Q := by
  refine ⟨Bool, [true, false], fun _ => True, fun b => b = true, ?_⟩
  intro h
  have hs : krifkaDerivScrambled [true, false] (fun _ => True) (fun b => b = true) := by
    unfold krifkaDerivScrambled; decide
  rw [h] at hs
  have hu : ¬ krifkaDerivUnscrambled [true, false] (fun _ => True) (fun b => b = true) := by
    unfold krifkaDerivUnscrambled; decide
  exact hu hs

end Scrambling

end Krifka2004
