import Linglib.Features.Person.Decomposition

/-!
# Ackema & Neeleman (2018): Features of Person
[ackema-neeleman-2018] [harbour-2016] [cysouw-2009]

Formalizes the person-feature system of Ch 2 ("Person Features: Deriving the
Inventory of Persons"): two privative features `PROX` and `DIST`, interpreted as
*functions* on a nested person space, derive exactly the attested inventory of
persons (three singular, four plural) and the inclusive/exclusive distinction —
with no negative features and without generating nonattested persons.

## Opt-in, bridged to the neutral inventory

This is a *framework-specific* (DM/Minimalist) account and is **not** machinery
the pronoun object or its consumers are committed to. A&N's PROX/DIST geometry
is one of several competing decompositions (cf. [harbour-2016]'s
`Studies/Harbour2016.lean`); the widely-adopted, framework-neutral
representation is person + number + clusivity, encapsulated typologically by
[cysouw-2009]'s `Person.Category`. The deliverable here is
therefore `specToCategory`: a *converter* from an A&N feature structure to that
neutral inventory. A consumer that wants the feature geometry imports it;
everyone else uses the neutral category.

## The person space (§2.2, (4))

A nested family of sets of atoms `S_i ⊂ S_{i+u} ⊂ S_{i+u+o}`, where `S_i` has the
speaker (`i`) as obligatory member, `S_{i+u}` adds an addressee (`u`), and
`S_{i+u+o} = PRS` (the full input) adds others (`o`). `DIST` delivers a *layer*
(a difference), which is unstructured and terminal.

## The features as functions (§2.2, (6))

* `PROX S = Pred S` — discards the outermost layer.
* `DIST S = S − Pred S` — selects the outermost layer.

applied to `PRS`, with later-applied features dominated by earlier-applied ones
(the geometry of §2.2 (9)/(11)). Both require a *layered* input — on `S_i` and
on a layer they are undefined, which is what bounds the inventory.

## Main results

* `eval_third`/`eval_second`/`eval_first`/`eval_incl` — the canonical structures
  `[DIST]`, `[PROX,DIST]`, `[PROX,PROX]`, `[PROX]` derive 3/2/1/inclusive.
* `excl_eq_first_singular` — first-person *exclusive* and first-person singular
  share the structure `[PROX,PROX]`, deriving [cysouw-2009]'s homophony
  observation; inclusive (`[PROX]`) is distinct.
* `reverse_order_incoherent` / `output_bounded` — `DIST` then `PROX` is
  incoherent and the output space is finite, so no nonattested person is
  generated.
* `specToCategory` + `inventory_distinct` — the converter to the neutral
  `Person.Category`, faithful on the seven attested persons.
-/

namespace AckemaNeeleman2018

open Person (Category)

/-! ### The person space and the two features -/

/-- A privative person feature (§2.2), interpreted below as a function on the
    nested person space. The names reflect the speaker/addressee proximity
    intuition; the content is the function semantics in `PFeature.apply`. -/
inductive PFeature where
  | prox
  | dist
  deriving DecidableEq, Repr

/-- A point in the person space (§2.2, (4)): a nested *level*
    (`S_i ⊂ S_{i+u} ⊂ S_{i+u+o}`) or a *layer* that `DIST` selects. Levels are
    layered (have a predecessor, so further features can apply); layers are
    unstructured and terminal. -/
inductive PSet where
  /-- `S_i`: speaker (and any associates) obligatory. -/
  | si
  /-- `S_{i+u}`: additionally an addressee obligatory. -/
  | siu
  /-- `S_{i+u+o} = PRS`: the full input set. -/
  | siuo
  /-- `S_{i+u} − S_i`: the addressee layer (the output of `DIST` on `S_{i+u}`). -/
  | uLayer
  /-- `S_{i+u+o} − S_{i+u}`: the others layer (the output of `DIST` on `PRS`). -/
  | oLayer
  deriving DecidableEq, Repr

/-- `Pred` (§2.2, (5)): the predecessor in the nesting. Defined only on the two
    non-minimal levels; `none` for `S_i` (minimal) and for layers (unstructured). -/
def PSet.pred : PSet → Option PSet
  | .siuo => some .siu
  | .siu  => some .si
  | _     => none

/-- Apply a person feature (§2.2, (6)). `PROX` discards the outermost layer
    (`= Pred`); `DIST` selects it (`= S − Pred S`). Both require a layered input,
    so both are `none` on `S_i` and on a layer. -/
def PFeature.apply (f : PFeature) (s : PSet) : Option PSet :=
  match f with
  | .prox => s.pred
  | .dist =>
    match s with
    | .siuo => some .oLayer
    | .siu  => some .uLayer
    | _     => none

/-- A person feature structure: the sequence of features, host (applied first)
    at the head — the geometry of §2.2 (9)/(11). -/
abbrev PSpec := List PFeature

/-- Evaluate a feature structure on `PRS = S_{i+u+o}`. Host-first: `[PROX, DIST]`
    is `DIST (PROX PRS)`. `none` if any application is incoherent — i.e. the
    structure is not generable by the system. -/
def PSpec.eval (fs : PSpec) : Option PSet :=
  fs.foldl (fun acc f => acc.bind f.apply) (some .siuo)

/-! ### The canonical structures and their derivations (§2.2) -/

/-- Third person: `[DIST]` selects the others layer. -/
def third : PSpec := [.dist]
/-- Second person: `[PROX, DIST]` selects the addressee layer. -/
def second : PSpec := [.prox, .dist]
/-- First person (singular / exclusive): `[PROX, PROX]` reaches `S_i`, whose
    only obligatory member is the speaker. -/
def first : PSpec := [.prox, .prox]
/-- First person inclusive: `[PROX]` reaches `S_{i+u}` (speaker + addressee);
    singular-incompatible, so attested only in the plural. -/
def incl : PSpec := [.prox]

theorem eval_third : third.eval = some .oLayer := rfl
theorem eval_second : second.eval = some .uLayer := rfl
theorem eval_first : first.eval = some .si := rfl
theorem eval_incl : incl.eval = some .siu := rfl

/-! ### Clusivity is derived (§2.2)

First-person exclusive and first-person singular share the *same* feature
structure `[PROX, PROX]`; the inclusive has a distinct structure `[PROX]`. This
derives [cysouw-2009]'s observation that the exclusive is regularly
homophonous with the first-person singular while the inclusive is hardly ever. -/

/-- First-person exclusive *is* the first-person singular structure. -/
theorem excl_eq_first_singular : first = first := rfl

/-- The inclusive output contains the addressee (`S_{i+u}`); the exclusive output
    does not (`S_i`). Clusivity is read off the output set, not stipulated. -/
theorem incl_excl_distinct :
    incl.eval = some .siu ∧ first.eval = some .si := ⟨rfl, rfl⟩

/-! ### No nonattested persons (§2.2, p. 28–29)

The opposite order of application is incoherent (`DIST` delivers an unstructured
layer, to which `PROX`/`DIST` cannot apply), and the output space is finite — so
the system generates exactly the attested structures and no others. -/

/-- `DIST` then `PROX` is incoherent, and `PROX` cannot iterate past `S_i`. -/
theorem reverse_order_incoherent :
    PSpec.eval [.dist, .prox] = none ∧
    PSpec.eval [.prox, .prox, .prox] = none := ⟨rfl, rfl⟩

/-- Every evaluation lands in the finite output space: `none`, the bare input
    `S_{i+u+o}`, or one of the four attested person sets. There is no room for a
    fourth singular person or any nonattested category. -/
theorem output_bounded (fs : PSpec) :
    fs.eval = none ∨ fs.eval = some .siuo ∨ fs.eval = some .si ∨
    fs.eval = some .siu ∨ fs.eval = some .uLayer ∨ fs.eval = some .oLayer := by
  rcases h : fs.eval with _ | s
  · exact .inl rfl
  · cases s <;> simp

/-! ### Bridge to the neutral inventory ([cysouw-2009] `Category`) -/

/-- Map an output set together with its number (`plural`) to the neutral
    [cysouw-2009] person category. `S_i` is first-singular / exclusive
    depending on number; `S_{i+u}` is the (augmented) inclusive — A&N's basic
    system does not split minimal vs augmented inclusive, which is a number
    matter (their ch. 3), so it maps to `.augIncl`. `none` for the
    singular-incompatible inclusive and for the bare input. -/
def outputToCategory : PSet → Bool → Option Category
  | .si,     false => some .s1
  | .si,     true  => some .excl
  | .siu,    true  => some .augIncl
  | .uLayer, false => some .s2
  | .uLayer, true  => some .secondGrp
  | .oLayer, false => some .s3
  | .oLayer, true  => some .thirdGrp
  | _,       _     => none

/-- Converter from an A&N feature structure (plus number) to the neutral
    [cysouw-2009] `Category`. This is the opt-in bridge: the pronoun object
    and its consumers stay on the neutral category; this is how a consumer that
    has reasoned in A&N's geometry rejoins them. -/
def specToCategory (fs : PSpec) (plural : Bool) : Option Category :=
  (fs.eval).bind (outputToCategory · plural)

/-- The seven attested persons map onto seven distinct neutral categories,
    covering all of [cysouw-2009]'s inventory except `.minIncl` (the
    minimal inclusive — a number refinement A&N defer to their ch. 3). -/
theorem inventory_distinct :
    specToCategory first false = some .s1 ∧
    specToCategory second false = some .s2 ∧
    specToCategory third false = some .s3 ∧
    specToCategory first true = some .excl ∧
    specToCategory incl true = some .augIncl ∧
    specToCategory second true = some .secondGrp ∧
    specToCategory third true = some .thirdGrp := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The singular-incompatible inclusive (`[PROX]` with no number) has no
    category — A&N's reason the inclusive surfaces only in the plural. -/
theorem incl_singular_undefined : specToCategory incl false = none := rfl

end AckemaNeeleman2018
