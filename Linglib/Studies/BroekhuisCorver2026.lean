module

public import Linglib.Fragments.Dutch.Adpositions
public import Linglib.Syntax.WordOrder
public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Linglib.Studies.Helmantel2002

/-!
# Broekhuis and Corver 2026: Dutch adpositions

Dutch adpositions are traditionally sorted into four classes by where they stand relative to their
complement: prepositions, postpositions, circumpositions, and intransitive adpositions. This file
formalizes the argument that the classification is epiphenomenal. Each class is the surface effect
of one movement rule inside the adpositional phrase. A complement is selected below the adposition
and raises to the specifier of a phrase-internal functional projection when the rule says so: a
nominal complement stays where it is selected unless the phrase is directional, while a
prepositional complement or an R-pronoun raises. A raised complement precedes the adposition, so
the phrase is head-final; an in-situ one follows it. Postpositions are then directional
prepositions with a raised complement, and circumpositions are postpositions whose complement is
itself a prepositional phrase, so that the first part of a circumposition is the head of the
raised complement and the second part is the head of the whole.

The same head direction settles extraction. Dutch resists preposition stranding, but an element
that precedes the adpositional head can leave the phrase, and precisely the complements that
raise precede it: R-pronouns and the complements of directional postpositions can be extracted,
ordinary nominal complements of prepositions cannot, and the complement of a circumposition
patterns with the prepositional case because it sits inside the raised prepositional phrase. An
R-pronoun never yields the postpositional order, since *de wandeling er op* 'the hike on it' has
only the locational reading, so a circumpositional phrase R-pronominalizes through its
prepositional complement, and under wh-movement the first part of a circumposition pied-pipes
alone, which shows that it heads a phrase.

The lexical generalizations are checked against the Dutch adposition fragment, which follows the
authors' grammar: the rule reproduces every recorded postpositional use from the path it denotes,
every circumposition of the grammar is a listed preposition followed by a listed postposition or
particle, every postposition but *af* is also a preposition, an adposition with both uses is
locational before its complement unless it is one of the grammar's directional prepositions,
circumpositions take only nominal complements, and the morphologically complex prepositions
resist R-pronominalization. The chapter itself notes that *af* and *heen*, the second parts of
*van … af* and *over … heen*, are not commonly used as prepositions, although they once were,
and remain postpositions or particles with a directional meaning.

The chapter says that the raising of a nominal complement is semantically conditioned and does
not state the condition. Helmantel's analysis, which the chapter names as a starting point,
supplies one: the complement raises when the phrase is directional and the adposition is not
inherently directional, since an inherently directional adposition such as *naar* 'to' checks
the directionality itself. That condition entails the chapter's rule and keeps the grammar's
inherently directional prepositions out of the postpositional order.

## Main definitions

* `ComplementKind`, `Raises`: what a phrase-internal complement is, and when it raises to the
  specifier of the functional projection.
* `position`, `headDirection`: where the complement is pronounced, and the head direction of
  the phrase that results.
* `linearization`: the traditional four-way classification, read off the head direction.
* `Extractable`: extraction requires the extracted element to precede the adpositional head.
* `verbClass`: the transitivity class of a verb of motion with a spatial complementive.

## Main results

* `linearization_eq_post_iff`, `linearization_eq_circum_iff`: each surface class is the
  effect of one complement kind and directionality, not a lexical property.
* `linearization_rPronoun`: an R-pronoun complement never gives the postpositional order.
* `range_linearization`: the rule derives every class of the traditional classification and
  no other order.
* `extractable_iff_raises`, `extractable_iff_of_linearization_eq_pre`,
  `extractable_of_linearization_ne_pre`: extraction is raising, so from a prepositional phrase
  only an R-pronoun leaves and from any other phrase the complement does.
* `raises_nominal_of_dpRaises`, `pointLocative_not_postP`: Helmantel's condition on nominal
  raising entails the chapter's rule, and under it the inherently directional prepositions have
  no postpositional use.
* `linearization_direction_post`, `circumP_parts`: the rule reproduces every postpositional
  use of the fragment and every circumposition decomposes into listed parts.
* `postP_subset_preP`, `circumP_complement_nominal`, `no_rPron_not_postP`: the lexical
  restrictions the analysis predicts.
* `perfect_op`, `postP_selects_zijn`: a postpositional phrase denotes a path and its verb takes
  *zijn* 'be', while the prepositional phrase of the same adposition takes *hebben* 'have'.

## Implementation notes

* The chapter's extraction evidence is modelled over complement kinds only, one level deep. The
  extraction of modifiers such as measure phrases from a prepositional phrase, the pied-piping
  of the first part of a circumposition alone under wh-movement, and the restriction of
  pronominal complements to human referents, which R-pronouns lift, are described in the
  chapter and not formalized. The raised prepositional phrase inside a circumposition is taken
  to be a plain prepositional phrase whose complement stays in situ.
* The chapter offers the raising analysis as a hypothesis that idealizes away the exceptional
  prepositional phrases with a prepositional complement, such as *van na de oorlog* 'from
  after the war'.
* The perfect auxiliary follows the chapter's account of the contrast between *heeft op de
  heuvel gereden* and *is de heuvel op gereden*: a path complementive makes the verb of motion
  telic and unaccusative. `verbClass` records that account, and the auxiliary is then the
  selection rule's, whichever way the language treats its reflexives.

## TODO

`Raises` idealizes the chapter's semantic condition to directionality, so
`linearization_eq_post_iff` predicts a postpositional order for every directional preposition.
Helmantel's condition removes *naar*, *tot* and *van*, but *vanaf*, *vanuit* and *via*, which
she does not classify, still come out postpositional although the grammar records no such use,
and the prepositional phrase inside *van het dak af* 'off the roof' is read as locational
although *van* denotes a source path.

## References

* [H. Broekhuis and N. Corver, *Adpositions and Adpositional Phrases: A Syntactic View from
  Dutch* (2026)][broekhuis-corver-2026a]
* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume VII: Adpositions and Adpositional
  Phrases* (2026)][broekhuis-corver-2026c]
* [M. Helmantel, *Interactions in the Dutch Adpositional Domain* (2002)][helmantel-2002]
-/

@[expose] public section

namespace BroekhuisCorver2026

open Dutch.Adpositions
open ArgumentStructure.AuxiliarySelection

/-! ### The internal structure of an adpositional phrase -/

/-- What a transitive adposition selects: a noun phrase, a prepositional phrase, or an R-pronoun,
the proform of a locational prepositional phrase. An intransitive adposition selects nothing,
`Option.none`. -/
inductive ComplementKind where
  | nominal
  | prePP
  | rPronoun
  deriving DecidableEq, Repr, Fintype

/-- The raising rule: a prepositional phrase or an R-pronoun raises to the specifier of the
phrase-internal functional projection, and a nominal complement only when the phrase is
directional, under a semantic condition the chapter leaves open and this file idealizes to
directionality. -/
def Raises : ComplementKind → Case.PathDir → Prop
  | .nominal, d => d ≠ .place
  | .prePP, _ => True
  | .rPronoun, _ => True

instance : ∀ k, DecidablePred (Raises k)
  | .nominal, d => inferInstanceAs (Decidable (d ≠ .place))
  | .prePP, _ => inferInstanceAs (Decidable True)
  | .rPronoun, _ => inferInstanceAs (Decidable True)

section Phrase

variable (k : ComplementKind) (d : Case.PathDir)

/-- The three positions of the phrase, the specifier of the functional projection, the adposition,
and the complement's base position, and where the complement is pronounced: in the specifier
when it raises, in its base position otherwise. -/
def position : Fin 3 := if Raises k d then 0 else 2

/-- The adposition's position. -/
def headPosition : Fin 3 := 1

/-- The head direction of the phrase, read off the positions of the adposition and its complement:
head-final exactly when the complement has raised. -/
def headDirection : HeadDirection := .ofLT headPosition (position k d)

/-- Extraction from an adpositional phrase requires the extracted element to precede the
adpositional head. -/
def Extractable : Prop := position k d < headPosition

instance : Decidable (Extractable k d) := inferInstanceAs (Decidable (_ < _))

variable {k d}

theorem headDirection_eq_headFinal : headDirection k d = .headFinal ↔ Raises k d := by
  unfold headDirection headPosition position; split <;> simp [*]

theorem headDirection_eq_headInitial : headDirection k d = .headInitial ↔ ¬ Raises k d := by
  unfold headDirection headPosition position; split <;> simp [*]

/-- A complement can be extracted exactly when it has raised. -/
theorem extractable_iff_raises : Extractable k d ↔ Raises k d := by
  unfold Extractable headPosition position; split <;> simp [*]

end Phrase

/-- The traditional classification, read off the head direction and the complement. The head
precedes an in-situ complement and follows a raised one; a raised prepositional phrase carries
its own head before the noun phrase, so the whole is a circumposition; and *er op* counts as a use
of the preposition, since an R-pronoun proforms the locational prepositional phrase. -/
def linearization : Option ComplementKind → Case.PathDir → Option Adposition.Linearization
  | none, _ => none
  | some k, d =>
    some <| match k, headDirection k d with
      | .nominal, .headFinal => .post
      | .prePP, .headFinal => .circum
      | _, _ => .pre

/-- A postposition is nothing but a directional adposition with a raised nominal complement, which
is why the postpositional use of an adposition is always the directional one. -/
theorem linearization_eq_post_iff (k : ComplementKind) (d : Case.PathDir) :
    linearization (some k) d = some .post ↔ k = .nominal ∧ d ≠ .place := by
  cases k <;> cases d <;> decide

/-- A circumposition is nothing but an adposition whose complement is a prepositional phrase: the
second adpositional element is the head, and the first is the head of the raised complement. -/
theorem linearization_eq_circum_iff (k : ComplementKind) (d : Case.PathDir) :
    linearization (some k) d = some .circum ↔ k = .prePP := by
  cases k <;> cases d <;> decide

/-- An R-pronoun never yields the postpositional order: *de wandeling er op* 'the hike on it'
has only the locational reading, so R-pronominalization is confined to prepositional phrases,
and a circumpositional phrase R-pronominalizes through its prepositional complement. -/
theorem linearization_rPronoun (d : Case.PathDir) :
    linearization (some .rPronoun) d = some .pre := by
  cases d <;> rfl

/-- The rule derives each of the four traditional classes, so none of them need be listed in the
lexicon, and derives no other order: an adposition never surfaces inside its complement. -/
theorem range_linearization :
    Set.range (Function.uncurry linearization) = {some .inposition}ᶜ := by
  ext o
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨⟨k, d⟩, rfl⟩
    cases k with
    | none => cases d <;> decide
    | some k => cases k <;> cases d <;> decide
  · rcases o with _ | _ | _ | _ | _
    exacts [⟨(none, .place), rfl⟩, ⟨(some .nominal, .place), rfl⟩,
      ⟨(some .nominal, .goal), rfl⟩, ⟨(some .prePP, .place), rfl⟩, absurd rfl h]

/-! ### Extraction -/

/-- The nominal complement of a plain preposition stays behind and cannot be extracted, which is
the resistance to preposition stranding, while the raised complement of a directional
postposition can be. -/
theorem extractable_nominal_iff (d : Case.PathDir) : Extractable .nominal d ↔ d ≠ .place :=
  extractable_iff_raises

/-- An R-pronoun has raised and can be extracted, whether the adposition it leaves behind is
stranded or pied-piped. -/
theorem extractable_rPronoun (d : Case.PathDir) : Extractable .rPronoun d :=
  extractable_iff_raises.2 trivial

/-- From a prepositional phrase only an R-pronoun can be extracted. -/
theorem extractable_iff_of_linearization_eq_pre {k : ComplementKind} {d : Case.PathDir}
    (h : linearization (some k) d = some .pre) : Extractable k d ↔ k = .rPronoun := by
  revert h; cases k <;> cases d <;> decide

/-- From a postpositional or a circumpositional phrase the complement can be extracted. -/
theorem extractable_of_linearization_ne_pre {k : ComplementKind} {d : Case.PathDir}
    (h : linearization (some k) d ≠ some .pre) : Extractable k d := by
  revert h; cases k <;> cases d <;> decide

/-- A circumposition's nominal complement is the complement of the raised prepositional phrase, a
plain prepositional phrase, so its extractability is settled inside that phrase: like any
prepositional complement it cannot be extracted, while an R-pronoun in the same position can.
This is why circumpositions pattern with prepositions rather than with postpositions. -/
theorem circumP_patterns_with_preP :
    ¬ Extractable .nominal .place ∧ Extractable .rPronoun .place :=
  ⟨fun h ↦ (extractable_nominal_iff _).1 h rfl, extractable_rPronoun _⟩

/-! ### The condition on nominal raising -/

/-- The semantic condition the chapter leaves open is, in Helmantel's analysis, that the
adposition is not inherently directional: a directional phrase raises its nominal complement
when its directionality is syntactic rather than lexical, and that raising entails the chapter's
idealized rule. -/
theorem raises_nominal_of_dpRaises {inherent : Prop} {d : Case.PathDir}
    (h : Helmantel2002.DPRaises (d ≠ .place) inherent) : Raises .nominal d :=
  h.1

/-- Under that condition the inherently directional prepositions *naar*, *tot* and *van* raise no
complement and have no postpositional use, as the fragment records, which removes them from the
rule's overprediction. -/
theorem pointLocative_not_postP :
    ∀ a ∈ Helmantel2002.pointLocatives, .post ∉ a.linearization :=
  fun a ha h ↦ by simp [Helmantel2002.pointLocative_linearization a ha] at h

/-! ### The Dutch lexicon -/

/-- The rule reproduces every postpositional use the grammar records: the postpositional order is
derived from the path that use denotes. -/
theorem linearization_direction_post :
    ∀ a ∈ inventory, .post ∈ a.linearization →
      linearization (some .nominal) (a.direction .post) = some .post :=
  fun a ha h ↦ (linearization_eq_post_iff _ _).2 ⟨rfl, direction_post_ne_place a ha h⟩

/-- A circumposition is a postposition with a prepositional-phrase complement, so each
circumposition of the grammar is a listed preposition followed by a listed postposition or
particle. -/
theorem circumP_parts :
    ∀ a ∈ inventory, a.isComplex →
      ∃ b ∈ inventory, ∃ c ∈ inventory, a.form = .complex [b.form.text, c.form.text] ∧
        .pre ∈ b.linearization ∧ (.post ∈ c.linearization ∨ c.intransitive) := by
  decide

/-- Every postposition but *af* is also a preposition, so the postpositional order is derived from
the prepositional one; *af*, the one postposition the grammar records without a prepositional
use, is a directional adposition whose complement always raises. -/
theorem postP_subset_preP :
    ∀ a ∈ inventory, .post ∈ a.linearization →
      .pre ∈ a.linearization ∨ a.form = .simple "af" :=
  pre_of_post

/-- The second elements *af* and *heen* of *van … af* and *over … heen* are not prepositions on
their own, as the chapter notes, and head the raised phrase as postpositions. -/
theorem circumP_parts_not_preP : .pre ∉ af.linearization ∧ .pre ∉ heen.linearization := by
  decide

/-- An adposition with both orders is locational before its complement, *op de berg* 'on the
mountain' against *de berg op* 'up the mountain', unless it is one of the grammar's directional
prepositions, *over* 'across' and *voorbij* 'past', whose complement raises in either order. -/
theorem postP_has_both_readings :
    ∀ a ∈ inventory, .post ∈ a.linearization → .pre ∈ a.linearization →
      a.direction .pre = .place ∨ a.form = .simple "over" ∨ a.form = .simple "voorbij" := by
  decide

/-- A circumposition takes only a nominal complement, the complement of the raised prepositional
phrase. -/
theorem circumP_complement_nominal :
    ∀ a ∈ inventory, .circum ∈ a.linearization → a.complement = [.np] :=
  complement_of_circum

/-- Every postposition takes a nominal complement, the one that raises; *door* also takes a clause,
in its prepositional use only. -/
theorem postP_complement_np :
    ∀ a ∈ inventory, .post ∈ a.linearization → .np ∈ a.complement := by
  decide

/-- The morphologically complex prepositions resist R-pronominalization: *tijdens het journaal*
'during the news' but not *er tijdens*. -/
theorem complex_no_rPron :
    tijdens.rPronoun = false ∧ ondanks.rPronoun = false ∧ zonder.rPronoun = false :=
  ⟨rfl, rfl, rfl⟩

/-- An adposition that cannot be R-pronominalized has no postpositional use either. -/
theorem no_rPron_not_postP :
    ∀ a ∈ inventory, a.rPronoun = false → .post ∉ a.linearization := by
  decide

/-! ### Directional phrases and the perfect auxiliary -/

/-- *Op* denotes a goal path after its complement and *van* a source path before it, so the two
path shapes are independent of the order. -/
theorem op_van_paths : op.direction .post = .goal ∧ van.direction .pre = .source := ⟨rfl, rfl⟩

/-- The transitivity class of a verb of motion with a spatial complementive: a path makes the
event a change of location and the verb unaccusative, a location leaves it unergative. -/
def verbClass (d : Case.PathDir) : TransitivityClass :=
  if d = .place then .unergative else .unaccusative

/-- Under any selection rule the verb takes *zijn* 'be' exactly when its complementive denotes a
path. -/
theorem selection_verbClass_eq_be_iff (r : Bool) (d : Case.PathDir) :
    selection r (verbClass d) = .be ↔ d ≠ .place := by
  unfold verbClass; split <;> simp [*, selection]

/-- *De fietser heeft op de heuvel gereden* 'the cyclist rode on the hill' against *de fietser is
de heuvel op gereden* 'the cyclist rode up the hill': the prepositional phrase of *op* is
locational and its verb takes *hebben* 'have', the postpositional phrase denotes a goal path and
its verb takes *zijn* 'be'. -/
theorem perfect_op (r : Bool) :
    selection r (verbClass (op.direction .pre)) = .have ∧
      selection r (verbClass (op.direction .post)) = .be :=
  ⟨rfl, rfl⟩

/-- A postpositional phrase denotes a path and is the complementive of a verb of traversing, which
is unaccusative and takes *zijn* 'be'. -/
theorem postP_selects_zijn (r : Bool) :
    ∀ a ∈ inventory, .post ∈ a.linearization → selection r (verbClass (a.direction .post)) = .be :=
  fun a ha h ↦ (selection_verbClass_eq_be_iff r _).2 (direction_post_ne_place a ha h)

end BroekhuisCorver2026
