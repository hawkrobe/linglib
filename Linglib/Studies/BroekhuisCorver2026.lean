module

public import Linglib.Fragments.Dutch.Adpositions
public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection

/-!
# Broekhuis and Corver 2026: Dutch adpositions

Dutch adpositions are traditionally sorted into four classes by where they stand relative to their
complement: prepositions, postpositions, circumpositions, and intransitive adpositions. This file
formalizes the argument that the classification is epiphenomenal. Each class is the surface effect
of one movement rule inside the adpositional phrase. A nominal complement stays in the position
where the adposition selects it unless the phrase is directional, while a prepositional complement
or an R-pronoun moves to the specifier of a phrase-internal functional projection. Postpositions
are then directional prepositions with a raised complement, and circumpositions are postpositions
whose complement is itself a prepositional phrase.

The same rule predicts what can be extracted. Dutch resists preposition stranding, but an element
that precedes the adpositional head can leave the phrase, and precisely the complements that move
precede it: R-pronouns and the complements of directional postpositions can be extracted, ordinary
nominal complements of prepositions cannot, and the complement of a circumposition patterns with
the prepositional case because it sits inside the raised prepositional phrase.

The lexical generalizations are checked against the Dutch adposition fragment, which follows the
authors' grammar: every postpositional use denotes a path, every postposition but *af* is also a
preposition, an adposition with both uses is locational before its complement unless it is one
of the grammar's directional prepositions, circumpositions take only nominal complements, and
the morphologically complex prepositions resist R-pronominalization.

## Main definitions

* `ComplementKind`, `movesToSpec`: what a phrase-internal complement is, and when it raises.
* `surfaceOrder`: the traditional four-way classification, derived.
* `Extractable`: extraction requires the extracted element to precede the adpositional head.

## Main results

* `postP_iff_directional_nominal`, `circumP_iff_prePP_complement`: each surface class is the
  effect of one complement kind and directionality, not a lexical property.
* `extraction_pattern`, `circumP_patterns_with_preP`: the extraction asymmetries follow.
* `postP_directional`, `postP_subset_preP`: every postposition is a directional adposition,
  and all but *af* are prepositions too.
* `circumP_complement_nominal`, `no_rPron_not_postP`: the complement-type and
  R-pronominalization restrictions.
* `postP_selects_zijn`: a postpositional phrase denotes a path and its verb takes *zijn* 'be'.

## TODO

The grammar's eight directional prepositions, *naar* 'to' among them, have no postpositional
use, although their phrases are directional; the analysis attributes this to a semantic
condition on the raising of a nominal complement that `movesToSpec` does not formalize, so
`postP_iff_directional_nominal` predicts a postpositional order for them.

## References

* [H. Broekhuis and N. Corver, *Adpositions and Adpositional Phrases: A Syntactic View from
  Dutch* (2026)][broekhuis-corver-2026a]
* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume VII: Adpositions and Adpositional
  Phrases* (2026)][broekhuis-corver-2026c]
* [A. Sorace, *Gradients in auxiliary selection with intransitive verbs* (2000)][sorace-2000]
-/

@[expose] public section

namespace BroekhuisCorver2026

open Dutch.Adpositions
open ArgumentStructure.AuxiliarySelection

/-! ### The internal structure of an adpositional phrase -/

/-- The traditional classification of Dutch adpositions by the position of the adposition relative
to its complement. -/
inductive PPSurfaceOrder where
  /-- Adposition before its complement. -/
  | preP
  /-- Adposition after its complement. -/
  | postP
  /-- Complement enclosed by two adpositional elements. -/
  | circumP
  /-- No complement: an intransitive adposition or a verbal particle. -/
  | intransP
  deriving DecidableEq, Repr

/-- What an adposition selects: a noun phrase, a prepositional phrase, an R-pronoun, or nothing. -/
inductive ComplementKind where
  | nominal
  | prePP
  | rPronoun
  | absent
  deriving DecidableEq, Repr

/-- Whether the complement raises to the specifier of the phrase-internal functional projection. A
nominal complement stays where the adposition selects it unless the phrase is directional, in which
case raising is semantically conditioned; a prepositional complement or an R-pronoun raises by
default. -/
def movesToSpec : ComplementKind → Bool → Bool
  | .nominal, directional => directional
  | .prePP, _ => true
  | .rPronoun, _ => true
  | .absent, _ => false

/-- The surface order the raising produces. An R-pronoun raises across the adposition without
making it a postposition: the adposition still takes a nominal complement elsewhere. -/
def surfaceOrder : ComplementKind → Bool → PPSurfaceOrder
  | .nominal, directional => if directional then .postP else .preP
  | .prePP, _ => .circumP
  | .rPronoun, _ => .preP
  | .absent, _ => .intransP

/-- A postposition is nothing but a directional adposition with a raised nominal complement, which
is why the postpositional use of an adposition is always the directional one. -/
theorem postP_iff_directional_nominal (k : ComplementKind) (d : Bool) :
    surfaceOrder k d = .postP ↔ (k = .nominal ∧ d = true) := by
  cases k <;> cases d <;> simp [surfaceOrder]

/-- A circumposition is nothing but an adposition whose complement is a prepositional phrase: the
second adpositional element is the head, and the first is the head of the raised complement. -/
theorem circumP_iff_prePP_complement (k : ComplementKind) (d : Bool) :
    surfaceOrder k d = .circumP ↔ k = .prePP := by
  cases k <;> cases d <;> simp [surfaceOrder]

/-- Every one of the four classes is produced by the rule, so none of them need be listed in the
lexicon. -/
theorem every_order_derived (o : PPSurfaceOrder) : ∃ k d, surfaceOrder k d = o := by
  cases o
  exacts [⟨.nominal, false, rfl⟩, ⟨.nominal, true, rfl⟩, ⟨.prePP, false, rfl⟩,
    ⟨.absent, false, rfl⟩]

/-! ### Extraction -/

/-- Extraction from an adpositional phrase requires the extracted element to precede the
adpositional head, so a complement can be extracted exactly when it has raised. -/
def Extractable (k : ComplementKind) (directional : Bool) : Prop :=
  movesToSpec k directional = true

instance (k : ComplementKind) (d : Bool) : Decidable (Extractable k d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The extraction facts follow from the rule that derives the word orders. The nominal complement
of a plain preposition stays behind and cannot be extracted, which is the resistance to preposition
stranding; an R-pronoun and the complement of a directional postposition have raised and can be. -/
theorem extraction_pattern :
    ¬ Extractable .nominal false ∧ Extractable .rPronoun false ∧ Extractable .nominal true := by
  decide

/-- A circumposition's nominal complement is the complement of the raised prepositional phrase, so
its extractability is settled inside that phrase: like any prepositional complement it cannot be
extracted, while an R-pronoun in the same position can. This is why circumpositions pattern with
prepositions rather than with postpositions. -/
theorem circumP_patterns_with_preP :
    ¬ Extractable .nominal false ∧ Extractable .rPronoun false := ⟨by decide, by decide⟩

/-! ### The Dutch lexicon -/

/-- Every postpositional use denotes a path, as the raising analysis requires: the postpositional
order is the directional reading with a raised complement. -/
theorem postP_directional :
    ∀ a ∈ inventory, .post ∈ a.linearization → a.direction .post ≠ .place :=
  direction_post_ne_place

/-- Every postposition but *af* is also a preposition, so the postpositional order is derived from
the prepositional one; *af*, the one postposition the grammar records without a prepositional
use, is a directional adposition whose complement always raises. -/
theorem postP_subset_preP :
    ∀ a ∈ inventory, .post ∈ a.linearization →
      .pre ∈ a.linearization ∨ a.form = .simple "af" :=
  pre_of_post

/-- The second elements *af* and *heen* of *van … af* and *over … heen* are not prepositions on
their own. -/
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

/-- A postpositional phrase denotes a path and is the complementive of a verb of traversing, which
is unaccusative and takes *zijn* 'be': *de fietser is de heuvel op gereden* 'the cyclist rode up
the hill' against *de fietser heeft op de heuvel gereden* ([sorace-2000]). -/
theorem postP_selects_zijn :
    ∀ a ∈ inventory, .post ∈ a.linearization →
      a.direction .post ≠ .place ∧ canonicalSelection .unaccusative = .be :=
  fun a ha h ↦ ⟨direction_post_ne_place a ha h, rfl⟩

end BroekhuisCorver2026
