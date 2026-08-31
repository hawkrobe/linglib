import Linglib.Fragments.Dutch.Adpositions
import Linglib.Semantics.ArgumentStructure.AuxiliarySelection

/-!
# Broekhuis and Corver 2026: Dutch adpositions

Dutch adpositions are traditionally sorted into four classes by where they stand relative to their
complement: prepositions, postpositions, circumpositions, and intransitive adpositions. This file
formalizes the argument that the classification is epiphenomenal. Each class is the surface effect
of one movement rule inside the adpositional phrase — a nominal complement stays in the position
where the adposition selects it unless the phrase is directional, while a prepositional complement
or an R-pronoun moves to the specifier of a phrase-internal functional projection. Postpositions
are then directional prepositions with a raised complement, and circumpositions are postpositions
whose complement is itself a prepositional phrase.

The same rule predicts what can be extracted. Dutch resists preposition stranding, but an element
that precedes the adpositional head can leave the phrase, and precisely the complements that move
precede it: R-pronouns and the complements of directional postpositions can be extracted, ordinary
nominal complements of prepositions cannot, and the complement of a circumposition patterns with
the prepositional case because it sits inside the raised prepositional phrase.

The lexical generalizations are stated over the Dutch adposition Fragment: every postposition is
also a preposition, postpositional uses are directional, postpositional and circumpositional uses
take only nominal complements, and the morphologically complex prepositions resist
R-pronominalization.

## Main definitions

* `ComplementKind`, `movesToSpec` — what a phrase-internal complement is, and when it raises
* `surfaceOrder` — the traditional four-way classification, derived
* `Extractable` — extraction requires the extracted element to precede the adpositional head

## Main results

* `postP_iff_directional_nominal`, `circumP_iff_prePP_complement` — each surface class is the
  effect of one complement kind and directionality, not a lexical property
* `extraction_pattern`, `circumP_patterns_with_preP` — the extraction asymmetries follow
* `postP_subset_preP`, `postP_has_both_readings` — every postposition is a directional preposition
* `postP_complement_nominal`, `circumP_complement_nominal` — the complement-type restriction
* `postP_selects_zijn` — a directional postposition gives a telic phrase and the *be* auxiliary

## References

* [broekhuis-corver-2026]
* [sorace-2000]
-/

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

/-- Every adposition with a postpositional use also has a prepositional use, as the raising
analysis requires: the postpositional order is derived from the prepositional one. -/
theorem postP_subset_preP : ∀ a ∈ dutchAdpositions, a.postPOk → a.prePOk := by decide

/-- The second elements of circumpositions are not prepositions on their own. -/
theorem circumP_parts_not_preP : af.prePOk = false ∧ heen.prePOk = false := ⟨rfl, rfl⟩

/-- An adposition with a postpositional use has both a locational and a directional reading — *op
de heuvel* 'on the hill' against *de heuvel op* 'onto the hill' — the directional one being the
postpositional order. -/
theorem postP_has_both_readings :
    ∀ a ∈ dutchAdpositions, a.postPOk → a.locational ∧ a.directional := by decide

/-- Every adposition with a directional reading has a path. -/
theorem directional_has_pathType :
    ∀ a ∈ dutchAdpositions, a.directional → a.pathType.isSome := by decide

/-- Postpositional and circumpositional uses take neither adjectival nor clausal complements, in
contrast with prepositional uses. -/
theorem postP_complement_nominal :
    ∀ a ∈ dutchAdpositions, a.postPOk →
      ∀ t ∈ a.complTypes, t ≠ .adjectival ∧ t ≠ .clausal := by decide

/-- The same for circumpositional uses. -/
theorem circumP_complement_nominal :
    ∀ a ∈ dutchAdpositions, a.circumPart.isSome →
      ∀ t ∈ a.complTypes, t ≠ .adjectival ∧ t ≠ .clausal := by decide

/-- The morphologically complex prepositions resist R-pronominalization: *tijdens het journaal*
but not *er tijdens*. -/
theorem complex_no_rPron :
    tijdens.rPronOk = false ∧ ondanks.rPronOk = false ∧ zonder.rPronOk = false :=
  ⟨rfl, rfl, rfl⟩

/-- An adposition that cannot be R-pronominalized has no postpositional use either. -/
theorem no_rPron_not_postP :
    ∀ a ∈ dutchAdpositions, a.rPronOk = false → a.postPOk = false := by decide

/-! ### Directional phrases and the perfect auxiliary -/

/-- A postpositional use denotes a bounded path, so the phrase is telic. -/
theorem postP_telic :
    ∀ a ∈ dutchAdpositions, a.postPOk → a.pathType.map Prod.snd = some .telic := by decide

/-- *Op* is a goal-oriented bounded path in its postpositional use, *van* a source-oriented one;
both are telic, so the two path shapes are independent of telicity. -/
theorem op_van_paths :
    op.pathType = some (.goal, .telic) ∧ van.pathType = some (.source, .telic) := ⟨rfl, rfl⟩

/-- A telic directional phrase makes its clause unaccusative, and Dutch unaccusatives take *zijn*
'be': *de fietser is de heuvel op gereden* against *de fietser heeft op de heuvel gereden*
([sorace-2000]). -/
theorem postP_selects_zijn (a : DutchAdposition) (ha : a ∈ dutchAdpositions) (h : a.postPOk) :
    a.pathType.map Prod.snd = some .telic ∧ canonicalSelection .unaccusative = .be :=
  ⟨postP_telic a ha h, rfl⟩

end BroekhuisCorver2026
