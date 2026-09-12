import Linglib.Data.Examples.JackendoffAudring2020
import Linglib.Data.Forms.JackendoffAudring2020
import Linglib.Morphology.Construction.Schema
import Linglib.Morphology.Construction.SameExcept
import Linglib.Morphology.Construction.Inheritance
import Linglib.Morphology.Paradigm.Linkage
import Linglib.Morphology.Paradigm.Morphome
import Linglib.Core.Order.Flat
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Jackendoff and Audring (2020): The Texture of the Lexicon

This file formalizes the Relational Morphology of [jackendoff-audring-2020], in which
morphological motivation is shared structure recorded by nondirectional relational links
between fully specified lexical entries, not inheritance from an abstract base. The
mixed-direction pairs of Objection 10 to inheritance, Section 3.4.4, are the test: *assassin*
and *assassinate* build the second on the first in phonology and the first on the second in
semantics, so no acyclic inheritance hierarchy holds both demands (`assassin_cycle`), while a
sister link with a coindex per shared part carries both, (41) (`assassin_pairs`), and reads the
same transposed (`assassin_pairs_symm`). Bumped up a level, Section 4.8.2, the link between the
*-ism* and *-ist* schemas, (47), pairs every ideology's noun with its adherent's, whatever the
base and the ideology (`ismist_pairs`), the open-ended relation the book illustrates with
*Trumpism*. Ablaut, Section 5.3, is a sister link off the syllabic nucleus: the general schema
(25) pairs exactly the stems and pasts that are the same except at the nucleus
(`ablaut_pairs_iff`), the *sing*/*sang* subschema (26) is a special case of it
(`ablaut_pairs_of_nucleusPair`) whose pairs are nucleus contrasts
(`contrast_of_nucleusPair`), and the German present-tense schema (45) has the same
phonological shape. The cells (45) serves, the second and third singular present, are a
morphome, Section 5.4.4: the syncretism class of the special stem of *sprechen* is a value
conjunction of no feature of the paradigm (`spricht_morphome`). The Same Verb Problem, Section
5.6, is a shared morphosyntax-phonology pivot without a shared semantics: two lexemes selecting
the same pivot inflect alike at every cell (`realize_eq_of_sameVerb`), which pairs the two
*draw*s of (60) and *take* with *take part*, (57) to (59), and separates the homophones *ring*
and *wring*. Structural Intersection, Section 7.8.1, is the meet: the schema (6) is the
intersection of its three sisters (5) (`ishSchema_body_eq_inf`), is the most they have in
common (`instantiates_ishSchema_iff`), and absorbs a newly encountered sister
(`ishSchema_inf_foolish`).

## Implementation notes

* Lexical entries and schemas are slot-indexed descriptions over a flat carrier, a constant
  above `⊥` and a variable at `⊥`; a relational coindex is a variable subscripting a slot of
  each entry, which a paired instantiation fills alike
  (`Morphology.Construction.Schema.InstantiatesAt`). The containment of
  the semantics of *assassinate* in that of *assassin*, (41), is rendered as a shared slot.
* The zero exponence of the present and the infinitive of *walk*, (19), the double
  coindexation of Section 4.3, appears as a syncretism of the paradigm (`walk_syncretism`).
* The cycle theorem renders the paradox of Objection 10 through the well-foundedness of an
  inheritance hierarchy; the book argues from the above-and-below paradox and makes no
  well-foundedness claim.
* The syllables and the *-ish* adjectives are the CLDF forms of
  `Data/Forms/JackendoffAudring2020.json`, read as slot-indexed segments by
  `Data.Forms.Form.slots`; a syllable's positions are onset, nucleus and coda.
* The correspondence between a schema's variable coindices and the constant coindices of its
  instances, left unformalized in Section 4.13.2, is the subscripting of
  `Morphology.Construction.Schema.InstantiatesAt`; a productive variable is one marked open
  over and above its attested fillers.

## References

* [jackendoff-audring-2020]
* [booij-2010]
* [aronoff-1994]
* [spencer-2013]
* [albright-hayes-2003]
-/

namespace JackendoffAudring2020

open Morphology Morphology.Construction

/-! ### Sister words -/

/-- The parts of the entries (41): the shared phonology and the shared predicate MURDER, the
person that *assassin* adds and the affix that *assassinate* adds. -/
inductive Part
  | asasin
  | murder
  | person
  | ate
  deriving DecidableEq

/-- The variables of (41): the phonology of *assassin*, which is the base of *assassinate*
(coindex 2), the predicate MURDER of both (coindex 1), the person that *assassin* adds and the
affix that *assassinate* adds. -/
inductive AssassinVar
  | phon
  | murder
  | person
  | ate
  deriving DecidableEq

/-- The slots of *assassin*: its phonology, the predicate it contains, and the person. -/
inductive AssassinSlot
  | phon
  | murder
  | person
  deriving DecidableEq

/-- The slots of *assassinate*: its base, its affix, and its predicate. -/
inductive AssassinateSlot
  | base
  | affix
  | murder
  deriving DecidableEq

/-- The entries (41a) and (41b) with their coindices, as one fully specified description over
the shared variables. -/
def assassinPair : Schema AssassinVar (Flat Part) :=
  ⟨λ | .phon => ↑Part.asasin | .murder => ↑Part.murder | .person => ↑Part.person
     | .ate => ↑Part.ate, ∅⟩

/-- The subscripting of the slots of *assassin* by the variables of (41). -/
def assassinSub : AssassinSlot → AssassinVar
  | .phon => .phon
  | .murder => .murder
  | .person => .person

/-- The subscripting of the slots of *assassinate* by the variables of (41). -/
def assassinateSub : AssassinateSlot → AssassinVar
  | .base => .phon
  | .affix => .ate
  | .murder => .murder

/-- The entry (41a): the pair read at the slots of *assassin*. -/
def assassin : Schema AssassinSlot (Flat Part) := assassinPair.comap assassinSub

/-- The entry (41b): the pair read at the slots of *assassinate*. -/
def assassinate : Schema AssassinateSlot (Flat Part) := assassinPair.comap assassinateSub

/-- The two entries are a paired instantiation of (41): they share the base phonology and the
predicate, and neither contains all of the other. -/
theorem assassin_pairs :
    assassinPair.InstantiatesAt (Sum.elim assassinSub assassinateSub)
      (Sum.elim assassin.body assassinate.body) :=
  ⟨assassinPair.body, le_rfl, funext λ p => by rcases p with p | p <;> cases p <;> rfl⟩

/-- The link is nondirectional: neither word is derived from the other. -/
theorem assassin_pairs_symm :
    assassinPair.InstantiatesAt (Sum.elim assassinateSub assassinSub)
      (Sum.elim assassinate.body assassin.body) :=
  Schema.instantiatesAt_elim_swap.2 assassin_pairs

/-- The pair as nodes of an inheritance hierarchy. -/
inductive Pair
  | assassin
  | assassinate
  deriving DecidableEq

/-- Objection 10: the phonology demands that *assassinate* inherit from *assassin* and the
semantics that *assassin* inherit from *assassinate*; no acyclic hierarchy holds both. -/
theorem assassin_cycle (h : Hierarchy Pair) (hphon : h.parent .assassinate = some .assassin)
    (hsem : h.parent .assassin = some .assassinate) : False :=
  h.parent_asymm hphon hsem

/-! ### Sister schemas -/

/-- The material of the schemas (47) over bases `B` and ideologies `I`: a base, an ideology,
the two affixes, and the relation ADHERENT. -/
inductive Atom (B I : Type*)
  | base (b : B)
  | ideology (i : I)
  | ism
  | ist
  | adherent

/-- The variables of the schemas (47): the base `X` and the ideology, shared by the two schemas
(coindices α and β), the two affixes and the relation ADHERENT. -/
inductive IsmIstVar
  | base
  | ideology
  | ism
  | ist
  | adherent
  deriving DecidableEq

/-- The slots of the *-ism* schema: base, affix, semantics. -/
inductive IsmSlot
  | base
  | affix
  | sem
  deriving DecidableEq

/-- The slots of the *-ist* schema: base, affix, the relation ADHERENT, and its ideology. -/
inductive IstSlot
  | base
  | affix
  | relation
  | ideology
  deriving DecidableEq

variable {B I : Type*}

/-- (47): the *-ism* and *-ist* schemas with their coindices as one description, the affixes
and ADHERENT pinned, the base and the ideology open. -/
def ismist : Schema IsmIstVar (Flat (Atom B I)) :=
  ⟨λ | .ism => ↑(Atom.ism : Atom B I) | .ist => ↑(Atom.ist : Atom B I)
     | .adherent => ↑(Atom.adherent : Atom B I) | _ => ⊥, {.base, .ideology}⟩

/-- The subscripting of the slots of the *-ism* schema by the variables of (47). -/
def ismSub : IsmSlot → IsmIstVar
  | .base => .base
  | .affix => .ism
  | .sem => .ideology

/-- The subscripting of the slots of the *-ist* schema by the variables of (47). -/
def istSub : IstSlot → IsmIstVar
  | .base => .base
  | .affix => .ist
  | .relation => .adherent
  | .ideology => .ideology

/-- (47a): the affix pinned to *-ism*, the base and the ideology open. -/
def ismSchema : Schema IsmSlot (Flat (Atom B I)) := ismist.comap ismSub

/-- (47b): the affix pinned to *-ist* and the semantics to ADHERENT of an open ideology. -/
def istSchema : Schema IstSlot (Flat (Atom B I)) := ismist.comap istSub

/-- The *-ism* noun on base `b` denoting the ideology `i`. -/
def ismWord (b : B) (i : I) : IsmSlot → Flat (Atom B I)
  | .base => ↑(Atom.base b : Atom B I)
  | .affix => ↑(Atom.ism : Atom B I)
  | .sem => ↑(Atom.ideology i : Atom B I)

/-- The *-ist* noun on base `b` denoting an adherent of `i`. -/
def istWord (b : B) (i : I) : IstSlot → Flat (Atom B I)
  | .base => ↑(Atom.base b : Atom B I)
  | .affix => ↑(Atom.ist : Atom B I)
  | .relation => ↑(Atom.adherent : Atom B I)
  | .ideology => ↑(Atom.ideology i : Atom B I)

/-- The variables of (47) filled by the base `b` and the ideology `i`. -/
def ismistWord (b : B) (i : I) : IsmIstVar → Flat (Atom B I)
  | .base => ↑(Atom.base b : Atom B I)
  | .ideology => ↑(Atom.ideology i : Atom B I)
  | .ism => ↑(Atom.ism : Atom B I)
  | .ist => ↑(Atom.ist : Atom B I)
  | .adherent => ↑(Atom.adherent : Atom B I)

/-- The relation is open-ended: for any base and any ideology, *X-ism* and *X-ist* are a paired
instantiation of the sister schemas, *Trumpism* and *Trumpist* included. -/
theorem ismist_pairs (b : B) (i : I) :
    ismist.InstantiatesAt (Sum.elim ismSub istSub) (Sum.elim (ismWord b i) (istWord b i)) :=
  ⟨ismistWord b i, λ v => by cases v <;> first | exact bot_le | exact le_rfl,
    funext λ p => by rcases p with p | p <;> cases p <;> rfl⟩

/-! ### Ablaut as a link off the nucleus -/

/-- The variables of the ablaut schemas: the onset and the coda, shared by stem and past, and
the two nuclei. -/
inductive NucleusVar
  | onset
  | coda
  | stem
  | past
  deriving DecidableEq

/-- The subscripting of the stem's three positions, onset, nucleus and coda, by the variables
of the ablaut schemas. -/
def stemSub : Fin 3 → NucleusVar := ![.onset, .stem, .coda]

/-- The subscripting of the past's positions by the variables of the ablaut schemas. -/
def pastSub : Fin 3 → NucleusVar := ![.onset, .past, .coda]

/-- Two syllables linked at every position but the nucleus, whose description pins the nuclei
`v` and `w`, `⊥` for an open nucleus: the shape of the ablaut schemas (25) and (26) and of the
German present-tense schema (45). -/
def nucleusPair (v w : Flat String) : Schema NucleusVar (Flat String) :=
  ⟨λ | .stem => v | .past => w | _ => ⊥, {.onset, .coda}⟩

/-- The general ablaut schema (25): both nuclei open. -/
def ablaut : Schema NucleusVar (Flat String) := nucleusPair ⊥ ⊥

/-- The *sing*/*sang* subschema (26): /ɪ/ in the stem, /æ/ in the past. -/
def singSang : Schema NucleusVar (Flat String) := nucleusPair ↑"ɪ" ↑"æ"

/-- The *string*/*strung* subschema, (26) with /ʌ/ for /æ/. -/
def stringStrung : Schema NucleusVar (Flat String) := nucleusPair ↑"ɪ" ↑"ʌ"

/-- A paired instantiation of a nucleus pair is a stem and a past that are the same except at
the nucleus, with the pinned nuclei. -/
theorem nucleusPair_iff {v w : Flat String} {s p : Fin 3 → Flat String} :
    (nucleusPair v w).InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p) ↔
      v ≤ s 1 ∧ w ≤ p 1 ∧ SameExcept s p {1} := by
  rw [Schema.instantiatesAt_elim_iff]
  constructor
  · rintro ⟨hs, hp, -, -, h⟩
    refine ⟨hs 1, hp 1, λ q hq => h q q ?_⟩
    fin_cases q <;> first | rfl | exact (hq rfl).elim
  · rintro ⟨hv, hw, h⟩
    refine ⟨λ q => ?_, λ q => ?_, λ a b hab => ?_, λ a b hab => ?_, λ a b hab => ?_⟩
    · fin_cases q <;> first | exact bot_le | exact hv
    · fin_cases q <;> first | exact bot_le | exact hw
    · fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab (by decide)
    · fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab (by decide)
    · fin_cases a <;> fin_cases b <;>
        first | exact absurd hab (by decide) | exact h (by simp)

/-- (25) pairs exactly the stems and pasts that are the same except at the nucleus. -/
theorem ablaut_pairs_iff {s p : Fin 3 → Flat String} :
    ablaut.InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p) ↔ SameExcept s p {1} := by
  simp [ablaut, nucleusPair_iff]

/-- A subschema with pinned nuclei is a special case of the general ablaut schema: every pair
of (26) is a pair of (25). -/
theorem ablaut_pairs_of_nucleusPair {v w : Flat String} {s p : Fin 3 → Flat String}
    (h : (nucleusPair v w).InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p)) :
    ablaut.InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p) :=
  ablaut_pairs_iff.2 (nucleusPair_iff.1 h).2.2

/-- A pair under a subschema with distinct pinned nuclei is a nucleus contrast: the same
except at the nucleus, where both are present and differ. -/
theorem contrast_of_nucleusPair {v w : String} (hvw : v ≠ w) {s p : Fin 3 → Flat String}
    (h : (nucleusPair ↑v ↑w).InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p)) :
    Contrast s p {1} := by
  obtain ⟨hv, hw, hs⟩ := nucleusPair_iff.1 h
  rw [Flat.coe_le_iff] at hv hw
  refine ⟨hs, λ q hq => ?_⟩
  rw [Set.mem_singleton_iff] at hq
  subst hq
  rw [hv, hw]
  exact ⟨Flat.coe_ne_bot, Flat.coe_ne_bot, λ h => hvw (Flat.coe_injective h)⟩

/-- Two syllables differing only in their nucleus are a paired instantiation of the subschema
pinning those nuclei. -/
theorem syllable_pairs (o v w c : String) :
    (nucleusPair ↑v ↑w).InstantiatesAt (Sum.elim stemSub pastSub)
      (Sum.elim ![↑o, ↑v, ↑c] ![↑o, ↑w, ↑c]) := by
  rw [nucleusPair_iff]
  refine ⟨le_rfl, le_rfl, λ q hq => ?_⟩
  fin_cases q <;> first | rfl | exact (hq rfl).elim

/-- *sing*/*sang*, (24), under (26); *string*/*strung* under its subschema; and the German
*sprech-*/*sprich-* of (43) under the shape of (45). -/
theorem ablaut_words :
    singSang.InstantiatesAt (Sum.elim stemSub pastSub)
        (Sum.elim Forms.sing.slots Forms.sang.slots) ∧
      stringStrung.InstantiatesAt (Sum.elim stemSub pastSub)
        (Sum.elim Forms.string.slots Forms.strung.slots) ∧
      ablaut.InstantiatesAt (Sum.elim stemSub pastSub)
        (Sum.elim Forms.sprech.slots Forms.sprich.slots) := by
  simp only [singSang, stringStrung, ablaut, nucleusPair_iff]
  refine ⟨⟨by decide, by decide, ?_⟩, ⟨by decide, by decide, ?_⟩,
    ⟨bot_le, bot_le, ?_⟩⟩ <;> intro q hq <;> fin_cases q <;> first | decide | exact (hq rfl).elim

/-! ### The present-tense cells of (45) as a morphome -/

/-- Person. -/
inductive Person
  | first
  | second
  | third
  deriving DecidableEq, Fintype

/-- Number. -/
inductive Number
  | sg
  | pl
  deriving DecidableEq, Fintype

/-- The present-tense cells of the paradigm (41). -/
abbrev GCell := Person × Number

/-- The two present-tense stems of *sprechen*, (41) to (43). -/
inductive GStem
  | sprech
  | sprich
  deriving DecidableEq

/-- The stem of each present-tense cell of *sprechen*, (41). -/
def sprechen : GCell → GStem
  | (.second, .sg) | (.third, .sg) => .sprich
  | _ => .sprech

/-- The features of the paradigm. -/
inductive GFeature
  | person
  | number
  deriving DecidableEq, Fintype

/-- The partitions the features induce. -/
def gFeatures : GFeature → Setoid GCell
  | .person => Setoid.ker Prod.fst
  | .number => Setoid.ker Prod.snd

instance (i : GFeature) : DecidableRel (gFeatures i) := by
  cases i <;> exact Setoid.ker.decidableRel _

/-- The cells of the special stem: second and third singular. -/
def specialCells : Finset GCell := {(.second, .sg), (.third, .sg)}

theorem sprechen_formCells : formCells sprechen .sprich = specialCells := by decide

/-- The special cells are a value conjunction of neither feature. -/
theorem specialCells_not_natural : ¬ IsValueConjunction gFeatures ↑specialCells := by
  rw [isValueConjunction_coe_iff]
  decide

/-- The pattern (45) is morphomic, as the book says citing [aronoff-1994]: the cells the special
stem serves are a syncretism class and no natural class of the paradigm. -/
theorem spricht_morphome : IsMorphome sprechen (IsValueConjunction gFeatures) ↑specialCells :=
  isMorphome_of_formCells sprechen (.second, .sg) _ sprechen_formCells (by decide)
    specialCells_not_natural

/-! ### The Same Verb Problem -/

/-- The lexemes of Section 5.6: main verb *take* and *take part*, (57) to (59); the two *draw*s
of (60) and *withdraw*, (62); and the homophones *ring*, *wring* and *ring* 'encircle'. -/
inductive Lexeme
  | take
  | takePart
  | drawPicture
  | drawElicit
  | withdraw
  | ring
  | wring
  | ringCity
  deriving DecidableEq, Fintype

/-- The morphosyntax-phonology pivots, one per relational coindex shared across lexemes. -/
inductive Pivot
  | take
  | draw
  | ring
  | wring
  | ringCity
  deriving DecidableEq, Fintype

/-- Tense. -/
inductive Tense
  | pres
  | past
  deriving DecidableEq, Fintype

/-- The paradigm linkage: each lexeme selects its pivot in every cell, with the cell's own
property set. -/
def linkage : Linkage Lexeme Pivot Tense where
  stems
    | .take, _ | .takePart, _ => {.take}
    | .drawPicture, _ | .drawElicit, _ | .withdraw, _ => {.draw}
    | .ring, _ => {.ring}
    | .wring, _ => {.wring}
    | .ringCity, _ => {.ringCity}
  pm _ σ := σ

/-- Two lexemes are the same verb when they share their form correspondents at every cell:
the relational coindex 23 of (60), a shared morphosyntax and phonology with no shared
semantics. -/
def SameVerb (l₁ l₂ : Lexeme) : Prop := ∀ σ, linkage.corr l₁ σ = linkage.corr l₂ σ

instance : DecidableRel SameVerb := λ l₁ l₂ =>
  inferInstanceAs (Decidable (∀ σ, linkage.corr l₁ σ = linkage.corr l₂ σ))

/-- Same verbs inflect alike at every cell, whatever their semantics: (57) to (61). -/
theorem realize_eq_of_sameVerb {W : Type*} [DecidableEq W] (rf : Pivot → Tense → W)
    {l₁ l₂ : Lexeme} (h : SameVerb l₁ l₂) (σ : Tense) :
    linkage.realize rf l₁ σ = linkage.realize rf l₂ σ :=
  linkage.realize_eq_of_corr_eq_lexeme rf (h σ)

/-- Sameness of verb is nondirectional: no use is the basic one, Section 3.6. -/
theorem SameVerb.symm {l₁ l₂ : Lexeme} (h : SameVerb l₁ l₂) : SameVerb l₂ l₁ :=
  λ σ => (h σ).symm

/-- The two *draw*s, (60), *take* with *take part*, (58), and *withdraw* with *draw*, (62), are
the same verb; the homophones *ring*, *wring* and *ring* 'encircle' are not. -/
example : SameVerb .drawPicture .drawElicit ∧ SameVerb .take .takePart ∧
    SameVerb .withdraw .drawPicture ∧ ¬ SameVerb .ring .wring ∧ ¬ SameVerb .ring .ringCity := by
  decide

/-! ### The regular paradigm -/

/-- The six cells of (16). -/
inductive VCell
  | pres
  | pres3sg
  | past
  | inf
  | prespt
  | ptcp
  deriving DecidableEq, Fintype

/-- The exponents of the regular paradigm (19): none for the present and the infinitive, whose
phonology is coindexed with the stem's. -/
inductive Exponent
  | bare
  | s
  | t
  | ing
  deriving DecidableEq

/-- The paradigm of *walk*, (19). -/
def walk : VCell → Exponent
  | .pres | .inf => .bare
  | .pres3sg => .s
  | .past | .ptcp => .t
  | .prespt => .ing

/-- The double coindexation of Section 4.3 as a syncretism: the present and the infinitive
share the stem's phonology, and the past the past participle's. -/
theorem walk_syncretism :
    formCells walk .bare = {.pres, .inf} ∧ formCells walk .t = {.past, .ptcp} := by
  decide

/-! ### Structural Intersection -/

/-- The schema (6) over the two slots of an *-ish* adjective, base and affix: the affix pinned,
the base a variable. -/
def ishSchema : Schema (Fin 2) (Flat String) := ⟨![⊥, ↑"ish"], {0}⟩

/-- Structural Intersection constructs the schema: the description of (6) is the meet of the
three sisters of (5), keeping what they share and leaving a variable where they differ. -/
theorem ishSchema_body_eq_inf :
    ishSchema.body = Forms.piggish.slots ⊓ Forms.childish.slots ⊓ Forms.sluggish.slots := by
  funext v
  fin_cases v <;> decide

/-- The schema is the most the sisters have in common: a description is instantiated by all
three exactly when it is instantiated by the schema's description. -/
theorem instantiates_ishSchema_iff {s : Schema (Fin 2) (Flat String)} :
    s.Instantiates ishSchema.body ↔
      s.Instantiates Forms.piggish.slots ∧ s.Instantiates Forms.childish.slots ∧
        s.Instantiates Forms.sluggish.slots := by
  rw [ishSchema_body_eq_inf, Schema.instantiates_inf_iff, Schema.instantiates_inf_iff,
    and_assoc]

theorem ishSchema_le_foolish : ishSchema.body ≤ Forms.foolish.slots := λ i => by
  fin_cases i <;> decide

/-- A newly encountered sister intersected with the schema yields the schema again, the
Minimal Generalization Learner's fixed point. -/
theorem ishSchema_inf_foolish : ishSchema.body ⊓ Forms.foolish.slots = ishSchema.body :=
  inf_eq_left.2 ishSchema_le_foolish

end JackendoffAudring2020
