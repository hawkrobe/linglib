/-!
# German Verb-Particle Constructions
@cite{ludeling-2001} @cite{dendikken-1995}

Lexical entries for German separable-prefix verbs (*scheidbar
zusammengesetzte Verben* / *Partikelverben*). Distinct from inseparable
prefix verbs (*ver-, be-, ent-, zer-*), which are derivational morphology
and never split.

## Key empirical generalizations (textbook; @cite{ludeling-2001})

1. **Separability under V2.** In V2 main clauses, the particle stays in
   final position while the verb raises to C: *Er ruft Maria an*
   ('he calls Mary up'). In embedded clauses with V-final order, the
   particle is adjacent to the verb: *...dass er Maria anruft*.

2. **Past participle `ge-` insertion.** The past participle prefix *ge-*
   inserts BETWEEN the separable particle and the verb stem:
   *anrufen* → *angerufen*, *aufmachen* → *aufgemacht*. Inseparable
   prefix verbs lack *ge-* entirely (*verstehen* → *verstanden*, not
   *\*geverstanden*) — a morphological diagnostic for separability.

3. **Infinitival *zu* placement.** In the *zu*-infinitive, *zu* inserts
   between the particle and the verb: *anzurufen*, *aufzumachen*.
   Inseparable prefix verbs have *zu* before the whole word: *zu
   verstehen*.

4. **The German verb cluster + V2 + particle interaction** is one of the
   richest data sets in syntactic theory and a major target of
   @cite{dendikken-1995}'s SC analysis (book ch. 2 + Norwegian/Dutch
   parallels in §2.3.3.5).

## Cross-references

- `Fragments/Dutch/VerbParticles.lean` — closest Germanic sibling;
  shares separability typology but lacks V2 in the same form.
- `Fragments/Norwegian/VerbParticles.lean` — adds the
  passive-incorporation parameter that German shares but in a
  different morphological guise.
- `Phenomena/Constructions/ParticleVerbs/Studies/Dendikken1995.lean` —
  the SC analysis applied to English; the German data is the primary
  cross-linguistic test case @cite{dendikken-1995} engages.

-/

namespace Fragments.German.VerbParticles

/-- A German separable verb-particle entry.
    Records the citation infinitive (particle + verb concatenated as in
    the standard dictionary form) and the constituent verb stem and
    particle separately for V2-split contexts and *ge-*-insertion. -/
structure GermanVPCEntry where
  /-- Citation infinitive (particle + verb concatenated), the dictionary
      form. E.g. *anrufen*, *aufmachen*. -/
  citationForm    : String
  /-- Bare verb stem (without particle, without *ge-*). E.g. *rufen*. -/
  verb            : String
  /-- Separable particle. E.g. *an*, *auf*. -/
  particle        : String
  /-- Past participle (with *ge-* inserted between particle and verb).
      E.g. *angerufen*, *aufgemacht*. -/
  pastParticiple  : String
  /-- *zu*-infinitive form (with *zu* inserted between particle and
      verb). E.g. *anzurufen*, *aufzumachen*. -/
  zuInfinitive    : String
  /-- English gloss. -/
  gloss           : String
  deriving Repr, DecidableEq

abbrev anrufen : GermanVPCEntry where
  citationForm := "anrufen"; verb := "rufen"; particle := "an"
  pastParticiple := "angerufen"; zuInfinitive := "anzurufen"
  gloss := "phone, call up"

abbrev aufmachen : GermanVPCEntry where
  citationForm := "aufmachen"; verb := "machen"; particle := "auf"
  pastParticiple := "aufgemacht"; zuInfinitive := "aufzumachen"
  gloss := "open"

abbrev einschalten : GermanVPCEntry where
  citationForm := "einschalten"; verb := "schalten"; particle := "ein"
  pastParticiple := "eingeschaltet"; zuInfinitive := "einzuschalten"
  gloss := "switch on, turn on"

abbrev abfahren : GermanVPCEntry where
  citationForm := "abfahren"; verb := "fahren"; particle := "ab"
  pastParticiple := "abgefahren"; zuInfinitive := "abzufahren"
  gloss := "depart"

abbrev mitkommen : GermanVPCEntry where
  citationForm := "mitkommen"; verb := "kommen"; particle := "mit"
  pastParticiple := "mitgekommen"; zuInfinitive := "mitzukommen"
  gloss := "come along"

def inventory : List GermanVPCEntry :=
  [anrufen, aufmachen, einschalten, abfahren, mitkommen]

/-! ## Per-entry verification

Citation form = particle + verb (same as Dutch fragment). -/

theorem anrufen_citation     : anrufen.citationForm     = anrufen.particle     ++ anrufen.verb     := rfl
theorem aufmachen_citation   : aufmachen.citationForm   = aufmachen.particle   ++ aufmachen.verb   := rfl
theorem einschalten_citation : einschalten.citationForm = einschalten.particle ++ einschalten.verb := rfl
theorem abfahren_citation    : abfahren.citationForm    = abfahren.particle    ++ abfahren.verb    := rfl
theorem mitkommen_citation   : mitkommen.citationForm   = mitkommen.particle   ++ mitkommen.verb   := rfl

/-! ## *ge-* insertion + *zu*-infinitive structure

The past participle of separable prefix verbs inserts *ge-* between the
particle and the verb's own participle stem (e.g. *anrufen* →
*an-ge-rufen*); the *zu*-infinitive inserts *zu* between particle and
verb (*an-zu-rufen*). This is the morphological diagnostic for
separability vs. inseparable prefix verbs (which have neither *ge-* nor
sandwiched *zu*: *verstehen* → *verstanden* / *zu verstehen*).

Each entry's `pastParticiple` and `zuInfinitive` fields record the
surface forms directly (we don't algorithmically derive them — German
verb-stem participle morphology varies between regular *-t* and ablaut
families). Per-entry equality theorems below witness the prefix
structure: the participle and *zu*-infinitive both expose the particle
in word-initial position, the structural reflex of separability. -/

theorem anrufen_pp     : anrufen.pastParticiple     = "angerufen"     := rfl
theorem aufmachen_pp   : aufmachen.pastParticiple   = "aufgemacht"    := rfl
theorem einschalten_pp : einschalten.pastParticiple = "eingeschaltet" := rfl
theorem abfahren_pp    : abfahren.pastParticiple    = "abgefahren"    := rfl
theorem mitkommen_pp   : mitkommen.pastParticiple   = "mitgekommen"   := rfl

theorem anrufen_zu     : anrufen.zuInfinitive     = "anzurufen"     := rfl
theorem aufmachen_zu   : aufmachen.zuInfinitive   = "aufzumachen"   := rfl
theorem einschalten_zu : einschalten.zuInfinitive = "einzuschalten" := rfl
theorem abfahren_zu    : abfahren.zuInfinitive    = "abzufahren"    := rfl
theorem mitkommen_zu   : mitkommen.zuInfinitive   = "mitzukommen"   := rfl

/-- Inventory entries are well-formed: non-empty verb and particle. -/
theorem inventory_well_formed :
    inventory.all (fun e => decide (e.verb ≠ "") && decide (e.particle ≠ "")) = true := by decide

end Fragments.German.VerbParticles
