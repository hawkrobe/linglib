/-!
# Russian Verbal Prefixes
@cite{svenonius-2004} @cite{dendikken-1995}

Lexical entries for Russian verbal prefixes, encoding @cite{svenonius-2004}'s
basic typological distinction between **lexical** and **superlexical**
prefixes — the central organizing fact about Slavic verbal prefixation.

## The lex/superlex distinction (@cite{svenonius-2004})

@cite{svenonius-2004} (abstract): "Most Slavic prefixes can be assigned
to one of two large categories, lexical and superlexical. The lexical
prefixes are like Germanic particles, in having resultative meanings,
often spatial, but often idiosyncratic. The superlexical prefixes are
like adverbs or auxiliary verbs, having aspectual and quantificational
meanings."

Structurally (paper §1):
- **Lexical** prefixes are R[esult] heads INSIDE VP — predicates of small
  clauses, analogous to Germanic verb particles.
- **Superlexical** prefixes are Asp[ect] heads OUTSIDE VP — adverbial,
  aspectual operators.

The *same* prefix can be either category. Svenonius's running example
is *za-* (paper §1):
- *Helder za-brosil mjač v vorota angličan* 'Helder kicked the ball
  into the English goal' — *za-* lexical, transparently resultative
  ('into'). Past form `za-brosil` of perfective infinitive *zabrosit'*.
- *Ricardo nervno za-brosal mjač* 'Ricardo began to nervously throw
  the ball' — *za-* superlexical INCP (inceptive 'start'). Past form
  `za-brosal` of imperfective infinitive *zabrosat'*.

Svenonius's terminology note (paper fn. 1): "superlexical" = Townsend's
"sublexical" = Isačenko's *Aktionsart* (originally *soveršajemost'
glagol'nogo dejstvija*).

## Diagnostic 56c: superlexicals select imperfective stems

@cite{svenonius-2004} §4.1 establishes six diagnostics for the
superlexical class. Diagnostic 56c is operationalised here: every
superlexical entry in the inventory has imperfective `stemAspect` (see
`svenonius_56c_superlex_selects_impf` below). Lexical entries have no
such constraint — they freely combine with either aspect base.

## Connection to den Dikken's affixal-particle thesis

@cite{dendikken-1995} (book §5.2.5 fn. 10) cites Russian *napisat'*
and Polish *zjeść* as instances of his "affixal particle" class —
alongside Dutch *ver-*, Sanuma *-ma*, Indonesian *-kan*. The
classification here is consistent with that claim for the **lexical**
prefixes (which are SC predicates per @cite{svenonius-2004}). For the
superlexicals, which originate outside VP and are adverbial,
@cite{dendikken-1995}'s affixal-particle category does not subdivide
the lex/superlex split that @cite{svenonius-2004} establishes.

## Cross-references

- `Fragments/{Dutch,Norwegian,German}/VerbParticles.lean` — Germanic
  VPC family. The Russian lexical prefixes are typologically the
  closest analogue per @cite{svenonius-2004} abstract.
- `Phenomena/Constructions/Causatives/Studies/Dendikken1995.lean` —
  the affixal-particle thesis from @cite{dendikken-1995} ch. 5.

## Scope

Records the lex/superlex categorial distinction with 6 entries (3
lexical, 3 superlexical, plus a *za-* minimal pair). Does NOT
formalize:
- The internal structure of the superlexical aspectual hierarchy
  (paper §3 details, including stacking orders).
- Secondary imperfectives (the *zabrosit'* → *zabrasyvat'* derivation;
  paper §4.5 evidence for lex/superlex structural ordering).
- Stacking of multiple superlexicals (Bulgarian *po-na-razkaža*-style
  cases).
- Cross-Slavic variation (Bulgarian, Polish facts in paper §2-§3).
- Additional superlexical subtypes the paper distinguishes (excessive
  *pere-*, attenuative *po-*, terminative *ot-*; the inventory here
  uses 6 of the ~9 subtypes).

-/

namespace Fragments.Russian.VerbalPrefixes

/-- Russian aspect — perfective vs imperfective. The bare stem of a
    Russian verb has one of these values; prefix application can shift
    aspect (lexical prefixes typically perfectivise; superlexical
    prefixes select imperfective stems per @cite{svenonius-2004}'s
    diagnostic 56c). -/
inductive Aspect where
  | perfective
  | imperfective
  deriving DecidableEq, Repr

/-- The aspectual subtypes @cite{svenonius-2004} identifies for the
    superlexical class (paper §3). Six of the ~9 subtypes the paper
    distinguishes; excessive, attenuative, and terminative deferred. -/
inductive SuperlexicalSubtype where
  /-- Delimitative: 'a bit, for a while' (canonical: *po-*). -/
  | delimitative
  /-- Cumulative: 'a lot, in quantity' (canonical: *na-* on cumulative
      reading). -/
  | cumulative
  /-- Completive: 'finish, complete' (canonical: *iz-*; *do-* per
      broader Slavicist literature, e.g. Romanova 2004). -/
  | completive
  /-- Repetitive: 're-, again' (canonical: *pere-*). -/
  | repetitive
  /-- Inceptive: 'start, begin' (canonical: *za-* on the (1c) reading). -/
  | inceptive
  /-- Distributive: 'one by one, distributively' (canonical Russian:
      *po-*; Bulgarian: *pere-*; allomorphy noted in paper §3 fn. 8). -/
  | distributive
  deriving DecidableEq

/-- @cite{svenonius-2004}'s lex/superlex split as a single ADT —
    the superlexical case carries its subtype, eliminating the need
    for a separate `Option`-typed field plus a consistency theorem
    (per CLAUDE.md "Don't encode conclusions as definitions"). -/
inductive PrefixClass where
  /-- Lexical: R-head inside VP, resultative/spatial,
      Germanic-particle-like. -/
  | lexical
  /-- Superlexical: Asp-head outside VP, aspectual/quantificational,
      adverb-like. The aspectual subtype is carried as an argument. -/
  | superlexical (subtype : SuperlexicalSubtype)
  deriving DecidableEq

/-- A Russian prefixed-verb entry. Uses Latin transliteration with
    final palatalisation marker `'` (consistent with @cite{svenonius-2004}
    and other linglib Russian fragments). -/
structure RussianPrefixedVerbEntry where
  /-- Bare verb stem (infinitive form, with final `'` for soft-sign
      ending). E.g. *brosit'* (PF), *brosat'* (IMPF), *nesti* (IMPF). -/
  bareStem        : String
  /-- Aspect of the bare stem before prefixation. Critical because
      Svenonius's diagnostic 56c distinguishes lex/superlex by which
      stem aspect is selected. -/
  stemAspect      : Aspect
  /-- The prefix morpheme (without dash). Field name shortened to `pfx`
      because `prefix` is a reserved Lean keyword. -/
  pfx             : String
  /-- The prefixed perfective infinitive (transparently formed by
      `pfx ++ bareStem` for the entries below; secondary
      morphophonological adjustments like *iz-* + voiceless stem →
      *is-* are not modelled and are absent from these entries). -/
  prefixedForm    : String
  /-- Lexical or superlexical (with subtype). -/
  prefixClass     : PrefixClass
  /-- Gloss of the bare stem (e.g. 'throw'). -/
  baseGloss       : String
  /-- Gloss of the prefixed perfective (e.g. 'throw into'). -/
  prefixedGloss   : String

/-! ## Lexical prefixes (R-heads, Germanic-particle-like) -/

/-- *za-brosit'* = 'kick into / throw into'. Paper §1 ex. (1a) —
    canonical lexical *za-*: transparently resultative spatial. Built
    on perfective base *brosit'*. -/
abbrev zabrosit : RussianPrefixedVerbEntry where
  bareStem := "brosit'"; stemAspect := .perfective
  pfx := "za"; prefixedForm := "zabrosit'"
  prefixClass := .lexical
  baseGloss := "throw"; prefixedGloss := "throw into, kick into"

/-- *vy-brosit'* = 'throw out'. Lexical *vy-* (analogous to English
    particle *out*; paper (4a) p. 207 cites secondary impf
    *vy-brasyvatj*). Built on perfective base *brosit'*. -/
abbrev vybrosit : RussianPrefixedVerbEntry where
  bareStem := "brosit'"; stemAspect := .perfective
  pfx := "vy"; prefixedForm := "vybrosit'"
  prefixClass := .lexical
  baseGloss := "throw"; prefixedGloss := "throw out"

/-- *pri-nesti* = 'bring' ('carry to'). Lexical *pri-* (allative).
    Built on imperfective determinate motion stem *nesti*. The lex
    classification of *pri-* is from broader Slavicist literature
    (e.g. Romanova 2004, Babko-Malaya 2003); paper §1-§5 doesn't
    work *pri-* as an example. -/
abbrev prinesti : RussianPrefixedVerbEntry where
  bareStem := "nesti"; stemAspect := .imperfective
  pfx := "pri"; prefixedForm := "prinesti"
  prefixClass := .lexical
  baseGloss := "carry"; prefixedGloss := "bring (carry to)"

/-! ## Superlexical prefixes (Asp-heads, adverb-like) -/

/-- *za-brosat'* = 'start throwing'. Paper §1 ex. (1c) — canonical
    superlexical *za-* (inceptive). Minimal pair with `zabrosit`
    above on the same prefix string *za-* but different `prefixClass`.
    Built on imperfective base *brosat'* (Svenonius diagnostic 56c). -/
abbrev zabrosat_inceptive : RussianPrefixedVerbEntry where
  bareStem := "brosat'"; stemAspect := .imperfective
  pfx := "za"; prefixedForm := "zabrosat'"
  prefixClass := .superlexical .inceptive
  baseGloss := "throw"; prefixedGloss := "start throwing"

/-- *po-sidet'* = 'sit for a while'. Canonical superlexical *po-*
    (delimitative). Built on imperfective base *sidet'*. -/
abbrev posidet : RussianPrefixedVerbEntry where
  bareStem := "sidet'"; stemAspect := .imperfective
  pfx := "po"; prefixedForm := "posidet'"
  prefixClass := .superlexical .delimitative
  baseGloss := "sit"; prefixedGloss := "sit for a while"

/-- *do-pisat'* = 'finish writing'. Superlexical *do-* (completive;
    *do-* is the standard Russian completive per broader Slavicist
    literature — paper §3 lists *iz-* as the canonical Bulgarian
    completive in (57)/(58)c). Built on imperfective base *pisat'*. -/
abbrev dopisat : RussianPrefixedVerbEntry where
  bareStem := "pisat'"; stemAspect := .imperfective
  pfx := "do"; prefixedForm := "dopisat'"
  prefixClass := .superlexical .completive
  baseGloss := "write"; prefixedGloss := "finish writing"

def inventory : List RussianPrefixedVerbEntry :=
  [zabrosit, vybrosit, prinesti, zabrosat_inceptive, posidet, dopisat]

/-! ## Concatenation theorems

The transparent prefix+stem concatenation property holds for all
entries here (we picked entries where no morphophonological
adjustment intervenes; voicing-assimilation prefixes (*iz-*, *raz-*,
*voz-*, *bez-*) with obstruent stems are deliberately avoided here. -/

theorem zabrosit_concat : zabrosit.prefixedForm = zabrosit.pfx ++ zabrosit.bareStem := rfl
theorem vybrosit_concat : vybrosit.prefixedForm = vybrosit.pfx ++ vybrosit.bareStem := rfl
theorem prinesti_concat : prinesti.prefixedForm = prinesti.pfx ++ prinesti.bareStem := rfl
theorem zabrosat_concat :
    zabrosat_inceptive.prefixedForm = zabrosat_inceptive.pfx ++ zabrosat_inceptive.bareStem := rfl
theorem posidet_concat  : posidet.prefixedForm  = posidet.pfx  ++ posidet.bareStem  := rfl
theorem dopisat_concat  : dopisat.prefixedForm  = dopisat.pfx  ++ dopisat.bareStem  := rfl

/-! ## Diagnostic theorems -/

/-- @cite{svenonius-2004}'s diagnostic 56c: superlexical prefixes
    select imperfective stems. Verified across the inventory. Lexical
    entries have no aspect-selection constraint (vacuously satisfy
    the implication). -/
theorem svenonius_56c_superlex_selects_impf :
    inventory.all (fun e =>
      match e.prefixClass with
      | .lexical => true
      | .superlexical _ => decide (e.stemAspect = Aspect.imperfective)) = true :=
  by decide

end Fragments.Russian.VerbalPrefixes
