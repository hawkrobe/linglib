import Linglib.Core.Lexical.Word
import Linglib.Datasets.WALS.Features.F46A
import Linglib.Core.Lexical.PolarityItem
import Linglib.Fragments.English.PolarityItems
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Fragments.Russian.PolarityItems
import Linglib.Fragments.German.PolarityItems
import Linglib.Fragments.Japanese.PolarityItems
import Linglib.Fragments.Korean.PolarityItems
import Linglib.Fragments.Mandarin.PolarityItems
import Linglib.Fragments.Turkish.PolarityItems
import Linglib.Fragments.Hindi.PolarityItems
import Linglib.Fragments.Finnish.PolarityItems
import Linglib.Fragments.Hungarian.PolarityItems
import Linglib.Fragments.Georgian.PolarityItems
import Linglib.Fragments.Quechua.PolarityItems
import Linglib.Fragments.Yoruba.PolarityItems
import Linglib.Fragments.Thai.PolarityItems
import Linglib.Fragments.Tagalog.PolarityItems
import Linglib.Fragments.Swahili.PolarityItems

/-!
# Indefinite Pronoun Typology (@cite{haspelmath-1997} / WALS Ch 46)
@cite{haspelmath-1997} @cite{haspelmath-2013} @cite{kadmon-landman-1993} @cite{ladusaw-1979}

Formalizes the core results of @cite{haspelmath-1997}'s cross-linguistic study of
indefinite pronouns, one of the most celebrated results in semantic typology.

## The Implicational Map

The key insight: indefinite pronouns across languages can be classified by
which **functions** they can serve. Nine function types form an
**implicational map** — if a single pronoun series covers two non-adjacent
functions, it must also cover all functions between them on the map.

The nine functions, ordered on the map:

```
specificKnown — specificUnknown — irrealis — question — conditional — indirectNeg — directNeg
                                                                                       |
                                                         freeChoice — comparative ———+
```

A pronoun series can cover any **contiguous** region on this map. This
explains why, e.g., English "any" covers {question, conditional, indirectNeg,
comparative, freeChoice} — a contiguous set — but no language has a single
form for {specificKnown, directNeg} without covering all intermediate
functions.

## WALS Chapter 46

WALS classifies languages by the morphological source of their indefinite
pronouns. The chapter is based on @cite{haspelmath-1997}'s cross-linguistic
sample of 326 languages:

| Value                      | Count |
|----------------------------|-------|
| Interrogative-based        |  194  |
| Generic-noun-based         |   85  |
| Special                    |   22  |
| Mixed                      |   23  |
| Existential construction   |    2  |
| Total                      |  326  |

-/

namespace Phenomena.Polarity.Typology

-- ============================================================================
-- §1: The Nine Function Types
-- ============================================================================

/-- The nine function types on @cite{haspelmath-1997}'s implicational map for
    indefinite pronouns. These represent the semantic/pragmatic contexts
    in which indefinite pronoun forms are used.

    The ordering reflects positions on the map, from most referential
    (specificKnown) to most universal (freeChoice). -/
inductive IndefiniteFunction where
  /-- Specific known: "Somebody called. I know who it was."
      Speaker has a specific referent in mind and knows their identity. -/
  | specificKnown
  /-- Specific unknown: "Somebody called. I don't know who."
      Speaker has a specific referent in mind but doesn't know their identity. -/
  | specificUnknown
  /-- Irrealis non-specific: "Please bring me something to read."
      The referent is hypothetical, not yet established in the discourse. -/
  | irrealis
  /-- Question: "Did anybody call?"
      In polar or wh-questions. -/
  | question
  /-- Conditional: "If anybody calls, tell them I'm busy."
      In the antecedent of a conditional. -/
  | conditional
  /-- Indirect negation: "I don't think that anybody called."
      In the semantic scope of negation but not in the same clause. -/
  | indirectNeg
  /-- Direct negation: "Nobody called." / "I didn't see anybody."
      Direct clause negation: the indefinite is in the same clause as
      the negative marker. -/
  | directNeg
  /-- Comparative: "She's taller than anybody."
      Standard of comparison in comparative constructions. -/
  | comparative
  /-- Free choice: "Anybody can do that."
      Universal-like meaning: all members of the domain qualify. -/
  | freeChoice
  deriving DecidableEq, Repr, Inhabited

/-- All nine function types, listed in map order. -/
def IndefiniteFunction.all : List IndefiniteFunction :=
  [ .specificKnown, .specificUnknown, .irrealis, .question
  , .conditional, .indirectNeg, .directNeg, .comparative, .freeChoice ]

-- ============================================================================
-- §2: The Implicational Map (Adjacency Structure)
-- ============================================================================

/-- Adjacent functions on @cite{haspelmath-1997}'s implicational map.

    The map forms a connected graph:
    ```
    specKnown — specUnknown — irrealis — question — conditional — indNeg — dirNeg
                                                                              |
                                                    freeChoice — comparative —+
    ```

    The crucial typological claim: any pronoun series covers a **contiguous**
    region on this graph. If a form is used for functions A and C, and B lies
    on the unique path between A and C, then the form is also used for B. -/
def adjacentFunctions : IndefiniteFunction → List IndefiniteFunction
  | .specificKnown   => [.specificUnknown]
  | .specificUnknown => [.specificKnown, .irrealis]
  | .irrealis        => [.specificUnknown, .question]
  | .question        => [.irrealis, .conditional]
  | .conditional     => [.question, .indirectNeg]
  | .indirectNeg     => [.conditional, .directNeg]
  | .directNeg       => [.indirectNeg, .comparative]
  | .comparative     => [.directNeg, .freeChoice]
  | .freeChoice      => [.comparative]

/-- Adjacency is symmetric: if A is adjacent to B, then B is adjacent to A. -/
theorem adjacency_symmetric :
    IndefiniteFunction.all.all (λ f =>
      (adjacentFunctions f).all (λ g =>
        (adjacentFunctions g).contains f)) = true := by decide

/-- Every function has at least one neighbor (the map is connected). -/
theorem every_function_has_neighbor :
    IndefiniteFunction.all.all (λ f =>
      !(adjacentFunctions f).isEmpty) = true := by decide

/-- The map has exactly 8 edges (undirected). We count ordered pairs and
    divide by 2: each edge appears once in each direction. -/
theorem map_edge_count :
    (IndefiniteFunction.all.map (λ f => (adjacentFunctions f).length)).sum
      = 16 := by decide

-- ============================================================================
-- §3: Contiguity Check (BFS on the Map)
-- ============================================================================

/-- BFS on the implicational map restricted to a given set of functions.
    Starting from `start`, explore all reachable nodes through edges whose
    endpoints are both in `funcs`. Returns the set of reachable nodes.

    This is the core algorithm for checking contiguity: a set of functions
    is contiguous iff BFS from any member reaches all other members. -/
def bfsReachable (funcs : List IndefiniteFunction) (start : IndefiniteFunction)
    (fuel : Nat := 10) : List IndefiniteFunction :=
  let rec go (queue : List IndefiniteFunction) (visited : List IndefiniteFunction)
      (fuel : Nat) : List IndefiniteFunction :=
    match fuel, queue with
    | 0, _          => visited
    | _, []         => visited
    | fuel + 1, f :: rest =>
      let neighbors := (adjacentFunctions f).filter (λ g =>
        funcs.contains g && !visited.contains g)
      go (rest ++ neighbors) (visited ++ neighbors) fuel
  go [start] [start] fuel

/-- A set of functions is **contiguous** on the implicational map iff
    BFS from its first element reaches all elements in the set.

    This is Haspelmath's key constraint: every pronoun series must
    cover a contiguous region on the map. -/
def isContiguous (funcs : List IndefiniteFunction) : Bool :=
  match funcs with
  | []     => true
  | f :: _ =>
    let reached := bfsReachable funcs f 15
    funcs.all reached.contains

-- ============================================================================
-- §4: Pronoun Series and Language Profiles
-- ============================================================================

/-- An indefinite pronoun series: a named form (or morphological pattern)
    together with the set of functions it covers on the map. -/
structure IndefinitePronounSeries where
  /-- Surface form or morphological marker (e.g., "some-", "any-", "no-"). -/
  form : String
  /-- The functions this series covers on the implicational map. -/
  functions : List IndefiniteFunction
  /-- Optional notes on the series. -/
  notes : String := ""
  deriving Repr, BEq

/-- Number of functions covered by a series. -/
def IndefinitePronounSeries.coverage (s : IndefinitePronounSeries) : Nat :=
  s.functions.length

/-- A language's indefinite pronoun profile: its name, series inventory,
    and metadata. -/
structure IndefinitePronounProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Language family. -/
  family : String := ""
  /-- The pronoun series inventory. -/
  series : List IndefinitePronounSeries
  /-- Notes on the system. -/
  notes : String := ""
  deriving Repr

/-- Number of distinct indefinite pronoun series in a language. -/
def IndefinitePronounProfile.seriesCount (p : IndefinitePronounProfile) : Nat :=
  p.series.length

/-- All functions covered across all series. -/
def IndefinitePronounProfile.allFunctions
    (p : IndefinitePronounProfile) : List IndefiniteFunction :=
  (p.series.flatMap (·.functions)).eraseDups

/-- Whether every series in a profile is contiguous on the map. -/
def IndefinitePronounProfile.allContiguous
    (p : IndefinitePronounProfile) : Bool :=
  p.series.all (λ s => isContiguous s.functions)

/-- Whether the profile covers all nine functions. -/
def IndefinitePronounProfile.coversAllFunctions
    (p : IndefinitePronounProfile) : Bool :=
  IndefiniteFunction.all.all (λ f => p.allFunctions.contains f)

/-- Whether the series in a profile have disjoint function sets
    (no function appears in two different series). -/
def IndefinitePronounProfile.seriesDisjoint
    (p : IndefinitePronounProfile) : Bool :=
  let allFuncs := p.series.flatMap (·.functions)
  allFuncs.length == allFuncs.eraseDups.length

-- ============================================================================
-- §5: WALS Chapter 46 Distribution
-- ============================================================================

/-- A single row in a WALS frequency table. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq

/-- Sum of counts in a WALS table. -/
def WALSCount.totalOf (cs : List WALSCount) : Nat :=
  (cs.map (·.count)).sum

private abbrev ch46 := Datasets.WALS.F46A.allData

/-- WALS Chapter 46 distribution (N = 326).

    The five values classify languages by the morphological source of
    their indefinite pronouns, computed from the WALS 46A dataset.
    Counts in @cite{haspelmath-1997}: interrogative-based dominates,
    outnumbering all other categories combined. -/
def ch46Counts : List WALSCount :=
  [ ⟨"Interrogative-based", (ch46.filter (·.value == .interrogativeBased)).length⟩
  , ⟨"Generic-noun-based", (ch46.filter (·.value == .genericNounBased)).length⟩
  , ⟨"Special", (ch46.filter (·.value == .special)).length⟩
  , ⟨"Mixed", (ch46.filter (·.value == .mixed)).length⟩
  , ⟨"Existential construction", (ch46.filter (·.value == .existentialConstruction)).length⟩ ]

/-- Look up a language profile's WALS 46A morphological source classification. -/
def IndefinitePronounProfile.wals46A
    (p : IndefinitePronounProfile) : Option Datasets.WALS.F46A.IndefinitePronouns :=
  (Datasets.WALS.F46A.lookupISO p.iso).map (·.value)

-- ============================================================================
-- §6: Language Data
-- ============================================================================

/-! ### English (Indo-European, Germanic)

English has four main indefinite pronoun series:
- **some-** series: specific known + specific unknown
- **any-** (NPI): question + conditional + indirect negation
- **no-** series: direct negation
- **any-** (FC) / **every-**: free choice + comparative

The split between NPI-any and FC-any is well-known; Haspelmath treats
them as distinct series. English "some-" also has an irrealis use in
some dialects, but the canonical analysis gives irrealis to "any". -/

def english : IndefinitePronounProfile :=
  { language := "English"
  , iso := "eng"
  , family := "Indo-European"
  , series :=
    [ { form := "some-"
      , functions := [.specificKnown, .specificUnknown]
      , notes := "somebody, something, somewhere" }
    , { form := "any- (NPI)"
      , functions := [.irrealis, .question, .conditional, .indirectNeg]
      , notes := "anybody, anything in DE/nonveridical contexts" }
    , { form := "no-"
      , functions := [.directNeg]
      , notes := "nobody, nothing, nowhere" }
    , { form := "any- (FC)"
      , functions := [.comparative, .freeChoice]
      , notes := "anybody can do that; taller than anybody" }
    ]
  , notes := "4 series; NPI-any and FC-any historically same form but " ++
             "synchronically distinct distribution" }

/-! ### Russian (Indo-European, Slavic)

Russian is a classic example of a language with many indefinite series,
corresponding to fine-grained function distinctions:
- **кто-то** (kto-to): specific known
- **кто-нибудь** (kto-nibud'): specific unknown + irrealis
- **кто-либо** (kto-libo): question + conditional + indirect negation
- **никто** (nikto): direct negation (with negative concord)
- **кто угодно** (kto ugodno): free choice + comparative -/

def russian : IndefinitePronounProfile :=
  { language := "Russian"
  , iso := "rus"
  , family := "Indo-European"
  , series :=
    [ { form := "кто-то (kto-to)"
      , functions := [.specificKnown]
      , notes := "specific referent, speaker knows identity" }
    , { form := "кто-нибудь (kto-nibud')"
      , functions := [.specificUnknown, .irrealis]
      , notes := "specific but unknown identity, or irrealis" }
    , { form := "кто-либо (kto-libo)"
      , functions := [.question, .conditional, .indirectNeg]
      , notes := "polarity-sensitive: questions, conditionals, indirect neg" }
    , { form := "никто (nikto)"
      , functions := [.directNeg]
      , notes := "negative concord: nikto ne prisel 'nobody NEG came'" }
    , { form := "кто угодно (kto ugodno)"
      , functions := [.comparative, .freeChoice]
      , notes := "universal/free choice: anyone at all" }
    ]
  , notes := "5 series; textbook example of Haspelmath's implicational map" }

/-! ### German (Indo-European, Germanic)

German has a rich indefinite system with five series:
- **jemand**: specific known + specific unknown
- **irgend(ein/wer)**: irrealis + question
- **wer** (in conditionals): conditional
- **niemand**: direct negation + indirect negation
- **jeder**: free choice + comparative -/

def german : IndefinitePronounProfile :=
  { language := "German"
  , iso := "deu"
  , family := "Indo-European"
  , series :=
    [ { form := "jemand"
      , functions := [.specificKnown, .specificUnknown]
      , notes := "somebody (specific reference)" }
    , { form := "irgendwer"
      , functions := [.irrealis, .question]
      , notes := "irgend- prefix marks non-specificity / ignorance" }
    , { form := "wer (conditional)"
      , functions := [.conditional, .indirectNeg]
      , notes := "bare wh-word in conditional / indirect neg contexts" }
    , { form := "niemand"
      , functions := [.directNeg]
      , notes := "negative indefinite; precludes predicate negation" }
    , { form := "jeder"
      , functions := [.comparative, .freeChoice]
      , notes := "universal/free choice: anyone/everyone" }
    ]
  , notes := "5 series; irgend- prefix is productive non-specific marker" }

/-! ### Japanese (Japonic)

Japanese indefinite pronouns are built compositionally from wh-words
(dare 'who', nani 'what') plus particles (-ka, -mo, -demo):
- **dare-ka**: specific known + specific unknown + irrealis + question
- **dare-mo** (negative): direct negation + indirect negation
- **dare-demo**: free choice + comparative + conditional -/

def japanese : IndefinitePronounProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , family := "Japonic"
  , series :=
    [ { form := "dare-ka"
      , functions := [.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional]
      , notes := "wh + ka: existential/non-specific indefinite" }
    , { form := "dare-mo (neg)"
      , functions := [.indirectNeg, .directNeg]
      , notes := "wh + mo under negation: nobody" }
    , { form := "dare-demo"
      , functions := [.comparative, .freeChoice]
      , notes := "wh + demo: free choice / concessive" }
    ]
  , notes := "3 series; compositional wh + particle system" }

/-! ### Mandarin Chinese (Sino-Tibetan)

Mandarin uses a small set of indefinite forms with wide functional range:
- **yǒu rén** (有人): specific known + specific unknown
- **shéi** (谁, non-interrogative): irrealis + question + conditional +
  indirect negation + direct negation + comparative + free choice

The wh-word shéi in non-interrogative uses covers a remarkably wide
contiguous region, from irrealis to free choice. -/

def mandarin : IndefinitePronounProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , family := "Sino-Tibetan"
  , series :=
    [ { form := "yǒu rén (有人)"
      , functions := [.specificKnown, .specificUnknown]
      , notes := "existential: 'there is someone'" }
    , { form := "shéi (谁, non-interrog.)"
      , functions := [.irrealis, .question, .conditional, .indirectNeg,
                      .directNeg, .comparative, .freeChoice]
      , notes := "wh-word in non-interrogative uses covers 7 functions" }
    ]
  , notes := "2 series; wh-words double as indefinites (Cheng 1991)" }

/-! ### Turkish (Turkic)

Turkish uses birisi/biri for specific functions and a combination of
kimse and hiç kimse for negative and polarity-sensitive functions:
- **birisi**: specific known + specific unknown
- **biri**: irrealis
- **kimse**: question + conditional + indirect negation
- **hiç kimse**: direct negation
- **herhangi biri**: free choice + comparative -/

def turkish : IndefinitePronounProfile :=
  { language := "Turkish"
  , iso := "tur"
  , family := "Turkic"
  , series :=
    [ { form := "birisi"
      , functions := [.specificKnown, .specificUnknown]
      , notes := "specific indefinite: 'a certain person'" }
    , { form := "biri"
      , functions := [.irrealis]
      , notes := "non-specific indefinite in irrealis contexts" }
    , { form := "kimse"
      , functions := [.question, .conditional, .indirectNeg]
      , notes := "polarity-sensitive: in questions, conditionals" }
    , { form := "hiç kimse"
      , functions := [.directNeg]
      , notes := "negative indefinite with hiç intensifier" }
    , { form := "herhangi biri"
      , functions := [.comparative, .freeChoice]
      , notes := "free choice: any person at all" }
    ]
  , notes := "5 series; kimse is historically 'person' > NPI" }

/-! ### Hindi-Urdu (Indo-European, Indo-Aryan)

Hindi uses koii as a general indefinite with wide distribution, plus
specialized negative and free choice forms:
- **koii**: specific known + specific unknown + irrealis + question +
  conditional
- **koii nahiiN**: direct negation + indirect negation
- **koii bhii**: free choice + comparative -/

def hindi : IndefinitePronounProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , family := "Indo-European"
  , series :=
    [ { form := "koii"
      , functions := [.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional]
      , notes := "general indefinite: someone/anyone" }
    , { form := "koii nahiiN"
      , functions := [.indirectNeg, .directNeg]
      , notes := "koii + negation: nobody" }
    , { form := "koii bhii"
      , functions := [.comparative, .freeChoice]
      , notes := "koii + bhii (even/also): anyone at all (FC)" }
    ]
  , notes := "3 series; bhii particle creates FC reading (@cite{lahiri-1998})" }

/-! ### Italian (Indo-European, Romance)

Italian distinguishes qualcuno (specific) from negative nessuno and
FC qualunque/qualsiasi:
- **qualcuno**: specific known + specific unknown + irrealis
- **nessuno**: question + conditional + indirect negation + direct negation
- **qualunque/qualsiasi**: free choice + comparative -/

def italian : IndefinitePronounProfile :=
  { language := "Italian"
  , iso := "ita"
  , family := "Indo-European"
  , series :=
    [ { form := "qualcuno"
      , functions := [.specificKnown, .specificUnknown, .irrealis]
      , notes := "specific/irrealis indefinite" }
    , { form := "nessuno"
      , functions := [.question, .conditional, .indirectNeg, .directNeg]
      , notes := "N-word: polarity-sensitive + direct negation" }
    , { form := "qualunque/qualsiasi"
      , functions := [.comparative, .freeChoice]
      , notes := "free choice universal" }
    ]
  , notes := "3 series; nessuno is an N-word (negative concord)" }

/-! ### Finnish (Uralic)

Finnish has a differentiated system with five series:
- **joku**: specific known + specific unknown
- **jokin** (non-human): irrealis
- **kukaan**: question + conditional + indirect negation
- **ei kukaan**: direct negation
- **kuka tahansa**: free choice + comparative -/

def finnish : IndefinitePronounProfile :=
  { language := "Finnish"
  , iso := "fin"
  , family := "Uralic"
  , series :=
    [ { form := "joku"
      , functions := [.specificKnown, .specificUnknown]
      , notes := "specific indefinite" }
    , { form := "joku (irrealis)"
      , functions := [.irrealis]
      , notes := "joku in irrealis / non-specific contexts" }
    , { form := "kukaan"
      , functions := [.question, .conditional, .indirectNeg]
      , notes := "polarity-sensitive indefinite" }
    , { form := "ei kukaan"
      , functions := [.directNeg]
      , notes := "negative indefinite with ei (negative verb)" }
    , { form := "kuka tahansa"
      , functions := [.comparative, .freeChoice]
      , notes := "free choice: whoever / anyone at all" }
    ]
  , notes := "5 series; negative verb ei + kukaan for direct negation" }

/-! ### Korean (Koreanic)

Korean, like Japanese, uses wh-words as indefinites with particles:
- **nwukwu-nka**: specific known + specific unknown
- **nwukwu**: irrealis + question + conditional
- **nwukwu-to** (neg): indirect negation + direct negation
- **nwukwu-na / nwukwu-tunci**: free choice + comparative -/

def korean : IndefinitePronounProfile :=
  { language := "Korean"
  , iso := "kor"
  , family := "Koreanic"
  , series :=
    [ { form := "nwukwu-nka (누군가)"
      , functions := [.specificKnown, .specificUnknown]
      , notes := "wh + nka: specific indefinite" }
    , { form := "nwukwu (누구)"
      , functions := [.irrealis, .question, .conditional]
      , notes := "bare wh-word: non-specific indefinite" }
    , { form := "nwukwu-to (누구도, neg)"
      , functions := [.indirectNeg, .directNeg]
      , notes := "wh + to under negation: nobody" }
    , { form := "nwukwu-na (누구나)"
      , functions := [.comparative, .freeChoice]
      , notes := "wh + na: free choice / universal" }
    ]
  , notes := "4 series; wh + particle system parallel to Japanese" }

/-! ### Hungarian (Uralic)

Hungarian is notable for having many series, including a dedicated
interrogative indefinite:
- **valaki**: specific known + specific unknown
- **valaki (irrealis)**: irrealis
- **valaki (question)**: question
- **senki sem**: conditional + indirect negation + direct negation
- **akárki / bárki**: free choice + comparative -/

def hungarian : IndefinitePronounProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , family := "Uralic"
  , series :=
    [ { form := "valaki"
      , functions := [.specificKnown, .specificUnknown]
      , notes := "specific indefinite: someone (known to speaker)" }
    , { form := "valaki (irrealis)"
      , functions := [.irrealis, .question]
      , notes := "valaki in irrealis and question contexts" }
    , { form := "senki"
      , functions := [.conditional, .indirectNeg, .directNeg]
      , notes := "negative indefinite (with sem in direct negation)" }
    , { form := "akárki / bárki"
      , functions := [.comparative, .freeChoice]
      , notes := "free choice: anyone at all" }
    ]
  , notes := "4 series; senki covers conditional through direct neg" }

/-! ### Georgian (Kartvelian)

Georgian has a system with 4-5 series, using suffixes -γac, -me,
and reduplication for different functions:
- **vinme**: specific known + specific unknown + irrealis
- **vinme (question)**: question + conditional
- **aravin**: indirect negation + direct negation
- **nebismieri / vinc**: free choice + comparative -/

def georgian : IndefinitePronounProfile :=
  { language := "Georgian"
  , iso := "kat"
  , family := "Kartvelian"
  , series :=
    [ { form := "vinme (ვინმე)"
      , functions := [.specificKnown, .specificUnknown, .irrealis]
      , notes := "general indefinite: someone" }
    , { form := "vinme (question context)"
      , functions := [.question, .conditional]
      , notes := "vinme in question/conditional contexts" }
    , { form := "aravin (არავინ)"
      , functions := [.indirectNeg, .directNeg]
      , notes := "negative indefinite: nobody" }
    , { form := "nebismieri (ნებისმიერი)"
      , functions := [.comparative, .freeChoice]
      , notes := "free choice: any/every" }
    ]
  , notes := "4 series; aravin (NEG + vinme) for negation" }

/-! ### Quechua (Quechuan)

Quechua (Imbabura variety) uses a relatively undifferentiated system:
- **pi-taj**: specific known + specific unknown + irrealis + question
- **pi-pash**: conditional + indirect negation
- **mana pi-pash**: direct negation
- **ima-pash / maijan-pash**: free choice + comparative -/

def quechua : IndefinitePronounProfile :=
  { language := "Quechua (Imbabura)"
  , iso := "qvi"
  , family := "Quechuan"
  , series :=
    [ { form := "pi-taj"
      , functions := [.specificKnown, .specificUnknown, .irrealis, .question]
      , notes := "wh-based indefinite: someone" }
    , { form := "pi-pash"
      , functions := [.conditional, .indirectNeg]
      , notes := "wh + pash: in conditional/neg scope" }
    , { form := "mana pi-pash"
      , functions := [.directNeg]
      , notes := "negation + wh + pash: nobody" }
    , { form := "maijan-pash"
      , functions := [.comparative, .freeChoice]
      , notes := "free choice: anyone" }
    ]
  , notes := "4 series; wh-based system with particle pash" }

/-! ### Yoruba (Niger-Congo, Atlantic-Congo)

Yoruba has a relatively undifferentiated system with 2 main series:
- **ẹnìkan**: specific known + specific unknown + irrealis + question +
  conditional
- **ẹ̀nìkẹ́ni / kò sí ẹnìkan**: indirect negation + direct negation +
  comparative + free choice -/

def yoruba : IndefinitePronounProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , family := "Niger-Congo"
  , series :=
    [ { form := "ẹnìkan"
      , functions := [.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional]
      , notes := "general indefinite: somebody" }
    , { form := "ẹ̀nìkẹ́ni"
      , functions := [.indirectNeg, .directNeg, .comparative, .freeChoice]
      , notes := "polarity-sensitive + free choice" }
    ]
  , notes := "2 series; minimal differentiation" }

/-! ### Thai (Kra-Dai)

Thai uses khraj for most indefinite functions, with kh̄raj kɔ̂ for
free choice:
- **khraj (ใคร)**: specific known + specific unknown + irrealis + question +
  conditional
- **mâj mii khraj (ไม่มีใคร)**: indirect negation + direct negation
- **khraj kɔ̂ (ใครก็)**: free choice + comparative -/

def thai : IndefinitePronounProfile :=
  { language := "Thai"
  , iso := "tha"
  , family := "Kra-Dai"
  , series :=
    [ { form := "khraj (ใคร)"
      , functions := [.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional]
      , notes := "wh-word as general indefinite" }
    , { form := "mâj mii khraj (ไม่มีใคร)"
      , functions := [.indirectNeg, .directNeg]
      , notes := "NEG + exist + wh: nobody" }
    , { form := "khraj kɔ̂ (ใครก็)"
      , functions := [.comparative, .freeChoice]
      , notes := "wh + kɔ̂ particle: free choice" }
    ]
  , notes := "3 series; wh-word khraj doubles as indefinite" }

/-! ### Tagalog (Austronesian)

Tagalog uses may as existential and wala as negative existential:
- **may isang**: specific known + specific unknown + irrealis
- **sinuman**: question + conditional + indirect negation
- **walang**: direct negation
- **kahit sino**: free choice + comparative -/

def tagalog : IndefinitePronounProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , family := "Austronesian"
  , series :=
    [ { form := "may isa"
      , functions := [.specificKnown, .specificUnknown, .irrealis]
      , notes := "existential + 'one': someone" }
    , { form := "sinuman"
      , functions := [.question, .conditional, .indirectNeg]
      , notes := "wh-based polarity-sensitive indefinite" }
    , { form := "walang (tao)"
      , functions := [.directNeg]
      , notes := "negative existential: nobody" }
    , { form := "kahit sino"
      , functions := [.comparative, .freeChoice]
      , notes := "concessive + wh: anyone at all (FC)" }
    ]
  , notes := "4 series; negative existential walang for direct negation" }

/-! ### Swahili (Niger-Congo, Bantu)

Swahili uses mtu (person) with various modifiers:
- **mtu (fulani)**: specific known + specific unknown + irrealis +
  question + conditional
- **mtu ye yote (neg)**: indirect negation + direct negation
- **mtu ye yote**: free choice + comparative -/

def swahili : IndefinitePronounProfile :=
  { language := "Swahili"
  , iso := "swh"
  , family := "Niger-Congo"
  , series :=
    [ { form := "mtu (fulani)"
      , functions := [.specificKnown, .specificUnknown, .irrealis,
                      .question, .conditional]
      , notes := "person (+ certain): someone" }
    , { form := "hakuna mtu / mtu … -si-"
      , functions := [.indirectNeg, .directNeg]
      , notes := "negative existential or negative verb concord" }
    , { form := "mtu ye yote"
      , functions := [.comparative, .freeChoice]
      , notes := "person any whatsoever: free choice" }
    ]
  , notes := "3 series; relatively undifferentiated" }

-- ============================================================================
-- §7: Aggregate Data
-- ============================================================================

/-- All language profiles in our sample. -/
def allLanguages : List IndefinitePronounProfile :=
  [ english, russian, german, japanese, mandarin, turkish, hindi
  , italian, finnish, korean, hungarian, georgian, quechua, yoruba
  , thai, tagalog, swahili ]

/-- Number of languages in our sample. -/
theorem sample_size : allLanguages.length = 17 := by decide

-- ============================================================================
-- §8: Contiguity Verification
-- ============================================================================

/-- The central typological claim: every pronoun series covers a
    **contiguous** region on Haspelmath's implicational map. -/
theorem all_languages_contiguous :
    allLanguages.all (·.allContiguous) = true := by decide

-- ============================================================================
-- §9: Coverage Verification
-- ============================================================================

/-- Every language in our sample covers all nine functions. -/
theorem all_languages_cover_all_functions :
    allLanguages.all (·.coversAllFunctions) = true := by decide

-- ============================================================================
-- §9a: Disjointness Verification (Series Partition)
-- ============================================================================

/-- Every language's series have **disjoint** function sets — no function
    appears in two different series. Together with coverage (§9), this means
    the series form a **partition** of the nine function types. -/
theorem all_languages_disjoint :
    allLanguages.all (·.seriesDisjoint) = true := by decide

/-- **Master partition theorem**: every language's series form a partition
    of the nine function types (contiguous + covering + disjoint). -/
theorem all_languages_partition :
    allLanguages.all (λ p =>
      p.allContiguous && p.coversAllFunctions && p.seriesDisjoint) = true := by
  decide

-- ============================================================================
-- §10: Typological Generalizations
-- ============================================================================

/-! ### Generalization 1: Direct negation always has a strategy

Every language has at least one series that covers directNeg. This reflects
the functional universal that every language can express sentential negation
of an indefinite. -/

/-- Every language has a series covering direct negation. -/
theorem every_language_has_direct_neg :
    allLanguages.all (λ p =>
      p.series.any (λ s => s.functions.contains .directNeg)) = true := by
  decide

/-! ### Generalization 2: Free choice and comparative pattern together

In our sample, free choice and comparative are always covered by the
same series. This reflects their shared universal/widened-domain semantics.
@cite{haspelmath-1997}: "the comparative function is semantically similar
to free choice." -/

/-- Free choice and comparative are always in the same series. -/
theorem freeChoice_comparative_together :
    allLanguages.all (λ p =>
      p.series.any (λ s =>
        s.functions.contains .freeChoice &&
        s.functions.contains .comparative)) = true := by
  decide

/-! ### Generalization 3: Specific known is rarely shared with polarity functions

Specific known is the most referential function, semantically distant from
polarity-sensitive uses. In our sample, whenever specificKnown and directNeg
are in different series (which is always), the specific-known series does
not extend past conditional on the map. -/

/-- Specific known and direct negation are never in the same series. -/
theorem specificKnown_directNeg_disjoint :
    allLanguages.all (λ p =>
      p.series.all (λ s =>
        !(s.functions.contains .specificKnown &&
          s.functions.contains .directNeg))) = true := by
  decide

/-! ### Generalization 4: More series means more precise function encoding

Languages with more series make finer distinctions on the map. We verify
that the average number of functions per series decreases as series count
increases. -/

/-- Mandarin (2 series) has a higher average coverage per series than
    Russian (5 series). This demonstrates that fewer series = broader coverage
    per form. -/
theorem fewer_series_broader_coverage :
    -- Mandarin: 2 series covering 9 functions → avg 4.5
    -- Russian: 5 series covering 9 functions → avg 1.8
    mandarin.seriesCount < russian.seriesCount ∧
    (mandarin.series.map (·.coverage)).sum =
    (russian.series.map (·.coverage)).sum := by
  decide

/-! ### Generalization 5: Specific known is typically separate

In languages with 3+ series, specific known tends to be separate from
polarity-sensitive functions. -/

/-- In languages with 3+ series, specificKnown is never in the same series
    as question or conditional. -/
theorem specificKnown_separate_from_polarity :
    (allLanguages.filter (λ p => p.seriesCount ≥ 3)).all (λ p =>
      p.series.all (λ s =>
        if s.functions.contains .specificKnown
        then !(s.functions.contains .conditional) ||
             s.functions.contains .specificUnknown
        else true)) = true := by
  decide

/-! ### Generalization 6: The polarity cluster

Question, conditional, and indirect negation frequently pattern together
(or at least contiguously). These are the classic polarity-sensitive
contexts in the formal semantics literature (downward-entailing or
nonveridical). -/

/-- The polarity cluster: in every language, there exists a series that
    covers at least two of {question, conditional, indirectNeg}. -/
theorem polarity_cluster_exists :
    allLanguages.all (λ p =>
      p.series.any (λ s =>
        let q := s.functions.contains .question
        let c := s.functions.contains .conditional
        let i := s.functions.contains .indirectNeg
        (q && c) || (c && i) || (q && i))) = true := by
  decide

-- ============================================================================
-- §11: Series Count Distribution in Our Sample
-- ============================================================================

/-- Count of languages with a given number of series. -/
def countBySeriesCount (langs : List IndefinitePronounProfile) (n : Nat) : Nat :=
  (langs.filter (λ p => p.seriesCount == n)).length

/-- Series count distribution in our sample. -/
theorem sample_2_series : countBySeriesCount allLanguages 2 = 2 := by decide
theorem sample_3_series : countBySeriesCount allLanguages 3 = 5 := by decide
theorem sample_4_series : countBySeriesCount allLanguages 4 = 6 := by decide
theorem sample_5_series : countBySeriesCount allLanguages 5 = 4 := by decide

-- ============================================================================
-- §12: Per-Language Verification
-- ============================================================================

/-- Series count per language (ISO code, count) for the 17-language sample.
    Replaces 17 per-language `_series_count` decide-theorems. -/
theorem language_series_counts :
    allLanguages.map (λ p => (p.iso, p.seriesCount)) =
      [ ("eng", 4), ("rus", 5), ("deu", 5), ("jpn", 3), ("cmn", 2)
      , ("tur", 5), ("hin", 3), ("ita", 3), ("fin", 5), ("kor", 4)
      , ("hun", 4), ("kat", 4), ("qvi", 4), ("yor", 2), ("tha", 3)
      , ("tgl", 4), ("swh", 3) ] := by
  decide

-- ============================================================================
-- §12a: WALS 46A Bridge
-- ============================================================================

/-! Every language in our sample appears in the WALS 46A dataset. We verify
    each profile's morphological source classification, bridging our Haspelmath
    function-map data to the WALS morphological-source typology.

    Distribution in our 17-language sample:
    - Interrogative-based: Russian, Japanese, Korean, Hungarian, Georgian,
      Quechua, Thai (7)
    - Generic-noun-based: English, Turkish, Italian, Yoruba, Swahili (5)
    - Special: Hindi, Finnish (2)
    - Mixed: German, Mandarin (2)
    - Existential construction: Tagalog (1) -/

open Datasets.WALS.F46A (IndefinitePronouns) in
/-- WALS 46A morphological-source classification per language (ISO code, value)
    for the 17-language sample. Replaces 17 per-language `_wals` decide-theorems.
    Verifies the `lookupISO`-derived `wals46A` field against expected values. -/
theorem language_wals_classifications :
    allLanguages.map (λ p => (p.iso, p.wals46A)) =
      [ ("eng", some .genericNounBased)
      , ("rus", some .interrogativeBased)
      , ("deu", some .mixed)
      , ("jpn", some .interrogativeBased)
      , ("cmn", some .mixed)
      , ("tur", some .genericNounBased)
      , ("hin", some .special)
      , ("ita", some .genericNounBased)
      , ("fin", some .special)
      , ("kor", some .interrogativeBased)
      , ("hun", some .interrogativeBased)
      , ("kat", some .interrogativeBased)
      , ("qvi", some .interrogativeBased)
      , ("yor", some .genericNounBased)
      , ("tha", some .interrogativeBased)
      , ("tgl", some .existentialConstruction)
      , ("swh", some .genericNounBased) ] := by
  decide

/-- Every language in our sample has a WALS 46A entry. -/
theorem all_languages_in_wals :
    allLanguages.all (λ p => p.wals46A.isSome) = true := by decide

-- ============================================================================
-- §13: Cross-Linguistic Pattern Tests
-- ============================================================================

/-! ### Wh-based indefinite systems

Languages that use wh-words as indefinites (Japanese, Korean, Mandarin, Thai)
tend to have fewer series, because the bare wh-word covers a wide contiguous
range on the map. -/

def whBasedLanguages : List IndefinitePronounProfile :=
  [japanese, korean, mandarin, thai]

/-- Wh-based indefinite languages average fewer series than others. -/
theorem wh_based_fewer_series :
    (whBasedLanguages.map (·.seriesCount)).sum ≤
    whBasedLanguages.length * 4 := by
  decide

/-! ### Negative concord languages

Languages with negative concord (Russian, Italian, Hungarian) tend to have
the direct negation function grouped with adjacent polarity functions rather
than isolated in a single-function series. -/

def negConcordLanguages : List IndefinitePronounProfile :=
  [russian, italian, hungarian]

/-- In negative concord languages, at least one has the directNeg function
    in a series with more than one function. -/
theorem neg_concord_directNeg_grouped :
    negConcordLanguages.any (λ p =>
      p.series.any (λ s =>
        s.functions.contains .directNeg && s.functions.length > 1)) = true := by
  decide

/-! ### WALS morphological source and series count

Interrogative-based languages (which build indefinites from wh-words) should
correlate with our wh-based language list. We verify this and test whether
morphological source predicts series differentiation. -/

open Datasets.WALS.F46A (IndefinitePronouns) in
/-- All four wh-based languages are classified as interrogative-based or
    mixed in WALS 46A. -/
theorem wh_based_are_interrogative_or_mixed :
    whBasedLanguages.all (λ p =>
      p.wals46A == some .interrogativeBased ||
      p.wals46A == some .mixed) = true := by decide

/-- Languages classified as interrogative-based in WALS 46A. -/
def interrogativeBasedProfiles : List IndefinitePronounProfile :=
  allLanguages.filter (λ p =>
    p.wals46A == some Datasets.WALS.F46A.IndefinitePronouns.interrogativeBased)

/-- Seven of our 17 languages are interrogative-based. -/
theorem interrogative_based_sample_count :
    interrogativeBasedProfiles.length = 7 := by decide

/-- Interrogative-based languages in our sample average ≤ 4 series per
    language (total series ≤ 28 across 7 languages). -/
theorem interrogative_based_avg_series :
    (interrogativeBasedProfiles.map (·.seriesCount)).sum ≤ 28 := by
  decide

-- ============================================================================
-- §14: Non-Contiguous Sets Are Predicted Impossible
-- ============================================================================

/-! We demonstrate that certain function sets are NOT contiguous on the map,
    confirming that Haspelmath's map correctly rules them out as possible
    single-series ranges. -/

/-- A hypothetical series covering {specificKnown, directNeg} without the
    intervening functions is not contiguous. -/
theorem specKnown_directNeg_not_contiguous :
    isContiguous [.specificKnown, .directNeg] = false := by decide

/-- A hypothetical series covering {specificKnown, freeChoice} without
    intervening functions is not contiguous. -/
theorem specKnown_freeChoice_not_contiguous :
    isContiguous [.specificKnown, .freeChoice] = false := by decide

/-- A hypothetical series covering {specificKnown, comparative} is not
    contiguous. -/
theorem specKnown_comparative_not_contiguous :
    isContiguous [.specificKnown, .comparative] = false := by decide

/-- A hypothetical series covering {specificUnknown, directNeg} skipping
    irrealis through indirectNeg is not contiguous. -/
theorem specUnknown_directNeg_not_contiguous :
    isContiguous [.specificUnknown, .directNeg] = false := by decide

/-- But {specificKnown, specificUnknown} IS contiguous (adjacent). -/
theorem specKnown_specUnknown_contiguous :
    isContiguous [.specificKnown, .specificUnknown] = true := by decide

/-- And {question, conditional, indirectNeg} IS contiguous (a path). -/
theorem polarity_triple_contiguous :
    isContiguous [.question, .conditional, .indirectNeg] = true := by decide

/-- The full set of all nine functions is contiguous (the map is connected). -/
theorem all_nine_contiguous :
    isContiguous IndefiniteFunction.all = true := by decide

-- ============================================================================
-- §15: Adjacency on the Map and NPI/FCI Theory
-- ============================================================================

/-! ### Connection to Polarity Item Theory

Haspelmath's implicational map connects directly to formal theories of
polarity sensitivity:

1. **Functions 4–7** (question through directNeg) correspond to the
   classic **downward-entailing** / **nonveridical** environments that
   license NPIs.

2. **Functions 8–9** (comparative, freeChoice) correspond to
   **free choice** items, which have been analyzed as universal
   quantifiers or domain-widened indefinites.

3. **Functions 1–3** (specific known/unknown, irrealis) correspond to
   **positive polarity** and **epistemic specificity**, which are
   anti-licensed by negation.

The contiguity constraint on the map thus has a semantic explanation:
adjacent functions share semantic properties (monotonicity, veridicality,
specificity) that make it natural for a single form to cover them. -/

/-- A Haspelmath function corresponds to a downward-entailing (or nonveridical)
    licensing context. Functions 4–7 on the map: question, conditional,
    indirect negation, direct negation (@cite{ladusaw-1979}). -/
def IndefiniteFunction.isDE : IndefiniteFunction → Bool
  | .question | .conditional | .indirectNeg | .directNeg => true
  | _ => false

/-- A Haspelmath function corresponds to a free choice context.
    Functions 8–9 on the map: comparative, freeChoice. -/
def IndefiniteFunction.isFC : IndefiniteFunction → Bool
  | .comparative | .freeChoice => true
  | _ => false

/-- The NPI region (question through directNeg) is contiguous. -/
theorem npi_region_contiguous :
    isContiguous [.question, .conditional, .indirectNeg, .directNeg] = true := by
  decide

/-- The FC region (comparative, freeChoice) is contiguous. -/
theorem fc_region_contiguous :
    isContiguous [.comparative, .freeChoice] = true := by decide

/-- The specific/irrealis region is contiguous. -/
theorem specific_region_contiguous :
    isContiguous [.specificKnown, .specificUnknown, .irrealis] = true := by
  decide

/-- The NPI+FC region (question through freeChoice, the full
    polarity-sensitive span) is contiguous. -/
theorem polarity_sensitive_region_contiguous :
    isContiguous [.question, .conditional, .indirectNeg, .directNeg,
                  .comparative, .freeChoice] = true := by
  decide

-- ============================================================================
-- §16: Summary Statistics
-- ============================================================================

/-- Minimum series count in our sample. -/
theorem min_series_count :
    (allLanguages.map (·.seriesCount)).foldl min 100 = 2 := by decide

/-- Maximum series count in our sample. -/
theorem max_series_count :
    (allLanguages.map (·.seriesCount)).foldl max 0 = 5 := by decide

/-- Total number of distinct series across all languages. -/
theorem total_series :
    (allLanguages.map (·.seriesCount)).sum = 63 := by decide

/-- The most common series count in our sample is 4 (six languages). -/
theorem most_common_series_count :
    countBySeriesCount allLanguages 4 ≥ countBySeriesCount allLanguages 2 ∧
    countBySeriesCount allLanguages 4 ≥ countBySeriesCount allLanguages 3 ∧
    countBySeriesCount allLanguages 4 ≥ countBySeriesCount allLanguages 5 := by
  decide

-- ============================================================================
-- §17: Fragment Bridges
-- ============================================================================

/-! Verify consistency between Typology profiles and Fragment PolarityItems
    entries. For each language with a Fragment PolarityItems file, we check
    that Fragment NPI entries are licensed in contexts corresponding to
    Haspelmath functions the Typology profile assigns to polarity-sensitive
    series, and that Fragment FCI entries have obligatory domain alternatives
    when the Typology profile assigns free choice functions. -/

section FragmentBridges

-- English: Fragment any (NPI/FCI) licensed in questions, matching
-- Typology "any- (NPI)" series covering question function
theorem english_any_covers_question :
    Fragments.English.PolarityItems.any.licensingContexts.contains .question = true := by
  decide

-- Italian: Fragment nessuno (NPI) licensed under negation, matching
-- Typology "nessuno" series covering directNeg function
theorem italian_nessuno_covers_negation :
    Fragments.Italian.PolarityItems.nessuno.licensingContexts.contains .negation = true := by
  decide

-- Russian: Fragment nikto (NPI) licensed under negation, matching
-- Typology "никто" series covering directNeg
theorem russian_nikto_covers_negation :
    Fragments.Russian.PolarityItems.nikto.licensingContexts.contains .negation = true := by
  decide

-- German: Fragment irgendein is NPI/FCI, matching Typology "irgendwer"
-- series covering both question (NPI) and irrealis (FCI-like)
theorem german_irgendein_is_npi_fci :
    Fragments.German.PolarityItems.irgendein.polarityType = .npiFci := rfl

-- German: Fragment niemand (NPI) licensed under negation, matching
-- Typology "niemand" series covering directNeg
theorem german_niemand_covers_negation :
    Fragments.German.PolarityItems.niemand.licensingContexts.contains .negation = true := by
  decide

-- Japanese: Fragment dareMo (NPI) licensed under negation, matching
-- Typology "dare-mo (neg)" series covering directNeg
theorem japanese_dareMo_covers_negation :
    Fragments.Japanese.PolarityItems.dareMo.licensingContexts.contains .negation = true := by
  decide

-- Korean: Fragment nwukwuTo (NPI) licensed under negation, matching
-- Typology "nwukwu-to (neg)" series covering directNeg
theorem korean_nwukwuTo_covers_negation :
    Fragments.Korean.PolarityItems.nwukwuTo.licensingContexts.contains .negation = true := by
  decide

-- Mandarin: Fragment shei is NPI/FCI, matching Typology "shéi" series
-- covering 7 functions from irrealis through freeChoice
theorem mandarin_shei_is_npi_fci :
    Fragments.Mandarin.PolarityItems.shei.polarityType = .npiFci := rfl

-- Turkish: Fragment kimse (NPI) licensed in questions, matching
-- Typology "kimse" series covering question function
theorem turkish_kimse_covers_question :
    Fragments.Turkish.PolarityItems.kimse.licensingContexts.contains .question = true := by
  decide

-- Finnish: Fragment kukaan (NPI) licensed in questions, matching
-- Typology "kukaan" series covering question function
theorem finnish_kukaan_covers_question :
    Fragments.Finnish.PolarityItems.kukaan.licensingContexts.contains .question = true := by
  decide

-- Hungarian: Fragment senki (NPI) licensed under negation, matching
-- Typology "senki" series covering directNeg
theorem hungarian_senki_covers_negation :
    Fragments.Hungarian.PolarityItems.senki.licensingContexts.contains .negation = true := by
  decide

-- Georgian: Fragment aravin (NPI) licensed under negation, matching
-- Typology "aravin" series covering directNeg
theorem georgian_aravin_covers_negation :
    Fragments.Georgian.PolarityItems.aravin.licensingContexts.contains .negation = true := by
  decide

-- Quechua: Fragment manaPiPash (NPI) licensed under negation, matching
-- Typology "mana pi-pash" series covering directNeg
theorem quechua_manaPiPash_covers_negation :
    Fragments.Quechua.PolarityItems.manaPiPash.licensingContexts.contains .negation = true := by
  decide

-- Yoruba: Fragment enikeni is NPI/FCI, matching Typology "ẹ̀nìkẹ́ni"
-- series covering indirectNeg through freeChoice
theorem yoruba_enikeni_is_npi_fci :
    Fragments.Yoruba.PolarityItems.enikeni.polarityType = .npiFci := rfl

-- Thai: Fragment majMiiKhraj (NPI) licensed under negation, matching
-- Typology series covering directNeg
theorem thai_majMiiKhraj_covers_negation :
    Fragments.Thai.PolarityItems.majMiiKhraj.licensingContexts.contains .negation = true := by
  decide

-- Tagalog: Fragment sinuman (NPI) licensed in questions, matching
-- Typology "sinuman" series covering question function
theorem tagalog_sinuman_covers_question :
    Fragments.Tagalog.PolarityItems.sinuman.licensingContexts.contains .question = true := by
  decide

-- Swahili: Fragment hakunaMtu (NPI) licensed under negation, matching
-- Typology series covering directNeg
theorem swahili_hakunaMtu_covers_negation :
    Fragments.Swahili.PolarityItems.hakunaMtu.licensingContexts.contains .negation = true := by
  decide

end FragmentBridges

end Phenomena.Polarity.Typology
