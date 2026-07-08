import Linglib.Syntax.Reciprocal
import Linglib.Studies.Siloni2012
import Linglib.Studies.Winter2018
import Linglib.Fragments.Romance.BrazilianPortuguese.Reciprocals
import Linglib.Fragments.Romance.Catalan.Reciprocals
import Linglib.Fragments.Romance.Italian.Reciprocals
import Linglib.Fragments.Romance.Spanish.Reciprocals
import Linglib.Fragments.Swahili.Reciprocals

/-!
# Palmieri (2024): Lexical and Grammatical Reciprocity

[palmieri-2024]

LOT Dissertation 670, Utrecht University. Chapter 2 (Romance) is
formalized here; the Swahili chapters and the reflexivity/reciprocity
questionnaires are Todos.

Romance is not monolithically syntactic about reciprocity, against the
language-level lex-syn parameter of [siloni-2012]
(`Siloni2012.italian.formation = .syntactic`): a class of verbs ('hug',
'kiss', 'meet', 'marry', …) has BOTH a transitive entry — whose
reciprocal reading requires *se*, the grammatical strategy — and an
intransitive lexical reciprocal entry that surfaces without *se* in
language-specific environments (Table 2.2: BP finite clauses, analytic
causatives in all four languages, Spanish/Catalan absolute
participials). Definition (44): a Romance lexical reciprocal is a verb
with some construction where a reciprocal interpretation emerges without
*se* or any other reciprocity element.

The semantic diagnostic is **pseudo-reciprocity** (§4.3): grammatical
reciprocity accumulates unidirectional events (their (50)), while
lexical reciprocals denote a single collective event, subsuming
[winter-2018]'s plain reciprocals (symmetric bases, 'meet') and
non-plain ones — 'divorce' fails the collective-to-unidirectional
direction (their (53)) and 'kiss' the converse (their (54)), matching
Winter's Table 3 rows (`divorce_agrees_with_winter`,
`kiss_agrees_with_winter`). Without *se* only the pseudo-reciprocal
reading survives; *se*-clauses with lexical reciprocals are three-ways
ambiguous (§4.3, p. 38). The reciprocal 'with'-construction tracks the
lexical class (§4.4, after [kemmer-1993]), including non-symmetric
members ('confer', 'break up') and *si*-retaining Italian instances —
refining [siloni-2012]'s French-based restriction.

## Main declarations

* `VerbClass` — Table 2.1's three classes, with `combinesWithSe`,
  `reciprocityByItself`, and the two-entry `formations`.
* `Language`, `Environment`, `seOmissible` — Table 2.2.
* `SeReading` + `readingsWith`/`readingsWithoutSe` — the §4.3 ambiguity
  and its *se*-less resolution.
* `withConstruction_iff_lexical` — the 'with'-construction tracks
  lexical formation across the class system.
* `romance_not_monolithic` — the recorded divergence from [siloni-2012].
* `lexicalReciprocals` — the (43) verb list across BP/Catalan/Italian/
  Spanish.
-/

namespace Palmieri2024

open Reciprocal

/-! ### The three verb classes (Table 2.1) -/

/-- Table 2.1: the three classes of Romance verbs. -/
inductive VerbClass where
  /-- 'chat' (It. *chiacchierare*): no transitive entry, cannot combine
      with *se*, invariably reciprocal by itself (their (31)). -/
  | reciprocalIntransitive
  /-- 'describe': unambiguously transitive; reciprocity only through the
      grammatical *se* strategy (their (32)). -/
  | plainTransitive
  /-- 'hug': a transitive entry that combines with *se*, plus a lexical
      reciprocal entry that surfaces without *se* in the Table 2.2
      environments (their (34), (38), (40), (42)). -/
  | reciprocalTransitive
  deriving DecidableEq, Repr

/-- Whether the class combines with *se* (Table 2.1, column 1). -/
def VerbClass.combinesWithSe : VerbClass → Bool
  | .reciprocalIntransitive => false
  | .plainTransitive        => true
  | .reciprocalTransitive   => true

/-- Whether the class expresses reciprocity by itself (Table 2.1,
    column 2). -/
def VerbClass.reciprocityByItself : VerbClass → Bool
  | .reciprocalIntransitive => true
  | .plainTransitive        => false
  | .reciprocalTransitive   => true

/-- The formation loci a class realizes: the two-entry proposal (p. 30).
    Class 3 has both a lexical reciprocal entry and a transitive entry
    fed by the grammatical (*se*) strategy — [siloni-2012]'s formation
    contrast is verb-level in Romance, not language-level. -/
def VerbClass.formations : VerbClass → List Formation
  | .reciprocalIntransitive => [.lexical]
  | .plainTransitive        => [.syntactic]
  | .reciprocalTransitive   => [.lexical, .syntactic]

/-- The recorded divergence from [siloni-2012]: Italian carries lexical
    reciprocal entries (class 3, e.g. *abbracciare* 'hug', (40)) even
    though the language-level lex-syn parameter classifies Italian as
    syntax-set. The newer work draws the comparison (chronological
    dependency). -/
theorem romance_not_monolithic :
    Formation.lexical ∈ VerbClass.reciprocalTransitive.formations ∧
    Siloni2012.italian.formation = Formation.syntactic :=
  ⟨List.mem_cons_self .., rfl⟩

/-! ### The se-less environments (Table 2.2) -/

/-- The four Romance languages of chapter 2. -/
inductive Language where
  | brazilianPortuguese
  | italian
  | spanish
  | catalan
  deriving DecidableEq, Repr

/-- The syntactic environments where class-3 verbs may express
    reciprocity without *se* (§3). -/
inductive Environment where
  /-- Finite clauses (their (34): BP *Mary e Lisa abraçaram*). -/
  | finiteClause
  /-- Analytic causatives (their (38b), (40): Sp. *hice abrazar*,
      It. *ho fatto abbracciare*). -/
  | analyticCausative
  /-- Absolute constructions with participials (their (42b): Ca.
      *abraçats en Teo i la Ana*). -/
  | absoluteParticipial
  deriving DecidableEq, Repr

/-- Table 2.2: whether a class-3 verb can receive a reciprocal
    interpretation without *se* in a given environment. -/
def seOmissible : Language → Environment → Bool
  | .brazilianPortuguese, .finiteClause        => true
  | .brazilianPortuguese, .analyticCausative   => true
  | .brazilianPortuguese, .absoluteParticipial => false
  | .italian,             .analyticCausative   => true
  | .italian,             _                    => false
  | .spanish,             .finiteClause        => false
  | .spanish,             _                    => true
  | .catalan,             .finiteClause        => false
  | .catalan,             _                    => true

/-- Every language has a diagnostic environment — lexical reciprocity is
    detectable in all four languages (the existence claim behind
    definition (44)); analytic causatives are the pan-Romance
    diagnostic. -/
theorem every_language_diagnosable :
    ∀ l : Language, seOmissible l .analyticCausative = true := by
  intro l; cases l <;> rfl

/-! ### Readings and the se-less disambiguation (§4.3) -/

/-- The readings available to a plural-subject clause (§4.3, p. 38):
    the lexical pseudo-reciprocal (single collective event), the
    grammatical plain reciprocal (accumulated unidirectional events,
    their (50)), and the grammatical reflexive. -/
inductive SeReading where
  | lexicalPseudoReciprocal
  | grammaticalReciprocal
  | grammaticalReflexive
  deriving DecidableEq, Repr

/-- Readings of a *se*-clause by verb class: class-3 *se*-clauses are
    three-ways ambiguous (their (56a)/(57a)); plain transitives lack the
    lexical reading (their (55)); class-1 verbs do not combine with
    *se*. -/
def readingsWithSe : VerbClass → List SeReading
  | .reciprocalIntransitive => []
  | .plainTransitive        => [.grammaticalReciprocal, .grammaticalReflexive]
  | .reciprocalTransitive   =>
      [.lexicalPseudoReciprocal, .grammaticalReciprocal,
       .grammaticalReflexive]

/-- Readings without *se* (in a Table 2.2 environment): only the
    pseudo-reciprocal survives — the reflexive/reciprocal ambiguity
    disappears (p. 30; their (56b)/(57b): no reflexive reading without
    *se*). -/
def readingsWithoutSe : VerbClass → List SeReading
  | .plainTransitive => []
  | _                => [.lexicalPseudoReciprocal]

/-- The *se*-less disambiguation: dropping *se* from a class-3 clause
    removes exactly the grammatical readings. -/
theorem seless_kills_grammatical_readings :
    readingsWithoutSe .reciprocalTransitive =
      [.lexicalPseudoReciprocal] ∧
    SeReading.grammaticalReflexive ∉
      readingsWithoutSe .reciprocalTransitive := by
  exact ⟨rfl, by decide⟩

/-! ### Pseudo-reciprocity and Winter's Table 3 (§4.3) -/

/-- Their (53) matches [winter-2018]'s *divorce* row: the collective
    form does not entail two unidirectional relations (a divorce can be
    initiated by one side) — Pr₂ fails. -/
theorem divorce_agrees_with_winter :
    Winter2018.divorce.pr2 = some false := rfl

/-- Their (54) matches [winter-2018]'s *kiss* row: two unidirectional
    kisses do not make a mutual kiss — Pr₁ fails. -/
theorem kiss_agrees_with_winter :
    Winter2018.kiss.pr1 = some false := rfl

/-! ### The reciprocal 'with'-construction (§4.4) -/

/-- Whether the class allows the reciprocal 'with'-construction: yes for
    both lexical classes — including non-symmetric members, *contra*
    the symmetric-only restriction (their (59): It. *consultarsi con*,
    *lasciarsi con*; attested *baciarsi con*, *abbracciarsi con* (60)) —
    and never for unambiguous transitives (their (61):
    \**ringraziarsi con*). NB the Italian construction retains *si*,
    unlike French (\**s'est embrassé avec*, [siloni-2012] via
    ex. 39 of that discussion) — the availability contrast is
    class-level, not language-level. -/
def VerbClass.allowsWithConstruction : VerbClass → Bool
  | .plainTransitive => false
  | _                => true

/-- The [kemmer-1993] generalization over the class system: the
    'with'-construction is available exactly where a lexical entry is —
    derived by relating the two independent class tables. -/
theorem withConstruction_iff_lexical (c : VerbClass) :
    c.allowsWithConstruction = true ↔ Formation.lexical ∈ c.formations := by
  cases c <;> simp [VerbClass.allowsWithConstruction, VerbClass.formations]

/-! ### The (43) verb list -/

/-- A lexical reciprocal meaning attested with a transitive alternate,
    with the languages attesting it (their (43)). -/
structure LexicalReciprocal where
  gloss : String
  languages : List Language
  deriving DecidableEq, Repr

/-- Their (43): lexical reciprocals with a transitive alternate across
    BP (b), Catalan (c), Italian (i), and Spanish (s). -/
def lexicalReciprocals : List LexicalReciprocal :=
  let bp := Language.brazilianPortuguese
  let c := Language.catalan
  let i := Language.italian
  let s := Language.spanish
  [ ⟨"break up", [c, i, s]⟩
  , ⟨"confer", [bp, i, s]⟩
  , ⟨"cuddle", [i, s]⟩
  , ⟨"date", [bp, i]⟩
  , ⟨"greet", [bp]⟩
  , ⟨"hug", [bp, c, i, s]⟩
  , ⟨"kiss", [bp, c, i, s]⟩
  , ⟨"know each other", [i]⟩
  , ⟨"marry", [bp, c, i, s]⟩
  , ⟨"meet", [bp, c, i, s]⟩
  , ⟨"run into each other", [c, i, s]⟩ ]

/-- Per-language lexical-reciprocal inventories, from the Appendix A
    fragment data (`Fragments/Romance/{Lang}/Reciprocals.lean`). -/
def inventory : Language → List Verb
  | .brazilianPortuguese => BrazilianPortuguese.Reciprocals.lexicalReciprocals
  | .italian             => Italian.Reciprocals.lexicalReciprocals
  | .spanish             => Spanish.Reciprocals.lexicalReciprocals
  | .catalan             => Catalan.Reciprocals.lexicalReciprocals

/-- Every language's fragment attests lexical reciprocals — the
    Appendix A grounding of definition (44). -/
theorem every_language_attests :
    ∀ l : Language, inventory l ≠ [] := by
  intro l; cases l <;> decide

/-- The witness behind `romance_not_monolithic`, grounded in the
    Italian fragment: *abbracciare* 'hug' (their (40)) carries a lexical
    reciprocal entry alongside its homophonous transitive alternate. -/
theorem abbracciare_grounds_divergence :
    "abbracciare" ∈ Italian.Reciprocals.lexicalReciprocals.map Verb.form := by
  decide

/-- Swahili lexical reciprocals ([palmieri-2024] ch. 4, Appendix C) may
    lack a binary base altogether: *jibizana* 'discuss' is in the
    reciprocal inventory but in no derivational pair — lexical
    reciprocity is not always derivational, the Bantu analogue of
    Romance class 1. -/
theorem jibizana_no_binary_base :
    "jibizana" ∈ Swahili.Reciprocals.lexicalReciprocals.map Verb.form ∧
    ∀ p ∈ Swahili.Reciprocals.derivedFrom, p.1.form ≠ "jibizana" := by
  decide

end Palmieri2024
