module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Multiset.Basic
public import Linglib.Data.UD.UPOS

/-!
# The lexical alphabet of syntactic objects

The leaves of syntactic objects are drawn from `SO₀`, the lexical items and syntactic features. This
file defines that alphabet: categorial features `Cat`, a selectional stack `SelStack` consumed left
to right, the feature bundle `SimpleLI` of a category and its selectional requirements,
`LexicalItem` as a nonempty list of bundles (a head that has incorporated another carries both), and
`LexicalItem.Token`, a lexical item with the index that tells its tokens apart. It is
carrier-agnostic; the carrier built over tokens is `SyntacticObject/Basic.lean`. `ConventionDir` is
the harmonic head-side parameter, and `uposToCat` the map from Universal Dependencies part-of-speech
tags into `Cat`.

## Main definitions

* `Minimalist.Cat`, `Minimalist.SelStack`, `Minimalist.SimpleLI`, `Minimalist.LexicalItem`,
  `Minimalist.LexicalItem.Token`
* `Minimalist.ConventionDir`

## References

* [marcolli-chomsky-berwick-2025], §1.1 (Definition 1.1.1) and §1.13 (Lemma 1.13.5)
* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist

/-- The categorial features, the head categories of the clausal spine and the nominal and
    adpositional extended projections. -/
inductive Cat where
  | V     -- verb
  | N     -- noun
  | A     -- adjective
  | P     -- preposition
  | D     -- determiner
  | T     -- tense
  | C     -- complementizer
  | v     -- light verb
  | n     -- nominal categorizer / gender (little-n, [marantz-2001]; Distributed Morphology)
  | a     -- adjectival categorizer (little-a, [panagiotidis-2015]; DegP complement)
  | Place -- locational head ([dendikken-2010]; PlaceP, F1 in adpositional EP)
  | Path  -- directional head ([dendikken-2010] [svenonius-2010]; PathP, F2 in adpositional EP)
  | Num   -- number ([ritter-1991]; NumP between nP and QP/DP)
  | Dem   -- demonstrative ([cinque-2005]; DemP above NumP in the nominal extended projection)
  | Q     -- quantity / classifier ([borer-2005]; QP between NumP and DP)
  | Voice -- Voice head ([kratzer-1996]; [schaefer-2008])
  | Appl  -- Applicative head ([pylkkanen-2008]; [cuervo-2003])
  | Foc   -- focus ([rizzi-1997] split-CP; hosts [FoC] feature, triggers A-bar movement)
  | Top   -- topic ([rizzi-1997] split-CP; hosts [G]/givenness, topic fronting)
  | Fin   -- finiteness ([rizzi-1997] split-CP; allocutive probe in Magahi/Galician)
  | SA    -- speech act head ([speas-tenny-2003]; hosts speaker/addressee)
  /-- The say/assertion layer ([major-2021], [krifka-2023], [moulton-2009]), embedding the
      content of a verbal or representational sign. Unlike the root illocutionary layer `SA`, it
      is clause-internal, in the embedded left periphery with Say > Foc > T, and requires no CP
      ([kiss-2023], [egressy-2026]). -/
  | Say
  | Force -- force ([rizzi-1997] split-CP; clause-typing [decl]/[interrog])
  | Neg   -- negation ([pollock-1989]; [zanuttini-1997]; hosts [±neg])
  | Mod   -- modality ([cinque-1999]; modal auxiliaries)
  | Rel   -- relative (cartographic left periphery, [rizzi-1997])
  | Pol   -- polarity ([laka-1990]; ΣP for affirmation/negation)
  | Asp   -- aspect ([cinque-1999]; inner inflectional, between Voice and T)
  | Evid  -- evidential ([cinque-1999]; outer inflectional, above T below Fin)
  /-- The nominalizer ([keine-2020]): the Hindi nominalized clause, a clause type distinct from
      CP. -/
  | Nmlz
  /-- The inherent-case shell ([newman-2024]): KP wraps DP for oblique or inherent case. -/
  | K
  deriving Repr, DecidableEq, Inhabited

/-- A selectional stack, consumed left to right. -/
abbrev SelStack := List Cat

/-- A category with its selectional stack, and optionally a phonological form for
    linearization. -/
structure SimpleLI where
  cat : Cat
  sel : SelStack
  phonForm : String := ""
  /-- The [wh] feature, read by wh-movement and the multiple-wh-fronting parameter. -/
  wh : Bool := false
  /-- The [E] feature, which leaves the head's complement unpronounced ([merchant-2001]). -/
  ellipsis : Bool := false
  deriving Repr, DecidableEq

/-- A lexical item is a nonempty list of feature bundles, one for a simple item and several for a
    head that has incorporated others. -/
structure LexicalItem where
  features : List SimpleLI
  nonempty : features ≠ []
  deriving Repr, DecidableEq

/-- The simple lexical item with one feature bundle. -/
def LexicalItem.simple (cat : Cat) (sel : SelStack) (phonForm : String := "") (wh : Bool := false)
    (ellipsis : Bool := false) : LexicalItem :=
  ⟨[⟨cat, sel, phonForm, wh, ellipsis⟩], by simp⟩

/-- The outer, projecting category, that of the first feature bundle. -/
def LexicalItem.outerCat (li : LexicalItem) : Cat := (li.features.head li.nonempty).cat

/-- The outer selectional stack, that of the first feature bundle. -/
def LexicalItem.outerSel (li : LexicalItem) : SelStack := (li.features.head li.nonempty).sel

/-- The outer [wh] feature, that of the first feature bundle. -/
def LexicalItem.outerWh (li : LexicalItem) : Bool := (li.features.head li.nonempty).wh

/-- The outer [E] feature, that of the first feature bundle. -/
def LexicalItem.outerEllipsis (li : LexicalItem) : Bool := (li.features.head li.nonempty).ellipsis

/-- The outer phonological form, that of the first feature bundle, or `none` for a silent
item. -/
def LexicalItem.outerPhonForm? (li : LexicalItem) : Option String :=
  let p := (li.features.head li.nonempty).phonForm
  if p.isEmpty then none else some p

/-- A complex lexical item carries more than one feature bundle. -/
def LexicalItem.IsComplex (li : LexicalItem) : Prop := 1 < li.features.length

instance (li : LexicalItem) : Decidable li.IsComplex := inferInstanceAs (Decidable (_ < _))

/-- Head-to-head movement: the target keeps projecting, with the mover's bundles appended. -/
def LexicalItem.combine (target mover : LexicalItem) : LexicalItem :=
  ⟨target.features ++ mover.features, by
    cases htf : target.features with
    | nil => exact absurd htf target.nonempty
    | cons hd tl => simp⟩

/-- A token of a lexical item. Syntactic objects are compared as values, so two occurrences of
one item, the two *the*s of a transitive clause, are different leaves only through their tokens;
the index tells apart the tokens of one item, and tokens of different items differ anyway. -/
structure LexicalItem.Token where
  /-- The lexical item. -/
  item : LexicalItem
  /-- The index among the tokens of `item`. -/
  id : ℕ
  deriving Repr, DecidableEq

/-- The placeholder head of a bare trace, which remembers no token. Selection reads it as a
saturated silent noun, and its index lies above those lexical tokens use, so it equals none of
them. -/
def LexicalItem.Token.bareTrace : LexicalItem.Token := ⟨.simple .N [], 10000⟩

/-! ### Head-side convention (MCB Lemma 1.13.5) -/

/-- The harmonic head-side convention: a head function determines a planar embedding by placing
    the head daughter to the left (`initial`) or to the right (`final`) of every binary node
    ([marcolli-chomsky-berwick-2025], Lemma 1.13.5). -/
inductive ConventionDir where
  | initial
  | final
  deriving Repr, DecidableEq, Inhabited

/-- The category of a Universal Dependencies part-of-speech tag. -/
def uposToCat : UD.UPOS → Cat
  | .VERB  => .V
  | .AUX   => .T
  | .NOUN  => .N
  | .PROPN => .N  -- proper nouns are N (but project to DP)
  | .ADJ   => .A
  | .ADP   => .P
  | .DET   => .D
  | .SCONJ => .C
  | .CCONJ => .C
  | _      => .N  -- default

end Minimalist
