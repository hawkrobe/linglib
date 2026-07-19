/-!
# Form status of morphemes
[zwicky-pullum-1983] [bickel-nichols-2007]

Typological classification of bound and free formatives by attachment
position, host selectivity, and syntactic independence.

## Main definitions

- `AttachmentSide`, `FormativePosition`: where a formative attaches.
- `SelectionDegree`: how restrictive a morpheme's host selection is.
- `MorphStatus`: the free-word / clitic / affix scale, with `IsAffix`
  and `IsClitic` predicates.
-/

namespace Features

/-- Side on which a bound morpheme attaches to its host. -/
inductive AttachmentSide where
  | prefix     -- attaches before stem (English *un-*, *re-*)
  | suffix     -- attaches after stem (English *-ed*, *-s*, *-n't*)
  | infix      -- inserts within stem (Tagalog *-um-*)
  | circumfix  -- wraps around stem (German *ge-...-t*)
  deriving DecidableEq, Repr

/-- Typological position classification for formatives.
    [bickel-nichols-2007] Table 3.2 (p. 198), flattened: the table crosses
    five positions (Prae/In/Post/Simul/Detached) with formative types; this
    enum keeps the positions, promoting circumfixation (the table's common
    Simul subtype) and endoclisis (an In subtype) to their own cases.

    Superset of `AttachmentSide`: adds simulfixation, detached formatives
    (Wackernagel clitics, free auxiliaries), and endoclisis (clitic
    insertion inside a word). -/
inductive FormativePosition where
  | praefixed     -- formative precedes host (= `AttachmentSide.prefix`)
  | postfixed     -- formative follows host (= `AttachmentSide.suffix`)
  | infixed       -- formative inserted within host (= `AttachmentSide.infix`)
  | circumfixed   -- formative wraps host (= `AttachmentSide.circumfix`)
  /-- Several tokens of one morpheme realized at different places in the
  word ([bickel-nichols-2007] p. 200, after Hagège) — NOT process
  morphology: bare ablaut, substitution, and subtraction are In-position
  formatives, reduplication is Prae/Post, in the source table. -/
  | simultaneous
  | detached      -- not attached to its host (may still be phonologically bound)
  | endoclitic    -- clitic inserted inside a word (Udi, European Portuguese)
  deriving DecidableEq, Repr

/-- Map `AttachmentSide` to the richer `FormativePosition` classification. -/
def AttachmentSide.toFormativePosition : AttachmentSide → FormativePosition
  | .prefix    => .praefixed
  | .suffix    => .postfixed
  | .infix     => .infixed
  | .circumfix => .circumfixed

/-- How restrictive a morpheme is about what it can attach to.

[zwicky-pullum-1983] criterion A: clitics exhibit low selection
(attach to virtually any word), while affixes exhibit high selection
(attach only to specific stems or categories). -/
inductive SelectionDegree where
  /-- Attaches to words of virtually any category (prepositions, verbs,
      adjectives, adverbs). Characteristic of simple clitics. -/
  | low
  /-- Attaches to words of a single major category (e.g., past tense
      *-ed* to verbs, plural *-s* to nouns). Characteristic of
      inflectional affixes. -/
  | singleCategory
  /-- Attaches only to a closed list of stems (e.g., *-n't* only to
      finite auxiliaries). Maximally selective. -/
  | closedClass
  deriving DecidableEq, Repr

/-- Affixes are more selective than clitics. -/
def SelectionDegree.IsHighSelection (s : SelectionDegree) : Prop :=
  s ≠ .low

instance : DecidablePred SelectionDegree.IsHighSelection := fun s => by
  unfold SelectionDegree.IsHighSelection; exact inferInstance

/-- Morphological status of a linguistic form.

Classifies forms by their degree of syntactic independence and
mode of combination. The clitic–affix boundary is the central
question of [zwicky-pullum-1983]: the criteria A–F serve to
locate a given morpheme on this scale. -/
inductive MorphStatus where
  /-- Syntactically independent word. -/
  | freeWord
  /-- Simple clitic: phonologically bound form that can attach to
      hosts of virtually any syntactic category.
      [bickel-nichols-2007]: defined primarily by low selectivity
      (categorical freedom) + phonological dependence, not necessarily
      by being a reduced variant of a free word. Many simple clitics
      have no free-word counterpart (Latin *-que*). English contracted
      auxiliaries (*'s*, *'ve*, *'d*) are a subcase where a free variant
      exists. -/
  | simpleClitic
  /-- Special clitic: either no corresponding free word
      exists, or the distribution differs from the free word.
      Romance pronominal clitics, Latin *-que*. -/
  | specialClitic
  /-- Inflectional affix: paradigmatic, category-preserving, highly
      selective, with possible gaps and idiosyncrasies.
      English *-ed*, *-s*, *-est*, *-n't*. -/
  | inflAffix
  /-- Derivational affix: potentially category-changing, often
      productive but may show lexical restrictions.
      English *-ness*, *un-*, *-ize*. -/
  | derivAffix
  deriving DecidableEq, Repr

/-- Is this an affix (inflectional or derivational)? -/
def MorphStatus.IsAffix (s : MorphStatus) : Prop :=
  s = .inflAffix ∨ s = .derivAffix

instance : DecidablePred MorphStatus.IsAffix :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Is this a clitic (simple or special)? -/
def MorphStatus.IsClitic (s : MorphStatus) : Prop :=
  s = .simpleClitic ∨ s = .specialClitic

instance : DecidablePred MorphStatus.IsClitic :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Morphological boundness: the coarse two-way cut of the wordhood
scale. A general per-entry morphological feature — relevant to
acquisition ([clark-2017]: free morphemes are acquired more readily
than bound ones) and to coordination typology
([mitrovic-sauerland-2016]), among others. `MorphStatus.boundness`
derives it from the finer scale. -/
inductive Boundness where
  /-- Independent word (Hungarian "is", English "and"). -/
  | free
  /-- Clitic or suffix (Georgian "-c", Latin "-que"). -/
  | bound
  deriving DecidableEq, Repr, BEq

/-- The coarse boundness of a morph status: free words are free,
clitics and affixes are bound. -/
def MorphStatus.boundness : MorphStatus → Boundness
  | .freeWord => .free
  | _ => .bound

end Features
