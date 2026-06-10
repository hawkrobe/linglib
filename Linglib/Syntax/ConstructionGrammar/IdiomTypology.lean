/-!
# Construction Grammar: Idiom Typology

[fillmore-kay-oconnor-1988] §1's classification of idiomatic expressions,
the founding taxonomy of Construction Grammar: decoding vs. encoding idioms
(following [makkai-1972], §1.1.1), grammatical vs. extragrammatical
(§1.1.2), substantive vs. formal (§1.1.3), and the familiar-pieces
typology of §1.2. Originates with that paper; consumed by later
construction-grammar studies (Kay & Fillmore 1999's WXDY, Osborne & Groß
2012's catena analysis).

## Main declarations

- `IdiomInterpretability`, `IdiomGrammaticality`, `IdiomFormality`: the three classificatory dimensions
- `IdiomType`: their product
- `FamiliarityPattern`: §1.2's pieces × arrangement typology
-/

namespace ConstructionGrammar

/-- Decoding vs. encoding idioms ([fillmore-kay-oconnor-1988] §1.1.1,
following [makkai-1972]). A *decoding* idiom cannot be interpreted without
prior learning ("kick the bucket"). An *encoding* idiom can be understood
on first hearing, but its conventionality must be learned ("answer the
door"). Decoding idioms are generally also encoding idioms. -/
inductive IdiomInterpretability where
  | decoding
  | encoding
  deriving DecidableEq, Repr

/-- Grammatical vs. extragrammatical idioms ([fillmore-kay-oconnor-1988]
§1.1.2). *Grammatical* idioms have words filling proper grammatical slots
("kick the bucket", "spill the beans"); *extragrammatical* idioms have
anomalous structure ("first off", "by and large", "so far so good"). -/
inductive IdiomGrammaticality where
  | grammatical
  | extragrammatical
  deriving DecidableEq, Repr

/-- Substantive vs. formal idioms ([fillmore-kay-oconnor-1988] §1.1.3).
*Substantive* (lexically filled) idioms have fixed lexical content ("kick
the bucket"); *formal* idioms are productive syntactic patterns "dedicated
to semantic and pragmatic purposes not knowable from their form alone"
("the X-er the Y-er"). -/
inductive IdiomFormality where
  | substantive
  | formal
  deriving DecidableEq, Repr

/-- Combined idiom classification: the product of
[fillmore-kay-oconnor-1988] §1.1's three dimensions. -/
structure IdiomType where
  interpretability : IdiomInterpretability
  grammaticality : IdiomGrammaticality
  formality : IdiomFormality
  deriving DecidableEq, Repr

/-- Familiar-pieces typology ([fillmore-kay-oconnor-1988] §1.2): how
familiar are an idiom's pieces, and how familiar is their arrangement?
Unfamiliar pieces unfamiliarly arranged: "kith and kin" (§1.2.1); familiar
pieces unfamiliarly arranged: "all of a sudden", bare "home" (§1.2.2);
familiar pieces familiarly arranged: "hang one on", rhetorical questions
(§1.2.3). -/
inductive FamiliarityPattern where
  | unfamiliarPiecesUnfamiliarlyArranged
  | familiarPiecesUnfamiliarlyArranged
  | familiarPiecesFamiliarlyArranged
  deriving DecidableEq, Repr

end ConstructionGrammar
