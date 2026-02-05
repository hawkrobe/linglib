/-
# Kind Reference and Bare Nominals: Empirical Patterns

Theory-neutral data on kind reference, bare nominals, cross-linguistic patterns, scopelessness, and scrambling effects.

## Main definitions

`BareNominalType`, `CrossLingDatum`, `BareSingularDatum`, `ScopeDatum`, `ScramblingPosition`, `ScramblingScopeDatum`, `PredLevel`, `PredicateDatum`, `SingularKindDatum`, `TaxonomicDatum`, `PredicateClass`, `BPInterpDatum`

## References

- Carlson (1977), Chierchia (1998), Dayal (2004), Cohen & Erteschik-Shir (2002), Krifka et al. (1995), Le Bruyn & de Swart (2022), de Hoop (1996), Ruys (2001)
-/

namespace Phenomena.Generics.KindReference

/-- Check if a string contains a substring -/
def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

-- Cross-Linguistic Bare Nominal Patterns

/-- Language typology for bare nominal licensing. -/
inductive BareNominalType where
  | barePluralOnly
  | definiteRequired
  | fullyBare
  | classifier
  deriving Repr, DecidableEq, BEq

/-- Cross-linguistic kind reference datum. -/
structure CrossLingDatum where
  language : String
  nominalType : BareNominalType
  sentence : String
  gloss : String
  bareKindOK : Bool
  defKindOK : Bool
  bareSgKindOK : Bool
  notes : String

-- English

def englishBarePlural : CrossLingDatum :=
  { language := "English"
  , nominalType := .barePluralOnly
  , sentence := "Dogs are mammals"
  , gloss := "dogs are mammals"
  , bareKindOK := true
  , defKindOK := false  -- "The dogs" = specific group, not kind
  , bareSgKindOK := false  -- "*Dog is a mammal"
  , notes := "Bare plural for kinds; bare singular ungrammatical"
  }

def englishDefiniteSingularKind : CrossLingDatum :=
  { language := "English"
  , nominalType := .barePluralOnly
  , sentence := "The lion is a predator"
  , gloss := "the lion is a predator"
  , bareKindOK := false
  , defKindOK := true  -- Singular kind with "the"
  , bareSgKindOK := false
  , notes := "Singular kinds require 'the'"
  }

def englishMassNoun : CrossLingDatum :=
  { language := "English"
  , nominalType := .barePluralOnly
  , sentence := "Gold is valuable"
  , gloss := "gold is valuable"
  , bareKindOK := true  -- Bare mass OK for kind
  , defKindOK := false
  , bareSgKindOK := true  -- Mass nouns pattern with bare plurals
  , notes := "Bare mass nouns OK for kind reference"
  }

-- French (Romance)

def frenchPluralKind : CrossLingDatum :=
  { language := "French"
  , nominalType := .definiteRequired
  , sentence := "Les chiens sont des mammifères"
  , gloss := "the dogs are PART mammals"
  , bareKindOK := false  -- "*Chiens sont mammifères"
  , defKindOK := true
  , bareSgKindOK := false
  , notes := "Definite required for kind reference"
  }

def frenchSingularKind : CrossLingDatum :=
  { language := "French"
  , nominalType := .definiteRequired
  , sentence := "Le lion est un prédateur"
  , gloss := "the lion is a predator"
  , bareKindOK := false
  , defKindOK := true
  , bareSgKindOK := false
  , notes := "Both sg and pl kinds use definite"
  }

-- Hindi

def hindiKind : CrossLingDatum :=
  { language := "Hindi"
  , nominalType := .fullyBare
  , sentence := "kutte bhaukte haiN"
  , gloss := "dog.PL bark.IMPF be.PL"
  , bareKindOK := true
  , defKindOK := false  -- No definite article
  , bareSgKindOK := true
  , notes := "Bare nominal for kind; same form for definite in context"
  }

def hindiDefiniteContext : CrossLingDatum :=
  { language := "Hindi"
  , nominalType := .fullyBare
  , sentence := "kuttaa bhauk rahaa hai"
  , gloss := "dog.SG bark PROG be.SG"
  , bareKindOK := false  -- Progressive blocks kind
  , defKindOK := false
  , bareSgKindOK := false
  , notes := "Same bare form gets definite reading with progressive"
  }

-- Russian

def russianKind : CrossLingDatum :=
  { language := "Russian"
  , nominalType := .fullyBare
  , sentence := "Sobaki lajut"
  , gloss := "dog.PL bark.PL"
  , bareKindOK := true
  , defKindOK := false  -- No articles
  , bareSgKindOK := true
  , notes := "No articles; bare nominals for kinds"
  }

-- Mandarin

def mandarinKind : CrossLingDatum :=
  { language := "Mandarin"
  , nominalType := .classifier
  , sentence := "Gǒu huì jiào"
  , gloss := "dog can bark"
  , bareKindOK := true
  , defKindOK := false
  , bareSgKindOK := true  -- No sg/pl distinction
  , notes := "Classifier language; bare noun is kind-denoting"
  }

-- Bare Singular Restriction (English)

/-- Bare singular grammaticality datum -/
structure BareSingularDatum where
  sentence : String
  grammatical : Bool
  npType : String  -- "bare sg count", "bare pl", "bare mass", etc.
  position : String  -- "subject", "object", etc.
  notes : String

def bareSgSubject : BareSingularDatum :=
  { sentence := "*Dog barks"
  , grammatical := false
  , npType := "bare sg count"
  , position := "subject"
  , notes := "Bare singular count noun ungrammatical as subject"
  }

def barePlSubject : BareSingularDatum :=
  { sentence := "Dogs bark"
  , grammatical := true
  , npType := "bare pl"
  , position := "subject"
  , notes := "Bare plural OK"
  }

def bareMassSubject : BareSingularDatum :=
  { sentence := "Water is wet"
  , grammatical := true
  , npType := "bare mass"
  , position := "subject"
  , notes := "Bare mass noun OK"
  }

def bareSgObject : BareSingularDatum :=
  { sentence := "*I saw dog"
  , grammatical := false
  , npType := "bare sg count"
  , position := "object"
  , notes := "Bare singular count noun ungrammatical as object"
  }

def barePlObject : BareSingularDatum :=
  { sentence := "I saw dogs"
  , grammatical := true
  , npType := "bare pl"
  , position := "object"
  , notes := "Bare plural OK as object"
  }

-- Scopelessness

/-- Scope ambiguity datum -/
structure ScopeDatum where
  sentence : String
  /-- Is the object NP scopally ambiguous? -/
  ambiguous : Bool
  /-- Available readings -/
  narrowScope : String
  wideScope : Option String
  notes : String

def negationBarePlural : ScopeDatum :=
  { sentence := "I didn't see dogs"
  , ambiguous := false
  , narrowScope := "¬∃x[dog(x) ∧ saw(I,x)]"
  , wideScope := none
  , notes := "Bare plural obligatorily narrow scope"
  }

def negationSomeDogs : ScopeDatum :=
  { sentence := "I didn't see some dogs"
  , ambiguous := true
  , narrowScope := "¬∃x[dog(x) ∧ saw(I,x)]"
  , wideScope := some "∃x[dog(x) ∧ ¬saw(I,x)]"
  , notes := "'Some' can scope over negation"
  }

def universalBarePlural : ScopeDatum :=
  { sentence := "Every student read books"
  , ambiguous := false
  , narrowScope := "∀x[student(x) → ∃y[book(y) ∧ read(x,y)]]"
  , wideScope := none
  , notes := "Bare plural cannot scope over universal"
  }

def universalSomeBooks : ScopeDatum :=
  { sentence := "Every student read some books"
  , ambiguous := true
  , narrowScope := "∀x[student(x) → ∃y[book(y) ∧ read(x,y)]]"
  , wideScope := some "∃y[book(y) ∧ ∀x[student(x) → read(x,y)]]"
  , notes := "'Some books' can scope over 'every student'"
  }

-- Scrambling and Scope (Le Bruyn & de Swart 2022)


/-- Scrambling position. -/
inductive ScramblingPosition where
  | unscrambled
  | scrambled
  deriving Repr, DecidableEq, BEq

/-- Scrambling scope datum. -/
structure ScramblingScopeDatum where
  sentence : String
  language : String
  gloss : Option String := none
  translation : String
  position : ScramblingPosition
  narrowOK : Bool
  wideOK : Bool
  kindReferenceOK : Bool := true
  notes : String

-- Dutch unscrambled (baseline)

def dutchUnscrambledNeg : ScramblingScopeDatum :=
  { sentence := "Helen praat niet met geesten op zolder"
  , language := "Dutch"
  , gloss := some "Helen talks not with ghosts on attic"
  , translation := "Helen doesn't talk to ghosts in the attic"
  , position := .unscrambled
  , narrowOK := true
  , wideOK := false  -- Only ¬∃
  , notes := "Unscrambled: bare plural narrow scope only"
  }

-- Dutch scrambled bare plurals with negation (Le Bruyn & de Swart 2022, ex. 34-35)

def dutchScrambledMensen : ScramblingScopeDatum :=
  { sentence := "... dat je mensen niet hebt uitgenodigd"
  , language := "Dutch"
  , gloss := some "that you people not have invited"
  , translation := "There are people you didn't invite"
  , position := .scrambled
  , narrowOK := false  -- not "you didn't invite anyone"
  , wideOK := true     -- ∃ > ¬
  , notes := "Scrambled BP: obligatory wide scope over negation"
  }

def dutchScrambledBoeken : ScramblingScopeDatum :=
  { sentence := "Het klopt dat ik boeken niet heb uitgelezen"
  , language := "Dutch"
  , gloss := some "it is.true that I books not have finished"
  , translation := "It's true that there are books I didn't finish"
  , position := .scrambled
  , narrowOK := false
  , wideOK := true
  , notes := "Scrambled BP: wide scope, not 'I finished no books'"
  }

-- Scrambled bare plurals CAN still be kind-referring (Le Bruyn & de Swart 2022, ex. 36-37)

def dutchScrambledKindMensen : ScramblingScopeDatum :=
  { sentence := "... dat ik mensen altijd gehaat heb"
  , language := "Dutch"
  , gloss := some "that I people always hated have"
  , translation := "that I've always hated people"
  , position := .scrambled
  , narrowOK := true   -- Kind reading with 'hate'
  , wideOK := false
  , kindReferenceOK := true  -- kind reference maintained
  , notes := "Scrambled BP can still be kind-referring with kind-level predicate"
  }

def dutchScrambledKindBoeken : ScramblingScopeDatum :=
  { sentence := "... dat ik boeken altijd gehaat heb"
  , language := "Dutch"
  , gloss := some "that I books always hated have"
  , translation := "that I've always hated books"
  , position := .scrambled
  , narrowOK := true
  , wideOK := false
  , kindReferenceOK := true
  , notes := "Kind reference possible even in scrambled position"
  }

-- German scrambling data

def germanScrambledKomponenten : ScramblingScopeDatum :=
  { sentence := "Ich habe Komponenten nicht gefunden"
  , language := "German"
  , gloss := some "I have components not found"
  , translation := "There were components I couldn't find"
  , position := .scrambled
  , narrowOK := false
  , wideOK := true
  , notes := "German scrambled BP: wide scope over negation"
  }

def germanScrambledMenschen : ScramblingScopeDatum :=
  { sentence := "Ich habe Menschen nicht wiedererkannt"
  , language := "German"
  , gloss := some "I have people not recognized"
  , translation := "There are people I didn't recognize"
  , position := .scrambled
  , narrowOK := false
  , wideOK := true
  , notes := "German: specific people the speaker didn't recognize"
  }

-- Modified bare plurals CAN scope wide even unscrambled (Carlson 1977, Geurts 2010)

def modifiedBPwideScope : ScramblingScopeDatum :=
  { sentence := "John didn't see parts of that machine"
  , language := "English"
  , translation := "John didn't see parts of that machine"
  , position := .unscrambled
  , narrowOK := true
  , wideOK := true  -- Modified BP: not kind-denoting
  , kindReferenceOK := false  -- Not a natural kind
  , notes := "Modified BP: ∃-shift available since not kind-denoting (Chierchia's escape hatch)"
  }

def scramblingData : List ScramblingScopeDatum :=
  [ dutchUnscrambledNeg
  , dutchScrambledMensen, dutchScrambledBoeken
  , dutchScrambledKindMensen, dutchScrambledKindBoeken
  , germanScrambledKomponenten, germanScrambledMenschen
  , modifiedBPwideScope ]

-- Kind-Level vs Object-Level Predicates

/-- Predicate type for kind application -/
inductive PredLevel where
  /-- Applies directly to kinds: extinct, widespread, evolve -/
  | kind
  /-- Applies to individuals; needs coercion for kinds: bark, sleep -/
  | object
  deriving Repr, DecidableEq, BEq

/-- Predicate classification datum -/
structure PredicateDatum where
  predicate : String
  level : PredLevel
  exampleSentence : String
  /-- Does it apply directly to kind-denoting NP? -/
  directKindApplication : Bool
  notes : String

-- Kind-level predicates

def beExtinct : PredicateDatum :=
  { predicate := "be extinct"
  , level := .kind
  , exampleSentence := "The dodo is extinct"
  , directKindApplication := true
  , notes := "True of kinds, not individuals"
  }

def beWidespread : PredicateDatum :=
  { predicate := "be widespread"
  , level := .kind
  , exampleSentence := "Rats are widespread"
  , directKindApplication := true
  , notes := "Distribution of kind"
  }

def beRare : PredicateDatum :=
  { predicate := "be rare"
  , level := .kind
  , exampleSentence := "White tigers are rare"
  , directKindApplication := true
  , notes := "Frequency of instantiation"
  }

def evolveFrom : PredicateDatum :=
  { predicate := "evolve from"
  , level := .kind
  , exampleSentence := "The horse evolved from a smaller ancestor"
  , directKindApplication := true
  , notes := "Evolutionary history of species"
  }

def beInvented : PredicateDatum :=
  { predicate := "be invented"
  , level := .kind
  , exampleSentence := "The wheel was invented in Mesopotamia"
  , directKindApplication := true
  , notes := "Creation of artifact kind"
  }

-- Object-level predicates (need DKP for kind subjects)

def beBarkingInYard : PredicateDatum :=
  { predicate := "be barking in the yard"
  , level := .object
  , exampleSentence := "Dogs are barking in the yard"
  , directKindApplication := false  -- Gets existential via DKP
  , notes := "Requires instances; existential reading"
  }

def beInGarden : PredicateDatum :=
  { predicate := "be in the garden"
  , level := .object
  , exampleSentence := "Dogs are in the garden"
  , directKindApplication := false
  , notes := "Location predicate; existential reading"
  }

-- Singular Kind Reference

/-- Type of singular kind licensing -/
inductive SingularKindLicense where
  /-- Extinct - no instances to distinguish -/
  | extinct
  /-- Invention/artifact - conceptualized as atomic -/
  | invention
  /-- Taxonomic - species-level predication -/
  | taxonomic
  deriving Repr, DecidableEq, BEq

/-- Singular kind datum -/
structure SingularKindDatum where
  sentence : String
  np : String
  license : SingularKindLicense
  grammatical : Bool
  notes : String

def dodoExtinct : SingularKindDatum :=
  { sentence := "The dodo is extinct"
  , np := "the dodo"
  , license := .extinct
  , grammatical := true
  , notes := "No instances - singular OK"
  }

def computerRevolutionized : SingularKindDatum :=
  { sentence := "The computer has revolutionized communication"
  , np := "the computer"
  , license := .invention
  , grammatical := true
  , notes := "Artifact kind - conceptualized as atomic"
  }

def lionPredator : SingularKindDatum :=
  { sentence := "The lion is a predator"
  , np := "the lion"
  , license := .taxonomic
  , grammatical := true
  , notes := "Taxonomic predication"
  }

def whaleEndangered : SingularKindDatum :=
  { sentence := "The whale is endangered"
  , np := "the whale"
  , license := .taxonomic
  , grammatical := true
  , notes := "Kind-level predicate"
  }

-- Modification blocks singular kind reading

def tallLionOdd : SingularKindDatum :=
  { sentence := "?The tall lion is a predator"
  , np := "the tall lion"
  , license := .taxonomic
  , grammatical := false
  , notes := "Modification blocks kind reading"
  }

-- Taxonomic vs Individual Readings

/-- Taxonomic reading datum -/
structure TaxonomicDatum where
  sentence : String
  /-- Is taxonomic (sub-kind) reading available? -/
  taxonomicOK : Bool
  /-- Is individual reading available? -/
  individualOK : Bool
  notes : String

def dogEvolvedWolf : TaxonomicDatum :=
  { sentence := "The dog evolved from the wolf"
  , taxonomicOK := true
  , individualOK := false
  , notes := "Only taxonomic makes sense"
  }

def dogSleeping : TaxonomicDatum :=
  { sentence := "The dog is sleeping"
  , taxonomicOK := false
  , individualOK := true
  , notes := "Only individual reading"
  }

def dogMammal : TaxonomicDatum :=
  { sentence := "The dog is a mammal"
  , taxonomicOK := true
  , individualOK := true
  , notes := "Ambiguous: kind or individual"
  }

-- Generic vs Existential (with Bare Plurals)

/-- Predicate class affecting BP interpretation -/
inductive PredicateClass where
  /-- Individual-level: permanent properties (intelligent, tall) -/
  | iLevel
  /-- Stage-level with locative argument (present, available) -/
  | sLevelLocArg
  /-- Stage-level with locative adjunct (hungry, tired) -/
  | sLevelLocAdj
  deriving Repr, DecidableEq, BEq

/-- Bare plural interpretation datum -/
structure BPInterpDatum where
  sentence : String
  predClass : PredicateClass
  /-- Generic reading available? -/
  genericOK : Bool
  /-- Existential reading available? -/
  existentialOK : Bool
  notes : String

def boysAreBrave : BPInterpDatum :=
  { sentence := "Boys are brave"
  , predClass := .iLevel
  , genericOK := true
  , existentialOK := false
  , notes := "I-level forces generic"
  }

def boysArePresent : BPInterpDatum :=
  { sentence := "Boys are present"
  , predClass := .sLevelLocArg
  , genericOK := true
  , existentialOK := true
  , notes := "S-level with locative arg allows existential"
  }

def boysAreHungry : BPInterpDatum :=
  { sentence := "Boys are hungry"
  , predClass := .sLevelLocAdj
  , genericOK := true
  , existentialOK := false
  , notes := "S-level but locative adjunct - no existential"
  }

def firemenAvailable : BPInterpDatum :=
  { sentence := "Firemen are available"
  , predClass := .sLevelLocArg
  , genericOK := true
  , existentialOK := true
  , notes := "Implicit locative argument"
  }

-- Aggregate Data

def crossLingData : List CrossLingDatum :=
  [englishBarePlural, englishDefiniteSingularKind, englishMassNoun,
   frenchPluralKind, frenchSingularKind,
   hindiKind, hindiDefiniteContext, russianKind, mandarinKind]

def bareSingularData : List BareSingularDatum :=
  [bareSgSubject, barePlSubject, bareMassSubject, bareSgObject, barePlObject]

def scopeData : List ScopeDatum :=
  [negationBarePlural, negationSomeDogs, universalBarePlural, universalSomeBooks]

def predicateData : List PredicateDatum :=
  [beExtinct, beWidespread, beRare, evolveFrom, beInvented,
   beBarkingInYard, beInGarden]

def singularKindData : List SingularKindDatum :=
  [dodoExtinct, computerRevolutionized, lionPredator, whaleEndangered, tallLionOdd]

def bpInterpData : List BPInterpDatum :=
  [boysAreBrave, boysArePresent, boysAreHungry, firemenAvailable]

-- Empirical Generalizations

-- Bare plurals are scopeless
#guard scopeData.filter (λ d => d.sentence.startsWith "I didn't see dogs" ||
                                   d.sentence.startsWith "Every student read books")
      |>.all (λ d => !d.ambiguous)

-- Kind-level predicates apply directly to kinds
#guard predicateData.filter (λ p => p.level == .kind)
      |>.all (λ p => p.directKindApplication)

-- English bare singular count nouns are ungrammatical
#guard bareSingularData.filter (λ d => d.npType == "bare sg count")
      |>.all (λ d => !d.grammatical)

-- English bare plurals and mass nouns are grammatical
#guard bareSingularData.filter (λ d => d.npType == "bare pl" || d.npType == "bare mass")
      |>.all (λ d => d.grammatical)

-- I-level predicates block existential BP reading
#guard bpInterpData.filter (λ d => d.predClass == .iLevel)
      |>.all (λ d => !d.existentialOK)

-- Scrambled bare plurals take wide scope (Dutch/German)
#guard scramblingData.filter (λ d => d.position == .scrambled &&
         containsSubstr d.sentence "niet" && d.kindReferenceOK)
      |>.all (λ d => d.wideOK)

-- Scrambled BPs can still be kind-referring (with appropriate predicates)
#guard scramblingData.filter (λ d => d.position == .scrambled &&
         containsSubstr d.sentence "gehaat")
      |>.all (λ d => d.kindReferenceOK)

end Phenomena.Generics.KindReference
