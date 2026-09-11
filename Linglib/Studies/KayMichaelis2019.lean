import Linglib.Syntax.ConstructionGrammar.Composition
import Linglib.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Studies.FillmoreKayOConnor1988

/-!
# Kay and Michaelis (2019): Constructional Meaning and Compositionality

This file formalizes the two formal claims of the survey chapter [kay-michaelis-2019]. First,
rules of semantic combination are construction-relative: a construction specifies how the
semantics of the daughters combine into the semantics of the mother and what the construction
itself adds (Sections 1 and 4). The substrate's `CompositionRule` and `Constructicon.interps`
give that architecture content over the licensing layer's local trees, a token's readings being
whatever the syntactically matching constructions' rules produce from its daughters' readings;
the chapter's opening contrast, *purple plum* composed by intersection and *alleged thief* by
operator application under one syntactic configuration, falls out as two constructions sharing
a typed form whose rules accept disjoint daughter denotations, so that each token gets exactly
one reading (`purple_plum_intersective`, `alleged_thief_operator`). Second, the kinds of
meaning a construction contributes, truth-conditional content, argument structure, conventional
implicature, illocutionary force, metalinguistic comment and information flow (Sections 3 and
9), are `MeaningKind`, instantiated on the chapter's own cases already in the library: caused
motion, *let alone* and the incredulity response.

## References

* [kay-michaelis-2019]
* [fillmore-kay-oconnor-1988]
-/

namespace KayMichaelis2019

open ConstructionGrammar

/-! ### §3: kinds of constructional meaning

The chapter's classification, offered as "neither definitive nor
exhaustive"; `informationFlow` is §9's strand. -/

/-- A kind of meaning contributed by a construction ([kay-michaelis-2019]
§3, §9). -/
inductive MeaningKind where
  | literal                  -- §3(i), §4: truth-conditional content
  | argumentStructure        -- §3(ii), §5
  | conventionalImplicature  -- §3(iii), §6: incl. pragmatic presupposition
  | illocutionaryForce       -- §3(iv), §7
  | metalinguistic           -- §3(v), §8
  | informationFlow          -- §9: topic/focus presuppositions
  deriving DecidableEq, Repr

/-! ### §4: construction-relative composition

"The construction also specifies how the semantics of the daughters are
combined to produce the semantics of the mother, and what additional
semantics, if any, is contributed by the construction itself" — the
`CompositionRule` architecture of
`ConstructionGrammar.Composition`, instantiated below. -/

/-! ### §1: *purple plum* vs. *alleged thief*

"A purple plum is a member of the set of purple things and a member of
the set of plums. But an alleged thief is not a member of the
intersection of the set of thieves and the set of alleged things." Two
modification constructions share one syntactic form; their rules accept
disjoint daughter shapes, so each token composes exactly one way. -/

/-- Demo denotations: first-order predicates and predicate operators. -/
inductive Den (E : Type*) where
  | pred : (E → Prop) → Den E
  | op : ((E → Prop) → (E → Prop)) → Den E

/-- Intersective modification: both daughters denote predicates; the
mother denotes their intersection (*purple plum*). -/
def intersectiveRule (E : Type*) : CompositionRule (Den E)
  | [.pred a, .pred n] => some (.pred (λ x => a x ∧ n x))
  | _ => none

/-- Operator modification: the adjective denotes a predicate operator
applied to the head's predicate (*alleged thief*). -/
def operatorRule (E : Type*) : CompositionRule (Den E)
  | [.op f, .pred n] => some (.pred (f n))
  | _ => none

/-- The shared prenominal-modification form. -/
def modificationForm : TypedForm String :=
  [ { filler := .open_ .ADJ }
  , { filler := .open_ .NOUN, isHead := true } ]

/-- Intersective Adj+N modification: its meaning pole is the
intersective rule. -/
def intersectiveModification (E : Type*) :
    Construction (CompositionRule (Den E)) :=
  { name := "Intersective modification"
  , form := modificationForm
  , meaning := intersectiveRule E }

/-- Operator Adj+N modification: its meaning pole is the operator rule. -/
def operatorModification (E : Type*) :
    Construction (CompositionRule (Den E)) :=
  { name := "Operator modification"
  , form := modificationForm
  , meaning := operatorRule E }

/-- §1's premise: one rule of syntactic formation, two semantic
specifications — the constructions share their typed form. -/
theorem same_form (E : Type*) :
    (intersectiveModification E).form = (operatorModification E).form := rfl

/-- The demo network: both modification constructions. -/
def demoCx (E : Type*) : Constructicon (CompositionRule (Den E)) :=
  { constructions := [intersectiveModification E, operatorModification E]
  , links := [] }

/-- Toy POS lexicon. -/
def demoPos : String → Option UD.UPOS
  | "purple" | "alleged" => some .ADJ
  | "plum" | "thief" => some .NOUN
  | _ => none

section Demo

variable {E : Type*} (purple plum thief : E → Prop)
  (alleged : (E → Prop) → (E → Prop))

/-- Toy denotation lexicon: *purple* is a predicate, *alleged* an
operator. -/
def demoLex : String → Option (Den E)
  | "purple" => some (.pred purple)
  | "alleged" => some (.op alleged)
  | "plum" => some (.pred plum)
  | "thief" => some (.pred thief)
  | _ => none

/-- *Purple plum* has exactly one reading: the intersection. The operator
construction matches the form but its rule rejects two predicate
daughters. -/
theorem purple_plum_intersective :
    (demoCx E).interps demoPos (demoLex purple plum thief alleged)
        (.node [.word "purple", .word "plum"])
      = [.pred (λ x => purple x ∧ plum x)] := rfl

/-- *Alleged thief* has exactly one reading: the operator applied to the
head predicate — not an intersection. -/
theorem alleged_thief_operator :
    (demoCx E).interps demoPos (demoLex purple plum thief alleged)
        (.node [.word "alleged", .word "thief"])
      = [.pred (alleged thief)] := rfl

/-- With only the intersective construction, *alleged thief* has no
reading at all: the chapter's point that intersection cannot be the
single rule of adjectival modification. -/
theorem alleged_thief_needs_operator_construction :
    ({ constructions := [intersectiveModification E], links := [] }
        : Constructicon (CompositionRule (Den E))).interps demoPos
        (demoLex purple plum thief alleged)
        (.node [.word "alleged", .word "thief"])
      = [] := rfl

end Demo

/-! ### §§5–7 instantiated

The chapter's cases that the library already formalizes, with the kind of
meaning each contributes. -/

/-- The chapter's example constructions by meaning kind: caused motion
(§5, exx. 19–22, *Frank sneezed the tissue off the table*), *let alone*
(§6, ex. 32), and the incredulity type (§7, ex. 14, *Him get first
prize?!*). -/
def chapterCases : List (Construction Unit × MeaningKind) :=
  [ (causedMotion.map λ _ => (), .argumentStructure)
  , (_root_.FillmoreKayOConnor1988.letAloneConstruction, .conventionalImplicature)
  , (_root_.FillmoreKayOConnor1988.incredulityResponse, .illocutionaryForce) ]

end KayMichaelis2019
