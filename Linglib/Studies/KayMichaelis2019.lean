import Linglib.Syntax.ConstructionGrammar.Licensing
import Linglib.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Studies.FillmoreKayOConnor1988

/-!
# [kay-michaelis-2019]: Constructional Meaning and Compositionality

The survey chapter's two formal claims. First (§1, §4): rules of semantic
combination are construction-relative — a construction "specifies how the
semantics of the daughters are combined to produce the semantics of the
mother, and what additional semantics, if any, is contributed by the
construction itself". `CompositionRule` and `Constructicon.interps` give
that architecture computational content over the licensing layer's local
trees: a token's readings are whatever the syntactically matching
constructions' rules produce from its daughters' readings. The chapter's
opening contrast — *purple plum* composes by intersection, *alleged thief*
by operator application, under one syntactic configuration — falls out as
two constructions sharing a `TypedForm` whose rules accept disjoint
daughter-denotation shapes, so each token gets exactly one reading.

Second (§3): the kinds of meaning constructions contribute —
truth-conditional content, argument structure, conventional implicature,
special illocutionary forces, metalinguistic comments, information flow
(§9) — as `MeaningKind`, instantiated on the chapter's own cases already
in the library (caused motion §5, *let alone* §6, the incredulity type
§7).

## Main declarations

- `KayMichaelis2019.MeaningKind`: §3's classification (+ §9)
- `KayMichaelis2019.CompositionRule`, `Constructicon.interps`: §4's
  daughters-to-mother composition, all readings of a token
- `KayMichaelis2019.purple_plum_intersective`,
  `alleged_thief_operator`, `same_form`: the §1 contrast
- `KayMichaelis2019.chapterCases`: §§5–7 instantiated
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
semantics, if any, is contributed by the construction itself." -/

/-- A composition rule: from the daughters' denotations to the mother's,
partial because a rule demands daughter denotations of the right shape. -/
abbrev CompositionRule (D : Type*) := List D → Option D

mutual

/-- All readings of a token: each construction whose typed form the
daughters instantiate contributes the readings its composition rule
produces from the daughters' readings; words read from the lexicon. -/
def _root_.ConstructionGrammar.Constructicon.interps {D : Type*}
    (cx : Constructicon) (pos : String → Option UD.UPOS)
    (rules : Construction → Option (CompositionRule D))
    (lex : String → Option D) : Token → List D
  | .word w => (lex w).toList
  | .node ts =>
      cx.constructions.flatMap (λ c =>
        if formMatches pos c.form ts then
          (cx.interpsList pos rules lex ts).filterMap
            (λ seq => (rules c).bind (· seq))
        else [])

/-- All sequences of daughter readings. -/
def _root_.ConstructionGrammar.Constructicon.interpsList {D : Type*}
    (cx : Constructicon) (pos : String → Option UD.UPOS)
    (rules : Construction → Option (CompositionRule D))
    (lex : String → Option D) : List Token → List (List D)
  | [] => [[]]
  | t :: ts =>
      (cx.interps pos rules lex t).flatMap (λ d =>
        (cx.interpsList pos rules lex ts).map (d :: ·))

end

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
  [ { filler := .open_ .ADJ, role := some "modifier" }
  , { filler := .open_ .NOUN, role := some "head", isHead := true } ]

/-- Intersective Adj+N modification. -/
def intersectiveModification : Construction :=
  { name := "Intersective modification"
  , form := modificationForm
  , meaning := "x is Adj and x is N" }

/-- Operator Adj+N modification. -/
def operatorModification : Construction :=
  { name := "Operator modification"
  , form := modificationForm
  , meaning := "x satisfies Adj applied to N" }

/-- §1's premise: one rule of syntactic formation, two semantic
specifications — the constructions share their typed form. -/
theorem same_form :
    intersectiveModification.form = operatorModification.form := rfl

/-- The demo network: both modification constructions. -/
def demoCx : Constructicon :=
  { constructions := [intersectiveModification, operatorModification]
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

/-- Rule assignment for the demo network. -/
def demoRules : Construction → Option (CompositionRule (Den E)) :=
  λ c =>
    if c = intersectiveModification then some (intersectiveRule E)
    else if c = operatorModification then some (operatorRule E)
    else none

/-- *Purple plum* has exactly one reading: the intersection. The operator
construction matches the form but its rule rejects two predicate
daughters. -/
theorem purple_plum_intersective :
    demoCx.interps demoPos demoRules (demoLex purple plum thief alleged)
        (.node [.word "purple", .word "plum"])
      = [.pred (λ x => purple x ∧ plum x)] := rfl

/-- *Alleged thief* has exactly one reading: the operator applied to the
head predicate — not an intersection. -/
theorem alleged_thief_operator :
    demoCx.interps demoPos demoRules (demoLex purple plum thief alleged)
        (.node [.word "alleged", .word "thief"])
      = [.pred (alleged thief)] := rfl

/-- With only the intersective construction, *alleged thief* has no
reading at all: the chapter's point that intersection cannot be the
single rule of adjectival modification. -/
theorem alleged_thief_needs_operator_construction :
    ({ constructions := [intersectiveModification], links := [] }
        : Constructicon).interps demoPos demoRules
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
def chapterCases : List (Construction × MeaningKind) :=
  [ (causedMotion.construction, .argumentStructure)
  , (_root_.FillmoreKayOConnor1988.letAloneConstruction, .conventionalImplicature)
  , (_root_.FillmoreKayOConnor1988.incredulityResponse, .illocutionaryForce) ]

end KayMichaelis2019
