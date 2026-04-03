import Linglib.Theories.Semantics.Lexical.Noun.Kind.Carlson1977

/-!
# German Bare Plural Word Order
@cite{magri-2009} @cite{diesing-1992}

Distributional restrictions on bare plural subjects (BPS) in German,
conditioned by predicate level. The key diagnostic is the placement of
BPS relative to the modal particles *ja doch* ('indeed/after all') in
the Mittelfeld (middle field).

@cite{diesing-1992} first observed:
- S-predicate *verfügbar* ('available'): BPS can sit both LEFT and RIGHT
  of *ja doch*
- I-predicate *intelligent*: BPS can only sit LEFT of *ja doch*

@cite{magri-2009} §4.5 provides a semantic account: there is no syntactic
difference between s- and i-predicate subjects. Rather, when the BPS sits
to the right of *ja doch* (= VP-internal at Surface Structure), the truth
conditions are identical to the basic "Firemen are tall" BPS — whose
∃-reading is ruled out by the Mismatch Hypothesis for i-predicates.

The key advantage over @cite{diesing-1992}'s syntactic account: the semantic
account correctly predicts that universally quantified subjects like *alle
Studenten* ('all students') are fine to the right of *ja* (ex. 132), since
universal quantifiers are maximal in their Horn scale and blind
strengthening is vacuous.

## Cross-Module Connections

- `Phenomena.Generics.BarePlurals`: English BPS reading data
- `Phenomena.ScalarImplicatures.Studies.Magri2009`: BH+MH mechanism
-/

namespace Fragments.German.BarePluralWordOrder

open Semantics.Lexical.Noun.Kind.Carlson1977 (PredicateLevel)

/-- Position of the bare plural subject relative to *ja doch*. -/
inductive BPSPosition where
  | leftOfJaDoch   -- Mittelfeld, left of particles (topic position)
  | rightOfJaDoch  -- Mittelfeld, right of particles (VP-internal)
  deriving DecidableEq, Repr

/-- A German BPS word order datum. -/
structure JaDochDatum where
  predicate : String
  predicateLevel : PredicateLevel
  bpsPosition : BPSPosition
  acceptable : Bool
  gloss : String
  deriving Repr

/-- @cite{diesing-1992} ex. (8a)/(125a): s-predicate *verfügbar*, BPS left of
*ja doch* — OK. Both generic and existential readings available. -/
def verfuegbar_left : JaDochDatum where
  predicate := "verfügbar"
  predicateLevel := .stageLevel
  bpsPosition := .leftOfJaDoch
  acceptable := true
  gloss := "...weil Feuerwehrmänner ja doch verfügbar sind"

/-- @cite{diesing-1992} ex. (8a)/(125a): s-predicate *verfügbar*, BPS right of
*ja doch* — OK. Existential reading available in both positions. -/
def verfuegbar_right : JaDochDatum where
  predicate := "verfügbar"
  predicateLevel := .stageLevel
  bpsPosition := .rightOfJaDoch
  acceptable := true
  gloss := "...weil ja doch Feuerwehrmänner verfügbar sind"

/-- @cite{diesing-1992} ex. (8d)/(125b): i-predicate *intelligent*, BPS left
of *ja doch* — OK. Generic reading available. -/
def intelligent_left : JaDochDatum where
  predicate := "intelligent"
  predicateLevel := .individualLevel
  bpsPosition := .leftOfJaDoch
  acceptable := true
  gloss := "...weil Feuerwehrmänner ja doch intelligent sind"

/-- @cite{diesing-1992} ex. (8c)/(125b): i-predicate *intelligent*, BPS right
of *ja doch* — ODD.

@cite{magri-2009} §4.5: this is odd (not ungrammatical) because the
truth conditions are identical to the basic ∃-BPS reading, whose
strengthened meaning contradicts common knowledge via the MH. -/
def intelligent_right : JaDochDatum where
  predicate := "intelligent"
  predicateLevel := .individualLevel
  bpsPosition := .rightOfJaDoch
  acceptable := false
  gloss := "#...weil ja doch Feuerwehrmänner intelligent sind"

def allJaDochData : List JaDochDatum :=
  [verfuegbar_left, verfuegbar_right, intelligent_left, intelligent_right]

-- Per-datum verification theorems

/-- S-predicates allow BPS in both positions. -/
theorem slp_both_positions :
    (allJaDochData.filter (λ d => d.predicateLevel == .stageLevel)).all
      (λ d => d.acceptable) = true := by native_decide

/-- I-predicates block BPS to the RIGHT of *ja doch*. -/
theorem ilp_right_blocked :
    (allJaDochData.filter (λ d =>
      d.predicateLevel == .individualLevel && d.bpsPosition == .rightOfJaDoch)).all
      (λ d => !d.acceptable) = true := by native_decide

/-- I-predicates allow BPS to the LEFT of *ja doch* (generic reading). -/
theorem ilp_left_ok :
    (allJaDochData.filter (λ d =>
      d.predicateLevel == .individualLevel && d.bpsPosition == .leftOfJaDoch)).all
      (λ d => d.acceptable) = true := by native_decide

/-- The predicate level + position determines acceptability:
the ONLY unacceptable configuration is ILP + right of *ja doch*. -/
theorem acceptability_pattern :
    allJaDochData.all (λ d =>
      d.acceptable == !(d.predicateLevel == .individualLevel &&
                        d.bpsPosition == .rightOfJaDoch)) = true := by native_decide

end Fragments.German.BarePluralWordOrder
