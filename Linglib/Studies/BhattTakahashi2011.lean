import Linglib.Data.Examples.BhattTakahashi2011
import Linglib.Studies.Lechner2004
import Linglib.Syntax.Minimalist.Movement.HeimKennedy
import Linglib.Syntax.Tree.Basic
import Linglib.Core.Order.Branching

/-!
# Bhatt and Takahashi (2011): Reduced and unreduced phrasal comparatives

A phrasal comparative is either the reduction of a clausal source, with the two-place degree
head, or genuinely phrasal, with a three-place head taking an individual standard
([bhatt-takahashi-2011]). The binding generalization of §2, that the standard is c-commanded
by everything that c-commands the associate, holds in English, the signature of reduction
(the disjoint-reference battery of [lechner-2004]), and fails in Hindi-Urdu, where the
standard is an external PP that the matrix pronoun never c-commands; the scope generalization
of §4, that a quantifier in the *than*-phrase must scope out exactly when its base position
c-commands the degree trace, sorts the two languages the same way, Hindi-Urdu scoping out
obligatorily. Each language's realized analyses are read off its data, Japanese realizes both
by the subcategorization of *yori*, and §6 proposes that both degree heads are available
crosslinguistically, their distribution fixed by what *than*, *yori* and *-se* combine with.

## Implementation notes

The binding rows are read into [lechner-2004]'s `BindingDatum` schema and the scope rows into
the reduced *than*-clause LFs of (43a) and (43b), on which the Heim–Kennedy constraint
(`Minimalist.IsHeimKennedy`) at the quantifier's base position decides than-phrase-internal
scope. The Single Standard Restriction and
the Precedence Constraint of §3, which need a linear-order interface, and the derivation of
Japanese's analyses from *yori*'s subcategorization are not formalized; the Japanese cell is
stated.

## References

* [bhatt-takahashi-2011]
* [lechner-2004]
* [lechner-2001]
* [merchant-2009]
-/

namespace BhattTakahashi2011

open Core.Order Core.Order.Branching Data.Examples Features Lechner2004 Minimalist Syntax
open Syntax.Tree

/-! ### The rows -/

/-- A judgment as the acceptability grade of the schema. -/
def acceptabilityOf : Judgment → Acceptability
  | .acceptable => .ok
  | .marginal => .marginal
  | .questionable => .degraded
  | .unacceptable => .unacceptable
  | .ungrammatical => .unacceptable

/-- A binding row in [lechner-2004]'s schema: whether the matrix pronoun c-commands the
associate, and whether the coreferential reading the row states is attested. -/
def bindingOf (e : LinguisticExample) : Option BindingDatum :=
  (e.feature? "pron_c_commands_associate").bind λ s =>
    let cc : Option Bool := match s with | "yes" => some true | "no" => some false | _ => none
    cc.map λ b =>
      ⟨e.id, acceptabilityOf e.judgment, b,
        decide (e.judgment = .acceptable ∨ e.judgment = .marginal)⟩

/-- The rows of one language. -/
def rowsOf (glottocode : String) : List LinguisticExample :=
  Examples.all.filter (·.language = glottocode)

/-- The English minimal pairs (11)–(13). -/
def englishBindingPairs : List BindingDatum := (rowsOf "stan1293").filterMap bindingOf

/-- The Hindi-Urdu datum (35). -/
def hindiUrduBindingPairs : List BindingDatum := (rowsOf "hind1269").filterMap bindingOf

/-! ### The binding diagnostic (§2, §3.4) -/

/-- (10): the English data realize the reduction analysis, coreference into the standard being
possible exactly when the pronoun does not c-command the associate, and rule out the direct
analysis, which predicts coreference throughout. -/
theorem english_binding :
    realizesReduction englishBindingPairs ∧ ¬ realizesDirect englishBindingPairs := by
  decide

/-- (35): the Hindi-Urdu datum realizes the direct analysis and rules out reduction, the pronoun
c-commanding the associate yet coreferring into the standard. -/
theorem hindi_urdu_binding :
    realizesDirect hindiUrduBindingPairs ∧ ¬ realizesReduction hindiUrduBindingPairs := by
  decide

/-! ### The scope diagnostic (§4) -/

/-- A reduced *than*-clause LF: the tree, the quantifier's base position and the degree trace. -/
structure ThanClause where
  tree : Tree Unit String
  qp : TreePath
  trace : TreePath

/-- The reduced *than*-clause of (43a), *than Craige assigned every second year student d-many
papers*, in a VP shell: the quantifier's base position c-commands the degree trace. -/
def thanClause43a : ThanClause where
  tree := binder 1 (bin (leaf "Craige") (bin (leaf "assigned")
    (bin (leaf "every second year student") (bin (leaf "t") (bin (tr 1) (leaf "many papers"))))))
  qp := ⟨[0, 1, 1, 0]⟩
  trace := ⟨[0, 1, 1, 1, 1, 0]⟩

/-- The reduced *than*-clause of (43b), *than Craige assigned d-many students every paper by
Klein*: the quantifier's base position does not c-command the degree trace. -/
def thanClause43b : ThanClause where
  tree := binder 1 (bin (leaf "Craige") (bin (leaf "assigned")
    (bin (bin (tr 1) (leaf "many students")) (bin (leaf "t") (leaf "every paper by Klein")))))
  qp := ⟨[0, 1, 1, 1, 1]⟩
  trace := ⟨[0, 1, 1, 0, 0]⟩

/-- A scope row's *than*-clause: the configuration of (43a) when the quantifier's base position
c-commands the degree trace and that of (43b) when it does not. -/
def thanClauseOf (e : LinguisticExample) : Option ThanClause :=
  match e.feature? "qp_base_c_commands_degree_trace" with
  | some "yes" => some thanClause43a
  | some "no" => some thanClause43b
  | _ => none

/-- (43): under reduction, than-phrase-internal scope is available exactly when the quantifier in
its base position satisfies the Heim–Kennedy constraint against the degree abstraction at the
root of the *than*-clause. -/
def RAPredictsScope (e : LinguisticExample) : Prop :=
  ∀ c ∈ thanClauseOf e,
    (IsHeimKennedy (cCommandAt c.tree) c.qp ⊥ c.trace ↔
      e.feature? "than_internal_scope" = some "available")

instance (e : LinguisticExample) : Decidable (RAPredictsScope e) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The English scope data (43a–b) follow the reduction generalization. -/
theorem english_scope : ∀ e ∈ rowsOf "stan1293", RAPredictsScope e := by decide

/-- Hindi-Urdu (40) does not: a quantifier whose base position is below the degree trace still
scopes out, which the direct analysis, with no degree trace in the *than*-phrase, predicts. -/
theorem hindi_urdu_scope : ∃ e ∈ rowsOf "hind1269", ¬ RAPredictsScope e := by decide

/-! ### The typology (§6) -/

/-- The surveyed languages. -/
inductive Language where
  | english
  | hindiUrdu
  | japanese
  deriving DecidableEq, Repr

/-- The analyses each language realizes: English and Hindi-Urdu from their binding data,
Japanese both, a clausal or multiple-standard complement of *yori* taking the two-place head
and a DP complement the three-place one (§6). -/
def headAvailability : Language → HeadAvailability
  | .english => headAvailabilityFromBinding englishBindingPairs
  | .hindiUrdu => headAvailabilityFromBinding hindiUrduBindingPairs
  | .japanese => ⟨true, true⟩

/-- English realizes reduction alone and Hindi-Urdu the direct analysis alone, so the three
languages occupy three cells of the grid. -/
theorem three_cells :
    headAvailability .english = ⟨true, false⟩ ∧ headAvailability .hindiUrdu = ⟨false, true⟩ ∧
      ∀ l l' : Language, headAvailability l = headAvailability l' → l = l' := by
  refine ⟨by decide, by decide, ?_⟩
  intro l l'; cases l <;> cases l' <;> decide

end BhattTakahashi2011
