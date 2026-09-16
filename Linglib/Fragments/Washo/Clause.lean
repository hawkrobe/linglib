import Linglib.Syntax.Category.Verb.Basic
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Washo clausal embedding

The complement-taking predicates of Washo (Hokan/isolate, ISO 639-3 `was`) with quotable data
in [bochnak-hanink-2021], as verb entries, and the two clause-typers at the right edge of the
clauses they embed (Table 1): the clausal nominalizer *-gi ~ -ge*, the exponent of
[hanink-2021]'s index head over a finite clause in the independent mood *-i*, and the dependent
mood *-aʔ*. A predicate's frames carry its transitivity, the observable behind the paper's
split: the nominalizer-takers select internal arguments, shown by the plain DP objects of 'know'
and 'see' and by subject/object agreement, and the *-aʔ*-takers are intransitive, shown by the
*how* question word they take and by the reflexive *gum-* on 'dream' (§3.2.2). 'Know',
'remember' and 'believe' belong to a small inherently negative class whose positive reading
carries the negative suffix *-e:s*, and 'remember' is negated 'forget' (fn. 7).

Forms follow the paper's orthography after [jacobsen-1964]: `:` marks vowel length, ʔ ɨ ŋ are
IPA, and stress is acute. The complementation-against-modification analysis is
`Studies/BochnakHanink2021.lean`.

## References

* [bochnak-hanink-2021]
* [hanink-2021]
* [noonan-2007]
* [jacobsen-1964]
-/

namespace Washo.Clause

open Morphology (Morph)

/-! ### Clause-typers -/

/-- The clausal nominalizer *-ge*, the accusative form of *-gi ~ -ge* that attitude complements
bear (fn. 6), types a nominalized clause in the independent mood and is licensed by the nominal
projection. -/
def ge : Complementizer where
  morphs := [.suff "ge"]
  coding := some .nominalized
  verbForm := some .Fin
  licenser := some .nominal

/-- The dependent mood *-aʔ* types the bare clause under a non-nominalizing predicate and never
a matrix clause ((2), (13)–(16)). -/
def aq : Complementizer where
  morphs := [.suff "aʔ"]
  verbForm := some .Fin
  licenser := some .verbal

/-! ### Predicates -/

/-- A Washo complement-taking predicate is the cross-linguistic verb entry with its
[noonan-2007] class and the clause-typer at the right edge of the clause it embeds. -/
structure Embedder extends Verb where
  /-- The [noonan-2007] class, `none` where the paper's data give no clear assignment. -/
  ctpClass : Option CTPClass
  /-- The clause-typer on the embedded clause (Table 1). -/
  typer : Complementizer
  deriving Repr

/-- The negative suffix *-e:s*. -/
def es : Morph := .suff "e:s"

/-- The reflexive prefix *gum-*. -/
def gum : Morph := .pref "gum"

/-- *hamup'ay* 'forget' ((1), (9), (34)). -/
def hamupay : Embedder where
  form := "hamup'ay"
  frames := [Frame.gerund]
  ctpClass := some .knowledge
  typer := ge

/-- *hamup'ay-e:s* 'remember' is negated 'forget' ((8), (86)). -/
def hamupayEs : Embedder := { hamupay with form := hamupay.form ++ toString es }

/-- *ašaš-e:s* 'know', the positive form of *ašaš* 'not know', also takes a plain familiar DP,
'that man' ((6), (79), (87)). -/
def ashashEs : Embedder where
  form := "ašaš" ++ toString es
  frames := [Frame.gerund, Frame.np]
  ctpClass := some .knowledge
  typer := ge

/-- *i:gi* 'see' takes a nominalized clause on the propositional reading, an internally headed
relative, and a plain DP ((10), (20), (88), (89)). -/
def iigi : Embedder where
  form := "i:gi"
  frames := [Frame.gerund, Frame.np]
  ctpClass := some .perception
  typer := ge

/-- *damal* 'hear' is attested with event nominalizations, 'it raining' and 'the man singing'
((11), (84)). -/
def damal : Embedder where
  form := "damal"
  frames := [Frame.gerund]
  ctpClass := some .perception
  typer := ge

/-- *hamu* 'think' is intransitive, questioned with *how* rather than *what* ((2), (13), (41),
(49)). -/
def hamu : Embedder where
  form := "hamu"
  frames := []
  ctpClass := some .propAttitude
  typer := aq

/-- *i:d* 'say' is intransitive ((14), (47), (50)). -/
def iid : Embedder where
  form := "i:d"
  frames := []
  ctpClass := some .utterance
  typer := aq
  speechActVerb := true

/-- *mɨtgi:bɨl-e:s* 'believe' is negated 'disbelieve' ((16)). -/
def metgiibilEs : Embedder where
  form := "mɨtgi:bɨl" ++ toString es
  frames := []
  ctpClass := some .propAttitude
  typer := aq

/-- *suʔuʔuš* 'dream' without the reflexive is transitive, 'dream of bread', and its nominalized
clause is an internally headed relative, not a *that*-clause ((53), (55)). -/
def suus : Embedder where
  form := "suʔuʔuš"
  frames := [Frame.np, Frame.gerund]
  ctpClass := none
  typer := ge

/-- *gum-suʔuʔuš* 'dream' with the reflexive is intransitive and embeds the dependent-mood clause
read as a *that*-clause ((15), (52), (54)). -/
def gumsuus : Embedder :=
  { suus with
    form := toString gum ++ suus.form
    voiceType := some .reflexive
    frames := []
    typer := aq }

/-- The predicates with quotable per-predicate data. -/
def embedders : List Embedder :=
  [hamupay, hamupayEs, ashashEs, iigi, damal, hamu, iid, metgiibilEs, suus, gumsuus]

/-- The embedded clause bears the dependent mood under an intransitive predicate and the
nominalizer under a transitive one (Table 1 read against transitivity). -/
theorem typer_eq : ∀ v ∈ embedders, v.typer = if v.frames = [] then aq else ge := by
  decide

end Washo.Clause
