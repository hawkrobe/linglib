import Linglib.Syntax.Category.Verb.Basic
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Adyghe clausal embedding

Adyghe (Northwest Caucasian, ISO 639-3 `ady`) has no embedded declarative and no embedded
polar interrogative of the matrix shape. A tensed clause under *gʷəpšəsa* 'think', *ŝe* 'know',
*gʷərəʔʷe* 'understand', *ʔʷa* 'say' or *qəč'ewəpč'a* 'ask' has the shape of a relative
clause: its verb carries the relativizer *ze-* and the applicative *re-*, and the clause ends in
the case suffix a noun phrase would bear, absolutive *-r* or oblique *-m* according to the
matrix predicate. A constituent question under 'ask' is a headless relative without *re-*, and
the same predicates take plain noun-phrase objects. The volitional and aspectual predicates such
as *raʔežʼa* 'begin' take an infinitive in *-new* instead.

Forms follow Caponigro and Polinsky's transliteration: ʷ marks labialization, ʼ ejectives, ə
schwa. Factivity values are textbook consensus for the predicate concepts; the paper runs no
projection tests. The data are Caponigro and Polinsky's; the relativization analysis is stated
in `Studies/Deal2026.lean`.

## References

* [caponigro-polinsky-2011]
* [noonan-2007]
-/

namespace Adyghe

/-! ### Clause-typers -/

/-- The relativizer *ze-* with the applicative *re-*, on the verb of every tensed clause under an
attitude predicate; the clause ends in a case suffix ((98), (99), (108)). -/
def zeRe : Complementizer where
  morphs := [.pref "ze", .pref "re"]
  coding := some .indicative
  licenser := some .nominal

/-- The infinitive suffix *-new* of the volitional and aspectual class ((54)). -/
def new : Complementizer where
  morphs := [.suff "new"]
  coding := some .infinitive
  licenser := some .verbal

/-! ### Predicates -/

/-- The case suffix at the right edge of a predicate's clausal complement, absolutive *-r* or
oblique *-m*, which the matrix predicate assigns ((98), (99)). -/
inductive ComplementCase where
  | abs
  | obl
  deriving DecidableEq, Repr

/-- An Adyghe complement-taking predicate is a verb entry with its [noonan-2007] class and the
case it assigns to a clausal complement. -/
structure Verb extends _root_.Verb where
  /-- The [noonan-2007] class, `none` where the data give no clear assignment. -/
  ctpClass : Option CTPClass
  /-- The case suffix on the clausal complement, `none` for an infinitival complement. -/
  complementCase : Option ComplementCase
  deriving Repr

/-- *gʷəpšəsa* 'think', which rejects a bare finite complement, takes the relative-shaped one,
and takes plain noun-phrase objects ((96), (98), (102)). -/
def gwepshesa : Verb where
  form := "gʷəpšəsa"
  frames := [Frame.finiteClause, Frame.np]
  ctpClass := some .propAttitude
  attitude := some (.doxastic .nonVeridical)
  complementCase := some .abs

/-- *qəč'ewəpč'a* 'ask', whose polar-question complement carries *ze-re-* and whose
constituent-question complement is a headless relative; it takes plain noun-phrase objects
((69), (99), (103)). -/
def chewepcha : Verb where
  form := "qəč'ewəpč'a"
  frames := [Frame.question, Frame.np]
  ctpClass := some .utterance
  speechActVerb := true
  complementCase := some .obl

/-- *ŝe* 'know', also *jeŝe*, whose one relative-shaped complement is ambiguous between the
declarative and the polar reading ((101)). -/
def she : Verb where
  form := "ŝe"
  frames := [Frame.finiteClause, Frame.question]
  ctpClass := some .knowledge
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  complementCase := some .abs

/-- *gʷərəʔʷe* 'understand', whose complement is truth-conditionally equivalent with and
without an overt head noun 'news' or 'verity' ((108)–(110)). -/
def gwereqwe : Verb where
  form := "gʷərəʔʷe"
  frames := [Frame.finiteClause]
  ctpClass := some .knowledge
  attitude := some (.doxastic .veridical)
  complementCase := some .abs

/-- *ʔʷa* 'say'. -/
def qwa : Verb where
  form := "ʔʷa"
  frames := [Frame.finiteClause]
  ctpClass := some .utterance
  speechActVerb := true
  complementCase := some .abs

/-- *raʔežʼa* 'begin', which takes an infinitive in *-new* ((54)). -/
def raqezha : Verb where
  form := "raʔežʼa"
  frames := [Frame.infinitival]
  ctpClass := some .phasal
  complementCase := none

/-- The predicates with per-predicate data in the paper. -/
def verbs : List Verb := [gwepshesa, chewepcha, she, gwereqwe, qwa, raqezha]

end Adyghe
