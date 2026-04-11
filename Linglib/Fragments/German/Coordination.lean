import Linglib.Core.Coordination

/-!
# German Coordination Morphology
@cite{schwarzer-2026}

German conjunction morphology. German uses a J-only strategy
(like English and Irish): the single conjunction particle *und*
realizes the J (set intersection) operator.

*oder* "or" is the disjunction counterpart; *aber* / *sondern*
are adversative.
-/

namespace Fragments.German.Coordination

open Core.Coordination

/-- *und* — conjunction proper (J particle, free word).
    "Die Stadt beendet [DP die Überarbeitung] und [CP dass für
    Neugeborene ein Baum gepflanzt wird]." -/
def und : CoordEntry where
  form := "und"
  gloss := "and"
  role := .j
  boundness := .free

/-- *oder* — disjunction. -/
def oder : CoordEntry where
  form := "oder"
  gloss := "or"
  role := .disj
  boundness := .free

/-- *aber* — adversative ("but", contrastive). -/
def aber : CoordEntry where
  form := "aber"
  gloss := "but"
  role := .advers
  boundness := .free

/-- *sondern* — adversative ("but rather", corrective; requires negation). -/
def sondern : CoordEntry where
  form := "sondern"
  gloss := "but.rather"
  role := .advers
  boundness := .free
  note := "corrective; requires negation in first conjunct"

/-- German uses a J-only conjunction strategy. -/
def conjunctionStrategy : ConjunctionStrategy := .jOnly

/-- German J-only strategy realizes exactly 1 overt morpheme. -/
theorem german_overt_count : conjunctionStrategy.overtMorphemeCount = 1 := rfl

end Fragments.German.Coordination
