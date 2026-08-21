import Linglib.Morphology.DistributedMorphology.Neighborhood

/-!
# Vocabulary items

A Vocabulary Item pairs a specification with the exponent that realizes it
([halle-marantz-1993]): the features of the terminal it spells out, together
with the features it requires of the neighboring terminals — its contextual
environment, `/ __ ]X]`. Form and meaning share the type: an alloseme is an
item whose exponent is a denotation (`DistributedMorphology/Allosemy.lean`).
The selection-engine instance lives in `DistributedMorphology/Basic.lean`.
-/

namespace DistributedMorphology

/-- A Vocabulary Item: a specification paired with an exponent, applicable at
any neighborhood containing every feature it mentions. -/
structure VocabularyItem (F E : Type*) where
  /-- The features the item spells out, with those it requires of the
  adjacent terminals. -/
  spec : Neighborhood (List F)
  /-- The exponent the item inserts. -/
  exponent : E
  deriving DecidableEq, Repr

variable {F E : Type*}

namespace VocabularyItem

/-- The features the item spells out at its own terminal. -/
def features (i : VocabularyItem F E) : List F := i.spec.focus

/-- A context-free item: the features it spells out and its exponent. -/
def ofFeatures (fs : List F) (e : E) : VocabularyItem F E := ⟨fs, e⟩

/-- `fs ⟷ e`: the context-free Vocabulary Item spelling out `fs` as `e`. -/
scoped infixr:25 " ⟷ " => ofFeatures

@[simp] theorem spec_ofFeatures (fs : List F) (e : E) : (fs ⟷ e).spec = ↑fs := rfl

@[simp] theorem exponent_ofFeatures (fs : List F) (e : E) : (fs ⟷ e).exponent = e := rfl

end VocabularyItem

end DistributedMorphology
