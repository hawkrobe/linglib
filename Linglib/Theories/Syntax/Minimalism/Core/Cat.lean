/-!
# Categorial Inventory

@cite{chomsky-2013}

The 28-constructor `Cat` inductive enumerates the head categories of the
Minimalist Program clausal spine and nominal extended projection. Each
constructor cites the work that introduced (or refined) the category in
question; together they cover the cartographic left periphery, the
inflectional spine, the v/Voice/Appl event-structure layer, the
nominal categorizer-and-quantity sequence, and the adpositional
Place/Path articulation.

`SelStack` is the selectional-feature stack consumed left-to-right by
Merge, expressed as a list of `Cat`s — the public surface for combining
heads in the lexicon.

This file is intentionally minimal so that consumer files (Polarity,
Coreference, Borer 2005 demonstration, Mereological Syntax, Konnelly &
Cowper 2020 pronouns, etc.) can depend on the categorial inventory
without dragging in the full SyntacticObject / Merge / containment
infrastructure of `Minimalism.Core.Basic`.
-/

namespace Minimalism

/-- Categorial features (Definition 10) -/
inductive Cat where
  | V     -- verb
  | N     -- noun
  | A     -- adjective
  | P     -- preposition
  | D     -- determiner
  | T     -- tense
  | C     -- complementizer
  | v     -- light verb
  | n     -- nominal categorizer / gender (little-n, @cite{marantz-2001}; Distributed Morphology)
  | a     -- adjectival categorizer (little-a, @cite{panagiotidis-2015}; DegP complement)
  | Place -- locational head (@cite{dendikken-2010}; PlaceP, F1 in adpositional EP)
  | Path  -- directional head (@cite{dendikken-2010} @cite{svenonius-2010}; PathP, F2 in adpositional EP)
  | Num   -- number (@cite{ritter-1991}; NumP between nP and QP/DP)
  | Q     -- quantity / classifier (@cite{borer-2005}; QP between NumP and DP)
  | Voice -- Voice head (@cite{kratzer-1996}; @cite{schaefer-2008})
  | Appl  -- Applicative head (@cite{pylkknen-2008}; @cite{cuervo-2003})
  | Foc   -- focus (@cite{rizzi-1997} split-CP; hosts [FoC] feature, triggers A-bar movement)
  | Top   -- topic (@cite{rizzi-1997} split-CP; hosts [G]/givenness, topic fronting)
  | Fin   -- finiteness (@cite{rizzi-1997} split-CP; allocutive probe in Magahi/Galician)
  | SA    -- speech act head (@cite{speas-tenny-2003}; hosts speaker/addressee)
  | Force -- force (@cite{rizzi-1997} split-CP; clause-typing [decl]/[interrog])
  | Neg   -- negation (@cite{pollock-1989}; @cite{zanuttini-1997}; hosts [±neg])
  | Mod   -- modality (@cite{cinque-1999}; modal auxiliaries)
  | Rel   -- relative (cartographic left periphery, @cite{rizzi-1997})
  | Pol   -- polarity (@cite{laka-1990}; ΣP for affirmation/negation)
  | Asp   -- aspect (@cite{cinque-1999}; inner inflectional, between Voice and T)
  | Evid  -- evidential (@cite{cinque-1999}; outer inflectional, above T below Fin)
  | Nmlz  -- nominalizer (@cite{keine-2020}; Hindi -naa/-ne nominalized clause; clause type distinct from CP)
  | K     -- inherent case shell (@cite{newman-2024}; KP wraps DP for oblique/inherent case; explains no-IO-passive languages)
  deriving Repr, DecidableEq, Inhabited

/-- Selectional stack consumed left-to-right -/
abbrev SelStack := List Cat

end Minimalism
