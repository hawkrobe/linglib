/-!
# Formative position and boundness
[bickel-nichols-2007]

Where a formative sits relative to its host, and whether it is free or
bound.
-/

namespace Morphology

/-- Typological position classification for formatives.
    [bickel-nichols-2007] Table 3.2 (p. 198), flattened: the table crosses
    five positions (Prae/In/Post/Simul/Detached) with formative types; this
    enum keeps the positions, promoting circumfixation (the table's common
    Simul subtype) and endoclisis (an In subtype) to their own cases. -/
inductive FormativePosition where
  | praefixed     -- formative precedes host
  | postfixed     -- formative follows host
  | infixed       -- formative inserted within host
  | circumfixed   -- formative wraps host
  /-- Several tokens of one morpheme realized at different places in the
  word ([bickel-nichols-2007] p. 200, after Hagège) — NOT process
  morphology: bare ablaut, substitution, and subtraction are In-position
  formatives, reduplication is Prae/Post, in the source table. -/
  | simultaneous
  | detached      -- not attached to its host (may still be phonologically bound)
  | endoclitic    -- clitic inserted inside a word (Udi, European Portuguese)
  deriving DecidableEq, Repr

/-- Morphological boundness: the coarse two-way cut of the wordhood
scale. A general per-entry morphological feature — relevant to
acquisition ([clark-2017]: free morphemes are acquired more readily
than bound ones) and to coordination typology
([mitrovic-sauerland-2016]), among others. -/
inductive Boundness where
  /-- Independent word (Hungarian "is", English "and"). -/
  | free
  /-- Clitic or suffix (Georgian "-c", Latin "-que"). -/
  | bound
  deriving DecidableEq, Repr, BEq

end Morphology
