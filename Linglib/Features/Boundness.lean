/-!
# Boundness

Morphological boundness of a lexical item: a free word versus a bound
clitic or suffix. A general per-entry morphological feature, not specific to
any one construction — relevant to acquisition ([clark-2017] argues free
morphemes are acquired more readily than bound ones) and to coordination
typology ([mitrovic-sauerland-2016]), among others.
-/

/-- Morphological boundness: free word vs bound clitic/suffix. -/
inductive Boundness where
  /-- Independent word (Hungarian "is", English "and"). -/
  | free
  /-- Clitic or suffix (Georgian "-c", Latin "-que"). -/
  | bound
  deriving DecidableEq, Repr, BEq
