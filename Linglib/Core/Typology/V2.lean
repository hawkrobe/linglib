/-!
# V2Data

Theory-neutral V2 data: for each clause form, whether verb movement to
second position is observed. Used by `Fragments/{Lang}/V2.lean` files
for descriptive encoding of cross-Germanic V2 variation
(@cite{westergaard-2009}).
-/

structure V2Data where
  name : String
  declV2 : Bool      -- V2 in root declaratives
  whQV2 : Bool       -- V2 in wh-questions
  ynQV2 : Bool       -- V2 in yes/no-questions
  exclV2 : Bool      -- V2 in exclamatives
  impV2 : Bool       -- V2 in imperatives
  embFinV2 : Bool    -- V-to-I in embedded finite clauses
  embQV2 : Bool      -- V2 in embedded questions
  deriving Repr, DecidableEq
