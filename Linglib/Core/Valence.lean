/-!
# Valence

Transitivity / argument structure of a predicate — the one `Core/Word`
morphological type with no Universal Dependencies equivalent. Extracted to its
own light module so verb lexical entries (`Semantics/Lexical/VerbEntry`) can
type argument structure without pulling the heavier `Core.Word` / `Core.UD`
import closure.
-/

/-- Transitivity / argument structure. No direct UD equivalent. -/
inductive Valence where
  | intransitive  -- sleep, arrive
  | transitive    -- see, eat
  | ditransitive  -- give, send (double object)
  | dative        -- give X to Y (prepositional dative)
  | locative      -- put X on Y
  | copular       -- be (takes predicate)
  | clausal       -- manage to VP, believe that S (xcomp/ccomp complement)
  deriving Repr, DecidableEq, Inhabited
