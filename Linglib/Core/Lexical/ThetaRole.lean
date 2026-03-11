/-!
# Theta Roles

Theory-neutral semantic role labels classifying the relationship between a
verb's arguments and the event it describes. Used by all syntactic frameworks
(Minimalism, HPSG, CCG, Construction Grammar) and all language fragments.

These are **cluster concepts** (@cite{dowty-1991}): each label names a typical
combination of entailments, not a primitive. The fine-grained decomposition
lives in `Theories/Semantics/Events/EntailmentProfile.lean`.
-/

/-- Theta roles for argument structure.
    Language-independent semantic categories classifying the relationship
    between a verb's arguments and the event it describes. Used by both
    Theory-layer modules (Semantics.Events.ThematicRoles) and Fragment-layer
    modules (English/Korean/Japanese/... Predicates). -/
inductive ThetaRole where
  | agent       -- Volitional causer (John kicked the ball)
  | patient     -- Affected entity (John kicked the ball)
  | theme       -- Entity in a state/location (The book is on the table)
  | experiencer -- Perceiver/cognizer (John knows that p)
  | goal        -- Recipient/target (John gave Mary a book)
  | source      -- Origin (John came from Paris)
  | instrument  -- Means (John opened the door with a key)
  | stimulus    -- Cause of experience (The noise frightened John)
  deriving DecidableEq, Repr, BEq
