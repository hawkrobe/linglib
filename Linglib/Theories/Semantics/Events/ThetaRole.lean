/-!
# Theta Roles (Derived Convenience Labels)

@cite{dowty-1991} @cite{grimm-2011} @cite{beavers-2010} @cite{levin-2019}

Theta roles are **derived convenience labels** that name clusters in
entailment-profile space (`EntailmentProfile.lean`). They are NOT
primitives: the authoritative representation of argument semantics is
the entailment profile, and role labels are computed from it via
`EntailmentProfile.toRole`.

The field consensus (@cite{levin-2019}) is that discrete thematic roles
have been superseded by entailment-based representations:
- **Proto-Agent/Proto-Patient** entailment profiles (@cite{dowty-1991})
- **Agentivity lattice** with privative features (@cite{grimm-2011})
- **Affectedness hierarchy** on P-Patient entailments (@cite{beavers-2010})

Role labels remain useful as a **shared interface vocabulary** for
linking theories, neo-Davidsonian logical forms, and cross-framework
comparison. All syntactic frameworks (Minimalism, HPSG, CCG, Construction
Grammar) and language fragments use them, but they should be understood
as derived from — not prior to — entailment structure.

See `EntailmentProfile.toRole` for the canonical profiles → labels mapping.
See `ThetaRole.canonicalProfile` for the inverse labels → profiles mapping.
-/

/-- Theta roles for argument structure — derived convenience labels.
    Each label names a cluster of entailments in proto-role space
    (@cite{dowty-1991}). The canonical mapping from profiles to labels
    is `EntailmentProfile.toRole`; the inverse is `ThetaRole.canonicalProfile`. -/
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
