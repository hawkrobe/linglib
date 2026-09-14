/-!
# Mass/count

The morphosyntactic mass/count feature ([krifka-2026]). No UD equivalent, so it is a
linglib feature taxonomy rather than a `UD.*` alias.
-/

/-- Morphosyntactic mass/count feature. A formal feature parallel to grammatical
    gender — not an ontological distinction. Determines kind-anaphor morphology:
    [MASS] → *it*, [COUNT] → *they*. Evidence: *pollen*[MASS] → *it* vs
    *pollen grains*[COUNT] → *they* for the same referent ([krifka-2026] §2). -/
inductive MassCount where
  | mass   -- mass nouns: *mold*, *pollen*, *milk*, *gold*
  | count  -- count nouns: *spider*, *pollen grain*, *dog*, *cup*
  deriving Repr, DecidableEq, Hashable
