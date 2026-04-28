/-!
# Pronoun strength (Cardinaletti & Starke 1999)
@cite{cardinaletti-starke-1999}

Three-way typology of pronoun forms based on phonological/syntactic
deficiency, from @cite{cardinaletti-starke-1999}'s tripartite theory:

- **Strong**: full, stressed forms — can be coordinated, modified, focused.
- **Weak**: reduced, unstressed — cannot be coordinated or focused.
- **Clitic**: phonologically deficient — must attach to a host.

This is per-entry feature substrate consumed by multiple study files:
@cite{patel-grosz-grosz-2017}'s PER/DEM typology (each PronounForm carries a
list of available strengths) and @cite{ariel-2001}'s Accessibility Marking
Scale (where strength corresponds to accessibility level).
-/

set_option autoImplicit false

namespace Features

/-- @cite{cardinaletti-starke-1999}'s three-way pronoun strength classification. -/
inductive PronounStrength where
  /-- Full, stressed forms (e.g., English *me*, French *moi*). -/
  | strong
  /-- Reduced, unstressed forms (e.g., English *'em*). -/
  | weak
  /-- Phonologically deficient, attached to host (e.g., French *me*, *te*, *le*). -/
  | clitic
  deriving DecidableEq, Repr

end Features
