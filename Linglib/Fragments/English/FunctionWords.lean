import Linglib.Core.Lexical.Word

/-!
# English Miscellaneous Function Words Fragment

Closed-class items that don't fit a more specific Fragment file:

- **Prepositions** (`to_`, `on`, `in_`, `at_`, `by_`, `with_`,
  `from_`, `before`, `after`)
- **Coordinating conjunctions** (`and_`, `or_`, `but`, `nor`)
- **Discourse particles** — focus-sensitive `just_`, `only_`
- **Adverbial quantifiers** (@cite{percus-2000}) — `always`, `usually`,
  `sometimes`, `never`

The auxiliaries (modals + do-support + be + have + modal adverbs +
infinitival particle) live in `Fragments/English/Auxiliaries.lean`.
The complementizers (`that`, `if`, `whether`, ...) live in
`Fragments/English/Complementizers.lean`.

This file may be split further as topic-specific Fragment files
emerge.
-/

namespace Fragments.English.FunctionWords

-- ============================================================================
-- Prepositions
-- ============================================================================

structure PrepEntry where
  form : String
  /-- Can introduce an agent in passive? -/
  passiveAgent : Bool := false
  deriving Repr, BEq

def to_ : PrepEntry := { form := "to" }
def on : PrepEntry := { form := "on" }
def in_ : PrepEntry := { form := "in" }
def at_ : PrepEntry := { form := "at" }
def by_ : PrepEntry := { form := "by", passiveAgent := true }
def with_ : PrepEntry := { form := "with" }
def from_ : PrepEntry := { form := "from" }
def before : PrepEntry := { form := "before" }
def after : PrepEntry := { form := "after" }

def allPrepositions : List PrepEntry := [to_, on, in_, at_, by_, with_, from_, before, after]

def PrepEntry.toWord (p : PrepEntry) : Word :=
  { form := p.form, cat := .ADP, features := {} }

-- ============================================================================
-- Conjunctions
-- ============================================================================

structure ConjEntry where
  form : String
  /-- Coordinating or subordinating? -/
  coordinating : Bool := true
  deriving Repr, BEq

def and_ : ConjEntry := { form := "and" }
def or_ : ConjEntry := { form := "or" }
def but : ConjEntry := { form := "but" }
def nor : ConjEntry := { form := "nor" }

def allConjunctions : List ConjEntry := [and_, or_, but, nor]

def ConjEntry.toWord (c : ConjEntry) : Word :=
  { form := c.form, cat := if c.coordinating then .CCONJ else .SCONJ, features := {} }

-- ============================================================================
-- Discourse Particles (Focus-sensitive)
-- ============================================================================

structure ParticleEntry where
  form : String
  /-- Does this particle require the CQ to be commonly shared? -/
  requiresSharedCQ : Bool
  /-- Can it access non-Roothian alternatives? -/
  nonRoothianAlts : Bool
  deriving Repr, BEq

def just_ : ParticleEntry := { form := "just", requiresSharedCQ := false, nonRoothianAlts := true }
def only_ : ParticleEntry := { form := "only", requiresSharedCQ := true, nonRoothianAlts := false }

def allParticles : List ParticleEntry := [just_, only_]

-- ============================================================================
-- Adverbial Quantifiers (@cite{percus-2000})
-- ============================================================================

/-- Quantificational force for adverbial quantifiers. -/
inductive AdvQuantForce where
  | universal     -- "always"
  | existential   -- "sometimes"
  | proportional  -- "usually"
  | negative      -- "never"
  deriving DecidableEq, Repr

/-- An adverbial quantifier entry: a closed-class adverb that quantifies
    over situations (times, events, occasions).

    In @cite{percus-2000}'s framework, adverbial quantifiers take a situation
    pronoun that determines their domain and introduce a new λs binder
    over their nuclear scope. Generalization Y constrains the situation
    pronoun to be bound by the nearest c-commanding λ. -/
structure AdvQuantEntry where
  form : String
  /-- Quantificational force. -/
  force : AdvQuantForce
  deriving Repr, BEq

def always : AdvQuantEntry := { form := "always", force := .universal }
def usually : AdvQuantEntry := { form := "usually", force := .proportional }
def sometimes : AdvQuantEntry := { form := "sometimes", force := .existential }
def never : AdvQuantEntry := { form := "never", force := .negative }

def allAdvQuants : List AdvQuantEntry := [always, usually, sometimes, never]

end Fragments.English.FunctionWords
