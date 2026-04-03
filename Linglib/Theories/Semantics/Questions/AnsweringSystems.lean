import Linglib.Core.Polarity

/-!
# Answering System Typology
@cite{holmberg-2016}

Cross-linguistic variation in how languages answer polar questions.

## The Binary Parameter

@cite{holmberg-2016}'s central typological contribution: languages divide into
two types based on what "yes" means in response to a negative question
("Doesn't John drink?"):

- **Truth-based**: "yes" affirms the proposition in the question.
  To "Doesn't he drink?", "yes" = "he doesn't drink" (Japanese, Mandarin, Thai).
- **Polarity-based**: "yes" assigns positive polarity.
  To "Doesn't he drink?", "yes" = "he does drink" (English, Swedish, German).

## Answer Strategy

Orthogonally, languages vary in whether answers use dedicated particles
or echo the finite verb:

- **Particle**: dedicated yes/no words (English *yes/no*, Japanese *hai/iie*)
- **Verb echo**: echoed finite verb (Finnish *juo/ei juo*, Welsh *ydy/nac ydy*)
- **Mixed**: both available (Swedish *ja/nej* + verb echo)

## Connection to PolP

In @cite{holmberg-2016}'s syntax, every finite clause has a polarity head
(PolP) bearing a valued or unvalued [±Pol] feature. In polar questions,
[±Pol] is unvalued — the answer values it. The answering system parameter
determines whether "yes" values the variable as [+Pol] (polarity-based)
or affirms the question's primary proposition (truth-based).
-/

namespace Semantics.Questions

/-- How a language interprets "yes" in response to negative polar questions.

    The diagnostic: "Doesn't John drink?" → "Yes" means...
    - Truth-based: "He doesn't drink" (affirms the proposition)
    - Polarity-based: "He does drink" (assigns positive polarity) -/
inductive AnsweringSystem where
  /-- "Yes" affirms the proposition in the question (Japanese, Mandarin, Thai, Cantonese) -/
  | truthBased
  /-- "Yes" assigns positive polarity (English, Swedish, German, French, Finnish) -/
  | polarityBased
  deriving DecidableEq, Repr

/-- How a language forms answers to polar questions.

    Orthogonal to `AnsweringSystem` — either system can combine with
    either strategy. -/
inductive AnswerStrategy where
  /-- Dedicated yes/no particles (English *yes/no*, Japanese *hai/iie*) -/
  | particle
  /-- Echoed finite verb (Finnish *juo/ei juo*, Welsh *ydy/nac ydy*) -/
  | verbEcho
  /-- Both particle and verb echo available (Swedish *ja/nej* + verb echo) -/
  | mixed
  deriving DecidableEq, Repr

/-- A language's polar answer profile: answering system + answer strategy. -/
structure PolarAnswerProfile where
  /-- How "yes" is interpreted relative to negative questions -/
  system : AnsweringSystem
  /-- How answers are formed (particle, verb echo, or both) -/
  strategy : AnswerStrategy
  /-- Does the language have a dedicated polarity-reversing particle
      (e.g., Swedish *jo*, German *doch*, French *si*)? -/
  hasPolarityReversal : Bool := false
  deriving DecidableEq, Repr

/-- The diagnostic prediction: what does "yes" mean in response to
    "Doesn't John drink?" under each answering system?

    Returns the polarity of the proposition expressed by "yes". -/
def AnsweringSystem.yesToNegativeQuestion : AnsweringSystem → Core.Polarity
  | .truthBased    => .negative  -- "yes" = "he doesn't drink"
  | .polarityBased => .positive  -- "yes" = "he does drink"

/-- Truth-based and polarity-based systems give opposite answers
    to negative questions. -/
theorem answering_systems_diverge_on_negative :
    AnsweringSystem.truthBased.yesToNegativeQuestion ≠
    AnsweringSystem.polarityBased.yesToNegativeQuestion := by decide

/-! ## Negation Height and Answering System Derivation

@cite{holmberg-2016} Ch 4.3-4.7 derives the answering system from whether
the negation in the question can assign value to the polarity variable [±Pol].
The crucial factor is structural accessibility: if negation is close enough to
[±Pol] to value it, the focused answer particle clashes with the inherited
negative value → polarity-based. If negation is too distant or not in a
c-command relation with [±Pol], the particle freely assigns value → truth-based.

- **Low negation** (VP-internal, below PolP scope): negation cannot reach [±Pol].
  "Yes" affirms the (negative) proposition → truth-based.
  Examples: Japanese, Mandarin Chinese, Thai.

- **Middle negation** (NegP between TP and PolP, or merged with Pol): negation
  values [Pol] as [-Pol], creating a feature clash with an affirmative particle.
  "Yes" assigns [+Pol] → polarity-based.
  Examples: English (default), Swedish (§4.5), Finnish (§4.6, higher variety
  of middle), German.

- **High negation** (C-domain, above PolP scope): negation scopes over [±Pol]
  rather than valuing it. Used in positively-biased negative questions where
  the negation eliminates the negative alternative.
  Examples: English *-n't* in positively-biased readings (§4.8), English
  outer negation (§4.3).

This is the book's deepest explanatory contribution: the binary answering-system
parameter is not stipulated but derived from independently motivated syntactic
variation in negation height. -/

/-- Structural height of sentential negation relative to PolP.

    Note: this classifies *constructions*, not languages. A single language
    may have multiple negation heights (e.g., English has middle by default,
    low when scoped under an adverb, and high in positively-biased questions). -/
inductive NegationHeight where
  /-- Negation below PolP — VP-internal (Japanese, Mandarin, Thai) -/
  | low
  /-- Negation at PolP level — NegP between TP and PolP, or merged with Pol
      (English default, Swedish, Finnish, German) -/
  | middle
  /-- Negation above PolP — C-domain, scoping over [±Pol]
      (English *-n't* in positively-biased questions) -/
  | high
  deriving DecidableEq, Repr

/-- Derive the answering system from negation height.

    Low negation → truth-based: negation scopes below [±Pol], so the
    question's primary proposition includes negation. "Yes" affirms
    the (negative) proposition.

    Middle/high negation → polarity-based: negation is at or above [±Pol],
    so "yes" values [±Pol] as [+Pol] regardless of negation. -/
def NegationHeight.predictedSystem : NegationHeight → AnsweringSystem
  | .low    => .truthBased
  | .middle => .polarityBased
  | .high   => .polarityBased

/-- Middle and high negation both predict polarity-based systems. -/
theorem middle_high_same_prediction :
    NegationHeight.middle.predictedSystem = NegationHeight.high.predictedSystem := rfl

/-- Low negation predicts a different system from middle negation. -/
theorem low_differs_from_middle :
    NegationHeight.low.predictedSystem ≠ NegationHeight.middle.predictedSystem := by decide

end Semantics.Questions
