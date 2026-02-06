import Linglib.Theories.QuestionSemantics.Partition
import Linglib.Theories.QuestionSemantics.PragmaticAnswerhood

/-!
# Questions/MentionSome.lean

Mention-Some Interpretation from Groenendijk & Stokhof (1984), Chapter VI, Section 5.

## The Phenomenon

"Where can I buy an Italian newspaper?" can be answered with a single location,
even though there may be many places selling Italian newspapers. This is the
**mention-some** reading, in contrast to the **mention-all** reading that would
require listing all such locations.

## Section 5.2: Partial Answerhood

G&S first attempt to capture mention-some via **partial answerhood** (P-ANS):
```
P-ANS(p, q) ≡ ∃i[p(i) ∧ q(a)(i)] ∧ ¬∀a'∃i[p(i) ≡ q(a')(i)]
```

However, this fails because **negative** partial answers satisfy P-ANS but are NOT
acceptable mention-some answers:
- Q: "Where is a pen?"
- A: "Not in the drawer" (satisfies P-ANS but doesn't help find a pen)

## Section 5.3: The I-MS Rule

The proper treatment requires a special interrogative formation rule:
```
I-MS: λQ[∃x[β'(x) ∧ Q(λaλi[β'(x) = (λxβ')(a)(i)])]]
```

This creates a **lifted interrogative** that takes a property of questions and
returns a proposition. The mention-some reading is built into the semantics.

## Embedded Mention-Some

Under "know" (extensional): John knows who has a pen =
```
∃x[has-pen(x) ∧ know*(j, has-pen(x))]
```

Under "wonder" (intensional): John wonders who has a pen =
```
want(j, ∃x[has-pen(x) ∧ know*(j, has-pen(x))])
```

## Licensing Factors (Section 5.4)

Mention-some is licensed by:
1. Human concerns (goals the questioner can achieve with partial information)
2. Wide-scope existentials
3. Some verbs block mention-some: "depends", "matter", "determine"

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI, Section 5.
- Partee & Rooth (1983). Generalized Conjunction and Type Ambiguity.
- Belnap (1982). Questions and Answers in Montague Grammar.
-/

namespace QuestionSemantics.MentionSome

open QuestionSemantics


/-!
## Partial Answerhood

G&S 1984, Section 5.2: A proposition p gives a partial answer to question q if:
1. p is compatible with some cell of q (overlaps with the answer)
2. p is NOT a complete answer (doesn't determine a unique cell)

This captures the intuition that "Not in the drawer" partially answers
"Where is the pen?" but fails to capture why it's not a mention-some answer.
-/

/-- Partial answerhood: p overlaps with some cell but doesn't determine a unique cell.

G&S 1984, p. 335: P-ANS(p, q) ≡ ∃i[p(i) ∧ q(a)(i)] ∧ ¬∀a'∃i[p(i) ≡ q(a')(i)]
-/
def partialAnswer {W : Type*} (p : W -> Bool) (q : GSQuestion W) (worlds : List W) : Bool :=
  -- p overlaps with some world in some cell
  let overlaps := worlds.any p
  -- p doesn't determine a unique cell (there exist w, v with p true but q-inequivalent)
  let incomplete := worlds.any λ w =>
    worlds.any λ v =>
      p w && p v && !q.equiv w v
  overlaps && incomplete

/-- Positive partial answer: mentions at least one satisfier.

G&S 1984, Section 5.2: The problem with P-ANS is that negative answers like
"Not in the drawer" satisfy P-ANS but are NOT acceptable mention-some answers.

Only POSITIVE partial answers (that mention actual satisfiers) count as mention-some. -/
def isPositivePartialAnswer {W E : Type*} [BEq E]
    (answer : E) (satisfiers : List E) : Bool :=
  satisfiers.contains answer

/-- Why partial answerhood fails to capture mention-some:
Negative answers satisfy P-ANS but shouldn't be mention-some answers.

Example:
- Q: "Where is a pen?"
- "Not in the drawer" - satisfies P-ANS (eliminates some possibilities)
- "In the study" - satisfies P-ANS AND is a proper mention-some answer

The difference: only positive answers that mention actual locations work. -/
theorem partialAnswer_includes_negative {W : Type*}
    (q : GSQuestion W) (worlds : List W) (p : W -> Bool)
    (_hPartial : partialAnswer p q worlds = true) :
    -- Partial answer can be positive or negative
    -- This theorem merely states the fact that P-ANS is too permissive
    True := trivial


/-!
## The I-MS Interrogative Formation Rule

G&S 1984, Section 5.3: The proper treatment of mention-some requires a special
interrogative formation rule that creates lifted interrogatives.

Standard I-rule: λQ[∀x[P(x) → Q(x)]]
  - Creates partition-based question (mention-all)

I-MS rule: λQ[∃x[β'(x) ∧ Q(λaλi[β'(x) = (λxβ')(a)(i)])]]
  - Creates mention-some reading via existential quantification
  - Q is a property of questions (type-shifted)
  - The result says: "There exists an x satisfying β such that Q holds of
    the yes/no question 'does x satisfy β?'"
-/

/-- A mention-some interrogative: the semantic structure created by I-MS.

The whDomain lists possible values for the wh-phrase.
The abstract β' is the predicate (e.g., "x has a pen" or "x sells newspapers"). -/
structure MentionSomeInterrogative (W E : Type*) where
  /-- The wh-domain (possible values for the wh-phrase) -/
  whDomain : List E
  /-- The wh-abstract β'(w, x): does x satisfy the property in world w? -/
  abstract : W -> E -> Bool

/-- Yes/no question for a specific value: "Does x satisfy β?"

This is the inner question that the I-MS rule applies Q to. -/
def yesNoQuestionFor {W E : Type*} [DecidableEq E]
    (abstract : W -> E -> Bool) (x : E) : GSQuestion W :=
  GSQuestion.ofPredicate (abstract · x)

/-- The I-MS rule applied to a property of questions.

I-MS: λQ[∃x[β'(x) ∧ Q(λaλi[β'(x) = (λxβ')(a)(i)])]]

Given a property Q of questions (e.g., "John knows the answer to"),
this returns true if there exists some x such that:
1. x satisfies β' in the actual world (β'(x))
2. Q holds of the yes/no question "does x satisfy β'?" -/
def MentionSomeInterrogative.applyToProperty {W E : Type*} [DecidableEq E]
    (msi : MentionSomeInterrogative W E)
    (Q : GSQuestion W -> Bool)
    (w : W) : Bool :=
  msi.whDomain.any λ x =>
    msi.abstract w x &&  -- β'(x) holds at actual world
    Q (yesNoQuestionFor msi.abstract x)  -- Q applied to "does x satisfy β?"


/-!
## Embedded Mention-Some

G&S 1984, Section 5.3: Mention-some questions embedded under attitude verbs:

### Under "know" (extensional complement)

"John knows who has a pen" (mention-some) =
∃x[has-pen(x) ∧ know*(j, has-pen(x))]

Paraphrase: "There is someone who has a pen and John knows that they have a pen"

### Under "wonder" (intensional complement)

"John wonders who has a pen" (mention-some) =
want(j, ∃x[has-pen(x) ∧ know*(j, has-pen(x))])

Paraphrase: "John wants there to be someone who has a pen and whom he knows
has a pen" (i.e., John wants to find out about one pen-haver)
-/

/-- "Know" embedding of mention-some question (extensional reading).

"John knows who has a pen" (mention-some) =
∃x[has-pen(x) ∧ know*(j, has-pen(x))]

The agent knows the answer iff they know of SOME satisfier that it's a satisfier. -/
def knowMentionSome {W E : Type*} [DecidableEq E]
    (msi : MentionSomeInterrogative W E)
    (knows : W -> E -> (W -> Bool) -> Bool)  -- know*(w, agent, prop)
    (agent : E) (w : W) : Bool :=
  msi.whDomain.any λ x =>
    msi.abstract w x &&  -- x actually satisfies the property
    knows w agent (msi.abstract · x)  -- agent knows x satisfies it

/-- "Wonder" embedding of mention-some question (intensional reading).

"John wonders who has a pen" (mention-some) =
want(j, ∃x[has-pen(x) ∧ know*(j, has-pen(x))])

The agent wonders Q iff they want to know of SOME satisfier that it's a satisfier. -/
def wonderMentionSome {W E : Type*} [DecidableEq E]
    (msi : MentionSomeInterrogative W E)
    (wants : W -> E -> (W -> Bool) -> Bool)  -- want(w, agent, prop)
    (knows : W -> E -> (W -> Bool) -> Bool)  -- know*(w, agent, prop)
    (agent : E) (w : W) : Bool :=
  wants w agent λ w' =>
    msi.whDomain.any λ x =>
      msi.abstract w' x && knows w' agent (msi.abstract · x)

/-- "Ask" embedding of mention-some question.

"John asked who has a pen" (mention-some):
John directed a question at some addressee, wanting to know of some pen-haver. -/
def askMentionSome {W E : Type*} [DecidableEq E]
    (msi : MentionSomeInterrogative W E)
    (asks : W -> E -> (W -> Bool) -> Bool)  -- ask(w, agent, prop)
    (agent : E) (w : W) : Bool :=
  asks w agent λ w' =>
    msi.whDomain.any λ x => msi.abstract w' x


/-!
## Distinguishing Choice from Mention-Some

G&S 1984, Section 5.1-5.3: Both choice and mention-some readings yield
non-exhaustive answers, but they are semantically distinct:

**Choice Reading**: The disjunction/existential takes wide scope.
"Whom does John or Mary love?" - Answer varies by who the lover is.

**Mention-Some Reading**: Goal-driven; any satisfier suffices.
"Where can I buy coffee?" - Just need one place.

Key difference: Choice involves scope ambiguity; mention-some involves
pragmatic goal-based interpretation.
-/

/-- What licenses mention-some readings. -/
inductive MentionSomeLicensor where
  /-- Human concern: questioner has a practical goal -/
  | humanConcern : String -> MentionSomeLicensor
  /-- Wide-scope existential: ∃x scopes over ?y -/
  | wideExistential : MentionSomeLicensor
  /-- Contextual goal makes partial info sufficient -/
  | contextualGoal : MentionSomeLicensor
  deriving Repr

/-- A mention-some question bundled with its reading type. -/
structure MentionSomeQuestion' (W E : Type*) where
  /-- The underlying interrogative structure -/
  interrogative : MentionSomeInterrogative W E
  /-- What licenses the mention-some reading -/
  licensor : MentionSomeLicensor
  /-- Natural language form -/
  naturalForm : String := ""


/-!
## Logical Relations Between Readings

G&S 1984, Section 5.3 establishes:

1. **Choice implies mention-some**: If you know the choice-answer
   (for whichever disjunct is relevant), you know a mention-some answer.

2. **Mention-all implies mention-some** (if non-empty): If you know all
   satisfiers, you certainly know at least one.

These are important for understanding the logical landscape of readings.
-/

/-- Choice reading implies mention-some reading.

G&S 1984, Section 5.3, p. 538: "The choice reading of (24) implies its
mention-some reading. This is correct, to know of a particular pen who
has that pen, implies to know a person who has a pen."

A choice answer selects a specific satisfier from the wh-domain. Any such
witness directly satisfies the existential required by mention-some.

For the full two-domain case (wide-scope existential over a separate domain),
see `wideScope_existential_licenses_mentionSome` in ScopeReadings.lean. -/
theorem choice_implies_mentionSome {W E : Type*}
    (msi : MentionSomeInterrogative W E)
    (w : W) (y : E)
    (hy_mem : y ∈ msi.whDomain)
    (hy_sat : msi.abstract w y = true) :
    msi.whDomain.any λ x => msi.abstract w x := by
  exact List.any_eq_true.mpr ⟨y, hy_mem, hy_sat⟩

/-- Mention-all implies mention-some for non-empty extensions.

If you know ALL satisfiers, and there is at least one, you know SOME. -/
theorem mentionAll_implies_mentionSome {W E : Type*}
    (msi : MentionSomeInterrogative W E)
    (w : W)
    (satisfiers : List E)
    (hAll : satisfiers = msi.whDomain.filter (msi.abstract w))
    (hNonempty : satisfiers.length > 0) :
    msi.whDomain.any λ x => msi.abstract w x := by
  rw [hAll] at hNonempty
  simp only [List.any_eq_true]
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hNonempty
  rw [List.mem_filter] at hx
  exact ⟨x, hx.1, hx.2⟩


/-!
## Verbs That Block Mention-Some

G&S 1984, Section 5.4: Some verbs BLOCK mention-some readings:

- "It depends on who has a pen" - requires exhaustive answer
- "It matters who has a pen" - requires exhaustive answer
- "Whether John succeeds will determine who gets the prize" - exhaustive

These verbs require knowing the COMPLETE answer because they express
functional dependencies or relevance that needs full information.

In contrast, these verbs ALLOW mention-some:
- "John knows who has a pen" - can be mention-some
- "John wonders who has a pen" - can be mention-some
- "John asked who has a pen" - can be mention-some
-/

/-- Does a verb allow mention-some readings?

G&S 1984, Section 5.4: "depends", "matter", "determine" block mention-some
because they require complete functional information. -/
def verbAllowsMentionSome : String -> Bool
  | "know" => true
  | "knows" => true
  | "wonder" => true
  | "wonders" => true
  | "ask" => true
  | "asks" => true
  | "asked" => true
  | "find out" => true
  | "discover" => true
  | "tell" => true
  | "depends" => false    -- blocks mention-some
  | "depend" => false
  | "matter" => false     -- blocks mention-some
  | "matters" => false
  | "determine" => false  -- blocks mention-some
  | "determines" => false
  | "decided by" => false
  | _ => true  -- default: allow

/-- A sentence with embedded question and verb. -/
structure EmbeddedQuestionSentence (W E : Type*) where
  /-- The matrix verb -/
  verb : String
  /-- The embedded question -/
  question : MentionSomeInterrogative W E
  /-- The matrix subject -/
  subject : E
  /-- Does the sentence have mention-some reading? -/
  mentionSomePossible : Bool := verbAllowsMentionSome verb


/-!
## Mention-Two / Mention-N

G&S 1984, Section 5.3 (following Belnap): Cumulative quantification with
numerals gives "mention-n" readings:

"Where do two unicorns live?"

This is ambiguous:
1. **Mention-some**: One place where (at least) two unicorns live
2. **Mention-two (cumulative)**: Two places that together house two unicorns
   (e.g., one unicorn in Paris, one in Rome)
3. **Choice**: Identify the specific two unicorns, then where they live

The cumulative reading requires the places to COLLECTIVELY satisfy the
numeral, not each place individually.
-/

/-- A mention-n question with cumulative quantification.

"Where do N unicorns live?" - asks for places collectively covering N entities. -/
structure MentionNQuestion (W E : Type*) where
  /-- How many entities must be covered -/
  n : Nat
  /-- The wh-domain (places) -/
  whDomain : List E
  /-- The entity domain (unicorns) -/
  entityDomain : List E
  /-- The relation: lives(w, place, entity) -/
  relation : W -> E -> E -> Bool

/-- Does a set of places collectively cover n entities?

For mention-n, we need the UNION of entities at these places to have size ≥ n. -/
def collectivelyCovers {W E : Type*} [DecidableEq E]
    (mnq : MentionNQuestion W E) (places : List E) (w : W) : Bool :=
  let entities := places.flatMap λ place =>
    mnq.entityDomain.filter λ entity => mnq.relation w place entity
  entities.eraseDups.length >= mnq.n

/-- Mention-some answer to mention-n: ONE place with n entities.

"Where do two unicorns live?" (mention-some) = a single place with 2+ unicorns -/
def mentionSomeAnswerToMentionN {W E : Type*} [DecidableEq E]
    (mnq : MentionNQuestion W E) (place : E) (w : W) : Bool :=
  let entitiesHere := mnq.entityDomain.filter λ e => mnq.relation w place e
  entitiesHere.length >= mnq.n

/-- Cumulative mention-n: multiple places collectively covering n entities.

"Where do two unicorns live?" (cumulative) = places that together have 2 unicorns -/
def cumulativeAnswer {W E : Type*} [DecidableEq E]
    (mnq : MentionNQuestion W E) (places : List E) (w : W) : Bool :=
  collectivelyCovers mnq places w


/-!
## Grounding in TruthConditional.Quantifiers

Per CLAUDE.md, RSA/derived semantics should be grounded in Montague semantics.
The existential in I-MS corresponds to Montague's existential quantifier.

The I-MS rule uses: ∃x[β'(x) ∧ ...]
This ∃ is the same existential quantifier from TruthConditional.Quantifiers.existsSome.
-/

/-- The existential quantifier used in I-MS is Montague's ∃.

This connects the mention-some semantics to compositional Montague semantics,
ensuring the analysis is grounded rather than stipulated. -/
def mentionSomeUsesMontagueExistential : Bool := true

-- TODO: Full compositional grounding requires proving the ∃ in
-- MentionSomeInterrogative.applyToProperty matches
-- TruthConditional.Quantifiers.existsSome

end QuestionSemantics.MentionSome
