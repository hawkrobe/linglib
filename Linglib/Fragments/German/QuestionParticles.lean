/-!
# German Question Particles
@cite{theiler-2021} @cite{zheng-2025}

Lexical entries for German interrogative/flavoring particles. The fragment
commits only to theory-neutral lexical primitives; the left-peripheral
layer assignment lives in `Phenomena.Questions.Studies.Theiler2021`
(*denn*) and `Phenomena.Questions.Studies.SeeligerRepp2018` (*doch wohl*).

## Particles

| Particle | Gloss | Bias |
|----------|-------|------|
| denn | highlighting-sensitive flavoring particle | +evidential |
| doch wohl | non-compositional RQ marker | +evidential, +epistemic |

German *denn* parallels Mandarin *nandao*: both require contextual evidence
prompting the question. Key difference: *denn* is compatible with wh-questions, while *nandao* is restricted to polar questions.

@cite{theiler-2021} analyzes *denn* as highlighting-sensitive: it signals that the
question is prompted by the highlighted/salient proposition in context.
In polar questions, this creates an evidential requirement; in wh-questions,
it merely signals informational need.

## Cross-Module Connections

- `Fragments.Mandarin.QuestionParticles.nandao`: cross-linguistic parallel
- `Kernel.nandaoFelicitous`: shared felicity mechanism (evidence + unexpectedness)

-/

namespace Fragments.German.QuestionParticles

/-- A German interrogative/flavoring particle entry. -/
structure QParticleEntry where
  form : String
  gloss : String
  polarOk : Bool
  declOk : Bool
  whOk : Bool
  requiresEvidentialBias : Bool
  requiresEpistemicBias : Bool
  deriving Repr, DecidableEq

/-- denn — highlighting-sensitive flavoring particle.
Signals the question is prompted by salient contextual evidence.
Compatible with both polar and wh-questions (unlike nandao). -/
def denn : QParticleEntry where
  form := "denn"
  gloss := "DENN (highlighting-sensitive flavoring particle)"
  polarOk := true
  declOk := false
  whOk := true
  requiresEvidentialBias := true
  requiresEpistemicBias := false

/-- *doch wohl* — non-compositional rejecting question marker.

    @cite{seeliger-repp-2018} SS 4.2: *doch* and *wohl* are both modal
    particles but their combination in RQs does not receive a compositional
    interpretation. Instead, *doch wohl* is a conventionalized marker that
    signals the speech act is a rejecting question (RQ).

    In isolation:
    - *doch* has a "conflict" meaning: signals a contrast between the
      proposition and the context (reminding / realizing the obvious)
    - *wohl* has a question-inducing function + reportative meaning shade:
      weakens the speaker's commitment to the proposition

    In RQs, *doch wohl* is obligatory — both particles are required to
    mark a declarative as a RQ. The combination enters syntactic Agree
    with the illocutionary operator REJECTQ.

    @cite{seeliger-repp-2018} SS 4.3: the formal means employed to mark
    RQs are *cues* for the speech act, not compositional building blocks.

    Cross-linguistically, *doch wohl* parallels Swedish fronted negation +
    *väl*, but the marking strategies are not the same across the two
    languages. -/
def dochWohl : QParticleEntry where
  form := "doch wohl"
  gloss := "MP+MP (non-compositional RQ marker)"
  polarOk := true
  declOk := false  -- doch wohl in RQs marks questions, not assertions
  whOk := false
  requiresEvidentialBias := true
  requiresEpistemicBias := true

def allQuestionParticles : List QParticleEntry := [denn, dochWohl]

theorem denn_evidential : denn.requiresEvidentialBias = true := rfl
theorem denn_no_epistemic : denn.requiresEpistemicBias = false := rfl

/-- Unlike Mandarin nandao, German denn is compatible with wh-questions
(@cite{theiler-2021} §3). -/
theorem denn_wh_ok : denn.whOk = true := rfl

-- doch wohl verification theorems
theorem dochWohl_form : dochWohl.form = "doch wohl" := rfl
theorem dochWohl_evidential : dochWohl.requiresEvidentialBias = true := rfl
theorem dochWohl_epistemic : dochWohl.requiresEpistemicBias = true := rfl
theorem dochWohl_not_assertion : dochWohl.declOk = false := rfl
theorem dochWohl_not_wh : dochWohl.whOk = false := rfl

/-- *doch wohl* requires BOTH evidential and epistemic bias, unlike
    *denn* which only requires evidential. This reflects the "insisting"
    nature of RQs vs. the merely "highlighting" nature of *denn*-questions. -/
theorem dochWohl_stricter_than_denn :
    dochWohl.requiresEvidentialBias = true ∧
    dochWohl.requiresEpistemicBias = true ∧
    denn.requiresEpistemicBias = false := ⟨rfl, rfl, rfl⟩

end Fragments.German.QuestionParticles
