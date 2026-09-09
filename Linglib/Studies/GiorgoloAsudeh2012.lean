import Linglib.Semantics.Composition.Writer

/-!
# Giorgolo and Asudeh (2012): ⟨M, η, ⋆⟩ Monads for Conventional Implicatures

This file formalizes [giorgolo-asudeh-2012]'s treatment of conventional implicature as the side
effect of a Writer monad, [shan-2001]'s program applied to [potts-2005]'s paired values: every
expression denotes a computation that yields its at-issue value and logs the side-issue propositions
its parts contribute, and the flow of information between the dimensions is fixed by the monad
itself, since bind hands the continuation only the value and can only extend the log
(`Writer.val_bind_congr`, `Writer.log_prefix_bind`, `Writer.tell_persists`), so no lexical item can
read or revise the side-issue dimension, as Potts's restriction demands and as the impossible
modifier *negex* of [barker-bernardi-shan-2010] would. Presupposition triggers log their conditions
in a second Writer layer of a monad transformer (`M`, `write`, `check`), whose projections compose
as the two Glue implications prescribe (`atIssue_seq`, `ciLog_seq`, `presupLog_seq`). The derivation
of "John, who likes cats, likes dogs also" puts the at-issue proposition, the conventional
implicature and the presupposition of *also* in their three places (`Ex20.atIssue_sentence`,
`Ex20.ciLog_sentence`, `Ex20.presupLog_sentence`); the presupposition is entailed by the side-issue
log (`Ex20.presupposition_of_ci`), an interaction available only once the computation has ended,
which is the paper's reply to [anderbois-brasoveanu-henderson-2010]'s case against
multidimensionality, while the relative clause never reaches the at-issue value
(`Ex20.atIssue_sentence_congr`).

## Implementation notes

* The monad is mathlib's `WriterT` over list logs, whose linguistic surface (`val`, `log`, `tell`
  and their lemmas) is `Semantics/Composition/Writer.lean`; the two channels are the transformer
  `WriterT (List CI) (Writer (List Presup))`, with `check` lifted from the presupposition monad
  as the paper's footnote prescribes.
* Glue's two implications are the two modes of composition: `⊸` elimination is the monad's `<*>`,
  Shan's monadic application, and `⊸*` elimination plain application to monadic arguments; the
  introduction rules, which reason hypothetically, are not needed for the derivation.
* The extension of *like* is a parameter: the presupposition of *also* follows from the logged
  implicature alone, given that cats are not dogs.

## References

* [giorgolo-asudeh-2012]
* [shan-2001]
* [potts-2005]
* [anderbois-brasoveanu-henderson-2010]
* [barker-bernardi-shan-2010]
-/

namespace GiorgoloAsudeh2012

universe u

variable {CI Presup A B : Type u}

/-! ### The two channels -/

/-- The two-channel monad: conventional implicatures are logged by the transformer and
presuppositional conditions by the monad it transforms, so that a computation's result is the
paper's ⟨⟨value, implicatures⟩, presuppositions⟩. -/
abbrev M (CI Presup : Type u) := WriterT (List CI) (Writer (List Presup))

/-- The at-issue value of a computation. -/
def atIssue (m : M CI Presup A) : A := m.run.val.1

/-- The conventional implicatures a computation logs. -/
def ciLog (m : M CI Presup A) : List CI := m.run.val.2

/-- The presuppositional conditions a computation logs. -/
def presupLog (m : M CI Presup A) : List Presup := m.run.log

/-- `write(t) = ⟨⊥, {t}⟩`: log a conventional implicature. -/
def write (p : CI) : M CI Presup PUnit := MonadWriter.tell [p]

/-- `check(t)`, lifted from the presupposition monad: log a condition to be checked once the
computation has ended. -/
def check (p : Presup) : M CI Presup PUnit := monadLift (Writer.tell p)

@[simp] theorem atIssue_pure (a : A) : atIssue (pure a : M CI Presup A) = a := rfl

@[simp] theorem ciLog_pure (a : A) : ciLog (pure a : M CI Presup A) = [] := rfl

@[simp] theorem presupLog_pure (a : A) : presupLog (pure a : M CI Presup A) = [] := rfl

@[simp] theorem atIssue_bind (m : M CI Presup A) (f : A → M CI Presup B) :
    atIssue (m >>= f) = atIssue (f (atIssue m)) := rfl

@[simp] theorem ciLog_bind (m : M CI Presup A) (f : A → M CI Presup B) :
    ciLog (m >>= f) = ciLog m ++ ciLog (f (atIssue m)) := rfl

@[simp] theorem presupLog_bind (m : M CI Presup A) (f : A → M CI Presup B) :
    presupLog (m >>= f) = presupLog m ++ presupLog (f (atIssue m)) := rfl

@[simp] theorem ciLog_write (p : CI) : ciLog (write p : M CI Presup PUnit) = [p] := rfl

@[simp] theorem presupLog_write (p : CI) : presupLog (write p : M CI Presup PUnit) = [] := rfl

@[simp] theorem ciLog_check (p : Presup) : ciLog (check p : M CI Presup PUnit) = [] := rfl

@[simp] theorem presupLog_check (p : Presup) : presupLog (check p : M CI Presup PUnit) = [p] :=
  rfl

/-- The at-issue value of a composition depends on the input's value alone: the continuation
never sees either log. -/
theorem atIssue_bind_congr {m m' : M CI Presup A} (f : A → M CI Presup B)
    (h : atIssue m = atIssue m') : atIssue (m >>= f) = atIssue (m' >>= f) := by
  simp only [atIssue_bind, h]

/-- The side-issue log is only extended: no item can revise an implicature already logged. -/
theorem ciLog_prefix_bind (m : M CI Presup A) (f : A → M CI Presup B) :
    ciLog m <+: ciLog (m >>= f) :=
  ⟨ciLog (f (atIssue m)), rfl⟩

/-! ### Shan's application

Glue's `⊸` elimination composes at-issue items by `A(f)(x) = f ⋆ λg. x ⋆ λy. η(g y)`, the monad's
`<*>`: the value is the application and both logs are threaded. -/

@[simp] theorem atIssue_seq (f : M CI Presup (A → B)) (x : M CI Presup A) :
    atIssue (f <*> x) = atIssue f (atIssue x) := rfl

@[simp] theorem ciLog_seq (f : M CI Presup (A → B)) (x : M CI Presup A) :
    ciLog (f <*> x) = ciLog f ++ ciLog x := rfl

@[simp] theorem presupLog_seq (f : M CI Presup (A → B)) (x : M CI Presup A) :
    presupLog (f <*> x) = presupLog f ++ presupLog x := rfl

/-! ### "John, who likes cats, likes dogs also" (20) -/

namespace Ex20

/-- John, the cats and the dogs. -/
inductive E
  | john
  | cats
  | dogs
  deriving DecidableEq, Repr

variable (like : E → E → Prop)

/-- `comma` (Table 1): `λj λl. j ⋆ λx. l ⋆ λf. write(f x) ⋆ λ_. η(x)`, the prosodic element
introducing the non-restrictive relative clause, which logs the clause's content about its
anchor and returns the anchor. -/
def comma (j : M Prop Prop E) (l : M Prop Prop (E → Prop)) : M Prop Prop E :=
  j >>= λ x => l >>= λ f => write (f x) >>= λ _ => pure x

/-- `also` (Table 1): `λv λo λs. s ⋆ λx. v ⋆ λf. o ⋆ λy. check(∃z. f z x ∧ z ≠ y) ⋆ λ_. η(f y x)`,
which logs the presupposition that the subject bears the relation to something other than the
object and returns the at-issue proposition. -/
def also (v : M Prop Prop (E → E → Prop)) (o s : M Prop Prop E) : M Prop Prop Prop :=
  s >>= λ x => v >>= λ f => o >>= λ y => check (∃ z, f z x ∧ z ≠ y) >>= λ _ => pure (f y x)

/-- The at-issue items of Table 1, η-lifted. -/
def john : M Prop Prop E := pure .john

def who : M Prop Prop ((E → Prop) → E → Prop) := pure id

def likes : M Prop Prop (E → E → Prop) := pure λ y x => like x y

def cats : M Prop Prop E := pure .cats

def dogs : M Prop Prop E := pure .dogs

/-- "who likes cats", by `⊸` elimination. -/
def whoLikesCats : M Prop Prop (E → Prop) := who <*> (likes like <*> cats)

/-- The sentence, by `⊸*` elimination. -/
def sentence : M Prop Prop Prop := also (likes like) dogs (comma john (whoLikesCats like))

/-- Figure 1, the at-issue proposition: John likes dogs. -/
theorem atIssue_sentence : atIssue (sentence like) = like .john .dogs := rfl

/-- Figure 1, the side-issue log: John likes cats. -/
theorem ciLog_sentence : ciLog (sentence like) = [like .john .cats] := rfl

/-- Figure 1, the presupposition of *also*: John likes something other than the dogs. -/
theorem presupLog_sentence :
    presupLog (sentence like) = [∃ z, like .john z ∧ z ≠ .dogs] := rfl

/-- Once both logs are exposed, the presupposition is entailed by the conventional implicature:
John likes cats, and cats are not dogs. -/
theorem presupposition_of_ci (h : ∀ q ∈ ciLog (sentence like), q) :
    ∀ p ∈ presupLog (sentence like), p := by
  rw [presupLog_sentence]
  rw [ciLog_sentence] at h
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact ⟨.cats, h _ (List.mem_singleton_self _), by decide⟩

/-- The relative clause never reaches the at-issue dimension: whatever it says, the sentence's
at-issue value is that John likes dogs. -/
theorem atIssue_sentence_congr (l l' : M Prop Prop (E → Prop)) :
    atIssue (also (likes like) dogs (comma john l)) =
      atIssue (also (likes like) dogs (comma john l')) := rfl

end Ex20

end GiorgoloAsudeh2012
