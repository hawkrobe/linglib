import Linglib.Syntax.ConstructionGrammar.Basic

/-!
# Construction Grammar: Licensing

The licensing model of constructional grammar ([sag-2012]; [goldberg-1995]):
an utterance token is grammatical iff every constituent in it instantiates
some construction of the network. `Constructicon.licenses` is the
recognizer — a constituent's daughters must match some construction's
typed form slot-by-slot (`formMatches`), and each daughter must itself be
licensed; words are licensed lexically.

Matching is relative to a POS lexicon `String → Option UD.UPOS`. `headed`
fillers are checked against immediate daughters (a flat approximation of
headedness), and `semantic` constraints are not checkable at this level
and match any token.

## Main declarations

- `Token`: utterance tokens (words and constituents)
- `SlotFiller.matches`, `formMatches`: slot/daughter matching
- `Constructicon.Licenses`: the licensing relation, via the recognizer
-/

namespace ConstructionGrammar

/-- An utterance token: a word or a constituent with daughter tokens. -/
inductive Token where
  | word : String → Token
  | node : List Token → Token

mutual

/-- Boolean equality on tokens (hand-rolled: `Token` is a nested
inductive, outside the deriving handlers' fragment). -/
def Token.beq : Token → Token → Bool
  | .word a, .word b => a == b
  | .node as, .node bs => Token.beqList as bs
  | _, _ => false

/-- Boolean equality on token lists. -/
def Token.beqList : List Token → List Token → Bool
  | [], [] => true
  | a :: as, b :: bs => Token.beq a b && Token.beqList as bs
  | _, _ => false

end

instance : BEq Token := ⟨Token.beq⟩

/-- Does a token satisfy a slot filler, relative to a POS lexicon?
`semantic` constraints are not checkable at this level and match any
token; `headed` requires the head word as an immediate daughter. -/
def SlotFiller.matches (pos : String → Option UD.UPOS) :
    SlotFiller String → Token → Bool
  | .fixed w, .word w' => w == w'
  | .open_ cat, .word w => pos w == some cat
  | .phrasal, .node _ => true
  | .headed h _, .node ts => ts.contains (.word h)
  | .semantic _, _ => true
  | _, _ => false

/-- A daughter sequence instantiates a typed form: same arity, and each
daughter matches its slot's filler. -/
def formMatches (pos : String → Option UD.UPOS)
    (form : TypedForm String) (ts : List Token) : Bool :=
  form.length == ts.length &&
  (form.zip ts).all (λ ⟨s, t⟩ => s.filler.matches pos t)

mutual

/-- The licensing recognizer: words are licensed lexically; a constituent
is licensed iff its daughters instantiate some construction of the network
and are each licensed themselves. -/
def Constructicon.licenses (cx : Constructicon)
    (pos : String → Option UD.UPOS) : Token → Bool
  | .word _ => true
  | .node ts =>
      cx.constructions.any (λ c => formMatches pos c.form ts) &&
      cx.licensesList pos ts

/-- All tokens in a list are licensed. -/
def Constructicon.licensesList (cx : Constructicon)
    (pos : String → Option UD.UPOS) : List Token → Bool
  | [] => true
  | t :: ts => cx.licenses pos t && cx.licensesList pos ts

end

/-- `cx` licenses token `t` (relative to a POS lexicon): every constituent
instantiates some construction of the network. Defined via the
`licenses` recognizer, so concrete cases are kernel-decidable. -/
def Constructicon.Licenses (cx : Constructicon)
    (pos : String → Option UD.UPOS) (t : Token) : Prop :=
  cx.licenses pos t = true

instance (cx : Constructicon) (pos : String → Option UD.UPOS) (t : Token) :
    Decidable (cx.Licenses pos t) :=
  inferInstanceAs (Decidable (_ = true))

end ConstructionGrammar
