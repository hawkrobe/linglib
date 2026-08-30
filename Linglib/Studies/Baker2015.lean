import Linglib.Syntax.Case.Dependent
import Linglib.Data.Examples.Baker2015

/-!
# Baker 2015: dependent case

Structural case cannot in general be read off agreement with a functional head: ergative
languages let the finite verb agree with ergative and absolutive subjects alike, and the
subject must already be ergative before Agree applies. The book takes up Marantz's dependent
case instead. In a spell-out domain, an NP with lexically governed case keeps it; of two
distinct caseless NPs one of which c-commands the other, the lower is valued accusative or the
higher ergative — which of these a language does is its alignment parameter, and a tripartite
language does both; whatever remains is unmarked, nominative in the clause and genitive in the
noun phrase. Sakha, Shipibo and Nez Perce show the three settings on the simplest transitive
and intransitive clauses, and the twenty-odd languages the book studies in depth sort into
those columns together with marked-nominative and marked-absolutive systems, which differ in
how the unmarked case is realized.

## Main definitions

* `alignment?`: the book's sorting of its languages by alignment type.
* `Observed`, `Realizes`: the case a gloss shows, and when the algorithm's output realizes it.
* `rows_case`: the book's introductory clauses, each derived by `assignCases` from its
  alignment type.

## References

* [baker-2015]
* [marantz-1991] — the disjunctive hierarchy and dependent case
* [baker-vinokurova-2010] — the c-command formulation
-/

namespace Baker2015

open Data.Examples Case

/-- The book's languages of focus by alignment type: accusative Sakha, Tamil, Amharic, Cuzco
    Quechua, Korean and Finnish; ergative Shipibo, Burushaski, Chukchi, Lezgian, Ingush,
    Greenlandic, Kewa and Wardaman; tripartite Nez Perce, Coast Tsimshian, Semelai, Diyari and
    Warlpiri. The marked-nominative and marked-absolutive languages differ in the realization of
    the unmarked case, which the algorithm does not fix. -/
def alignment? : String → Option Alignment.AlignmentType
  | "yaku1245" | "tami1289" | "amha1245" | "cusc1236" | "kore1280" | "finn1318" =>
    some .accusative
  | "ship1254" | "buru1296" | "chuk1273" | "lezg1247" | "ingu1240" | "kala1399" | "west2599"
  | "ward1246" => some .ergative
  | "nezp1238" | "coas1300" | "seme1247" | "dier1241" | "warl1254" => some .tripartite
  | _ => none

/-- The case a gloss shows: a dependent case, or an unmarked form — nominative, absolutive,
    or no marking at all. -/
inductive Observed
  | erg
  | acc
  | unmarked
  deriving DecidableEq, Repr

/-- The gloss labels of the book's examples. -/
def Observed.parse? : String → Option Observed
  | "ERG" => some .erg
  | "ACC" => some .acc
  | "NOM" | "ABS" | "unmarked" => some .unmarked
  | _ => none

/-- An assigned case realizes an observed one: the dependent cases as themselves, and the
    unmarked case as whatever label the language gives it. -/
def Realizes (c : Case) (src : Mechanism) : Observed → Prop
  | .erg => c = .erg ∧ src = .dependent
  | .acc => c = .acc ∧ src = .dependent
  | .unmarked => src = .unmarked

instance (c : Case) (src : Mechanism) (o : Observed) : Decidable (Realizes c src o) := by
  cases o <;> simp only [Realizes] <;> infer_instance

/-- The NPs of a row's clause, subject first: it c-commands the object. -/
def domain (r : LinguisticExample) : List NP :=
  ⟨"subject", none⟩ :: if r.feature? "transitive" = some "yes" then [⟨"object", none⟩] else []

/-- The observed case of a row's NP. -/
def observed? (r : LinguisticExample) (np : String) : Option Observed :=
  (r.feature? (np ++ "Case")).bind Observed.parse?

/-- Every clause the book introduces its languages with is derived by the algorithm from the
    language's alignment type: the ergative and accusative NPs are the dependent-case NPs and
    the nominative, absolutive and unmarked NPs the leftovers. -/
theorem rows_case :
    ∀ r ∈ Examples.all, ∀ lang ∈ alignment? r.language, ∀ np ∈ ["subject", "object"],
      ∀ o ∈ observed? r np, ∀ c ∈ getCaseOf np (assignCases lang (domain r)),
        ∀ src ∈ getMechanismOf np (assignCases lang (domain r)), Realizes c src o := by
  decide

/-- Agreement does not enter the algorithm: a subject is ergative in a transitive clause and
    unmarked in an intransitive one whether or not the verb agrees with it, as in Kewa and
    Burushaski. -/
theorem ergative_subject_independent_of_agreement :
    ∀ r ∈ Examples.all, alignment? r.language = some .ergative →
      getCaseOf "subject" (assignCases .ergative (domain r)) =
        some (if r.feature? "transitive" = some "yes" then .erg else .abs) := by
  decide

end Baker2015
