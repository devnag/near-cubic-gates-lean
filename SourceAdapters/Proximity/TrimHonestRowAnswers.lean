import SourceAdapters.Proximity.TrimHonestQueryProgram

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the concrete answer program agrees with the padded
source verifier's exact input to its finite canonical block constructor. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def rowPairs {n q : ℕ} (V : NonadaptiveVerifier n q) (coins : Fin (2 ^ V.randomBits)) :
    List (Bool × ℕ) :=
  (List.range q).map (QueryStep.paddedAddress (fun i => SourceCallee.addressPair (V.query coins i)))

def rowAnswers {n q N : ℕ} (V : NonadaptiveVerifier n q) (coins : Fin (2 ^ V.randomBits))
    (input : BitInput n) (proof : BitInput N) : BitInput q :=
  fun j => oracleValue input (finiteProofOracle proof) ((padQueries V).query coins j)

theorem row_pair_fields {n q : ℕ} (V : NonadaptiveVerifier n q) (coins : Fin (2 ^ V.randomBits)) :
    (rowPairs V coins).flatMap pairFields =
      QueryRows.rowFields (fun i => SourceCallee.addressPair (V.query coins i)) q := by
  simp [rowPairs, pairFields, QueryRows.rowFields, List.flatMap_map]

theorem row_answer_words {n q N : ℕ} (V : NonadaptiveVerifier n q) (coins : Fin (2 ^ V.randomBits))
    (input : BitInput n) (proof : BitInput N) :
    answerWords input proof (rowPairs V coins) = (List.ofFn (rowAnswers V coins input proof)).map Bool.toNat := by
  apply List.ext_getElem
  · simp [answerWords, rowPairs]
  · intro i hi hj
    have hi' : i < q := by simpa [answerWords, rowPairs] using hi
    simp only [answerWords, rowPairs, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [SourceCallee.padded_address V coins ⟨i, hi'⟩, answer_value_address]
    rfl

theorem row_answers {C : Ctx} {n q N : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (input : BitInput n) (proof : BitInput N)
    (a : DS VV MM) (hc : Cst a) (ready : OracleReady C input proof a)
    (hq : a.ram queryStore = QueryRows.rowFields (fun i => SourceCallee.addressPair (V.query coins i)) q)
    (hlen : a.env QueryStep.boundReg = q) (hold : (a.ram answerStore).length ≤ q)
    (hwidth : q < 2 ^ C.Wd) :
    Hs C answerProgram a (a.rc queryStore + a.rc answerStore + (6 * (n + N) + 21) * q + 8)
      (fun b => b.ram answerStore = (List.ofFn (rowAnswers V coins input proof)).map Bool.toNat ∧
        b.rc answerStore = q ∧ b.rc queryStore = 2 * q ∧
        OracleReady C input proof b ∧ QueryFrame answerLoopTemps a b) := by
  have run := answer_program input proof (rowPairs V coins) a hc ready
    (by rw [row_pair_fields]; exact hq) (by simpa [rowPairs] using hlen)
    (by simpa [rowPairs] using hold) (by simpa [rowPairs] using hwidth)
  have hp : (rowPairs V coins).length = q := by simp [rowPairs]
  simpa only [hp, row_answer_words V coins input proof] using run

end NearCubicGates.Adapters.Proximity.TrimHonest
