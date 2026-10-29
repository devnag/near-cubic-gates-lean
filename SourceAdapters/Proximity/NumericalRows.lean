import SourceAdapters.Proximity.ConstructorWidths

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": discharge every per-row numerical precondition
from explicit request caps and the source program's actual ordinary budget. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

variable {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest) budget)

include P in
theorem numerical_rows (S : SourceCircuit) (coins : Fin (2 ^ (V S).randomBits))
    (requestBound B Wd Lk Bk : ℕ)
    (hlen : RequestLengths V S coins requestBound)
    (hbud : ∀ request, (proofCallInput V request).length ≤ requestBound → budget request ≤ B)
    (hroom : requestBound ≤ Lk) (hclock : B ≤ Bk)
    (hwidth : widthDemand q (sourceCircuitWord S).length (V S).randomBits B ≤ Wd) :
    RowBounds V budget S coins Wd Lk Bk (widthMeasure q (V S).randomBits B) := by
  let Λ := widthMeasure q (V S).randomBits B
  have hparts : B + auxiliaryCap q (V S).randomBits + blockVariableBound q + 2 * q + 2 ^ q +
      (V S).randomBits + 20 = Λ := rfl
  have hpow : 0 ≤ (2 ^ q : ℕ) := Nat.zero_le _
  have hΛthree : Λ + 3 ≤ Wd := by
    change Λ + (sourceCircuitWord S).length + predicateBlockBits q + 10 ≤ Wd at hwidth
    omega
  have hΛ : Λ + 1 ≤ Wd := by omega
  have htwo : 2 ≤ Wd := by omega
  have hWlt := Nat.lt_two_pow_self (n := Wd)
  have hqueryBudget : ∀ j, budget (queryRequest V ⟨S, coins, j⟩) ≤ B := fun j => hbud _ (hlen.query j)
  have hbits : ∀ j, (addressPair ((V S).query coins j)).2.bits.length ≤ B := fun j =>
    (query_output_bits V proofLength honest budget P ⟨S, coins, j⟩).trans (hqueryBudget j)
  have hglobal : ∀ index < blockVariableBound q,
      natBitLength (addressPair (localAddress (V S) coins index)).2 ≤ Λ := by
    intro index hi
    have h := global_bitLength (V S) coins B hbits index hi
    omega
  have hblock : (proofCallInput V (blockRequest V (predicateTable (rowPredicate (V S) coins)))).length ≤
      requestBound := by
    rw [block_input]
    simpa only [List.length_append, List.length_ofFn, blockTag, List.length_cons, List.length_nil] using hlen.block
  refine ⟨htwo, hΛ, by omega, by omega, by omega, ?_, ?_, ?_, ?_,
    hlen.count.trans hroom, (hbud _ hlen.count).trans hclock,
    fun j => (hlen.query j).trans hroom, fun j => (hqueryBudget j).trans hclock,
    fun bits => (hlen.decision bits).trans hroom, fun bits => (hbud _ (hlen.decision bits)).trans hclock,
    hlen.block.trans hroom, (hbud _ hblock).trans hclock, ?_, ?_, ?_, ?_, ?_, hglobal⟩
  · have hr : coins.val.bits.length ≤ (V S).randomBits := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr coins.isLt
    omega
  · have hc := (V S).queryCount_le coins
    have hb := bits_length_le ((V S).queryCount coins)
    omega
  · intro j hj
    have hb := bits_length_le j
    omega
  · intro j
    exact (hbits j).trans (by omega)
  · intro index hi
    have hb := bits_length_le index
    omega
  · intro j _
    exact doubled_lt_power _ B Wd (padded_bits _ B hbits j) (by omega)
  · intro index hi
    have ha := auxiliary_le (V S) coins index hi
    omega
  · intro index hi
    have hg := hglobal index hi
    omega
  · intro index hi
    have hb := bits_length_le index
    omega

end NearCubicGates.Adapters.Proximity.SourceCallee
