import Proof.CaseAnalysis.RowsFamilyLoop

/-! The complete executed outer loop uses the same strict paper load as
the signed cuts. This bounds the actual driver and loop, not an assumed
original-source packet generator or the narrower internal-syntax Tprep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsFamilyBudget
open CloseoutRowsSourceDigits CloseoutRowsSourceLoad CloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_eq (N Q C : ℕ) :
    CloseoutRowsFamilyLoop.budget N Q C=N*oneCost Q C+N+3 := by
  unfold CloseoutRowsFamilyLoop.budget CloseoutRowsPacketOptional.cost oneCost
  ring

theorem bank_bound (S R K s N : ℕ) (hQ : K+1 ≤ S) (hload : K+R ≤ s) (hN : N ≤ 2^K) :
    CloseoutRowsCapacityDriver.budget S R+
        CloseoutRowsFamilyLoop.budget N (K+1) (4096*S^4*2^R)  ≤ 
      4000000*2^s*(S+1)^5*(R+1) := by
  have hb:=CloseoutRowsSourceLoad.bank_bound S R K s hQ hload
  have hm:=Nat.mul_le_mul_right (oneCost (K+1) (4096*S^4*2^R)) hN
  have hpow : 2^K ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)
  have hS : 1 ≤ (S+1)^5 := Nat.one_le_pow 5 (S+1) (by omega)
  have hp : 1 ≤ 2^s := Nat.one_le_two_pow
  have htail : 2^s ≤ 2^s*(S+1)^5*(R+1) := by
    calc
      _ = 2^s*1*1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hS) (by omega)
  rw [budget_eq]
  nlinarith

theorem source_bank_bound {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2)))
    (K s S : ℕ) (hQ : K+1 ≤ S) (hbank : ps.length ≤ 2^K)
    (hload : 200*load K (degree ps) B ≤ s) :
    CloseoutRowsCapacityDriver.budget S (width ps*(K+2))+
        CloseoutRowsFamilyLoop.budget (bank ps).length (K+1)
          (4096*S^4*2^(width ps*(K+2)))  ≤ 
      4000000*2^s*(S+1)^5*(width ps*(K+2)+1) := by
  apply bank_bound S _ K s _ hQ
  · have h:=digit_margin ps K s hload
    omega
  · simpa only [bank,List.length_map] using hbank

theorem packet_length {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w : ℕ) (rows : List (List Bool))
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length ≤ 2^w)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C:=capacity n p F w gs.length Q
    (CloseoutRowsPacketOptional.packet gs p F Q w C rows).length ≤ 110*(2*C+1)+1 := by
  dsimp only
  by_cases he : rows=[]
  · simp [CloseoutRowsPacketOptional.packet,he]
  · have hb:=CloseoutRowsPacketIndependent.packet_length (capacity n p F w gs.length Q)
      (CloseoutRowsPacketPolynomial.data gs p F Q w (capacity n p F w gs.length Q) rows [])
      (CloseoutRowsPacketPolynomial.data_bound gs p F Q w rows [] hl hw hF)
    simpa only [CloseoutRowsPacketOptional.packet,he,↓reduceIte,List.length_cons] using Nat.add_le_add_right hb 1

theorem stream_length {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w : ℕ) (bank : List (List (List Bool)))
    (hl : ∀ rows∈bank,∀ row∈rows,row.length=gs.length)
    (hw : ∀ rows∈bank,rows.length ≤ 2^w)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C:=capacity n p F w gs.length Q
    (CloseoutRowsFamilyLoop.stream gs p F Q w C bank).length ≤ bank.length*(110*(2*C+1)+1) := by
  dsimp only
  induction bank with
  | nil => simp [CloseoutRowsFamilyLoop.stream]
  | cons rows bank ih =>
    have hb:=packet_length gs p F Q w rows (hl rows (by simp)) (hw rows (by simp)) hF
    have ht:=ih (fun rs hrs=>hl rs (by simp [hrs])) (fun rs hrs=>hw rs (by simp [hrs]))
    simp only [CloseoutRowsFamilyLoop.stream,List.flatMap_cons,List.length_append,List.length_cons] at *
    nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsFamilyBudget
