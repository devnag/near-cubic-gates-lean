import Proof.MachineModel.OrdinaryMatrixScoreHalvesReset
import Proof.MachineModel.OrdinaryMatrixScoreRightEnumeration

/-! Actual left U-record pass, two paid resets, and right U-record pass.
The extra retained d-bit zero word is an explicit local caller obligation. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBothHalves
open LocalBitMultitape SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C State)
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def left := TapeEmbedding.machine 1 MatrixScoreLeftEnumeration.machine
noncomputable def right := TapeEmbedding.machine 1 MatrixScoreRightEnumeration.machine
noncomputable def prefixMachine := Composition.machine left MatrixScoreHalvesReset.machine
noncomputable def machine := Composition.machine prefixMachine right

def records (r : Request) (gate : Fin r.Gates) :=
  MatrixScoreLeftLoop.records r gate 0 r.U++MatrixScoreRightLoop.records r gate 0 r.U
def budget (r : Request) := (MatrixScoreLeftEnumeration.budget r+1+MatrixScoreHalvesReset.budget r.width r.M r.d (C r))+1+
  MatrixScoreRightEnumeration.budget r
noncomputable def initial (r : Request) (gate : Fin r.Gates) (state : State r) (cap : ℕ)
    (driver counter out : List Bool) :=
  let localInput := MatrixScoreLeftEnumeration.initial r gate state cap driver counter out
  RecoveryCalls.restarted machine
    (Fin.addCases (m := 29) (n := 1) (motive := fun _ => ℕ)
      (MatrixScoreLeftEnumeration.heads localInput.heads 1) (fun _ => 0))
    (Fin.addCases (m := 29) (n := 1) (motive := fun _ => List Bool)
      (MatrixScoreLeftEnumeration.tapes localInput.tapes r.U) (fun _ => frame (binary r.width 0)))

theorem both_run (r : Request) (gate : Fin r.Gates) (state : State r) (cap : ℕ) (driver counter out : List Bool)
    (hcap : cap≤C r+1) (hd : driver.length≤C r) (hc : counter.length≤C r) :
    ∃ final : State r,∃ actual,runFrom machine (budget r) (initial r gate state cap driver counter out)=some actual ∧
      actual.final.heads=MatrixScoreHalvesReset.heads (out++records r gate).length ∧
      actual.final.tapes=MatrixScoreHalvesReset.tapes (cutWord r.p (r.cuts.get gate)) r.width (r.phi (r.U-1))
        (C r) (r.S+1) (2^r.S) r.M (r.U+(r.U-1)) r.U r.U final.returnCap final.work
        (ZeroPadding.pad (C r) [true,true]) (zeros (C r)) (out++records r gate) r.cols ∧ actual.steps≤budget r := by
  obtain ⟨mid,lb,hl,lf,ls⟩ := MatrixScoreLeftEnumeration.enumeration_run r gate state cap driver counter out hcap hd hc
  have hleft := TapeEmbedding.run_embed MatrixScoreLeftEnumeration.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => frame (binary r.width 0)) _ _ lb hl
  let le := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => frame (binary r.width 0)) lb
  let middle := out++MatrixScoreLeftLoop.records r gate 0 r.U
  have hM := common_width r
  have hcm : 4*r.M+2≤C r := by unfold C; omega
  have hwl := r.widthLe
  have hcl : r.cols.length ≤ r.M := by rw [cols_length,hM]; omega
  have hc : r.width+r.cols.length+2 ≤ C r := by rw [cols_length]; unfold C; omega
  obtain ⟨reset,hr,rh,rt,rs⟩ := MatrixScoreHalvesReset.reset_run (cutWord r.p (r.cuts.get gate))
    r.width (r.phi (r.U-1)) (C r) (r.S+1) (2^r.S) r.M (r.U-1) r.U r.U mid.returnCap mid.work
    (ZeroPadding.pad (C r) [true,true]) (zeros (C r)) middle r.cols hcm (phi_lt r _) hcl (cols_fit r) hc
  rw [cols_length] at hr rs
  have hiReset : Composition.restart le.final MatrixScoreHalvesReset.machine.start=
      RecoveryCalls.restarted MatrixScoreHalvesReset.machine (MatrixScoreHalvesReset.heads middle.length)
        (MatrixScoreHalvesReset.tapes (cutWord r.p (r.cuts.get gate)) r.width (r.phi (r.U-1)) (C r) (r.S+1) (2^r.S)
          r.M (r.U-1) r.U r.U mid.returnCap mid.work (ZeroPadding.pad (C r) [true,true]) (zeros (C r)) middle
          r.cols) := by
    apply configuration_ext
    · rfl
    · change le.final.heads=_
      change (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => frame (binary r.width 0)) lb.final).heads=_
      rw [lf]
      change (Fin.addCases (m := 29) (n := 1) (motive := fun _ => ℕ) _ (fun _ : Fin 1 => 0) : Fin 30 → ℕ)=_
      simp only [Composition.rightConfig]
      rw [MatrixScoreLeftEnumeration.cfg_heads]
      rfl
    · change le.final.tapes=_
      change (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => frame (binary r.width 0)) lb.final).tapes=_
      rw [lf]
      change (Fin.addCases (m := 29) (n := 1) (motive := fun _ => List Bool) _ (fun _ : Fin 1 => frame (binary r.width 0)) : Fin 30 → List Bool)=_
      simp only [Composition.rightConfig]
      rw [MatrixScoreLeftEnumeration.cfg_tapes]
      rfl
  rw [← hiReset] at hr
  have hpref := Composition.run_join left MatrixScoreHalvesReset.machine _ _ _ le reset hleft hr
  obtain ⟨final,rb,hright,rf,rbs⟩ := MatrixScoreRightEnumeration.enumeration_run r gate mid middle
  have hexpand := TapeEmbedding.run_embed MatrixScoreRightEnumeration.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => frame (binary r.width 0)) _ _ rb hright
  let re := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => frame (binary r.width 0)) rb
  have hiRight : Composition.restart (Composition.joinedReceipt le reset).final right.start=
      TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => frame (binary r.width 0))
        (RecoveryCalls.restarted MatrixScoreRightEnumeration.machine
          (MatrixScoreLeftEnumeration.heads (MatrixScoreRightEnumeration.initial r gate mid middle).heads 1)
          (MatrixScoreLeftEnumeration.tapes (MatrixScoreRightEnumeration.initial r gate mid middle).tapes r.U)) := by
    apply configuration_ext
    · rfl
    · change reset.final.heads=_
      rw [rh]
      rfl
    · change reset.final.tapes=_
      rw [rt]
      have hz : MatrixScorePhi.value r.cols r.U=r.phi 0 := by
        have h := phi_right r 0
        rw [Nat.add_zero] at h
        exact h
      simp only [MatrixScoreRightEnumeration.initial,MatrixScoreRightLoop.data,RecoveryCalls.restarted,Nat.add_zero,hz]
      rfl
  rw [← hiRight] at hexpand
  have joined := Composition.run_join prefixMachine right _ _ _ (Composition.joinedReceipt le reset) re hpref hexpand
  refine ⟨final,Composition.joinedReceipt (Composition.joinedReceipt le reset) re,joined,?_,?_,?_⟩
  · change re.final.heads=_
    change (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => frame (binary r.width 0)) rb.final).heads=_
    rw [rf]
    change (Fin.addCases (m := 29) (n := 1) (motive := fun _ => ℕ) _ (fun _ : Fin 1 => 0) : Fin 30 → ℕ)=_
    simp only [Composition.rightConfig]
    rw [MatrixScoreRightEnumeration.cfg_heads]
    simp only [MatrixScoreRightLoop.data,RecoveryCalls.restarted,records,middle,List.append_assoc]
    rfl
  · change re.final.tapes=_
    change (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => frame (binary r.width 0)) rb.final).tapes=_
    rw [rf]
    change (Fin.addCases (m := 29) (n := 1) (motive := fun _ => List Bool) _ (fun _ : Fin 1 => frame (binary r.width 0)) : Fin 30 → List Bool)=_
    simp only [Composition.rightConfig]
    rw [MatrixScoreRightEnumeration.cfg_tapes]
    simp only [MatrixScoreRightLoop.data,RecoveryCalls.restarted,records,middle,List.append_assoc]
    rfl
  · change (lb.steps+1+reset.steps)+1+rb.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreBothHalves
