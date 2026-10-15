import Proof.CaseAnalysis.WitnessHeaderSwitch
import Proof.MachineModel.Runs

/-! A scanned native flag selects one actual template worker. Both paid
control transitions use the original call/stop interpreter. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSwitch
open LocalBitMultitape ExtDecompositionBatch CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stop (t : ℕ) : Machine t 1:=⟨0,0,fun _=>true,fun _ _=>none⟩
noncomputable def machine {t a b : ℕ} (p : Machine t a) (q : Machine t b) (slot : Fin t):=
  HeaderSwitch.machine (stop t) p q (fun _=>true) (fun cells=>cells slot)

theorem selected {t a b : ℕ} (p : Machine t a) (q : Machine t b) (slot : Fin t)
    (j : Fin 3) (hj : j=1 ∨ j=2) (fuel : ℕ) (H : Fin t→ℕ) (A : Fin t→List Bool)
    (r : ExecutionReceipt t (HeaderSwitch.sizes 1 a b j))
    (hr : runFrom (HeaderSwitch.programs (stop t) p q j) fuel
      ⟨(HeaderSwitch.programs (stop t) p q j).start,H,A⟩=some r)
    (hb : j=if readTapeBit (A slot) (H slot) then 1 else 2) :
    Step (machine p q slot) (fuel+2) H A r.final.heads r.final.tapes := by
  let cfg : Configuration t 1:=⟨0,H,A⟩
  let prior : ExecutionReceipt t 1:=⟨cfg,0,cfg.tapeCells⟩
  have hp : runFrom (stop t) 0 ⟨(stop t).start,H,A⟩=some prior:=rfl
  obtain ⟨actual,ha,_,hh,ht⟩:=HeaderSwitch.accepted (stop t) p q (fun _=>true)
    (fun cells=>cells slot) j hj 0 fuel H A prior r hp hr rfl hb
  have time : 0+1+fuel+1=fuel+2:=by omega
  rw [time] at ha
  exact Step.of_run ha hh ht

theorem true_run {t a b fuel : ℕ} (p : Machine t a) (q : Machine t b) (slot : Fin t)
    {H H' : Fin t→ℕ} {A A' : Fin t→List Bool} (h : Step p fuel H A H' A')
    (hb : readTapeBit (A slot) (H slot)=true) : Step (machine p q slot) (fuel+2) H A H' A' := by
  obtain ⟨r,hr,rh,rt,_⟩:=h
  exact (selected p q slot 1 (Or.inl rfl) fuel H A r hr (by rw [hb];rfl)).congr rh rt

theorem false_run {t a b fuel : ℕ} (p : Machine t a) (q : Machine t b) (slot : Fin t)
    {H H' : Fin t→ℕ} {A A' : Fin t→List Bool} (h : Step q fuel H A H' A')
    (hb : readTapeBit (A slot) (H slot)=false) : Step (machine p q slot) (fuel+2) H A H' A' := by
  obtain ⟨r,hr,rh,rt,_⟩:=h
  exact (selected p q slot 2 (Or.inr rfl) fuel H A r hr (by rw [hb];rfl)).congr rh rt

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSwitch
