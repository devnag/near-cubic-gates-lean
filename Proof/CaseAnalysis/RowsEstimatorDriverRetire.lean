import Proof.CaseAnalysis.RowsEstimatorDriverCleanBank

/-! Retire both physical D words with the original sweep and halted rewind.
The first D word becomes the rewind log; no third counter is constructed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverRetire
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 1 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def last:=Rewind.machine idle
def machine:=Composition.machine (RecoveryScratchErase.machine 1) last

theorem ready (D : ℕ) : ReadyRun machine (2*D+4)
    (fun _ : Fin 2=>List.replicate D true) (fun _ : Fin 2=>List.replicate D false) := by
  let backing:=fun _ : Fin 1=>List.replicate D true
  obtain ⟨x,hx,xf,xs⟩:=(RecoveryScratchErase.sweep_prefix D 0 backing).run (by rfl)
  let c : Configuration 1 1:=⟨0,fun _=>D,fun _=>List.replicate D false⟩
  obtain ⟨y,hy,yf,ys,_⟩:=Rewind.halted_run idle c D (by intro i;rfl) (by rfl)
  have he : Composition.restart x.final last.start=Rewind.recording c D := by
    rw [xf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Fin.addCases,RecoveryScratchErase.config,Rewind.recording,Rewind.config,c,Composition.restart]
    · funext i
      fin_cases i <;> simp [Fin.addCases,RecoveryScratchErase.config,RecoveryScratchErase.tapes,
        StablePartition.Workspace.overlay,Rewind.recording,Rewind.config,c,Composition.restart,backing]
  rw [←he] at hy
  have hr:=Composition.run_join (RecoveryScratchErase.machine 1) last _ _ _ x y hx hy
  have hi : Composition.leftConfig 3 (RecoveryScratchErase.config 0 (0+D) 0 backing)=
      initialConfiguration machine (fun _ : Fin 2=>List.replicate D true) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.leftConfig,RecoveryScratchErase.config,initialConfiguration]
    · funext i
      fin_cases i <;> simp [Fin.addCases,Composition.leftConfig,RecoveryScratchErase.config,RecoveryScratchErase.tapes,
        StablePartition.Workspace.overlay,initialConfiguration,backing]
  rw [hi] at hr
  have ht : D+1+1+(D+2)=2*D+4:=by omega
  rw [ht] at hr
  refine ⟨Composition.joinedReceipt x y,hr,?_,?_,?_⟩
  · change y.final.tapes=_
    rw [yf]
    funext i
    fin_cases i <;> simp [Fin.addCases,Rewind.finished,Rewind.config,c]
  · intro i
    change y.final.heads i=0
    rw [yf]
    fin_cases i <;> simp [Fin.addCases,Rewind.finished,Rewind.config]
  · change x.steps+1+y.steps=2*D+4
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverRetire
