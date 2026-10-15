import Proof.PCP.PCPUnaryStackPush
import Proof.PCP.PCPPairReusable
import Proof.Amplification.RecoveryRowLookupTapes

/-! A count-stack pop restores an actual raw unary loop driver. The framed
unary field is physically decoded and reset, preserving the stack cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPUnaryStackPop
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def popProgram := TapeEmbedding.machine 2 PCPStackReady.machine
def copySlots : Fin 3 → Fin 5 := ![1,3,4]
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def copyProgram := RecoveryFocus.machine copySlots Streaming.machine
noncomputable def machine := Composition.machine popProgram copyProgram
def entry (n : ℕ) (pre : List Bool) (z : ℕ) :=
  Composition.leftConfig 5 (TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => [])
    (PCPStackReady.popInput (List.replicate n true) pre z))
def heads (pre : List Bool) : Fin 5 → ℕ := ![pre.length,0,0,0,0]
def middle (n : ℕ) (pre : List Bool) (z : ℕ) : Fin 5 → List Bool :=
  ![pre++List.replicate (2*n+1+z) false,frame (List.replicate n true),
    List.replicate (2*n+2) false,[],[]]
def output (n : ℕ) (pre : List Bool) (z : ℕ) : Fin 5 → List Bool :=
  ![pre++List.replicate (2*n+1+z) false,frame (List.replicate n true),
    List.replicate (2*n+2) false,List.replicate n true,List.replicate n false]

theorem unary_copy (n : ℕ) :
    ReadyRun Streaming.machine (4*n+2) ![frame (List.replicate n true),[],[]]
      ![frame (List.replicate n true),List.replicate n true,List.replicate n false] := by
  obtain ⟨r,hr,hf,hs,_⟩ := Streaming.copy_run (List.replicate n true)
  simp only [List.length_replicate] at hr hf hs
  refine ⟨r,?_,?_,?_,hs⟩
  · convert hr using 2
    funext i; fin_cases i <;> rfl
  · rw [hf]
    funext i; fin_cases i <;> rfl
  · intro i
    rw [hf]
    simp [Streaming.finished,Streaming.config]

theorem pop_run (n : ℕ) (pre : List Bool) (z : ℕ) :
    ∃ r,runFrom machine (8*n+9) (entry n pre z)=some r ∧
      r.final.tapes=output n pre z ∧ r.final.heads=heads pre ∧ r.steps=8*n+9 := by
  obtain ⟨base,hr,ht,hh,hs⟩ := PCPStackReady.pop_run (List.replicate n true) pre z
  simp only [List.length_replicate] at hr ht hh hs
  let first := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) base
  have hfirst := TapeEmbedding.run_embed PCPStackReady.machine
    (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) _ _ base hr
  have hft : first.final.tapes=middle n pre z := by
    funext i
    fin_cases i <;> simp [first,TapeEmbedding.receipt,TapeEmbedding.config,ht,middle] <;> rfl
  have hfh : first.final.heads=heads pre := by
    funext i
    fin_cases i <;> simp [first,TapeEmbedding.receipt,TapeEmbedding.config,hh,heads] <;> rfl
  obtain ⟨last,hl,hlh,hlt,hls⟩ := (unary_copy n).focus_at copySlots copy_injective
    (heads pre) (middle n pre z) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  have hrestart : Composition.restart first.final copyProgram.start=
      (⟨Streaming.machine.start,heads pre,middle n pre z⟩ : Configuration 5 5) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hlast : runFrom copyProgram (4*n+2) (Composition.restart first.final copyProgram.start)=some last := by
    rw [hrestart]
    exact hl
  have h := Composition.run_join popProgram copyProgram (4*n+6) (4*n+2) _ first last hfirst hlast
  have he : (4*n+6)+1+(4*n+2)=8*n+9 := by omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt first last,h,?_,hlh,?_⟩
  · change last.final.tapes=_
    rw [hlt]
    funext i
    fin_cases i
    · exact install_other copySlots _ _ _ (by decide)
    · exact install_slot copySlots copy_injective _ _ 0
    · exact install_other copySlots _ _ _ (by decide)
    · exact install_slot copySlots copy_injective _ _ 1
    · exact install_slot copySlots copy_injective _ _ 2
  · change first.steps+1+last.steps=8*n+9
    change base.steps+1+last.steps=8*n+9
    rw [hs,hls]
    omega

end NearCubicWires.RepairOrdinary.PCPUnaryStackPop
