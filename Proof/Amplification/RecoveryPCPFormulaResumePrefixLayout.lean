import Proof.Amplification.RecoveryPCPFormulaResumeOutputState
import Proof.Amplification.RecoveryTseitinColdStream

/-! The cold tautology prefix and original PCP row loop share exactly the
formula append tape. All other cold-prefix scratch is disjoint and blank. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumePrefix
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowSlots (i : Fin 319) : Fin 580 := i.castAdd 261
def prefixSlots (i : Fin 262) : Fin 580 :=
  ⟨if i.val=239 then 276 else if i.val<239 then 319+i.val else 318+i.val,by
    have hi:=i.isLt; split_ifs <;> omega⟩
theorem row_injective : Function.Injective rowSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 580=>i.val) h)
theorem prefix_injective : Function.Injective prefixSlots := by
  intro i j h
  have hv:=congrArg (fun i : Fin 580=>i.val) h
  have hi:=i.isLt; have hj:=j.isLt
  apply Fin.ext
  dsimp [prefixSlots] at hv
  split_ifs at hv <;> omega
theorem prefix_outside (i : Fin 319) (hi : i.val≠276) : ∀ j,prefixSlots j≠rowSlots i := by
  intro j h
  have hv:=congrArg (fun i : Fin 580=>i.val) h
  have hj:=j.isLt; have hil:=i.isLt
  dsimp [prefixSlots,rowSlots] at hv
  split_ifs at hv <;> omega

noncomputable def prefixMachine := RecoveryFocus.machine prefixSlots RecoveryTseitinTautology.Cold.machine
noncomputable def rowsMachine := RecoveryFocus.machine rowSlots RecoveryPCPFormulaResumeRows.machine
noncomputable def machine := Composition.machine prefixMachine rowsMachine
noncomputable def heads (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) : Fin 580→Nat :=
  Fin.addCases (m:=319) (n:=261) (motive:=fun _=>Nat)
    (RecoveryPCPFormulaResumeRows.inputCfg p R Q cap logCap resetCap (2^R-1) []).heads (fun _=>0)
noncomputable def input (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) : Fin 580→List Bool :=
  install prefixSlots (Fin.addCases (m:=319) (n:=261) (motive:=fun _=>List Bool)
    (RecoveryPCPFormulaResumeRows.inputCfg p R Q cap logCap resetCap (2^R-1) []).tapes (fun _=>[]))
    (RecoveryTseitinTautology.Cold.driversInput (2^R))
def budget (cap R Q count : Nat) := RecoveryTseitinTautology.Cold.budget (2^R)+1+
  RecoveryPCPFormulaResumeRows.budget cap R Q count (2^R-1)

theorem prefix_heads (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) (i : Fin 262) :
    heads p R Q cap logCap resetCap (prefixSlots i)=0 := by
  by_cases hi : i.val=239
  · have he : i=239 := Fin.ext hi
    subst i
    exact (RecoveryPCPFormulaResumeRows.input_output p R Q cap logCap resetCap (2^R-1) []).1
  · have hlo : 319≤(prefixSlots i).val := by dsimp [prefixSlots]; split_ifs <;> omega
    let j : Fin 261 := ⟨(prefixSlots i).val-319,by have ht:=(prefixSlots i).isLt; omega⟩
    have he : prefixSlots i=j.natAdd 319 := by apply Fin.ext; dsimp [j]; omega
    rw [he]
    simp only [heads,Fin.addCases_right]

theorem input_rows (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) (i : Fin 319) :
    input p R Q cap logCap resetCap (rowSlots i)=
      (RecoveryPCPFormulaResumeRows.inputCfg p R Q cap logCap resetCap (2^R-1) []).tapes i := by
  by_cases hi : i.val=276
  · have he : i=276 := Fin.ext hi
    subst i
    change input _ _ _ _ _ _ (prefixSlots 239)=_
    rw [input,install_slot prefixSlots prefix_injective]
    exact (RecoveryPCPFormulaResumeRows.input_output p R Q cap logCap resetCap (2^R-1) []).2.symm
  · rw [input,install_other _ _ _ _ (prefix_outside i hi)]
    simp only [rowSlots,Fin.addCases_left]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumePrefix
