import Proof.SourceAssembly.SourcePoolCount
import Proof.SourceAssembly.SourceIndexExact

/- Concrete physical join: paid pool/decomposition, bounded rewind using its
retained capacity driver, exact native index frame in six new reusable ports. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyPoolIndex
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PoolColdSource
noncomputable section
attribute [local irreducible] PoolCold.machine Cold.machine SourceAssemblyIndexExact.framed

def coldPorts (a : DecompositionAlgorithm) : Fin 5→Fin (Cold.tapes a) :=
  ![Cold.port a (str a),Cold.port a (cnt a),SourceAssemblyCountDriver.port a,
    Cold.port a (drv a),Cold.port a (wsp a)]

theorem coldPorts_val (a : DecompositionAlgorithm) (i : Fin 5) :
    (coldPorts a i).val=SB a+(![0,1,13,8,9] : Fin 5→Nat) i := by
  fin_cases i <;> rfl

theorem coldPorts_injective (a : DecompositionAlgorithm) : Function.Injective (coldPorts a) := by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [coldPorts_val,coldPorts_val] at hv
  fin_cases i <;> fin_cases j <;> simp at hv ⊢

abbrev baseTapes (a : DecompositionAlgorithm) := 132+Cold.tapes a
def old (a : DecompositionAlgorithm) (i : Fin 5) : Fin (baseTapes a) :=
  PoolCold.slots a (coldPorts a i)
theorem old_injective (a : DecompositionAlgorithm) : Function.Injective (old a) :=
  (PoolCold.slots_injective a).comp (coldPorts_injective a)

def slots (a : DecompositionAlgorithm) : Fin 11→Fin (baseTapes a+6) :=
  fun i=>Fin.addCases (m:=5) (n:=6) (motive:=fun _=>Fin (baseTapes a+6))
    (fun i : Fin 5=>(old a i).castAdd 6) (fun i : Fin 6=>i.natAdd (baseTapes a)) i

theorem slots_injective (a : DecompositionAlgorithm) : Function.Injective (slots a) := by
  intro i j
  refine Fin.addCases (m:=5) (n:=6) (fun x=>?_) (fun x=>?_) i
  · refine Fin.addCases (m:=5) (n:=6) (fun y=>?_) (fun y=>?_) j
    · intro h
      simp only [slots,Fin.addCases_left] at h
      have he : old a x=old a y := by apply Fin.ext;exact congrArg (fun z : Fin (baseTapes a+6)=>z.val) h
      exact congrArg (fun z : Fin 5=>z.castAdd 6) (old_injective a he)
    · intro h
      simp only [slots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg Fin.val h
      change (old a x).val=baseTapes a+y.val at hv
      have hx:=(old a x).isLt
      omega
  · refine Fin.addCases (m:=5) (n:=6) (fun y=>?_) (fun y=>?_) j
    · intro h
      simp only [slots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg Fin.val h
      change baseTapes a+x.val=(old a y).val at hv
      have hy:=(old a y).isLt
      omega
    · intro h
      simp only [slots,Fin.addCases_right] at h
      apply Fin.ext
      have hv:=congrArg Fin.val h
      change baseTapes a+x.val=baseTapes a+y.val at hv
      simp only [Fin.val_natAdd]
      omega

def resetPorts (a : DecompositionAlgorithm) (i : Fin 5) := slots a (i.castAdd 6)
def indexMap : Fin 9→Fin 11 := ![0,5,6,1,2,7,8,9,10]
def indexPorts (a : DecompositionAlgorithm) (i : Fin 9) := slots a (indexMap i)
theorem reset_injective (a : DecompositionAlgorithm) : Function.Injective (resetPorts a) := by
  intro i j h
  have he:=slots_injective a h
  apply Fin.ext
  exact congrArg (fun z : Fin 11=>z.val) he
theorem index_injective (a : DecompositionAlgorithm) : Function.Injective (indexPorts a) :=
  (slots_injective a).comp (by decide : Function.Injective indexMap)

def reset (a : DecompositionAlgorithm) := RecoveryFocus.machine (resetPorts a)
  (SourceAssemblyClear.rewind 3)
def frameIndex (a : DecompositionAlgorithm) := RecoveryFocus.machine (indexPorts a)
  SourceAssemblyIndexExact.framed
def first (a : DecompositionAlgorithm) := TapeEmbedding.machine 6 (PoolCold.machine a)
def machine (a : DecompositionAlgorithm) := Composition.machine (Composition.machine (first a) (reset a)) (frameIndex a)

end
end SourceAssemblyPoolIndex
