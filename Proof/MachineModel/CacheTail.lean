import Proof.MachineModel.CacheRewind

/-! One paid body rewind, one Records call for the whole ordered child family,
and one paid cache rewind. No second occurrence loop is used. -/
namespace NearCubicWires.ExtDecompositionBatch.CacheTail
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound RepairOrdinary.DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodySlots : Fin 3 → Fin 7:=![0,5,6]
def cacheSlots : Fin 3 → Fin 7:=![2,5,6]
theorem body_injective : Function.Injective bodySlots:=by
  intro i j h;fin_cases i <;> fin_cases j <;> simp_all [bodySlots]
theorem cache_injective : Function.Injective cacheSlots:=by
  intro i j h;fin_cases i <;> fin_cases j <;> simp_all [cacheSlots]
noncomputable def bodyMachine:=RecoveryFocus.machine bodySlots CompetitorRecordRewind.machine
noncomputable def cacheMachine:=RecoveryFocus.machine cacheSlots CompetitorRecordRewind.machine
noncomputable def recordsMachine:=TapeEmbedding.machine 2 Records.machine
noncomputable def machine:=Composition.machine (Composition.machine bodyMachine recordsMachine) cacheMachine

def inputHeads {q:ℕ} (gs:List (ExactThresholdGate q)) : Fin 7 → ℕ:=
  ![(gs.flatMap exactWord).length,0,(natWord gs.length).length,1,1,0,0]
def readyHeads {q:ℕ} (gs:List (ExactThresholdGate q)) : Fin 7 → ℕ:=
  ![0,0,(natWord gs.length).length,1,1,0,0]
def writtenHeads {q:ℕ} (gs:List (ExactThresholdGate q)) : Fin 7 → ℕ:=
  ![(gs.flatMap exactWord).length,0,(exactListWord gs).length,1,1,0,0]
def outputHeads {q:ℕ} (gs:List (ExactThresholdGate q)) : Fin 7 → ℕ:=
  ![(gs.flatMap exactWord).length,0,0,1,1,0,0]
def input {q:ℕ} (C:ℕ) (gs:List (ExactThresholdGate q)) (backing:List Bool) : Fin 7 → List Bool:=
  ![gs.flatMap exactWord,backing,natWord gs.length,UnaryTemplate.tape q,UnaryTemplate.tape gs.length,
    List.replicate C true,List.replicate (C+1) false]
def output {q:ℕ} (C:ℕ) (gs:List (ExactThresholdGate q)) (backing:List Bool) : Fin 7 → List Bool:=
  ![gs.flatMap exactWord,Records.savedList gs backing,exactListWord gs,
    UnaryTemplate.tape q,UnaryTemplate.tape gs.length,List.replicate C true,List.replicate (C+1) false]

theorem body_run {q:ℕ} (C:ℕ) (gs:List (ExactThresholdGate q)) (backing:List Bool)
    (hc:(gs.flatMap exactWord).length≤C) :
    Step bodyMachine (2*C+2) (inputHeads gs) (input C gs backing) (readyHeads gs) (input C gs backing) := by
  have run:=CacheRewind.rewind_dock bodySlots body_injective (inputHeads gs) (input C gs backing) C hc rfl rfl rfl rfl
  apply run.congr _ rfl
  funext i;fin_cases i
  · exact dockH_slot bodySlots body_injective _ _ 0
  · exact dockH_other bodySlots _ _ 1 (by intro j;fin_cases j <;> decide)
  · exact dockH_other bodySlots _ _ 2 (by intro j;fin_cases j <;> decide)
  · exact dockH_other bodySlots _ _ 3 (by intro j;fin_cases j <;> decide)
  · exact dockH_other bodySlots _ _ 4 (by intro j;fin_cases j <;> decide)
  · exact dockH_slot bodySlots body_injective _ _ 1
  · exact dockH_slot bodySlots body_injective _ _ 2

theorem records_run {q:ℕ} (C:ℕ) (gs:List (ExactThresholdGate q)) (backing:List Bool) :
    Step recordsMachine ((gs.flatMap exactWord).length+(6*q+10)*gs.length+3)
      (readyHeads gs) (input C gs backing) (writtenHeads gs) (output C gs backing) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=Records.padded_run gs [] [] backing (natWord gs.length)
  simp only [List.length_nil,List.nil_append,List.append_nil,Nat.zero_add] at hr ht hh
  have core:Step Records.machine ((gs.flatMap exactWord).length+(6*q+10)*gs.length+3)
      ![0,0,(natWord gs.length).length,1,1]
      ![gs.flatMap exactWord,backing,natWord gs.length,UnaryTemplate.tape q,UnaryTemplate.tape gs.length]
      ![(gs.flatMap exactWord).length,0,(exactListWord gs).length,1,1]
      ![gs.flatMap exactWord,Records.savedList gs backing,exactListWord gs,
        UnaryTemplate.tape q,UnaryTemplate.tape gs.length]:=⟨r,hr,hh,ht,hs.le⟩
  have run:=core.embed ![0,0] ![List.replicate C true,List.replicate (C+1) false]
  have hi:(fun i=>Fin.addCases ![0,0,(natWord gs.length).length,1,1] ![0,0] i)=readyHeads gs:=by
    funext i;fin_cases i <;> rfl
  have ia:(fun i=>Fin.addCases ![gs.flatMap exactWord,backing,natWord gs.length,UnaryTemplate.tape q,UnaryTemplate.tape gs.length]
      ![List.replicate C true,List.replicate (C+1) false] i)=input C gs backing:=by
    funext i;fin_cases i <;> rfl
  have start:=run.congr_in hi ia
  apply start.congr
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

theorem cache_run {q:ℕ} (C:ℕ) (gs:List (ExactThresholdGate q)) (backing:List Bool)
    (hc:(exactListWord gs).length≤C) :
    Step cacheMachine (2*C+2) (writtenHeads gs) (output C gs backing) (outputHeads gs) (output C gs backing) := by
  have run:=CacheRewind.rewind_dock cacheSlots cache_injective (writtenHeads gs) (output C gs backing) C hc rfl rfl rfl rfl
  apply run.congr _ rfl
  funext i;fin_cases i
  · exact dockH_other cacheSlots _ _ 0 (by intro j;fin_cases j <;> decide)
  · exact dockH_other cacheSlots _ _ 1 (by intro j;fin_cases j <;> decide)
  · exact dockH_slot cacheSlots cache_injective _ _ 0
  · exact dockH_other cacheSlots _ _ 3 (by intro j;fin_cases j <;> decide)
  · exact dockH_other cacheSlots _ _ 4 (by intro j;fin_cases j <;> decide)
  · exact dockH_slot cacheSlots cache_injective _ _ 1
  · exact dockH_slot cacheSlots cache_injective _ _ 2

theorem tail_run {q:ℕ} (C:ℕ) (gs:List (ExactThresholdGate q)) (backing:List Bool)
    (hb:(gs.flatMap exactWord).length≤C) (hc:(exactListWord gs).length≤C) :
    Step machine ((gs.flatMap exactWord).length+(6*q+10)*gs.length+4*C+9)
      (inputHeads gs) (input C gs backing) (outputHeads gs) (output C gs backing) := by
  have run:=((body_run C gs backing hb).seq (records_run C gs backing)).seq (cache_run C gs backing hc)
  have time:2*C+2+1+((gs.flatMap exactWord).length+(6*q+10)*gs.length+3)+1+(2*C+2)=
      (gs.flatMap exactWord).length+(6*q+10)*gs.length+4*C+9:=by omega
  rw [time] at run
  exact run

end NearCubicWires.ExtDecompositionBatch.CacheTail
