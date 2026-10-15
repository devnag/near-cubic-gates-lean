import Proof.MachineModel.CacheHeader

/-! Finalize the actual accumulated total and copy it for the one cache header.
The count template and incidence scratch are retained for their consumers. -/
namespace NearCubicWires.ExtDecompositionBatch.CacheStart
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def totalSlots : Fin 2 → Fin 21:=![0,1]
def unarySlots : Fin 3 → Fin 21:=![0,2,3]
theorem total_injective : Function.Injective totalSlots:=by
  intro i j h;fin_cases i <;> fin_cases j <;> simp_all [totalSlots]
theorem unary_injective : Function.Injective unarySlots:=by
  intro i j h;fin_cases i <;> fin_cases j <;> simp_all [unarySlots]
def inputHeads (n : ℕ) (i : Fin 21):=if i=0 then n+1 else 0
def input (C n : ℕ) (i : Fin 21) : List Bool:=
  if i=0 then false::List.replicate n true
  else if i=1 ∨ i=2 ∨ i=19 then [] else List.replicate C false
def totalHeads : Fin 21 → ℕ:=fun i=>if i=0 then 1 else 0
def totalData (C n : ℕ) (i : Fin 21) : List Bool:=
  if i=0 then UnaryTemplate.tape n
  else if i=1 then List.replicate n false
  else if i=2 ∨ i=19 then [] else List.replicate C false
def unaryData (C n : ℕ) (i : Fin 21) : List Bool:=
  if i=2 then List.replicate n true else totalData C n i
noncomputable def totalMachine:=RecoveryFocus.machine totalSlots FinalizeT.machine
noncomputable def unaryMachine:=RecoveryFocus.machine unarySlots FinalUnary.machine
noncomputable def machine:=Composition.machine totalMachine unaryMachine

theorem total_run (C n : ℕ) :
    Step totalMachine (3*n+4) (inputHeads n) (input C n) totalHeads (totalData C n) := by
  obtain ⟨r,hr,hf,hs⟩:=FinalizeT.finalize_run n
  have core:Step FinalizeT.machine (3*n+4) ![n+1,0]
      ![false::List.replicate n true,[]] ![1,0]
      ![UnaryTemplate.tape n,List.replicate n false]:=
    ⟨r,hr,by rw [hf];rfl,by rw [hf];rfl,hs.le⟩
  have run:=core.dock totalSlots total_injective (inputHeads n) (input C n)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  apply run.congr
  · funext i
    by_cases h0:i=0
    · subst i;exact dockH_slot totalSlots total_injective _ _ 0
    by_cases h1:i=1
    · subst i;exact dockH_slot totalSlots total_injective _ _ 1
    · rw [dockH_other totalSlots _ _ i (by intro j;fin_cases j <;> simp_all [totalSlots,eq_comm])]
      simp [inputHeads,totalHeads,h0]
  · funext i
    by_cases h0:i=0
    · subst i;exact install_slot totalSlots total_injective _ _ 0
    by_cases h1:i=1
    · subst i;exact install_slot totalSlots total_injective _ _ 1
    · rw [install_other totalSlots _ _ i (by intro j;fin_cases j <;> simp_all [totalSlots,eq_comm])]
      simp [input,totalData,h0,h1]

theorem unary_run (C n : ℕ) (hn:n+2≤C) :
    Step unaryMachine (2*n+10) totalHeads (totalData C n) totalHeads (unaryData C n) := by
  let caps:Fin 3 → ℕ:=![0,0,C]
  have core:Step FinalUnary.machine (2*n+10) ![1,0,0]
      ![UnaryTemplate.tape n,[],List.replicate C false] ![1,0,0]
      ![UnaryTemplate.tape n,List.replicate n true,List.replicate C false] := by
    have run:=(FinalUnary.copy_run n).pad caps
    have hi:(fun i=>ZeroPadding.pad (caps i) (FinalUnary.input n i))=
        ![UnaryTemplate.tape n,[],List.replicate C false]:=by
      funext i;fin_cases i <;> simp [caps,FinalUnary.input,ZeroPadding.pad]
    rw [hi] at run
    apply run.congr rfl
    funext i;fin_cases i <;>
      simp [caps,FinalUnary.output,ZeroPadding.pad_zero,pad_replicate_false C (n+2) hn]
  have run:=core.dock unarySlots unary_injective totalHeads (totalData C n)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  apply run.congr
  · funext i
    by_cases h0:i=0
    · subst i;exact dockH_slot unarySlots unary_injective _ _ 0
    by_cases h2:i=2
    · subst i;exact dockH_slot unarySlots unary_injective _ _ 1
    by_cases h3:i=3
    · subst i;exact dockH_slot unarySlots unary_injective _ _ 2
    · exact dockH_other unarySlots _ _ i (by intro j;fin_cases j <;> simp_all [unarySlots,eq_comm])
  · funext i
    by_cases h0:i=0
    · subst i;exact install_slot unarySlots unary_injective _ _ 0
    by_cases h2:i=2
    · subst i;exact install_slot unarySlots unary_injective _ _ 1
    by_cases h3:i=3
    · subst i;exact install_slot unarySlots unary_injective _ _ 2
    · rw [install_other unarySlots _ _ i (by intro j;fin_cases j <;> simp_all [unarySlots,eq_comm])]
      simp only [unaryData,h2,↓reduceIte]

theorem start_run (C n : ℕ) (hn:n+2≤C) :
    Step machine (5*n+15) (inputHeads n) (input C n) totalHeads (unaryData C n) := by
  have run:=(total_run C n).seq (unary_run C n hn)
  have time:3*n+4+1+(2*n+10)=5*n+15:=by omega
  rw [time] at run
  exact run

end NearCubicWires.ExtDecompositionBatch.CacheStart
