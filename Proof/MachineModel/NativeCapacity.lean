import Proof.MachineModel.NativeCapacityParameters

/-! Physically construct the preparation capacity from the six small
dimensions, retaining every parameter field. No capacity-sized word is input. -/
namespace NearCubicWires.ExtIncidence.NativeCapacity
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 32) : Fin 52:=i.castAdd 20
def slots : Fin 22→Fin 52:=![22,32,33,34,35,36,37,38,39,40,41,30,42,43,44,45,46,47,48,49,50,51]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def first:=TapeEmbedding.machine 20 NativeCapacityParameters.machine
noncomputable def last:=RecoveryFocus.machine slots CloseoutRowsCapacityDriver.machine
noncomputable def machine:=Composition.machine first last
def input (n p F w N Q : ℕ) : Fin 52→List Bool:=
  Fin.addCases (m:=32) (n:=20) (motive:=fun _=>List Bool)
    (NativeCapacityParameters.input n p F w N Q) (fun _=>[])
def budget (n p F w N Q : ℕ):=NativeCapacityParameters.budget n p F w N Q+1+
  CloseoutRowsCapacityDriver.budget (CloseoutRowsPreparationBounds.scale n p F w N Q) (w*(Q+1))

theorem capacity_run (n p F w N Q : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget n p F w N Q) (input n p F w N Q) out ∧
      (∀ i,out (old i)=NativeCapacityParameters.output n p F w N Q i) ∧
      out 50=List.replicate (CloseoutRowsPreparationBounds.capacity n p F w N Q) true:=by
  obtain ⟨r,hr,rt,rh,_rs⟩:=NativeCapacityParameters.ready n p F w N Q
  have firstRun:=(Step.of_run hr (funext rh) rt).embed (fun _ : Fin 20=>0) (fun _=>[])
  let A : Fin 52→List Bool:=Fin.addCases (m:=32) (n:=20) (motive:=fun _=>List Bool)
    (NativeCapacityParameters.output n p F w N Q) (fun _=>[])
  let S:=CloseoutRowsPreparationBounds.scale n p F w N Q
  obtain ⟨drv,ready,value,keepS,keepR⟩:=CloseoutRowsCapacityDriver.driver_run S (w*(Q+1))
  have source : ∀ j,A (slots j)=CloseoutRowsCapacityDriver.input S (w*(Q+1)) j:=by
    intro j;fin_cases j
    · exact NativeCapacityParameters.scale_output n p F w N Q
    all_goals rfl
  obtain ⟨s,hs,st,sh,_ss⟩:=ready.focus slots slots_injective A source
  have zeroHeads : (fun i : Fin 52=>Fin.addCases (fun _ : Fin 32=>0) (fun _ : Fin 20=>0) i)=(fun _=>0):=by
    funext i
    fin_cases i <;> rfl
  have firstRun:=firstRun.congr_in zeroHeads rfl |>.congr zeroHeads rfl
  have whole:=firstRun.seq (Step.of_run hs (funext sh) st)
  let O:=install slots A drv
  have field (j : Fin 22) : O (slots j)=drv j:=install_slot slots slots_injective A drv j
  have retained (i : Fin 32) : O (old i)=NativeCapacityParameters.output n p F w N Q i:=by
    by_cases h22 : i=22
    · subst i;exact (field 0).trans (keepS.trans (NativeCapacityParameters.scale_output n p F w N Q).symm)
    by_cases h30 : i=30
    · subst i;exact (field 11).trans keepR
    rw [←show A (old i)=NativeCapacityParameters.output n p F w N Q i by
      simp only [A,old,Fin.addCases_left]]
    apply install_other slots A drv (old i)
    intro j he
    have hv:=congrArg (fun x : Fin 52=>x.val) he
    have hi:=i.isLt
    have n22 : i.val≠22:=fun h=>h22 (Fin.ext h)
    have n30 : i.val≠30:=fun h=>h30 (Fin.ext h)
    fin_cases j <;> simp [slots,old] at hv <;> omega
  obtain ⟨z,hz,zh,zt,zs⟩:=whole
  refine ⟨O,⟨z,hz,zt,fun i=>congrFun zh i,zs⟩,retained,(field 20).trans value⟩

end NearCubicWires.ExtIncidence.NativeCapacity
