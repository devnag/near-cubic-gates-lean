import Proof.Amplification.RecoveryCaseOneHierarchyActual
import Proof.MachineModel.GeneratedAmplifierEvaluator

/-! Canonical Boolean output for the ordinary language interface: false
has empty Nat.bits, so its framed result is the single closing delimiter. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneBooleanOutput
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def core : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==3
  rule := fun q bits=>if q.val=0 then
      some ⟨if bits 0 then 1 else 3,![none,some (bits 0)],![.stay,if bits 0 then .right else .stay]⟩
    else if q.val=1 then some ⟨2,![none,some true],![.stay,.right]⟩
    else if q.val=2 then some ⟨3,![none,some false],fun _=>.stay⟩ else none
def machine := Rewind.machine core
def input (b : Bool) : Fin 3→List Bool := ![[b],[],[]]

theorem core_run (b : Bool) : ∃ r,run core 3 ![[b],[]]=some r ∧
    r.final.tapes 1=frame b.toNat.bits ∧ r.steps≤3 := by
  cases b <;> exact ⟨_,rfl,rfl,by decide⟩

theorem ready (b : Bool) : ∃ out,ClockJoin.ReadyRun machine 8 (input b) out ∧
    out 1=frame b.toNat.bits := by
  obtain ⟨base,hbase,hout,hsteps⟩ := core_run b
  obtain ⟨r,hr,rt,rh,rs,_⟩ := Rewind.reset_run core 3 ![[b],[]] base hbase
  have hb : 2*base.steps+2≤8 := by omega
  have hm:=run_moreFuel machine _ (8-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  have hi : Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool) ![[b],[]] (fun _=>[])=input b := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hm
  exact ⟨r.final.tapes,⟨r,hm,rfl,rh,rs.le.trans hb⟩,(rt 1).trans hout⟩

end NearCubicWires.RepairSource.RecoveryCaseOneBooleanOutput
