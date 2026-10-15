import Proof.CaseAnalysis.RowsPacketFlag

/-! The fixed packet branch consumes one marker, skips an absent polynomial,
or executes the enclosing positive polynomial program. Every return is paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes (s : ℕ) : Fin 2→ℕ := ![3,s]
def programs {t s : ℕ} (source : Fin t) (body : Machine t s) :
    (j : Fin 2)→Machine t (sizes s j)
  | ⟨0,_⟩=>CloseoutRowsPacketFlag.machine source
  | ⟨1,_⟩=>body
  | ⟨j+2,hj⟩=>False.elim (by omega)
def next {t s : ℕ} (j : Fin 2) (q : Fin (sizes s j)) (_ : Fin t→Bool) : Option (Fin 2) :=
  if j.val=0 ∧ q.val=1 then some 1 else none
noncomputable def machine {t s : ℕ} (source : Fin t) (body : Machine t s) :=
  RecoveryCalls.machine (sizes s) (programs source body) 0 next

theorem absent_run {t s : ℕ} (source : Fin t) (body : Machine t s)
    (hh : Fin t→ℕ) (tt : Fin t→List Bool)
    (hbit : readTapeBit (tt source) (hh source)=false) :
    ∃ r,runFrom (machine source body) 2 ⟨(machine source body).start,hh,tt⟩=some r ∧
      r.final.heads=Function.update hh source (hh source+1) ∧
      r.final.tapes=tt ∧ r.steps=2 := by
  let after : Configuration t 3:=⟨2,Function.update hh source (hh source+1),tt⟩
  have flag := Timed.single (by rfl) (CloseoutRowsPacketFlag.flag_step source hh tt false hbit)
  have first := RecoveryCalls.body_timed (sizes s) (programs source body) 0 next 0 flag
  have stop := RecoveryCalls.stop_step (sizes s) (programs source body) 0 next 0 after
    (by rfl) (by simp [next,after])
  have last := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) stop
  have whole := first.trans last
  obtain ⟨r,hr,hf,hs⟩:=whole.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs⟩

theorem present_run {t s : ℕ} (source : Fin t) (body : Machine t s)
    (hh : Fin t→ℕ) (tt : Fin t→List Bool) (fuel : ℕ)
    (hbit : readTapeBit (tt source) (hh source)=true)
    (base : ExecutionReceipt t s)
    (hrun : runFrom body fuel
      ⟨body.start,Function.update hh source (hh source+1),tt⟩=some base) :
    ∃ r,runFrom (machine source body) (fuel+3) ⟨(machine source body).start,hh,tt⟩=some r ∧
      r.final.heads=base.final.heads ∧ r.final.tapes=base.final.tapes ∧ r.steps≤fuel+3 := by
  let after : Configuration t 3:=⟨1,Function.update hh source (hh source+1),tt⟩
  have flag := Timed.single (by rfl) (CloseoutRowsPacketFlag.flag_step source hh tt true hbit)
  have first := RecoveryCalls.body_timed (sizes s) (programs source body) 0 next 0 flag
  have ret := RecoveryCalls.return_step (sizes s) (programs source body) 0 next 0 1 after
    (by rfl) (by simp [next,after])
  have middle := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ret
  obtain ⟨n,hn,last⟩ := stop_receipt (sizes s) (programs source body) 0 next 1 fuel
    ⟨body.start,Function.update hh source (hh source+1),tt⟩ base hrun (by simp [next])
  have whole := (first.trans middle).trans last
  obtain ⟨r,hr,hf,hs⟩ := whole.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have htime : 1+1+n≤fuel+3 := by omega
  have more:=runFrom_moreFuel (machine source body) (1+1+n) (fuel+3-(1+1+n)) _ r hr
  rw [Nat.add_sub_of_le htime] at more
  exact ⟨r,more,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le.trans htime⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketBranch
