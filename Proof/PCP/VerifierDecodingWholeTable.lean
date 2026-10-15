import Proof.PCP.VerifierDecodingWholeCalls

/-! The complete guarded table suffix, including actual t reset, capped e
driver rewind, all records, exact delimiter, and rejecting result writes. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Whole
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_tail (word fields : List Bool) (limit t s x y : ℕ)
    (hp : HeaderMachine.parts word=some (t,s,fields)) (hspos : 0<s)
    (hv : StartFlags.valid fields (Front.bound s) s=true) (he : 2^t*s ≤ word.length) :
    ∃ n final, n≤t+(2^t*s)*(8*(Front.bound s).length+12*t+34)+15 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 2)
        ⟨(0 : Fin 3),(FrontTable.guarded word fields limit t s x y).heads,
          (FrontTable.guarded word fields limit t s x y).tapes⟩) final ∧
      machine.halted final.control=true ∧
      final.scanned 19=TableValidation.valid (Front.bound s) t (2^t*s) (FrontTable.tableState fields t s).bits ∧
      (TableValidation.valid (Front.bound s) t (2^t*s) (FrontTable.tableState fields t s).bits=true →
        Success word fields limit t s x y final) := by
  have hlen := GuardedPreparation.parts_lengths hp
  obtain ⟨r,hr,hf,hrsteps⟩ := FrontTable.reset_run word fields limit t s x y (by omega)
  have hreset := call_prefix 2 3 (t+2) _ r hr (by rfl)
  rw [hf] at hreset
  obtain ⟨tail,htail,htime,hbit,hgood⟩ := TableLayout.table_run
    (FrontTable.reset word fields limit t s x y) (Front.bound s) t word.length (2^t*s)
    (FrontTable.tableState fields t s) (FrontTable.table_entry word fields limit t s x y hp hspos hv)
    he (by simp [RecordsMachine.Inv,FrontTable.tableState])
  have hstop := stop_prefix 3 ((2^t*s)*(8*(Front.bound s).length+12*t+34)+11) _ tail htail (by rfl)
  have hall := hreset.trans hstop
  refine ⟨_,_,by omega,hall,?_,?_,?_⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · simpa [RecoveryCalls.stopped,Configuration.scanned] using hbit
  · intro ht
    obtain ⟨out,hout,hsource,_,hbits,hinv⟩ := hgood ht
    refine ⟨out,?_,hsource,hbits,hinv⟩
    rw [hout]
    rfl

theorem bound_width (s : ℕ) (hs : 0<s) : (Front.bound s).length ≤ s := by
  rw [Front.bound_length,←BitWidthMachine.width_eq s hs]
  exact ClockBinary.length_bound s s Nat.lt_two_pow_self

theorem guard_tail (word fields : List Bool) (limit t s x y : ℕ)
    (hp : HeaderMachine.parts word=some (t,s,fields)) (ht : 2≤t) (hspos : 0<s)
    (hv : StartFlags.valid fields (Front.bound s) s=true) :
    ∃ n final, n≤32*word.length^2+52*word.length+40 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1)
        (TableGuardLayout.input (FrontTable.front word fields limit t s x y))) final ∧
      machine.halted final.control=true ∧ final.scanned 19=tableValid word fields t s ∧
      (tableValid word fields t s=true → Success word fields limit t s x y final) := by
  have hlen := GuardedPreparation.parts_lengths hp
  have hj := bound_width s hspos
  obtain ⟨r,hr,hsteps,hbit,hgood⟩ := TableGuardLayout.guard_run
    (FrontTable.front word fields limit t s x y) word.length t s
    (FrontTable.guard_entry word fields limit t s x y) (by omega) (by omega) (by omega) hspos
  by_cases he : 2^t*s ≤ word.length
  · have hcall := call_prefix 1 2 (TableBoundMachine.budget word.length+2) _ r hr
      (by simp [next]; exact hbit.trans (by simp [he]))
    rw [hgood he] at hcall
    obtain ⟨n,final,hn,htail,hh,hresult,hout⟩ := table_tail word fields limit t s x y hp hspos hv he
    have hall := hcall.trans htail
    have hprod := Nat.mul_le_mul he
      (show 8*(Front.bound s).length+12*t+34≤20*word.length+34 by omega)
    refine ⟨_,final,?_,hall,hh,?_,?_⟩
    · dsimp [TableBoundMachine.budget] at hsteps
      nlinarith
    · simpa [tableValid,he] using hresult
    · intro hvtable
      exact hout (by simpa [tableValid,he] using hvtable)
  · have hcall := call_prefix 1 4 (TableBoundMachine.budget word.length+2) _ r hr
      (by simp [next]; exact hbit.trans (by simp [he]))
    have hall := hcall.trans (reject_tail r.final.heads r.final.tapes)
    refine ⟨_,_,?_,hall,?_,?_,by simp [tableValid,he]⟩
    · dsimp [TableBoundMachine.budget] at hsteps
      nlinarith
    · simp [machine,RecoveryCalls.machine,rejected,RecoveryCalls.stopped]
    · simpa [tableValid,he] using rejected_bit r.final.heads r.final.tapes

end NearCubicWires.RepairSource.VerifierDecoding.Whole
