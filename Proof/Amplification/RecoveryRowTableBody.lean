import Proof.Amplification.RecoveryRowTimeBound

/-! One complete table iteration: read, structural check, clause check,
and physical increment of the prior-row driver only on acceptance. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def bodyStates {t s : Nat} (_ : Machine t s) : Nat := s
noncomputable def tableBodySizes : Fin 2→Nat := ![bodyStates readWholeMachine,bodyStates priorAdvanceMachine]
noncomputable def tableBodyPrograms : (j : Fin 2)→Machine 68 (tableBodySizes j)
  | ⟨0,_⟩=>readWholeMachine
  | ⟨1,_⟩=>priorAdvanceMachine
  | ⟨n+2,h⟩=>False.elim (by omega)
def tableBodyNext (j : Fin 2) (_ : Fin (tableBodySizes j)) (scanned : Fin 68→Bool) : Option (Fin 2) :=
  if j.val=0 then if scanned 50 then some 1 else none else none
noncomputable def tableBodyMachine := RecoveryCalls.machine tableBodySizes tableBodyPrograms 0 tableBodyNext
def rowAdvanced (x : Children) (word bits input : List Bool) (out : ReadLeafResult x word bits input) :=
  priorSuccessor (readFinished x word bits input out)

theorem row_advanced_valid (x : Children) (word bits input : List Bool) (out : ReadLeafResult x word bits input)
    (hx : x.Valid word bits) (ho : (readFinished x word bits input out).Valid word bits)
    (hi : 4*x.base.state.bits.length ≤ input.length)
    (hcap : (x.total+1)*(RecoveryRowLookupStream.budget x.bank.row.width+3)+5 ≤ x.lookupCapacity) :
    (rowAdvanced x word bits input out).Valid word bits := by
  apply priorSuccessor_valid _ word bits ho
  have h := read_finished_retained x word bits input out hi
  have hw : (readFinished x word bits input out).bank.row.width=x.bank.row.width :=
    ho.2.1.2.1.trans (h.2.2.2.2.2.1.trans hx.2.1.2.1.symm)
  rw [h.2.2.1,h.2.2.2.2.1,hw]
  exact hcap

theorem table_body_trace (x : Children) (word bits pre input : List Bool) (rows : List Row) (rest : List Bool)
    (limit : Nat) (hx : x.Valid word bits) (hs : x.base.source=pre++frame input) (hpos : x.base.pos=pre.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) (hj : x.total ≤ limit)
    (hcap : (x.total+1)*(RecoveryRowLookupStream.budget x.bank.row.width+3)+5 ≤ x.lookupCapacity) :
    ∃ n heads tapes,n ≤ tableRowBudget x.base.state.bits.length limit ∧ heads 50=0 ∧
      tapes 50=[readWholeAnswer x word bits input] ∧
      Timed tableBodyMachine n (x.cfg tableBodyMachine.start) (RecoveryCalls.stopped tableBodySizes heads tapes) ∧
      (readWholeAnswer x word bits input=true → ∃ out : ReadLeafResult x word bits input,
        heads=(rowAdvanced x word bits input out).heads ∧ tapes=(rowAdvanced x word bits input out).tapes ∧
        (rowAdvanced x word bits input out).Valid word bits) := by
  have hbudget := read_whole_time_le x bits input x.base.state.bits.length limit rfl hx.2.1.2.1.le hj
  obtain ⟨first,hr0,_,hh0,ht0,hout0⟩ := read_whole_run x word bits pre input rows rest hx hs hpos hp
  cases ha : readWholeAnswer x word bits input
  · have hn : tableBodyNext 0 first.final.control first.final.scanned=none := by
      simp [tableBodyNext,Configuration.scanned,hh0,ht0,ha,readTapeBit]
    obtain ⟨n,hb,h⟩ := stop_receipt tableBodySizes tableBodyPrograms 0 tableBodyNext 0
      (readWholeTime x bits input) _ first hr0 hn
    exact ⟨n,first.final.heads,first.final.tapes,by omega,hh0,by simpa only [ha] using ht0,h,
      by simp only [Bool.false_eq_true,IsEmpty.forall_iff]⟩
  · obtain ⟨out,hf0,hvalid⟩ := hout0 ha
    have hi : 4*x.base.state.bits.length ≤ input.length := by
      simp only [readWholeAnswer,Bool.and_eq_true,RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at ha
      exact ha.1
    have hn : tableBodyNext 0 first.final.control first.final.scanned=some 1 := by
      simp [tableBodyNext,Configuration.scanned,hh0,ht0,ha,readTapeBit]
    obtain ⟨n0,hn0,h0⟩ := call_receipt tableBodySizes tableBodyPrograms 0 tableBodyNext 0 1
      (readWholeTime x bits input) _ first hr0 hn
    rw [hf0] at h0
    obtain ⟨last,hr1,hf1,_⟩ := prior_advance_run (readFinished x word bits input out)
    obtain ⟨n1,hn1,h1⟩ := stop_receipt tableBodySizes tableBodyPrograms 0 tableBodyNext 1
      (2*(readFinished x word bits input out).total+6) _ last hr1 (by rfl)
    rw [hf1] at h1
    have h := h0.trans h1
    have ht := (read_finished_retained x word bits input out hi).2.2.1
    rw [ht] at hn1
    refine ⟨n0+n1,(rowAdvanced x word bits input out).heads,(rowAdvanced x word bits input out).tapes,
      by omega,rfl,?_,h,?_⟩
    · rfl
    · intro _
      exact ⟨out,rfl,rfl,row_advanced_valid x word bits input out hx hvalid hi hcap⟩

theorem table_body_run (x : Children) (word bits pre input : List Bool) (rows : List Row) (rest : List Bool)
    (limit : Nat) (hx : x.Valid word bits) (hs : x.base.source=pre++frame input) (hpos : x.base.pos=pre.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) (hj : x.total ≤ limit)
    (hcap : (x.total+1)*(RecoveryRowLookupStream.budget x.bank.row.width+3)+5 ≤ x.lookupCapacity) :
    ∃ r,runFrom tableBodyMachine (tableRowBudget x.base.state.bits.length limit) (x.cfg tableBodyMachine.start)=some r ∧
      r.steps ≤ tableRowBudget x.base.state.bits.length limit ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[readWholeAnswer x word bits input] ∧
      (readWholeAnswer x word bits input=true → ∃ out : ReadLeafResult x word bits input,
        r.final=(rowAdvanced x word bits input out).cfg r.final.control ∧
        (rowAdvanced x word bits input out).Valid word bits) := by
  obtain ⟨n,heads,tapes,hn,hh,ht,h,hout⟩ := table_body_trace x word bits pre input rows rest limit hx hs hpos hp hj hcap
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [tableBodyMachine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel tableBodyMachine n (tableRowBudget x.base.state.bits.length limit-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hs.le.trans hn,?_,?_,?_⟩
  · simpa only [hf,RecoveryCalls.stopped] using hh
  · simpa only [hf,RecoveryCalls.stopped] using ht
  · intro ha
    obtain ⟨out,hheads,htapes,hvalid⟩ := hout ha
    refine ⟨out,?_,hvalid⟩
    rw [hf]
    apply configuration_ext
    · rfl
    · exact hheads
    · exact htapes

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
