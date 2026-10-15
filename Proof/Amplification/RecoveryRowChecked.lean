import Proof.Amplification.RecoveryRowLeafWhole

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def rowStates {t s : Nat} (_ : Machine t s) : Nat := s
noncomputable def wholeRowSizes : Fin 2→Nat := ![rowStates structureMachine,rowStates leafWholeMachine]
noncomputable def wholeRowPrograms : (j : Fin 2)→Machine 68 (wholeRowSizes j)
  | ⟨0,_⟩=>structureMachine
  | ⟨1,_⟩=>leafWholeMachine
  | ⟨n+2,h⟩=>False.elim (by omega)
def wholeRowNext (j : Fin 2) (_ : Fin (wholeRowSizes j)) (scanned : Fin 68→Bool) : Option (Fin 2) :=
  if j.val=0 then if scanned 50 then some 1 else none else none
noncomputable def wholeRowMachine := RecoveryCalls.machine wholeRowSizes wholeRowPrograms 0 wholeRowNext
noncomputable def wholeRowCfg (x : Children) (j : Fin 2) :=
  x.cfg (RecoveryCalls.code wholeRowSizes j (wholeRowPrograms j).start)
def wholeRowTime (x : Children) (bits : List Bool) :=
  structureTime x+1+leafWholeTime (structureOutput x bits)+1
def wholeRowAnswer (x : Children) (word bits : List Bool) :=
  (structureOutput x bits).base.valid && leafAnswer (structureOutput x bits) word

theorem whole_row_answer (x : Children) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest))
    (hrows : checkFrom [] rows=true) :
    wholeRowAnswer x word bits=(unpairCheck rows (dataRow x.base) && leafAnswer x word) := by
  unfold wholeRowAnswer leafAnswer
  rw [structure_answer x bits rows rest hp,check_eq rows (dataRow x.base) hrows,structure_leaf_check]

theorem whole_row_trace (x : Children) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hw : x.base.code.length=x.base.state.bits.length)
    (hk : x.base.kind.length=x.base.state.bits.length) (hc : x.base.count.length=x.base.state.bits.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    ∃ n heads tapes,n ≤ wholeRowTime x bits ∧ heads 50=0 ∧ tapes 50=[wholeRowAnswer x word bits] ∧
      Timed wholeRowMachine n (x.cfg wholeRowMachine.start) (RecoveryCalls.stopped wholeRowSizes heads tapes) ∧
      (wholeRowAnswer x word bits=true →
        ∃ out : RecoveryRowLeaf.LeafResult (structureOutput x bits).base.state
            (structureOutput x bits).base.extra (structureOutput x bits).base.kind word,
          heads=(leafFinished (structureOutput x bits) word out).heads ∧
          tapes=(leafFinished (structureOutput x bits) word out).tapes ∧
          (leafFinished (structureOutput x bits) word out).Valid word bits) := by
  obtain ⟨first,hr0,hf0,hb0,hv⟩ := structure_run x word bits rows rest hx hw hk hc hp
  cases ha : (structureOutput x bits).base.valid
  · have hn : wholeRowNext 0 first.final.control first.final.scanned=none := by
      rw [hf0]
      change (if (structureOutput x bits).base.valid then some (1 : Fin 2) else none)=none
      rw [ha]; rfl
    obtain ⟨n,hb,h⟩ := stop_receipt wholeRowSizes wholeRowPrograms 0 wholeRowNext 0 (structureTime x) _ first hr0 hn
    rw [hf0] at h
    refine ⟨n,(structureOutput x bits).heads,(structureOutput x bits).tapes,?_,rfl,?_,h,?_⟩
    · unfold wholeRowTime; omega
    · change [(structureOutput x bits).base.valid]=[wholeRowAnswer x word bits]
      simp only [wholeRowAnswer,ha,Bool.false_and]
    · simp only [wholeRowAnswer,ha,Bool.false_and,Bool.false_eq_true,IsEmpty.forall_iff]
  · have hn : wholeRowNext 0 first.final.control first.final.scanned=some 1 := by
      rw [hf0]
      change (if (structureOutput x bits).base.valid then some (1 : Fin 2) else none)=some 1
      rw [ha]; rfl
    obtain ⟨n0,hn0,h0⟩ := call_receipt wholeRowSizes wholeRowPrograms 0 wholeRowNext 0 1 (structureTime x) _ first hr0 hn
    rw [hf0] at h0
    obtain ⟨last,hr1,_,hh1,ht1,hout⟩ := leaf_whole_run (structureOutput x bits) word bits hv
    obtain ⟨n1,hn1,h1⟩ := stop_receipt wholeRowSizes wholeRowPrograms 0 wholeRowNext 1
      (leafWholeTime (structureOutput x bits)) _ last hr1 (by rfl)
    have h := h0.trans h1
    refine ⟨n0+n1,last.final.heads,last.final.tapes,?_,?_,?_,h,?_⟩
    · unfold wholeRowTime; omega
    · rw [hh1]; rfl
    · simpa only [wholeRowAnswer,ha,Bool.true_and] using ht1
    · intro hy
      have hl : leafAnswer (structureOutput x bits) word=true := by
        simpa only [wholeRowAnswer,ha,Bool.true_and] using hy
      obtain ⟨out,hf,hvalid⟩ := hout hl
      exact ⟨out,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hvalid⟩

theorem whole_row_run (x : Children) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hw : x.base.code.length=x.base.state.bits.length)
    (hk : x.base.kind.length=x.base.state.bits.length) (hc : x.base.count.length=x.base.state.bits.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    ∃ r,runFrom wholeRowMachine (wholeRowTime x bits) (x.cfg wholeRowMachine.start)=some r ∧
      r.steps ≤ wholeRowTime x bits ∧ r.final.heads 50=0 ∧ r.final.tapes 50=[wholeRowAnswer x word bits] ∧
      (wholeRowAnswer x word bits=true →
        ∃ out : RecoveryRowLeaf.LeafResult (structureOutput x bits).base.state
            (structureOutput x bits).base.extra (structureOutput x bits).base.kind word,
          r.final=(leafFinished (structureOutput x bits) word out).cfg r.final.control ∧
          (leafFinished (structureOutput x bits) word out).Valid word bits) := by
  obtain ⟨n,heads,tapes,hn,hh,ht,h,hout⟩ := whole_row_trace x word bits rows rest hx hw hk hc hp
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [wholeRowMachine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel wholeRowMachine n (wholeRowTime x bits-n) _ r hr
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
