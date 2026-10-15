import Proof.Amplification.RecoveryRowReadAmbient

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def readStates {t s : Nat} (_ : Machine t s) : Nat := s
noncomputable def readWholeSizes : Fin 2→Nat := ![readStates rowReadMachine,readStates wholeRowMachine]
noncomputable def readWholePrograms : (j : Fin 2)→Machine 68 (readWholeSizes j)
  | ⟨0,_⟩=>rowReadMachine
  | ⟨1,_⟩=>wholeRowMachine
  | ⟨n+2,h⟩=>False.elim (by omega)
def readWholeNext (j : Fin 2) (_ : Fin (readWholeSizes j)) (scanned : Fin 68→Bool) : Option (Fin 2) :=
  if j.val=0 then if scanned 50 then some 1 else none else none
noncomputable def readWholeMachine := RecoveryCalls.machine readWholeSizes readWholePrograms 0 readWholeNext
def readWholeTime (x : Children) (bits input : List Bool) :=
  RecoveryRowFields.budget x.base.state.bits.length+1+wholeRowTime (readChildren x input) bits+1
def readWholeAnswer (x : Children) (word bits input : List Bool) :=
  (readRow x.base.state.bits.length input).isSome && wholeRowAnswer (readChildren x input) word bits

theorem read_whole_trace (x : Children) (word bits pre input : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hs : x.base.source=pre++frame input) (hpos : x.base.pos=pre.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    ∃ n heads tapes,n ≤ readWholeTime x bits input ∧ heads 50=0 ∧ tapes 50=[readWholeAnswer x word bits input] ∧
      Timed readWholeMachine n (x.cfg readWholeMachine.start) (RecoveryCalls.stopped readWholeSizes heads tapes) ∧
      (readWholeAnswer x word bits input=true →
        ∃ out : RecoveryRowLeaf.LeafResult (structureOutput (readChildren x input) bits).base.state
            (structureOutput (readChildren x input) bits).base.extra (structureOutput (readChildren x input) bits).base.kind word,
          heads=(leafFinished (structureOutput (readChildren x input) bits) word out).heads ∧
          tapes=(leafFinished (structureOutput (readChildren x input) bits) word out).tapes ∧
          (leafFinished (structureOutput (readChildren x input) bits) word out).Valid word bits) := by
  obtain ⟨first,hr0,_,hh0,ht0,hout0⟩ := read_ambient_run x word pre input hx.1 hs hpos
  cases ha : (readRow x.base.state.bits.length input).isSome
  · have hn : readWholeNext 0 first.final.control first.final.scanned=none := by
      simp [readWholeNext,Configuration.scanned,hh0,ht0,ha,readTapeBit]
    obtain ⟨n,hb,h⟩ := stop_receipt readWholeSizes readWholePrograms 0 readWholeNext 0
      (RecoveryRowFields.budget x.base.state.bits.length) _ first hr0 hn
    refine ⟨n,first.final.heads,first.final.tapes,?_,hh0,?_,h,?_⟩
    · unfold readWholeTime; omega
    · simpa only [readWholeAnswer,ha,Bool.false_and] using ht0
    · simp only [readWholeAnswer,ha,Bool.false_and,Bool.false_eq_true,IsEmpty.forall_iff]
  · have hf0 := hout0 ha
    have hn : readWholeNext 0 first.final.control first.final.scanned=some 1 := by
      simp [readWholeNext,Configuration.scanned,hh0,ht0,ha,readTapeBit]
    obtain ⟨n0,hn0,h0⟩ := call_receipt readWholeSizes readWholePrograms 0 readWholeNext 0 1
      (RecoveryRowFields.budget x.base.state.bits.length) _ first hr0 hn
    rw [hf0] at h0
    have hi : 4*x.base.state.bits.length ≤ input.length := by
      simpa only [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] using ha
    have hv := read_children_valid x word bits input hx hi
    obtain ⟨hw,hk,hc⟩ := read_children_widths x input hi
    obtain ⟨last,hr1,_,hh1,ht1,hout1⟩ := whole_row_run (readChildren x input) word bits rows rest hv hw hk hc hp
    obtain ⟨n1,hn1,h1⟩ := stop_receipt readWholeSizes readWholePrograms 0 readWholeNext 1
      (wholeRowTime (readChildren x input) bits) _ last hr1 (by rfl)
    have h := h0.trans h1
    refine ⟨n0+n1,last.final.heads,last.final.tapes,?_,hh1,?_,h,?_⟩
    · unfold readWholeTime; omega
    · simpa only [readWholeAnswer,ha,Bool.true_and] using ht1
    · intro hy
      have hl : wholeRowAnswer (readChildren x input) word bits=true := by
        simpa only [readWholeAnswer,ha,Bool.true_and] using hy
      obtain ⟨out,hf,hvalid⟩ := hout1 hl
      exact ⟨out,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hvalid⟩

theorem read_whole_run (x : Children) (word bits pre input : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits) (hs : x.base.source=pre++frame input) (hpos : x.base.pos=pre.length)
    (hp : readMany (readRow x.bank.row.width) x.total bits=some (rows,rest)) :
    ∃ r,runFrom readWholeMachine (readWholeTime x bits input) (x.cfg readWholeMachine.start)=some r ∧
      r.steps ≤ readWholeTime x bits input ∧ r.final.heads 50=0 ∧ r.final.tapes 50=[readWholeAnswer x word bits input] ∧
      (readWholeAnswer x word bits input=true →
        ∃ out : RecoveryRowLeaf.LeafResult (structureOutput (readChildren x input) bits).base.state
            (structureOutput (readChildren x input) bits).base.extra (structureOutput (readChildren x input) bits).base.kind word,
          r.final=(leafFinished (structureOutput (readChildren x input) bits) word out).cfg r.final.control ∧
          (leafFinished (structureOutput (readChildren x input) bits) word out).Valid word bits) := by
  obtain ⟨n,heads,tapes,hn,hh,ht,h,hout⟩ := read_whole_trace x word bits pre input rows rest hx hs hpos hp
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [readWholeMachine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel readWholeMachine n (readWholeTime x bits input-n) _ r hr
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
