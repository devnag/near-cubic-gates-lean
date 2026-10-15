import Proof.MachineModel.GeneratedAmplifierSemantics

/-! The paid sequential raw-bit lookup. A physical fixed-width binary query
is decremented once per skipped bit. Zero data bits never delimit the table;
the typed in-range address proves that the selected bit is present. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Lookup
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryCommittedBit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev sizes : Fin 3→ℕ := ![7,2,2]
def programs : (i : Fin 3)→Machine 5 (sizes i)
  | ⟨0,_⟩ => predMachine
  | ⟨1,_⟩ => advance
  | ⟨2,_⟩ => writeResult true false
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (i : Fin 3) (_ : Fin (sizes i)) (bits : Fin 5→Bool) : Option (Fin 3) :=
  if i=0 then some (if bits 1 then 1 else 2) else if i=1 then some 0 else none
noncomputable abbrev machine := RecoveryCalls.machine sizes programs 0 next
def cost (width count : ℕ) := (count+1)*(4*width+7)

theorem scan_timed (skip : List Bool) (bit : Bool) (tail : List Bool) (d : Data) (pre : List Bool)
    (hs : d.source=pre++skip++bit::tail) (hp : d.pos=pre.length)
    (hq : value d.query=skip.length) (hc : 2*d.query.length+1≤d.capacity) :
    ∃ n,∃ out : Data,n≤cost d.query.length skip.length ∧ out.result=bit ∧
      Timed machine n (d.cfg machine.start) (out.cfg (RecoveryCalls.controlCode sizes none)) := by
  induction skip generalizing d pre with
  | nil =>
    have hz : value d.query=0 := hq
    obtain ⟨first,hfirst,hff,hfs⟩ := pred_run d hc
    have hf : first.final.scanned 1=false := by
      rw [hff]
      change decide (value d.query≠0)=false
      simp [hz]
    obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 2 _ _ first hfirst (by simp [next,hf])
    rw [hff] at h0
    change Timed machine n0 (d.cfg machine.start) (d.afterPred.cfg (RecoveryCalls.code sizes 2 (0 : Fin 2))) at h0
    have hread : readTapeBit d.afterPred.source d.afterPred.pos=bit := by
      change readTapeBit d.source d.pos=bit
      rw [hs,hp]
      simpa using Streaming.read_append pre tail bit
    obtain ⟨last,hl,hlf,hls⟩ := write_run d.afterPred true false
    change last.final=(d.afterPred.picked (readTapeBit d.afterPred.source d.afterPred.pos)).cfg 1 at hlf
    rw [hread] at hlf
    obtain ⟨n1,hn1,h1⟩ := stop_receipt sizes programs 0 next 2 _ _ last hl (by rfl)
    rw [hlf] at h1
    refine ⟨n0+n1,d.afterPred.picked bit,?_,rfl,h0.trans h1⟩
    change n0≤4*d.query.length+4+1 at hn0
    change n1≤1+1 at hn1
    simp only [cost,List.length_nil]
    omega
  | cons b bs ih =>
    have hz : value d.query≠0 := by simp only [List.length_cons] at hq; omega
    obtain ⟨first,hfirst,hff,hfs⟩ := pred_run d hc
    have hf : first.final.scanned 1=true := by
      rw [hff]
      change decide (value d.query≠0)=true
      simp [hz]
    obtain ⟨n0,hn0,h0⟩ := call_receipt sizes programs 0 next 0 1 _ _ first hfirst (by simp [next,hf])
    rw [hff] at h0
    change Timed machine n0 (d.cfg machine.start) (d.afterPred.cfg (RecoveryCalls.code sizes 1 (0 : Fin 2))) at h0
    obtain ⟨second,hsecond,hsf,hss⟩ := advance_run d.afterPred
    obtain ⟨n1,hn1,h1⟩ := call_receipt sizes programs 0 next 1 0 _ _ second hsecond (by rfl)
    rw [hsf] at h1
    have hs' : d.afterPred.atBit.source=(pre++[b])++bs++bit::tail := by
      change d.source=_
      rw [hs]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    have hp' : d.afterPred.atBit.pos=(pre++[b]).length := by simp [Data.atBit,Data.afterPred,hp]
    have hq' : value d.afterPred.atBit.query=bs.length := by
      change value (RecoveryListPredecessor.result d.query true)=_
      rw [RecoveryListPredecessor.predecessor_value d.query hz,hq]
      simp
    have hc' : 2*d.afterPred.atBit.query.length+1≤d.afterPred.atBit.capacity := by
      simpa only [Data.atBit,Data.afterPred,RecoveryListPredecessor.result_length] using hc
    obtain ⟨nt,out,hnt,hout,ht⟩ := ih d.afterPred.atBit (pre++[b]) hs' hp' hq' hc'
    refine ⟨n0+n1+nt,out,?_,hout,(h0.trans h1).trans ht⟩
    change n0≤4*d.query.length+4+1 at hn0
    change n1≤1+1 at hn1
    change nt≤cost (RecoveryListPredecessor.result d.query true).length bs.length at hnt
    rw [RecoveryListPredecessor.result_length] at hnt
    simp only [cost,List.length_cons] at *
    nlinarith

theorem lookup_run (skip : List Bool) (bit : Bool) (tail : List Bool) (d : Data) (pre : List Bool)
    (hs : d.source=pre++skip++bit::tail) (hp : d.pos=pre.length)
    (hq : value d.query=skip.length) (hc : 2*d.query.length+1≤d.capacity) :
    ∃ r,runFrom machine (cost d.query.length skip.length) (d.cfg machine.start)=some r ∧
      r.steps≤cost d.query.length skip.length ∧ r.final.tapes 4=[bit] ∧ r.final.heads 4=0 := by
  obtain ⟨n,out,hn,hout,ht⟩ := scan_timed skip bit tail d pre hs hp hq hc
  obtain ⟨r,hr,hf,hs'⟩ := ht.run (by simp [RecoveryCalls.machine,Data.cfg])
  have hm := runFrom_moreFuel machine n (cost d.query.length skip.length-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hs'.le.trans hn,?_,?_⟩
  · rw [hf]
    change [out.result]=[bit]
    rw [hout]
  · rw [hf]
    rfl

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Lookup
