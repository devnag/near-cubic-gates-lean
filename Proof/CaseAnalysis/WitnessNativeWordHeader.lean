import Proof.CaseAnalysis.WitnessBitFieldsReady
import Proof.MachineModel.OrdinaryMatrixNaturalHeader
import Proof.MachineModel.UWalkUnary

/-! Reuse the native header serializer, with its required one-bit zero word.
The ordinary frame and the source's length-prefixed natWord remain distinct. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeWord
open LocalBitMultitape RecoveryExecution RadixSemantics RepairRepresentation
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawWord (bits : List Bool):=MatrixNaturalHeader.header bits++bits
def word (bits : List Bool):=if bits=[] then [true,false,false] else rawWord bits

theorem word_eq (bits : List Bool) (h : bits=[] ∨ bits.getLast?=some true) : word bits=natWord (value bits):=by
  by_cases he:bits=[]
  · subst bits
    rfl
  · have hv:=BitFields.canonical_bits bits h
    have hn:0<value bits:=Nat.pos_of_ne_zero (by
      intro hz
      rw [hz,Nat.zero_bits] at hv
      exact he hv.symm)
    have hl:=DimensionProducer.bits_length (value bits) hn
    rw [hv] at hl
    rw [word,if_neg he,WilliamsInputHeader.natWord_eq,DimensionProducer.binary_bits _ hn,hv,←hl]
    simp [rawWord,MatrixNaturalHeader.header,List.append_assoc]

theorem header_ready (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun MatrixNaturalHeader.resetMachine (6*bits.length+6)
      (MatrixNaturalHeader.resetInput bits) out ∧ out 0=frame bits ∧
      out 1=List.replicate bits.length true ∧ out 2=rawWord bits:=by
  obtain ⟨base,hb,hf,hs⟩:=MatrixNaturalHeader.header_run bits
  obtain ⟨r,hr,ht,_,hh,hsteps,_⟩:=Rewind.Workspace.reset_workspace MatrixNaturalHeader.machine _ _ base hb 0
  change run MatrixNaturalHeader.resetMachine (2*base.steps+2) (MatrixNaturalHeader.resetInput bits)=some r at hr
  have htime:2*base.steps+2=6*bits.length+6:=by omega
  rw [htime] at hr hsteps
  refine ⟨r.final.tapes,⟨r,hr,rfl,hh,hsteps.le⟩,?_,?_,?_⟩
  · exact (ht 0).trans (by rw [hf];rfl)
  · exact (ht 1).trans (by rw [hf];rfl)
  · exact (ht 2).trans (by rw [hf];rfl)

namespace Zero
def machine : Machine 2 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==3
  rule:=fun q bits=>if q.val=0 then
      if bits 0 then some ⟨3,fun _=>none,fun _=>.stay⟩
      else some ⟨1,![none,some true],![.stay,.right]⟩
    else if q.val=1 then some ⟨2,![none,some false],![.stay,.right]⟩
    else if q.val=2 then some ⟨3,![none,some false],![.stay,.right]⟩
    else none
def input (bits : List Bool) : Fin 2→List Bool:=![List.replicate bits.length true,rawWord bits]
def cfg (q : Fin 4) (bits : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 4:=
  ⟨q,![0,pos],![List.replicate bits.length true,out]⟩

theorem raw_run (bits : List Bool) : ∃ r,
    run machine (if bits=[] then 3 else 1) (input bits)=some r ∧
      r.steps=(if bits=[] then 3 else 1) ∧ r.final.tapes 1=word bits:=by
  cases bits with
  | nil=>
    have h0:step machine (initialConfiguration machine (input []))=some (cfg 1 [] 1 [true]):=by
      simp [step,machine,input,initialConfiguration,rawWord,MatrixNaturalHeader.header,Configuration.scanned,readTapeBit]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> rfl
    have h1:step machine (cfg 1 [] 1 [true])=some (cfg 2 [] 2 [true,false]):=by
      simp [step,machine,cfg]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i
        · rfl
        · exact Streaming.write_append [true] false
    have h2:step machine (cfg 2 [] 2 [true,false])=some (cfg 3 [] 3 [true,false,false]):=by
      simp [step,machine,cfg]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i
        · rfl
        · exact Streaming.write_append [true,false] false
    obtain ⟨r,hr,hf,ht⟩:=((Timed.single (by rfl) h0).trans
      ((Timed.single (by rfl) h1).trans (Timed.single (by rfl) h2))).run (by rfl)
    exact ⟨r,hr,ht,by rw [hf];rfl⟩
  | cons b bits=>
    have hs:step machine (initialConfiguration machine (input (b::bits)))=
        some (cfg 3 (b::bits) 0 (rawWord (b::bits))):=by
      simp [step,machine,input,initialConfiguration,Configuration.scanned,List.replicate_succ,readTapeBit]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> rfl
    obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
    exact ⟨r,hr,ht,by rw [hf];rfl⟩

def readyMachine:=Rewind.machine machine
def readyInput (bits : List Bool) : Fin 3→List Bool:=Fin.addCases (motive:=fun _ : Fin (2+1)=>List Bool)
  (input bits) (fun _=>[])
theorem ready (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun readyMachine 8 (readyInput bits) out ∧ out 1=word bits:=by
  obtain ⟨base,hb,hs,hword⟩:=raw_run bits
  obtain ⟨r,hr,ht,_,hh,hsteps,_⟩:=Rewind.Workspace.reset_workspace machine _ _ base hb 0
  have hbound:2*base.steps+2 ≤ 8:=by split_ifs at hs <;> omega
  change run readyMachine (2*base.steps+2) (readyInput bits)=some r at hr
  have more:=run_moreFuel readyMachine _ (8-(2*base.steps+2)) (readyInput bits) r hr
  rw [Nat.add_sub_of_le hbound] at more
  exact ⟨r.final.tapes,⟨r,more,rfl,hh,hsteps.le.trans hbound⟩,(ht 1).trans hword⟩
end Zero

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeWord
