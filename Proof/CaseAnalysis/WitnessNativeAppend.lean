import Proof.CaseAnalysis.WitnessNodeGuard
import Proof.PCP.PCPPQueryField

/-! Reuse the native field copier directly. Even an unaccepted natural's
payload has a bounded unary bit-length header; it is never expanded to a
unary numeric value merely to append its descriptor bytes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeAppend
open LocalBitMultitape RecoveryExecution RadixSemantics StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payload (bits : List Bool):=if bits=[] then [false] else bits
theorem word_format (bits : List Bool) : NativeWord.word bits=
    List.replicate (payload bits).length true++false::payload bits:=by
  cases bits with
  | nil=>rfl
  | cons b bits=>simp [payload,NativeWord.word,NativeWord.rawWord,MatrixNaturalHeader.header,List.append_assoc]
theorem payload_bound (bits : List Bool) : (payload bits).length ≤ bits.length+1:=by
  cases bits <;> simp [payload]
theorem word_length (bits : List Bool) : (NativeWord.word bits).length=2*(payload bits).length+1:=by
  rw [word_format]
  simp
  omega

abbrev machine:=PCPPQueryField.machine true
def entry (bits backing out : List Bool):=PCPPQueryField.cfg 0 (NativeWord.word bits) 0 backing 0 out
def result (bits backing out : List Bool) : Configuration 3 4:=
  ⟨3,![(NativeWord.word bits).length,0,(out++NativeWord.word bits).length],
    ![NativeWord.word bits,overlay (UnaryTemplate.tape (payload bits).length) backing,out++NativeWord.word bits]⟩

theorem append_run (bits backing out : List Bool) : ∃ r,
    runFrom machine (2*bits.length+5) (entry bits backing out)=some r ∧
      r.final=result bits backing out ∧ r.steps ≤ 2*bits.length+5:=by
  obtain ⟨r,hr,hf,hs⟩:=PCPPQueryField.field_run true [] (payload bits) [] backing out
  have hword:=word_format bits
  simp only [List.nil_append,List.append_nil,←hword] at hr hf
  have ht:2*(payload bits).length+3 ≤ 2*bits.length+5:=by have h:=payload_bound bits;omega
  have more:=runFrom_moreFuel machine (2*(payload bits).length+3)
    (2*bits.length+5-(2*(payload bits).length+3)) (entry bits backing out) r hr
  rw [Nat.add_sub_of_le ht] at more
  refine ⟨r,more,?_,hs.le.trans ht⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i
    · simpa [PCPPQueryField.payload,PCPPQueryField.cfg,result] using (word_length bits).symm
    · rfl
    · simp [PCPPQueryField.payload,PCPPQueryField.cfg,PCPPQueryField.selected,result]
  · funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeAppend
