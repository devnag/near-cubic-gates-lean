import Proof.CaseAnalysis.RowsOriginalPairClean
import Proof.CaseAnalysis.RowsTupleSeekCount
import Proof.MachineModel.Encoding

/-! One retained original proof-coordinate emits its unary factor index.
The paid return keeps the index available for repeated template factors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBlock
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsTupleSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark (bit : Bool) : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q=0 then some ⟨1,![none,some bit],![.stay,.right]⟩ else none

theorem mark_run (bit : Bool) (source out : List Bool) :
    Step (mark bit) 1 (fieldHeads 0 out) (fieldData source out)
      (fieldHeads 0 (out++[bit])) (fieldData source (out++[bit])) := by
  have hs : step (mark bit) (countCfg 0 source 0 out)=some (countCfg 1 source 0 (out++[bit])) := by
    simp only [step,mark,countCfg,↓reduceIte]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,fieldHeads,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,fieldData,fieldHeads,Streaming.write_append]
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

def raw:=Composition.machine (mark true) (countMachine true)
def machine:=MaskedReset.machine raw (fun i=>decide (i=0))
def heads (out : List Bool) : Fin 3→ℕ:=![0,out.length,0]
def data (C n : ℕ) (out : List Bool) : Fin 3→List Bool:=
  ![ZeroPadding.pad C (List.replicate n true),out,List.replicate C false]

theorem run (C n : ℕ) (out : List Bool) (hc : n+3≤C) :
    Step machine (2*n+8) (heads out) (data C n out)
      (heads (out++ExtIncidence.block n)) (data C n (out++ExtIncidence.block n)) := by
  let tail:=List.replicate (C-n-1) false
  have source : ZeroPadding.pad C (List.replicate n true)=countWord n++tail := by
    unfold ZeroPadding.pad countWord tail
    rw [List.length_replicate]
    have he : C-n=(C-n-1)+1 := by omega
    rw [he,List.replicate_succ]
    simp only [List.append_assoc,List.singleton_append,Nat.add_sub_cancel]
  have last:=count_run true [] tail (out++[true]) n
  simp only [List.nil_append,List.length_nil,Nat.zero_add,selected,↓reduceIte] at last
  rw [←source] at last
  have whole:=(mark_run true (ZeroPadding.pad C (List.replicate n true)) out).seq last
  have reset:=whole.mask (cap:=C) (fun i=>decide (i=0)) (by
    intro i hi
    have he : i=0:=of_decide_eq_true hi
    subst i;rfl) (by omega)
  have result : (out++[true])++countWord n=out++ExtIncidence.block n := by
    simp [countWord,ExtIncidence.block,List.replicate_succ,List.append_assoc]
  rw [result] at reset
  have time : 2*(1+1+(n+1))+2=2*n+8 := by omega
  rw [time] at reset
  apply (reset.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBlock
