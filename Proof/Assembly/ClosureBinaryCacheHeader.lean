import Proof.Assembly.ClosureBinaryCacheMeasure

/-! A short physical read of the original native count header supplies
the bit-width term used by the exact reusable-bank reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdHeader
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation SignedSortKey

noncomputable def machine := Rewind.machine MatrixDimensionField.machine
def input (source : List Bool) : Fin 7→List Bool := fun i=>if i=0 then source else []
def output (n : Nat) (tail : List Bool) : Fin 7→List Bool :=
  ![natWord n++tail,List.replicate (natBitLength n) true,List.replicate (natBitLength n) true,
    UnaryTemplate.tape (natBitLength n),RepairOrdinary.frame (binary (natBitLength n) n),
    List.replicate (2*natBitLength n+1) false,List.replicate (6*natBitLength n+7) false]
def budget (n : Nat) := 12*natBitLength n+16

theorem run (n : Nat) (tail : List Bool) :
    Step machine (budget n) (fun _=>0) (input (natWord n++tail)) (fun _=>0) (output n tail) := by
  obtain ⟨r,hr,hf,hs⟩ := MatrixDimensionField.field_run [] (binary (natBitLength n) n) tail
  simp only [List.nil_append,List.length_nil,binary_length,Nat.zero_add] at hr hf hs
  have source : List.replicate (natBitLength n) true++false::(binary (natBitLength n) n++tail)=
      natWord n++tail := by simp [WilliamsInputHeader.natWord_eq,List.append_assoc]
  rw [source] at hr hf
  have hi : Composition.leftConfig 4 (MatrixDimensionField.input (natWord n++tail) 0)=
      initialConfiguration MatrixDimensionField.machine
        (![natWord n++tail,[],[],[],[],[]] : Fin 6→List Bool) := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>rfl
  rw [hi] at hr
  obtain ⟨last,hl,hkeep,hlog,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace
    MatrixDimensionField.machine _ _ r hr 0
  have hb : 2*r.steps+2=budget n := by rw [hs];unfold budget;omega
  rw [hb] at hl
  apply (Step.of_run hl (funext hh) rfl).congr_in rfl ?_ |>.congr rfl ?_
  · funext i;fin_cases i <;>rfl
  · funext i
    refine Fin.addCases (m:=6) (n:=1) (fun i=>?_) (fun i=>?_) i
    · rw [hkeep,hf]
      fin_cases i <;>simp [MatrixDimensionField.output,output,binary_length]
    · fin_cases i
      change last.final.tapes 6=List.replicate (6*natBitLength n+7) false
      simpa [hs,Fin.natAdd] using hlog

end NearCubicWires.P1Closure.BinaryCacheColdHeader
