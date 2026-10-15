import Proof.PCP.PCPPNativeNaturalAppend
import Proof.PCP.ProjectionNormalizationConstants
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.Assembly.ClosureBinarySerialization

/-! The physical cache prefix consumed by the complete assignment loop:
runtime native cardinality followed by the false sentinel's zero weights
and target. Only the zero/one words are in the finite program; the pool
cardinality and residual arity are runtime unary inputs. All actual private
header state is retained explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCachePrefix
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation RepairSource.CloseoutFinal.C10SupplierRowInput
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding

theorem literal_run (bits out : List Bool) :
    Step (HierarchyFixedWord.raw bits) bits.length (fun _=>out.length) (fun _=>out)
      (fun _=>(out++bits).length) (fun _=>out++bits) := by
  obtain ⟨r,hr,hf,_⟩ := Constants.write_run bits out
  have h:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  simpa only [Constants.cfg,List.take_zero,List.append_nil,Nat.add_zero,List.take_length,
    List.length_append] using h

noncomputable def zeros := CloseoutRowsDegreeLoop.machine (HierarchyFixedWord.raw (intWord 0))
noncomputable def zeroEntry (_j : Nat) (out : List Bool) :=
  (⟨(HierarchyFixedWord.raw (intWord 0)).start,fun _=>out.length,fun _=>out⟩ :
    Configuration 1 ((intWord 0).length+1))
def zeroWord (n : Nat) := (List.replicate n (intWord 0)).flatten

theorem zeros_run (n : Nat) (out : List Bool) :
    Step zeros (n*((intWord 0).length+3)+3) ![out.length,1]
      ![out,CompareMachine.word n] ![(out++zeroWord n).length,1]
      ![out++zeroWord n,CompareMachine.word n] := by
  obtain ⟨r,hr,hf,_⟩ := CloseoutRowsDegreeLoop.loop_run
    (HierarchyFixedWord.raw (intWord 0)) zeroEntry (fun _=>intWord 0)
    (intWord 0).length n (by intros;rfl) (by intros;exact literal_run _ _) out
  have word : (List.range n).flatMap (fun _=>intWord (0 : Int))=zeroWord n := by
    simp [List.flatMap,zeroWord]
  rw [word] at hf
  have h:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

noncomputable def headerResult (N : Nat) (out : List Bool) :=
  Classical.choose (PCPPNativeNaturalAppend.append_run N out)
theorem header_spec (N : Nat) (out : List Bool) :
    Step PCPPNativeNaturalAppend.machine (PCPPNativeNaturalAppend.budget N)
      (PCPPNativeNaturalAppend.heads out) (PCPPNativeNaturalAppend.data N out)
      (headerResult N out).final.heads (headerResult N out).final.tapes ∧
    (headerResult N out).final.tapes 17=out++natWord N ∧
    (headerResult N out).final.heads 17=(out++natWord N).length := by
  have h:=Classical.choose_spec (PCPPNativeNaturalAppend.append_run N out)
  exact ⟨Step.of_run h.1 rfl rfl,h.2.2.1,h.2.2.2.1⟩

def loopSlots : Fin 2→Fin 19 := ![17,18]
def targetSlot : Fin 1→Fin 19 := fun _=>17
noncomputable def first := TapeEmbedding.machine 1 PCPPNativeNaturalAppend.machine
noncomputable def middle := RecoveryFocus.machine loopSlots zeros
noncomputable def last := RecoveryFocus.machine targetSlot (HierarchyFixedWord.raw (intWord 1))
noncomputable def machine := Composition.machine (Composition.machine first middle) last
def inputHeads (out : List Bool) : Fin 19→Nat :=
  Fin.addCases (m:=18) (n:=1) (motive:=fun _=>Nat) (PCPPNativeNaturalAppend.heads out) (fun _=>1)
def input (N n : Nat) (out : List Bool) : Fin 19→List Bool :=
  Fin.addCases (m:=18) (n:=1) (motive:=fun _=>List Bool)
    (PCPPNativeNaturalAppend.data N out) (fun _=>CompareMachine.word n)
noncomputable def headerHeads (N : Nat) (out : List Bool) : Fin 19→Nat :=
  Fin.addCases (m:=18) (n:=1) (motive:=fun _=>Nat) (headerResult N out).final.heads (fun _=>1)
noncomputable def headerData (N n : Nat) (out : List Bool) : Fin 19→List Bool :=
  Fin.addCases (m:=18) (n:=1) (motive:=fun _=>List Bool)
    (headerResult N out).final.tapes (fun _=>CompareMachine.word n)
def replace {α : Type} (A : Fin 19→α) (v : α) := fun i=>if i=17 then v else A i
def prefixWord (N n : Nat) := natWord N++exactWord (falseGate n)
def budget (N n : Nat) := PCPPNativeNaturalAppend.budget N+1+
  (n*((intWord 0).length+3)+3)+1+(intWord 1).length

theorem false_word (n : Nat) : exactWord (falseGate n)=zeroWord n++intWord 1 := by
  simp [exactWord,falseGate,zeroWord,List.flatMap]

theorem run (N n : Nat) (out : List Bool) :
    Step machine (budget N n) (inputHeads out) (input N n out)
      (replace (headerHeads N out) (out++prefixWord N n).length)
      (replace (headerData N n out) (out++prefixWord N n)) := by
  obtain ⟨h,hword,hhead⟩:=header_spec N out
  have firstRun:=h.embed (fun _ : Fin 1=>1) (fun _=>CompareMachine.word n)
  let pre:=out++natWord N
  let H:=headerHeads N out
  let A:=headerData N n out
  have hh : H 17=pre.length:=hhead
  have ht : A 17=pre:=hword
  have z:=(zeros_run n pre).dock loopSlots (by decide) H A
    (by intro i;fin_cases i;exact hh;rfl)
    (by intro i;fin_cases i;exact ht;rfl)
  have zH : dockH loopSlots H (![(pre++zeroWord n).length,1] : Fin 2→Nat)=
      replace H (pre++zeroWord n).length := by
    funext i;by_cases hi:i=17
    · subst i;exact dockH_slot loopSlots (by decide) H _ 0
    · by_cases h18:i=18
      · subst i;exact dockH_slot loopSlots (by decide) H _ 1
      · simpa only [replace,if_neg hi] using dockH_other loopSlots H
          (![ (pre++zeroWord n).length,1] : Fin 2→Nat) i
          (by intro j;fin_cases j;exact Ne.symm hi;exact Ne.symm h18)
  have zA : install loopSlots A (![pre++zeroWord n,CompareMachine.word n] : Fin 2→List Bool)=
      replace A (pre++zeroWord n) := by
    apply HierarchyAllocation.install_eq loopSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      have h17 : i≠17:=fun h=>hi 0 (by subst i;rfl)
      simp only [replace,if_neg h17]
  have mid:=z.congr zH zA
  have t:=(literal_run (intWord 1) (pre++zeroWord n)).dock targetSlot (by decide)
    (replace H (pre++zeroWord n).length) (replace A (pre++zeroWord n))
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
  have tH : dockH targetSlot (replace H (pre++zeroWord n).length)
      (fun _=>(pre++zeroWord n++intWord 1).length)=
      replace H (pre++zeroWord n++intWord 1).length := by
    funext i;by_cases hi:i=17
    · subst i;exact dockH_slot targetSlot (by decide) _ _ 0
    · simpa only [replace,if_neg hi] using dockH_other targetSlot
        (replace H (pre++zeroWord n).length) (fun _=>(pre++zeroWord n++intWord 1).length)
        i (by intro j;exact Ne.symm hi)
  have tA : install targetSlot (replace A (pre++zeroWord n))
      (fun _=>pre++zeroWord n++intWord 1)=replace A (pre++zeroWord n++intWord 1) := by
    apply HierarchyAllocation.install_eq targetSlot (by decide)
    · intros;rfl
    · intro i hi
      have h17 : i≠17:=fun h=>hi 0 (by subst i;rfl)
      simp only [replace,if_neg h17]
  have joined:=(firstRun.seq mid).seq (t.congr tH tA)
  simpa only [machine,budget,inputHeads,input,first,middle,last,prefixWord,false_word,
    pre,H,A,List.append_assoc] using joined

end NearCubicWires.P1Closure.BinaryCachePrefix
