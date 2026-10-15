import Proof.PCP.PCPPNativeHierarchyReady

/-! The isolated false padding nodes are physically printed by a fixed
literal body and the actual unary padding count. The DAG prefix stays live. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativePadding
open LocalBitMultitape SourceInterfaces RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroNode := PCPPRequestNodeSchema.native (.const false : BooleanNode 0)
theorem zeroNode_length : zeroNode.length=9 := by decide
theorem zeroNode_eq (n : ℕ) : zeroNode=PCPPRequestNodeSchema.native (.const false : BooleanNode n) := rfl
noncomputable def machine := RepeatMachine.machine (HierarchyFixedWord.raw zeroNode) (fun _ _ => true)
noncomputable def configuration (phase : Fin 5) (out : List Bool) (count : ℕ) :=
  RepeatMachine.cfg phase (Constants.cfg zeroNode out 0 (by omega)) count 1
def emitted (count : ℕ) := (List.replicate count zeroNode).flatten
theorem iterate_append (n : ℕ) (out : List Bool) :
    RepeatMachine.iterate (fun bits => (true,bits++zeroNode)) n out=(true,out++emitted n) := by
  induction n generalizing out with
  | zero => simp [RepeatMachine.iterate,emitted]
  | succ n ih => simp [RepeatMachine.iterate,ih,emitted,List.replicate_succ,List.append_assoc]

theorem count_run (out : List Bool) (count : ℕ) :
    ∃ result,runFrom machine (12*count+3) (configuration 0 out count)=some result ∧
      result.steps ≤ 12*count+3 ∧ result.final=configuration 3 (out++emitted count) count := by
  have supplier : ∀ out : List Bool,True → ∃ result,
      runFrom (HierarchyFixedWord.raw zeroNode) 9 (Constants.cfg zeroNode out 0 (by omega))=some result ∧
      result.steps ≤ 9 ∧ result.final.heads=(Constants.cfg zeroNode (out++zeroNode) 0 (by omega)).heads ∧
      result.final.tapes=(Constants.cfg zeroNode (out++zeroNode) 0 (by omega)).tapes ∧
      (true : Bool)=true ∧ ((true : Bool)=true → True) := by
    intro out _
    obtain ⟨result,hr,hf,hs⟩ := Constants.write_run zeroNode out
    refine ⟨result,hr,hs.le,?_,?_,rfl,fun _ => trivial⟩
    · rw [hf]
      funext i
      simp [Constants.cfg]
    · rw [hf]
      funext i
      simp [Constants.cfg]
  obtain ⟨result,hr,hs,hf⟩ := RepeatMachine.repeat_run (HierarchyFixedWord.raw zeroNode)
    (fun _ _ => true) (fun out => Constants.cfg zeroNode out 0 (by omega))
    (fun out => (true,out++zeroNode)) (fun _ => True) 9 (fun _ _ => rfl) supplier count out trivial
  rw [iterate_append] at hf
  have ht : count*(9+3)+3=12*count+3 := by omega
  rw [ht] at hr hs
  exact ⟨result,hr,hs,hf⟩

def caps (count : ℕ) : Fin 2 → ℕ := ![0,count+2]
noncomputable def templateConfiguration (phase : Fin 5) (out : List Bool) (count : ℕ) :=
  ZeroPadding.config (caps count) (configuration phase out count)
theorem template_heads (phase : Fin 5) (out : List Bool) (count : ℕ) :
    (templateConfiguration phase out count).heads=![out.length,1] := by
  funext i; fin_cases i <;> rfl
theorem template_tapes (phase : Fin 5) (out : List Bool) (count : ℕ) :
    (templateConfiguration phase out count).tapes=![out,UnaryTemplate.tape count] := by
  funext i
  fin_cases i
  · change ZeroPadding.pad 0 (out++zeroNode.take 0)=out
    simp only [List.take_zero,List.append_nil,ZeroPadding.pad_zero]
  · exact DecompositionSerializerCount.padded_count count
theorem pad_run (out : List Bool) (count : ℕ) :
    ∃ result,runFrom machine (12*count+3) (templateConfiguration 0 out count)=some result ∧
      result.steps ≤ 12*count+3 ∧ result.final=templateConfiguration 3 (out++emitted count) count := by
  obtain ⟨raw,hr,rs,rf⟩ := count_run out count
  obtain ⟨result,run,rfinal,rsteps,_⟩ := ZeroPadding.run_config machine (caps count) _ _ raw hr
  exact ⟨result,run,by omega,by rw [rfinal,rf]; rfl⟩
theorem emitted_nodes (n count : ℕ) : emitted count=
    (List.replicate count (PCPPRequestNodeSchema.native (.const false : BooleanNode n))).flatten := rfl

end NearCubicWires.RepairOrdinary.PCPPNativePadding
