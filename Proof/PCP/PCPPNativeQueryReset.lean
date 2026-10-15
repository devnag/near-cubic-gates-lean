import Proof.PCP.PCPPNativeQueryResetLayout

/-! The paid whole-query reset retains the original descriptor, live output
and actual counters, and bounds every scratch tape for the subsequent sweep. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryReset
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reset_run {n r : ℕ} (base C F G : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hw : PCPPNativeNodeLoop.workspace base 0 C F projection oracle.nodes)
    (hC : PCPPNativeAddressAppend.budget base oracle.output.val+1 ≤ C) (hF : base+2*oracle.size+1 ≤ F)
    (hG : PCPPNativeQueryStep.budget base C F oracle+1 ≤ G) (hFG : F+1 ≤ G)
    (hrow : (rowCache projection).length ≤ G) :
    ∃ result,runFrom machine (2*PCPPNativeQueryStep.budget base C F oracle+2)
      (entry (PCPPNative.descriptor oracle) (rowCache projection) base C F G out)=some result ∧
      result.steps ≤ 2*PCPPNativeQueryStep.budget base C F oracle+2 ∧
      (∀ j,result.final.heads (retainedSlots j)=retainedHeads (out++PCPPNativeQuery.emitted base oracle projection) j ∧
        result.final.tapes (retainedSlots j)=retainedData (PCPPNative.descriptor oracle) (base+2*oracle.size+1) C F
          (out++PCPPNativeQuery.emitted base oracle projection) j) ∧
      (∀ i : Fin 169,i.val=1 ∨ (6 ≤ i.val ∧ i.val≠120) →
        result.final.heads i=0 ∧ (result.final.tapes i).length ≤ G) := by
  obtain ⟨raw,hr,rs,meaning⟩ := PCPPNativeQueryStep.step_run base C F oracle projection out hCF hw hC hF
  have hh : ∀ i,selected i=true → raw.final.heads i ≤ raw.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hr).1 i
    change raw.final.heads i ≤ PCPPNativeQuery.heads 0 out i+raw.steps at h
    simpa only [initial_head out i hi,Nat.zero_add] using h
  obtain ⟨reset,hreset,rf,rsteps,_⟩ := MaskedReset.reset_run
    PCPPNativeQueryStep.machine selected _ _ raw hr hh
  obtain ⟨result,hresult,resultFinal,resultSteps,_⟩ := ZeroPadding.run_config machine (caps G) _ _ reset hreset
  have more := runFrom_moreFuel machine _
    (2*PCPPNativeQueryStep.budget base C F oracle+2-(2*raw.steps+2)) _ result hresult
  rw [Nat.add_sub_of_le (by omega : 2*raw.steps+2 ≤ 2*PCPPNativeQueryStep.budget base C F oracle+2)] at more
  refine ⟨result,more,by rw [resultSteps,rsteps]; omega,?_,?_⟩
  · rw [resultFinal,rf]
    intro j
    fin_cases j
    · change 0=0 ∧ ZeroPadding.pad 0 (raw.final.tapes 0)=PCPPNative.descriptor oracle
      exact ⟨rfl,(ZeroPadding.pad_zero _).trans (meaning 0).2⟩
    · change raw.final.heads 2=0 ∧ ZeroPadding.pad 0 (raw.final.tapes 2)=List.replicate (base+2*oracle.size+1) true
      exact ⟨(meaning 2).1,(ZeroPadding.pad_zero _).trans (meaning 2).2⟩
    · change raw.final.heads 3=0 ∧ ZeroPadding.pad 0 (raw.final.tapes 3)=List.replicate (base+2*oracle.size+1) true
      exact ⟨(meaning 3).1,(ZeroPadding.pad_zero _).trans (meaning 3).2⟩
    · change raw.final.heads 4=0 ∧ ZeroPadding.pad 0 (raw.final.tapes 4)=List.replicate C true
      exact ⟨(meaning 4).1,(ZeroPadding.pad_zero _).trans (meaning 4).2⟩
    · change raw.final.heads 5=(out++PCPPNativeQuery.emitted base oracle projection).length ∧
        ZeroPadding.pad 0 (raw.final.tapes 5)=out++PCPPNativeQuery.emitted base oracle projection
      exact ⟨(meaning 5).1,(ZeroPadding.pad_zero _).trans (meaning 5).2⟩
    · change raw.final.heads 120=0 ∧ ZeroPadding.pad 0 (raw.final.tapes 120)=List.replicate F true
      exact ⟨(meaning 120).1,(ZeroPadding.pad_zero _).trans (meaning 120).2⟩
  · intro i hi
    rw [resultFinal,rf]
    by_cases h168 : i.val < 168
    · let j : Fin 168 := ⟨i.val,h168⟩
      have he : i=j.castAdd 1 := Fin.ext rfl
      have hjwork : work j := hi
      have hsel : selected j=true := by simp only [selected,decide_eq_true_eq]; exact Or.inr hjwork
      have hc := initial_work (PCPPNative.descriptor oracle) (rowCache projection) base C F out j hjwork
      have ht := PCPSerializerReuse.tape_support PCPPNativeQueryStep.machine _ _ raw hr j
        (max (rowCache projection).length (F+1)) 0
        (by change PCPPNativeQuery.heads 0 out j ≤ 0; rw [initial_head out j hsel])
        (hc.trans (le_max_left _ _))
      have hcap : caps G (j.castAdd 1)=G := by
        simp only [caps,Fin.val_castAdd]
        exact if_pos hi
      rw [he]
      simp only [ZeroPadding.config,SelectiveReset.finished,Rewind.config,Fin.addCases_left,hsel,ite_true,hcap,ZeroPadding.pad_length]
      refine ⟨True.intro,max_le le_rfl ?_⟩
      simp only [Nat.zero_add] at ht
      exact ht.trans (max_le (max_le hrow hFG) (by omega))
    · have he : i=(0 : Fin 1).natAdd 168 := Fin.ext (by change i.val=168; omega)
      rw [he]
      change 0=0 ∧ (ZeroPadding.pad G (List.replicate raw.steps false)).length ≤ G
      rw [ZeroPadding.pad_length,List.length_replicate]
      exact ⟨rfl,max_le le_rfl (by omega)⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQueryReset
