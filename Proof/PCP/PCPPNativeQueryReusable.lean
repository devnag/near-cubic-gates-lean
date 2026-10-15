import Proof.PCP.PCPPNativeQueryEraseLayout

/-! The full original-query emitter is now physically reusable. The actual
G-driven sweep erases its old projection row and parser work after the paid
selective reset, while retaining the original descriptor and new DAG base. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryReusable
open LocalBitMultitape SourceInterfaces RecoveryRootRound PCPPNativeNodeMachine PCPPNativeQueryReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget {n : ℕ} (base C F G : ℕ) (oracle : BooleanCircuit n) :=
  2*PCPPNativeQueryStep.budget base C F oracle+2*G+7

theorem query_run {n r : ℕ} (base C F G : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hw : PCPPNativeNodeLoop.workspace base 0 C F projection oracle.nodes)
    (hC : PCPPNativeAddressAppend.budget base oracle.output.val+1 ≤ C) (hF : base+2*oracle.size+1 ≤ F)
    (hG : PCPPNativeQueryStep.budget base C F oracle+1 ≤ G) (hFG : F+1 ≤ G)
    (hrow : (rowCache projection).length ≤ G) :
    ∃ result,runFrom machine (budget base C F G oracle)
      (entry (PCPPNative.descriptor oracle) (rowCache projection) base C F G out)=some result ∧
      result.steps ≤ budget base C F G oracle ∧
      result.final.heads=heads (out++PCPPNativeQuery.emitted base oracle projection) ∧
      result.final.tapes=data (PCPPNative.descriptor oracle) [] (base+2*oracle.size+1) C F G
        (out++PCPPNativeQuery.emitted base oracle projection) := by
  obtain ⟨reset,hr,rs,ret,work⟩ := reset_run base C F G oracle projection out hCF hw hC hF hG hFG hrow
  obtain ⟨a,ha,_,asteps,ah,atapes,akeep⟩ := RecoveryFocus.dock resetSlots
    (by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 171 => k.val) h)
    PCPPNativeQueryReset.machine _ (heads out) (data (PCPPNative.descriptor oracle) (rowCache projection) base C F G out) _
    (fun j => (reset_input _ _ base C F G out hFG j).1)
    (fun j => (reset_input _ _ base C F G out hFG j).2) reset hr
  have kept (j : Fin 6) :
      a.final.heads (resetSlots (retainedSlots j))=retainedHeads (out++PCPPNativeQuery.emitted base oracle projection) j ∧
      a.final.tapes (resetSlots (retainedSlots j))=retainedData (PCPPNative.descriptor oracle) (base+2*oracle.size+1) C F
        (out++PCPPNativeQuery.emitted base oracle projection) j :=
    ⟨(ah _).trans (ret j).1,(atapes _).trans (ret j).2⟩
  let backing : Fin 163 → List Bool := fun j => a.final.tapes (eraseSlots (j.castAdd 2))
  have scratch (j : Fin 163) :
      a.final.heads (eraseSlots (j.castAdd 2))=0 ∧ (backing j).length ≤ G := by
    let k : Fin 169 := ⟨(eraseSlots (j.castAdd 2)).val,(erase_work j).2⟩
    have he : eraseSlots (j.castAdd 2)=resetSlots k := Fin.ext rfl
    have hk := work k (erase_work j).1
    exact ⟨by rw [he,ah]; exact hk.1,by unfold backing; rw [he,atapes]; exact hk.2⟩
  have outside169 := akeep 169 (by intro j; apply Fin.ne_of_val_ne; change j.val≠169; omega)
  have outside170 := akeep 170 (by intro j; apply Fin.ne_of_val_ne; change j.val≠170; omega)
  have hin (j : Fin 165) : a.final.tapes (eraseSlots j)=
      (Fin.addCases (m := 164) (n := 1) (motive := fun _ : Fin 165 => List Bool)
        (Fin.addCases (m := 163) (n := 1) (motive := fun _ : Fin 164 => List Bool) backing (fun _ => List.replicate G true))
        (fun _ => List.replicate (G+1) false)) j := by
    refine Fin.addCases (m := 164) (n := 1) (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (m := 163) (n := 1) (fun k => ?_) (fun k => ?_) i
      · simp only [Fin.addCases_left]
        rfl
      · fin_cases k; exact outside169.2
    · fin_cases i; exact outside170.2
  have hheads (j : Fin 165) : a.final.heads (eraseSlots j)=0 := by
    refine Fin.addCases (m := 164) (n := 1) (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (m := 163) (n := 1) (fun k => ?_) (fun k => ?_) i
      · exact (scratch k).1
      · fin_cases k; exact outside169.1
    · fin_cases i; exact outside170.1
  have ready := RecoveryScratchErase.erase_ready G (G+1) backing (fun j => (scratch j).2)
  obtain ⟨b,hb,bh,bt,bs⟩ := ready.focus_at eraseSlots erase_injective a.final.heads a.final.tapes hin hheads
  have btapes : b.final.tapes=install eraseSlots a.final.tapes (erased G) := by
    rw [bt]
    apply congrArg (install eraseSlots a.final.tapes)
    unfold erased
    simp only [max_self]
  let result := Composition.joinedReceipt a b
  have hr := Composition.run_join first last _ _ _ a b ha hb
  have htime : 2*PCPPNativeQueryStep.budget base C F oracle+2+1+(2*G+4)=budget base C F G oracle := by
    unfold budget; omega
  rw [htime] at hr
  refine ⟨result,hr,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega
  · change b.final.heads=_
    rw [bh]
    funext i
    rcases coverage i with ⟨j,rfl⟩|⟨j,rfl⟩
    · exact (kept j).1.trans (retained_layout (PCPPNative.descriptor oracle) (base+2*oracle.size+1) C F G
        (out++PCPPNativeQuery.emitted base oracle projection) j).1.symm
    · rw [hheads]
      simp only [heads,erase_not_five,ite_false]
  · change b.final.tapes=_
    rw [btapes]
    funext i
    rcases coverage i with ⟨j,rfl⟩|⟨j,rfl⟩
    · rw [install_other eraseSlots _ _ _ (retained_away j)]
      exact (kept j).2.trans (retained_layout (PCPPNative.descriptor oracle) (base+2*oracle.size+1) C F G
        (out++PCPPNativeQuery.emitted base oracle projection) j).2.symm
    · rw [install_slot eraseSlots erase_injective]
      exact erased_data (PCPPNative.descriptor oracle) (base+2*oracle.size+1) C F G
        (out++PCPPNativeQuery.emitted base oracle projection) j

end NearCubicWires.RepairOrdinary.PCPPNativeQueryReusable
