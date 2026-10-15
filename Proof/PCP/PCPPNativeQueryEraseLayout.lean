import Proof.PCP.PCPPNativeQueryReuseLayout

/-! Pure coverage and post-sweep identities for the reusable query bank.
No whole controller is unfolded to recover its tape layout. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryReusable
open LocalBitMultitape PCPPNativeQueryReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def erased (G : ℕ) : Fin 165 → List Bool :=
  Fin.addCases (m := 164) (n := 1)
    (Fin.addCases (m := 163) (n := 1) (fun _ => List.replicate G false) (fun _ => List.replicate G true))
    (fun _ => List.replicate (G+1) false)
theorem erase_classify (j : Fin 165) :
    (eraseSlots j).val=1 ∨ (6 ≤ (eraseSlots j).val ∧ (eraseSlots j).val≠120) := by
  unfold eraseSlots
  split_ifs
  · exact Or.inl rfl
  · right
    change 6 ≤ j.val+5 ∧ j.val+5≠120
    have hn : j.val≠0 := by intro h; apply ‹¬j=0›; apply Fin.ext; exact h
    omega
  · right
    change 6 ≤ j.val+6 ∧ j.val+6≠120
    omega
theorem erase_work (j : Fin 163) :
    ((eraseSlots (j.castAdd 2)).val=1 ∨ (6 ≤ (eraseSlots (j.castAdd 2)).val ∧ (eraseSlots (j.castAdd 2)).val≠120)) ∧
      (eraseSlots (j.castAdd 2)).val < 169 := by
  refine ⟨erase_classify _,?_⟩
  have hj := j.isLt
  unfold eraseSlots
  simp only [Fin.val_castAdd]
  split_ifs
  · decide
  · change j.val+5 < 169
    omega
  · change j.val+6 < 169
    omega
theorem erase_not_five (j : Fin 165) : eraseSlots j≠5 := by
  intro h
  have hv := congrArg (fun i : Fin 171 => i.val) h
  simp only [eraseSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega
theorem retained_away (j : Fin 6) (k : Fin 165) : eraseSlots k≠resetSlots (retainedSlots j) := by
  intro h
  have hv := congrArg (fun i : Fin 171 => i.val) h
  have hr : (resetSlots (retainedSlots j)).val=0 ∨ (resetSlots (retainedSlots j)).val=2 ∨
      (resetSlots (retainedSlots j)).val=3 ∨ (resetSlots (retainedSlots j)).val=4 ∨
      (resetSlots (retainedSlots j)).val=5 ∨ (resetSlots (retainedSlots j)).val=120 := by
    fin_cases j <;> decide
  have he := erase_classify k
  rw [hv] at he
  omega

theorem coverage (i : Fin 171) :
    (∃ j : Fin 6,resetSlots (retainedSlots j)=i) ∨ ∃ j : Fin 165,eraseSlots j=i := by
  by_cases h0 : i.val=0
  · exact Or.inl ⟨0,Fin.ext h0.symm⟩
  by_cases h2 : i.val=2
  · exact Or.inl ⟨1,Fin.ext h2.symm⟩
  by_cases h3 : i.val=3
  · exact Or.inl ⟨2,Fin.ext h3.symm⟩
  by_cases h4 : i.val=4
  · exact Or.inl ⟨3,Fin.ext h4.symm⟩
  by_cases h5 : i.val=5
  · exact Or.inl ⟨4,Fin.ext h5.symm⟩
  by_cases h120 : i.val=120
  · exact Or.inl ⟨5,Fin.ext h120.symm⟩
  by_cases h1 : i.val=1
  · exact Or.inr ⟨0,Fin.ext h1.symm⟩
  by_cases hl : i.val < 120
  · let j : Fin 165 := ⟨i.val-5,by omega⟩
    have hj0 : j≠0 := by intro h; have hv : i.val-5=0 := congrArg (fun k : Fin 165 => k.val) h; omega
    have hjl : j.val < 115 := by change i.val-5 < 115; omega
    refine Or.inr ⟨j,?_⟩
    apply Fin.ext
    simp only [eraseSlots,hj0,hjl,ite_false,ite_true]
    change i.val-5+5=i.val
    omega
  · let j : Fin 165 := ⟨i.val-6,by omega⟩
    have hj0 : j≠0 := by intro h; have hv : i.val-6=0 := congrArg (fun k : Fin 165 => k.val) h; omega
    have hjl : ¬j.val < 115 := by change ¬i.val-6 < 115; omega
    refine Or.inr ⟨j,?_⟩
    apply Fin.ext
    simp only [eraseSlots,hj0,hjl,ite_false]
    change i.val-6+6=i.val
    omega

theorem work_data (bits : List Bool) (base C F G : ℕ) (out : List Bool) (i : Fin 171)
    (hi : (i.val=1 ∨ (6 ≤ i.val ∧ i.val≠120)) ∧ i.val < 169) :
    data bits [] base C F G out i=List.replicate G false := by
  rcases hi with ⟨hi,hi169⟩
  rcases hi with hi|hi
  · have he : i=1 := Fin.ext hi
    subst i
    exact PCPPNativeNodeReusable.pad_empty G
  · have h0 : i≠0 := by intro h; subst i; omega
    have h1 : i≠1 := by intro h; subst i; omega
    have h2 : i≠2 := by intro h; subst i; omega
    have h3 : i≠3 := by intro h; subst i; omega
    have h4 : i≠4 := by intro h; subst i; omega
    have h5 : i≠5 := by intro h; subst i; omega
    have h120 : i≠120 := by intro h; have hv : i.val=120 := congrArg (fun j : Fin 171 => j.val) h; omega
    have h169 : i≠169 := by intro h; have hv : i.val=169 := congrArg (fun j : Fin 171 => j.val) h; omega
    have h170 : i≠170 := by intro h; have hv : i.val=170 := congrArg (fun j : Fin 171 => j.val) h; omega
    simp only [data,h0,h1,h2,h3,h4,h5,h120,h169,h170,or_self,ite_false]

theorem erased_data (bits : List Bool) (base C F G : ℕ) (out : List Bool) (j : Fin 165) :
    erased G j=data bits [] base C F G out (eraseSlots j) := by
  refine Fin.addCases (m := 163) (n := 2) (fun i => ?_) (fun i => ?_) j
  · change erased G ((i.castAdd 1).castAdd 1)=_
    simp only [erased,Fin.addCases_left]
    exact (work_data bits base C F G out _ (erase_work i)).symm
  · fin_cases i <;> rfl
theorem retained_layout (bits : List Bool) (base C F G : ℕ) (out : List Bool) (j : Fin 6) :
    heads out (resetSlots (retainedSlots j))=retainedHeads out j ∧
      data bits [] base C F G out (resetSlots (retainedSlots j))=retainedData bits base C F out j := by
  fin_cases j <;> exact ⟨rfl,rfl⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQueryReusable
