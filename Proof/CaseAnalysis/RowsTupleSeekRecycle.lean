import Proof.CaseAnalysis.RowsTupleSeekReuseLayout

/-! Recycle the actual parser scratch using its paid capacity. The theorem
is symbolic in the worker's finite control and retains every live field. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem recycle_run {s : ℕ} (p : Machine 20 s) (fuel C : ℕ)
    (H H' : Fin 20 → ℕ) (A A' : Fin 20 → List Bool) (r : ExecutionReceipt 20 s)
    (hr : runFrom p fuel ⟨p.start,H,A⟩=some r)
    (hH : ∀ i,privateTapes i=true → H i=0)
    (hA : ∀ i,privateTapes i=true → A i=[])
    (hH' : ∀ i,privateTapes i=true → H' i=0)
    (hp : ∀ i,privateTapes i=false → r.final.heads i=H' i ∧ r.final.tapes i=A' i)
    (hC : r.steps+1 ≤ C) :
    Step (recycle p) (4*C+7) (reuseHeads H) (reuseData C A) (reuseHeads H') (reuseData C A') := by
  obtain ⟨m,hm,ms,mh,mt,ml,mlh,mlt⟩ := PaddedReset.reset_run p privateTapes fuel C
    ⟨p.start,H,A⟩ r hr hH (by intro i hi;change (A i).length ≤ C;rw [hA i hi];simp) hC
  have entry : PaddedReset.entry privateTapes C (⟨p.start,H,A⟩ : Configuration 20 s)=
      ⟨(MaskedReset.machine p privateTapes).start,
        Fin.addCases H (fun _ : Fin 1 => 0),
        Fin.addCases (cleanData C A) (fun _ : Fin 1 => List.replicate C false)⟩ := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m:=20) (n:=1) (fun j => ?_) (fun j => ?_) i
      · simp only [PaddedReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
          Fin.addCases_left,Rewind.Workspace.capacities,ZeroPadding.pad_zero]
        cases hj:privateTapes j
        · simp [cleanData,PaddedReset.pads,hj,ZeroPadding.pad_zero]
        · simp [cleanData,PaddedReset.pads,hj,hA j hj,ZeroPadding.pad]
      · fin_cases j
        simp [PaddedReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
          Rewind.Workspace.capacities,ZeroPadding.pad,Fin.addCases]
  rw [entry] at hm
  have first := (Step.of_run hm rfl rfl).embed (fun _ : Fin 2 => 0)
    ![List.replicate C true,List.replicate (C+1) false]
  let midH : Fin 23 → ℕ := Fin.addCases (m:=21) (n:=2) (motive:=fun _=>ℕ) m.final.heads (fun _=>0)
  let midA : Fin 23 → List Bool := Fin.addCases (m:=21) (n:=2) (motive:=fun _=>List Bool)
    m.final.tapes ![List.replicate C true,List.replicate (C+1) false]
  let backing : Fin 13 → List Bool := fun i => m.final.tapes ⟨i.val+1,by omega⟩
  have bound (i : Fin 13) : (backing i).length ≤ C := by
    exact ml ⟨i.val+1,by omega⟩ (by simp [privateTapes];omega)
  have erase := Step.of_ready (RecoveryScratchErase.erase_ready C (C+1) backing bound)
  have privateHead (i : Fin 13) : m.final.heads ⟨i.val+1,by omega⟩=0 := by
    change m.final.heads ((⟨i.val+1,by omega⟩ : Fin 20).castAdd 1)=0
    rw [mh]
    have hi : privateTapes ⟨i.val+1,by omega⟩=true := by simp [privateTapes];omega
    rw [hi];rfl
  have outside (i : Fin 20) (hi : privateTapes i=false) :
      reuseHeads H' (i.castAdd 3)=midH (i.castAdd 3) ∧
      reuseData C A' (i.castAdd 3)=midA (i.castAdd 3) := by
    rw [show i.castAdd 3=(i.castAdd 1).castAdd 2 from Fin.ext rfl]
    simp only [reuseHeads,reuseData,midH,midA,Fin.addCases_left]
    rw [mh,mt]
    simpa [cleanData,hi,PaddedReset.pads,ZeroPadding.pad_zero] using
      And.intro (hp i hi).1.symm (hp i hi).2.symm
  have last := dock_exact erase eraseSlots (by decide) midH (reuseHeads H') midA (reuseData C A')
    (by intro j
        refine Fin.addCases (m:=13) (n:=2) (fun i=>?_) (fun i=>?_) j
        · simpa [midH,eraseSlots,Fin.addCases,show i.val+1 < 21 by omega] using privateHead i
        · fin_cases i <;> rfl)
    (by intro j;fin_cases j <;> rfl)
    (by intro j;fin_cases j <;> simp [reuseHeads,eraseSlots,Fin.addCases]
        all_goals exact hH' _ (by decide))
    (by intro j;fin_cases j <;> simp [reuseData,cleanData,privateTapes,eraseSlots,Fin.addCases])
    (by intro i hi;fin_cases i
        · exact outside 0 (by decide)
        · exact False.elim (hi 0 rfl)
        · exact False.elim (hi 1 rfl)
        · exact False.elim (hi 2 rfl)
        · exact False.elim (hi 3 rfl)
        · exact False.elim (hi 4 rfl)
        · exact False.elim (hi 5 rfl)
        · exact False.elim (hi 6 rfl)
        · exact False.elim (hi 7 rfl)
        · exact False.elim (hi 8 rfl)
        · exact False.elim (hi 9 rfl)
        · exact False.elim (hi 10 rfl)
        · exact False.elim (hi 11 rfl)
        · exact False.elim (hi 12 rfl)
        · exact outside 14 (by decide)
        · exact outside 15 (by decide)
        · exact outside 16 (by decide)
        · exact outside 17 (by decide)
        · exact outside 18 (by decide)
        · exact outside 19 (by decide)
        · exact ⟨mlh.symm,mlt.symm⟩
        · exact False.elim (hi 13 rfl)
        · exact False.elim (hi 14 rfl))
  exact (first.seq last).enlarge (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
