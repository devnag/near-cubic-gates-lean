import Proof.Hierarchy.CompetitorMonomialFields

/-! Two physical clears used by the scalar fold: the non-accumulator
workspace before each term, and the three old accumulator cells before
copyback. Both use the same retained unary driver and reset word. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {k : ℕ} (slot : Fin k → Fin 88) : Fin (k+2) → Fin 88 :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => Fin 88)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => Fin 88) slot (fun _ => 84)) (fun _ => 85)
def eraseInput {k : ℕ} (cap : ℕ) (backing : Fin k → List Bool) : Fin (k+2) → List Bool :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => List Bool)
      backing (fun _ => List.replicate cap true)) (fun _ => List.replicate (cap+1) false)
noncomputable def clearProgram {k : ℕ} (slot : Fin k → Fin 88) :=
  RecoveryFocus.machine (extend slot) (RecoveryScratchErase.resetMachine k)
noncomputable def cleared {k : ℕ} (cap : ℕ) (slot : Fin k → Fin 88)
    (ambient : Fin 88 → List Bool) : Fin 88 → List Bool := fun i =>
  if ∃ j,slot j=i then List.replicate cap false else ambient i

theorem extend_cases {k : ℕ} (slot : Fin k → Fin 88) (j : Fin (k+2)) :
    extend slot j=if h : j.val<k then slot ⟨j.val,h⟩ else if j.val=k then 84 else 85 := by
  refine Fin.addCases (m := k+1) (n := 1) ?_ ?_ j
  · intro i
    refine Fin.addCases (m := k) (n := 1) ?_ ?_ i
    · intro a
      simp [extend,a.isLt]
    · intro a
      fin_cases a
      simp [extend]
  · intro i
    fin_cases i
    simp [extend]

theorem extend_injective {k : ℕ} (slot : Fin k → Fin 88)
    (hi : Function.Injective slot) (h84 : ∀ j,slot j≠84) (h85 : ∀ j,slot j≠85) :
    Function.Injective (extend slot) := by
  intro i j h
  rw [extend_cases,extend_cases] at h
  split_ifs at h with hi' hj' hj90 hi90 hj' hj90
  · have he := hi h
    exact Fin.ext (congrArg (fun a : Fin k => a.val) he)
  · exact False.elim (h84 _ h)
  · exact False.elim (h85 _ h)
  · exact False.elim (h84 _ h.symm)
  · exact Fin.ext (by omega)
  · have hv := congrArg Fin.val h
    change (84 : ℕ)=85 at hv
    omega
  · exact False.elim (h85 _ h.symm)
  · have hv := congrArg Fin.val h
    change (85 : ℕ)=84 at hv
    omega
  · exact Fin.ext (by omega)

theorem clear_run {k : ℕ} (slot : Fin k → Fin 88) (hi : Function.Injective slot)
    (h74 : ∀ j,slot j≠74) (h79 : ∀ j,slot j≠79) (h84 : ∀ j,slot j≠84) (h85 : ∀ j,slot j≠85)
    (cap outPos pos : ℕ) (ambient : Fin 88 → List Bool)
    (hd : ambient 84=List.replicate cap true) (hr : ambient 85=List.replicate (cap+1) false)
    (hb : ∀ j,(ambient (slot j)).length≤cap) :
    ∃ r : ExecutionReceipt 88 4,
      runFrom (clearProgram slot) (2*cap+4) (cfg outPos (clearProgram slot).start pos ambient)=some r ∧
      r.final.heads=heads outPos pos ∧ r.final.tapes=cleared cap slot ambient ∧ r.steps=2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine k) (2*cap+4)
      (eraseInput cap (fun j => ambient (slot j))) (eraseInput cap (fun _ => List.replicate cap false)) := by
    simpa only [eraseInput,max_self] using RecoveryScratchErase.erase_ready cap (cap+1) _ hb
  have hh : ∀ j,heads outPos pos (extend slot j)=0 := by
    intro j
    rw [extend_cases]
    split
    · have hn : (slot ⟨j.val,‹j.val<k›⟩).val≠79 := fun h => h79 _ (Fin.ext h)
      have hnOut : (slot ⟨j.val,‹j.val<k›⟩).val≠74 := fun h => h74 _ (Fin.ext h)
      simp [heads,hn,hnOut]
    · split <;> rfl
  have ht : ∀ j,ambient (extend slot j)=eraseInput cap (fun j => ambient (slot j)) j := by
    intro j
    refine Fin.addCases (m := k+1) (n := 1) ?_ ?_ j
    · intro i
      refine Fin.addCases (m := k) (n := 1) ?_ ?_ i
      · intro a; simp [extend,eraseInput]
      · intro a; fin_cases a; simpa [extend,eraseInput] using hd
    · intro i; fin_cases i; simpa [extend,eraseInput] using hr
  obtain ⟨r,hrun,hheads,htapes,hsteps⟩ := HierarchyBinary.focused_run (extend slot)
    (extend_injective slot hi h84 h85) _ _ _ ready (heads outPos pos) ambient hh ht
  refine ⟨r,hrun,hheads,?_,hsteps⟩
  rw [htapes]
  funext i
  by_cases hsome : ∃ j,slot j=i
  · obtain ⟨j,hj⟩ := hsome
    have hsome' : ∃ a,slot a=i := ⟨j,hj⟩
    rw [cleared,if_pos hsome']
    subst i
    simpa [extend,eraseInput] using install_slot (extend slot) (extend_injective slot hi h84 h85) ambient
      (eraseInput cap (fun _ => List.replicate cap false)) ((j.castAdd 1).castAdd 1)
  · rw [cleared,if_neg hsome]
    by_cases h84' : i=84
    · subst i
      have he := install_slot (extend slot) (extend_injective slot hi h84 h85) ambient
        (eraseInput cap (fun _ => List.replicate cap false)) ((0 : Fin 1).natAdd k |>.castAdd 1)
      simp only [extend,eraseInput,Fin.addCases_left,Fin.addCases_right] at he
      exact he.trans hd.symm
    · by_cases h85' : i=85
      · subst i
        have he := install_slot (extend slot) (extend_injective slot hi h84 h85) ambient
          (eraseInput cap (fun _ => List.replicate cap false)) ((0 : Fin 1).natAdd (k+1))
        simp only [extend,eraseInput,Fin.addCases_right] at he
        exact he.trans hr.symm
      · apply install_other
        intro j he
        rw [extend_cases] at he
        split_ifs at he
        · exact hsome ⟨_,he⟩
        · exact h84' he.symm
        · exact h85' he.symm

def workSlot (j : Fin 81) : Fin 88 :=
  if j.val<74 then ⟨j.val,by omega⟩ else if j.val<78 then ⟨j.val+1,by omega⟩
  else if j.val=78 then 80 else ⟨j.val+7,by omega⟩

theorem work_injective : Function.Injective workSlot := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [workSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem work_range (j : Fin 81) : (workSlot j).val<79 ∧ workSlot j≠74 ∨
    workSlot j=80 ∨ workSlot j=86 ∨ workSlot j=87 := by
  fin_cases j <;> decide

theorem work_avoids (j : Fin 81) (i : Fin 88)
    (hi : i=74 ∨ i=79 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85) : workSlot j≠i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [workSlot] at hv
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    split_ifs at hv <;> (try simp only at hv) <;> omega

theorem work_image (i : Fin 88)
    (hi : i.val<79 ∧ i≠74 ∨ i=80 ∨ i=86 ∨ i=87) : ∃ j,workSlot j=i := by
  rcases hi with ⟨hlt,hne⟩|rfl|rfl|rfl
  · have h74 : i.val≠74 := fun h => hne (Fin.ext h)
    by_cases hlo : i.val<74
    · exact ⟨⟨i.val,by omega⟩,by apply Fin.ext; simp [workSlot,hlo]⟩
    · refine ⟨⟨i.val-1,by omega⟩,?_⟩
      apply Fin.ext
      simp [workSlot,show ¬i.val-1<74 by omega,show i.val-1<78 by omega]
      omega
  · exact ⟨78,rfl⟩
  · exact ⟨79,rfl⟩
  · exact ⟨80,rfl⟩

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
