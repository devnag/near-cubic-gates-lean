import Proof.Hierarchy.CompetitorReusableSum

/-! Two physical clears used by the scalar fold: the non-accumulator
workspace before each term, and the three old accumulator cells before
copyback. Both use the same retained unary driver and reset word. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) : Fin 94 → ℕ := fun i => if i.val=88 then pos else 0
def cfg {s : ℕ} (q : Fin s) (pos : ℕ) (tapes : Fin 94 → List Bool) : Configuration 94 s :=
  ⟨q,heads pos,tapes⟩
def extend {k : ℕ} (slot : Fin k → Fin 94) : Fin (k+2) → Fin 94 :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => Fin 94)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => Fin 94) slot (fun _ => 90)) (fun _ => 91)
def eraseInput {k : ℕ} (cap : ℕ) (backing : Fin k → List Bool) : Fin (k+2) → List Bool :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => List Bool)
      backing (fun _ => List.replicate cap true)) (fun _ => List.replicate (cap+1) false)
noncomputable def clearProgram {k : ℕ} (slot : Fin k → Fin 94) :=
  RecoveryFocus.machine (extend slot) (RecoveryScratchErase.resetMachine k)
noncomputable def cleared {k : ℕ} (cap : ℕ) (slot : Fin k → Fin 94)
    (ambient : Fin 94 → List Bool) : Fin 94 → List Bool := fun i =>
  if ∃ j,slot j=i then List.replicate cap false else ambient i

theorem extend_cases {k : ℕ} (slot : Fin k → Fin 94) (j : Fin (k+2)) :
    extend slot j=if h : j.val<k then slot ⟨j.val,h⟩ else if j.val=k then 90 else 91 := by
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

theorem extend_injective {k : ℕ} (slot : Fin k → Fin 94)
    (hi : Function.Injective slot) (h90 : ∀ j,slot j≠90) (h91 : ∀ j,slot j≠91) :
    Function.Injective (extend slot) := by
  intro i j h
  rw [extend_cases,extend_cases] at h
  split_ifs at h with hi' hj' hj90 hi90 hj' hj90
  · have he := hi h
    exact Fin.ext (congrArg (fun a : Fin k => a.val) he)
  · exact False.elim (h90 _ h)
  · exact False.elim (h91 _ h)
  · exact False.elim (h90 _ h.symm)
  · exact Fin.ext (by omega)
  · have hv := congrArg Fin.val h
    change (90 : ℕ)=91 at hv
    omega
  · exact False.elim (h91 _ h.symm)
  · have hv := congrArg Fin.val h
    change (91 : ℕ)=90 at hv
    omega
  · exact Fin.ext (by omega)

theorem clear_run {k : ℕ} (slot : Fin k → Fin 94) (hi : Function.Injective slot)
    (h88 : ∀ j,slot j≠88) (h90 : ∀ j,slot j≠90) (h91 : ∀ j,slot j≠91)
    (cap pos : ℕ) (ambient : Fin 94 → List Bool)
    (hd : ambient 90=List.replicate cap true) (hr : ambient 91=List.replicate (cap+1) false)
    (hb : ∀ j,(ambient (slot j)).length≤cap) :
    ∃ r : ExecutionReceipt 94 4,
      runFrom (clearProgram slot) (2*cap+4) (cfg (clearProgram slot).start pos ambient)=some r ∧
      r.final.heads=heads pos ∧ r.final.tapes=cleared cap slot ambient ∧ r.steps=2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine k) (2*cap+4)
      (eraseInput cap (fun j => ambient (slot j))) (eraseInput cap (fun _ => List.replicate cap false)) := by
    simpa only [eraseInput,max_self] using RecoveryScratchErase.erase_ready cap (cap+1) _ hb
  have hh : ∀ j,heads pos (extend slot j)=0 := by
    intro j
    rw [extend_cases]
    split
    · have hn : (slot ⟨j.val,‹j.val<k›⟩).val≠88 := fun h => h88 _ (Fin.ext h)
      simp [heads,hn]
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
    (extend_injective slot hi h90 h91) _ _ _ ready (heads pos) ambient hh ht
  refine ⟨r,hrun,hheads,?_,hsteps⟩
  rw [htapes]
  funext i
  by_cases hsome : ∃ j,slot j=i
  · obtain ⟨j,hj⟩ := hsome
    have hsome' : ∃ a,slot a=i := ⟨j,hj⟩
    rw [cleared,if_pos hsome']
    subst i
    simpa [extend,eraseInput] using install_slot (extend slot) (extend_injective slot hi h90 h91) ambient
      (eraseInput cap (fun _ => List.replicate cap false)) ((j.castAdd 1).castAdd 1)
  · rw [cleared,if_neg hsome]
    by_cases h90' : i=90
    · subst i
      have he := install_slot (extend slot) (extend_injective slot hi h90 h91) ambient
        (eraseInput cap (fun _ => List.replicate cap false)) ((0 : Fin 1).natAdd k |>.castAdd 1)
      simp only [extend,eraseInput,Fin.addCases_left,Fin.addCases_right] at he
      exact he.trans hd.symm
    · by_cases h91' : i=91
      · subst i
        have he := install_slot (extend slot) (extend_injective slot hi h90 h91) ambient
          (eraseInput cap (fun _ => List.replicate cap false)) ((0 : Fin 1).natAdd (k+1))
        simp only [extend,eraseInput,Fin.addCases_right] at he
        exact he.trans hr.symm
      · apply install_other
        intro j he
        rw [extend_cases] at he
        split_ifs at he
        · exact hsome ⟨_,he⟩
        · exact h90' he.symm
        · exact h91' he.symm

def workSlot (j : Fin 83) : Fin 94 :=
  if j.val<2 then ⟨j.val+2,by omega⟩ else if j.val=2 then 5
  else if j.val<80 then ⟨j.val+4,by omega⟩ else ⟨j.val+5,by omega⟩
def accumulatorSlot : Fin 3 → Fin 94 := ![0,1,4]

theorem work_injective : Function.Injective workSlot := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [workSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem work_range (j : Fin 83) : (workSlot j).val<88 ∧ workSlot j≠0 ∧ workSlot j≠1 ∧
    workSlot j≠4 ∧ workSlot j≠6 ∧ workSlot j≠84 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp only [workSlot]
    split_ifs <;> (try simp only) <;> omega
  all_goals
    intro h
    have hv := congrArg Fin.val h
    simp only [workSlot] at hv
    split_ifs at hv <;> (try simp only at hv) <;> omega

theorem work_image (i : Fin 88) (h0 : i≠0) (h1 : i≠1) (h4 : i≠4) (h6 : i≠6) (h84 : i≠84) :
    ∃ j,workSlot j=i.castAdd 6 := by
  have hn0 : i.val≠0 := fun h => h0 (Fin.ext h)
  have hn1 : i.val≠1 := fun h => h1 (Fin.ext h)
  have hn4 : i.val≠4 := fun h => h4 (Fin.ext h)
  have hn6 : i.val≠6 := fun h => h6 (Fin.ext h)
  have hn84 : i.val≠84 := fun h => h84 (Fin.ext h)
  by_cases hlo : i.val<4
  · refine ⟨⟨i.val-2,by omega⟩,?_⟩
    apply Fin.ext
    simp [workSlot,show i.val-2<2 by omega]
    omega
  · by_cases h5 : i.val=5
    · exact ⟨2,Fin.ext h5.symm⟩
    · by_cases hmid : i.val<84
      · refine ⟨⟨i.val-4,by omega⟩,?_⟩
        apply Fin.ext
        simp [workSlot,show ¬i.val-4<2 by omega,show i.val-4≠2 by omega,show i.val-4<80 by omega]
        omega
      · refine ⟨⟨i.val-5,by omega⟩,?_⟩
        apply Fin.ext
        simp [workSlot,show ¬i.val-5<2 by omega,show i.val-5≠2 by omega,show ¬i.val-5<80 by omega]
        omega

end NearCubicWires.RepairOrdinary.CompetitorSumFold
