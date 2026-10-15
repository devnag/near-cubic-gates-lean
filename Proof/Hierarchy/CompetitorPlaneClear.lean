import Proof.Hierarchy.CompetitorPlaneFieldLoad
import Proof.Hierarchy.CompetitorPlaneKernel

/-! Physically clear the plane cell's selected local workspace while all
three global count/accumulator/output cursors remain untouched. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneWorkspace
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {k : ℕ} (slot : Fin k → Fin 27) : Fin (k+2) → Fin 27 :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => Fin 27)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => Fin 27) slot (fun _ => 21)) (fun _ => 22)
def eraseInput {k : ℕ} (cap : ℕ) (backing : Fin k → List Bool) : Fin (k+2) → List Bool :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => List Bool)
      backing (fun _ => List.replicate cap true)) (fun _ => List.replicate (cap+1) false)
noncomputable def clearProgram {k : ℕ} (slot : Fin k → Fin 27) :=
  RecoveryFocus.machine (extend slot) (RecoveryScratchErase.resetMachine k)
noncomputable def cleared {k : ℕ} (cap : ℕ) (slot : Fin k → Fin 27)
    (ambient : Fin 27 → List Bool) : Fin 27 → List Bool := fun i =>
  if ∃ j,slot j=i then List.replicate cap false else ambient i

theorem extend_cases {k : ℕ} (slot : Fin k → Fin 27) (j : Fin (k+2)) :
    extend slot j=if h : j.val<k then slot ⟨j.val,h⟩ else if j.val=k then 21 else 22 := by
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

theorem extend_injective {k : ℕ} (slot : Fin k → Fin 27)
    (hi : Function.Injective slot) (h21 : ∀ j,slot j≠21) (h22 : ∀ j,slot j≠22) :
    Function.Injective (extend slot) := by
  intro i j h
  rw [extend_cases,extend_cases] at h
  split_ifs at h with hi' hj' hj90 hi90 hj' hj90
  · have he := hi h
    exact Fin.ext (congrArg (fun a : Fin k => a.val) he)
  · exact False.elim (h21 _ h)
  · exact False.elim (h22 _ h)
  · exact False.elim (h21 _ h.symm)
  · exact Fin.ext (by omega)
  · have hv := congrArg Fin.val h
    change (21 : ℕ)=22 at hv
    omega
  · exact False.elim (h22 _ h.symm)
  · have hv := congrArg Fin.val h
    change (22 : ℕ)=21 at hv
    omega
  · exact Fin.ext (by omega)

theorem clear_run {k : ℕ} (slot : Fin k → Fin 27) (hi : Function.Injective slot)
    (h21 : ∀ j,slot j≠21) (h22 : ∀ j,slot j≠22)
    (cap : ℕ) (heads : Fin 27 → ℕ) (ambient : Fin 27 → List Bool)
    (hd : ambient 21=List.replicate cap true) (hr : ambient 22=List.replicate (cap+1) false)
    (hb : ∀ j,(ambient (slot j)).length≤cap) (hh : ∀ j,heads (extend slot j)=0) :
    ∃ r : ExecutionReceipt 27 4,
      runFrom (clearProgram slot) (2*cap+4)
        (RecoveryCalls.restarted (clearProgram slot) heads ambient)=some r ∧
      r.final.heads=heads ∧ r.final.tapes=cleared cap slot ambient ∧ r.steps=2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine k) (2*cap+4)
      (eraseInput cap (fun j => ambient (slot j))) (eraseInput cap (fun _ => List.replicate cap false)) := by
    simpa only [eraseInput,max_self] using RecoveryScratchErase.erase_ready cap (cap+1) _ hb
  have ht : ∀ j,ambient (extend slot j)=eraseInput cap (fun j => ambient (slot j)) j := by
    intro j
    refine Fin.addCases (m := k+1) (n := 1) ?_ ?_ j
    · intro i
      refine Fin.addCases (m := k) (n := 1) ?_ ?_ i
      · intro a; simp [extend,eraseInput]
      · intro a; fin_cases a; simpa [extend,eraseInput] using hd
    · intro i; fin_cases i; simpa [extend,eraseInput] using hr
  obtain ⟨r,hrun,hheads,htapes,hsteps⟩ := HierarchyBinary.focused_run (extend slot)
    (extend_injective slot hi h21 h22) _ _ _ ready heads ambient hh ht
  refine ⟨r,hrun,hheads,?_,hsteps⟩
  rw [htapes]
  funext i
  by_cases hsome : ∃ j,slot j=i
  · obtain ⟨j,hj⟩ := hsome
    have hsome' : ∃ a,slot a=i := ⟨j,hj⟩
    rw [cleared,if_pos hsome']
    subst i
    simpa [extend,eraseInput] using install_slot (extend slot) (extend_injective slot hi h21 h22) ambient
      (eraseInput cap (fun _ => List.replicate cap false)) ((j.castAdd 1).castAdd 1)
  · rw [cleared,if_neg hsome]
    by_cases h21' : i=21
    · subst i
      have he := install_slot (extend slot) (extend_injective slot hi h21 h22) ambient
        (eraseInput cap (fun _ => List.replicate cap false)) ((0 : Fin 1).natAdd k |>.castAdd 1)
      simp only [extend,eraseInput,Fin.addCases_left,Fin.addCases_right] at he
      exact he.trans hd.symm
    · by_cases h22' : i=22
      · subst i
        have he := install_slot (extend slot) (extend_injective slot hi h21 h22) ambient
          (eraseInput cap (fun _ => List.replicate cap false)) ((0 : Fin 1).natAdd (k+1))
        simp only [extend,eraseInput,Fin.addCases_right] at he
        exact he.trans hr.symm
      · apply install_other
        intro j he
        rw [extend_cases] at he
        split_ifs at he
        · exact hsome ⟨_,he⟩
        · exact h21' he.symm
        · exact h22' he.symm

end NearCubicWires.RepairOrdinary.CompetitorPlaneWorkspace
