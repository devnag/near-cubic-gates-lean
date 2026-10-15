import Proof.Hierarchy.CompetitorOddRowSliceEntry

namespace NearCubicWires.RepairOrdinary.CompetitorOddRowSliceDock
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorOddRowSlice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 22 → Fin 106 := ![87,45,88,86,35,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105]
def input (ambient : Fin 86 → List Bool) (u : ℕ) : Fin 106 → List Bool :=
  Fin.addCases (m := 86) (n := 20) (motive := fun _ => List Bool) ambient
    (fun i => if i=0 then UnaryTemplate.tape u else [])
def heads (pos driver : ℕ) : Fin 106 → ℕ := fun i => if i=32 then pos else if i=86 then driver else 0
def cfg {s : ℕ} (state : Fin s) (pos driver : ℕ) (tapes : Fin 106 → List Bool) : Configuration 106 s :=
  ⟨state,heads pos driver,tapes⟩
def move (direction : HeadMove) : Machine 106 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=86 then direction else .stay⟩ else none
noncomputable def sliceProgram := RecoveryFocus.machine slots CompetitorOddRowSlice.machine
noncomputable def tail := Composition.machine sliceProgram (move .right)
noncomputable def machine := Composition.machine (move .left) tail
def budget (u q : ℕ) := CompetitorOddRowSlice.budget u q+4

theorem move_run (direction : HeadMove) (pos driver : ℕ) (tapes : Fin 106 → List Bool) :
    ∃ r,runFrom (move direction) 1 (cfg 0 pos driver tapes)=some r ∧
      r.final=cfg 1 pos (direction.apply driver) tapes ∧ r.steps=1 := by
  have hstep : step (move direction) (cfg 0 pos driver tapes)=some (cfg 1 pos (direction.apply driver) tapes) := by
    simp only [step,move,cfg,Fin.val_zero,ite_true]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=86
      · subst i
        simp [applyAction,heads]
      · by_cases hj : i=32 <;> simp [applyAction,heads,hi,hj,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem dock_run (q pos : ℕ) (rows : List Row) (suffix : List Bool) (ambient : Fin 86 → List Bool)
    (hsource : ambient 45=sourceRows rows++suffix) (hq : ambient 35=List.replicate q true)
    (hv : ∀ row∈rows,rowValid (halfBytes rows.length q) row) :
    ∃ r,runFrom machine (budget rows.length q)
      (cfg machine.start pos 1 (input ambient rows.length))=some r ∧
      r.steps≤budget rows.length q ∧ r.final.heads=heads pos 1 ∧
      r.final.tapes 88=selectedRows rows ∧ r.final.tapes 86=UnaryTemplate.tape rows.length ∧
      (∀ i : Fin 86,r.final.tapes (i.castAdd 20)=ambient i) := by
  obtain ⟨produced,hready,h2,h1,h3,h4⟩ := ready_run q rows suffix hv
  have hin : ∀ i,input ambient rows.length (slots i)=readyInput rows.length q (sourceRows rows++suffix) i := by
    intro i
    fin_cases i <;> simp [input,slots,readyInput,CompetitorOddRowSlice.input,Fin.addCases,hsource,hq]
  obtain ⟨entry,he,hef,hes⟩ := move_run .left pos 1 (input ambient rows.length)
  obtain ⟨loop,hl,hlh,hlt,hls⟩ := CompetitorReusableDecision.bounded_focused_run slots (by decide)
    _ _ _ hready (heads pos 0) (input ambient rows.length)
    (by intro i; fin_cases i <;> rfl) hin
  let middle := install slots (input ambient rows.length) produced
  have heLoop : Composition.restart entry.final sliceProgram.start=
      RecoveryCalls.restarted sliceProgram (heads pos 0) (input ambient rows.length) := by rw [hef]; rfl
  have hl' : runFrom sliceProgram (CompetitorOddRowSlice.budget rows.length q)
      (Composition.restart entry.final sliceProgram.start)=some loop := by rw [heLoop]; exact hl
  obtain ⟨done,hd,hdf,hds⟩ := move_run .right pos 0 middle
  have heDone : Composition.restart loop.final (move .right).start=cfg 0 pos 0 middle := by
    apply configuration_ext
    · rfl
    · exact hlh
    · exact hlt
  have hd' : runFrom (move .right) 1 (Composition.restart loop.final (move .right).start)=some done := by
    rw [heDone]
    exact hd
  have htail := Composition.run_join sliceProgram (move .right) _ _ _ loop done hl' hd'
  have hall := Composition.run_join (move .left) tail _ _ _ entry (Composition.joinedReceipt loop done) he htail
  have htime : 1+1+(CompetitorOddRowSlice.budget rows.length q+1+1)=budget rows.length q := by unfold budget; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt entry (Composition.joinedReceipt loop done),hall,?_,?_,?_,?_,?_⟩
  · change entry.steps+1+(loop.steps+1+done.steps)≤budget rows.length q
    unfold budget
    omega
  · change done.final.heads=_
    rw [hdf]
    rfl
  · change done.final.tapes 88=_
    rw [hdf]
    exact (install_slot slots (by decide) (input ambient rows.length) produced 2).trans h2
  · change done.final.tapes 86=_
    rw [hdf]
    exact (install_slot slots (by decide) (input ambient rows.length) produced 3).trans h3
  · intro i
    change done.final.tapes (i.castAdd 20)=_
    rw [hdf]
    by_cases hi : i=45
    · subst i
      exact (install_slot slots (by decide) (input ambient rows.length) produced 1).trans (h1.trans hsource.symm)
    · by_cases hj : i=35
      · subst i
        exact (install_slot slots (by decide) (input ambient rows.length) produced 4).trans (h4.trans hq.symm)
      · have hk : ∀ j,slots j≠i.castAdd 20 :=
          (show ∀ i : Fin 86,i≠45 → i≠35 → ∀ j,slots j≠i.castAdd 20 by decide) i hi hj
        simpa only [cfg,middle,input,Fin.addCases_left] using
          install_other slots (input ambient rows.length) produced (i.castAdd 20) hk

theorem budget_bound (u q : ℕ) : budget u q≤256*(u*u+1)*(q+1) := by
  have hh : u/2≤u := Nat.div_le_self u 2
  have hu : u≤u*u+1 := by nlinarith
  have hhq := Nat.mul_le_mul_left q hh
  have huq := Nat.mul_le_mul_right q hu
  have hhuq := Nat.mul_le_mul_left u hhq
  unfold budget CompetitorOddRowSlice.budget runBudget prepareBudget loopBudget rowBudget halfBytes WilliamsUnaryProduct.budget
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorOddRowSliceDock
