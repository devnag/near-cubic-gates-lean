import Proof.PCP.PCPPairTails

/-! Whole fixed pair-node execution, including the physical comparison flag,
branch choice, square, additions and every controller return. Original fields,
normalized copies and the paid width are the explicit enclosing entry. -/
namespace NearCubicWires.RepairOrdinary.PCPPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem exact_time {t s bound : ℕ} {p : Machine t s}
    {input output : Fin t → List Bool} (h : ClockJoin.ReadyRun p bound input output) :
    ∃ time ≤ bound, ReadyRun p time input output := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  obtain ⟨hp,hhalt⟩ := prefix_of_run p bound _ base hr
  have htimed : Timed p base.steps (initialConfiguration p input) base.final :=
    ⟨base.peakTapeCells,hp⟩
  obtain ⟨r,hrun,hf,hsteps⟩ := htimed.run hhalt
  refine ⟨base.steps,hs,r,hrun,?_,?_,hsteps⟩
  · rw [hf]
    exact ht
  · intro i
    rw [hf]
    exact hh i

private theorem clock_bound (left right : List Bool) (branch : Bool) (time : ℕ)
    (h : time ≤ HierarchyMultiplyEntry.budget (width left right) (chosen branch left right)) :
    time+12*width left right+18 ≤ budget left right := by
  have hc : (chosen branch left right).length ≤ left.length+right.length := by
    cases branch
    · change right.length ≤ left.length+right.length
      omega
    · change left.length ≤ left.length+right.length
      omega
  have hm : time ≤ 128*(width left right+1)*(left.length+right.length+1) :=
    h.trans (Nat.mul_le_mul_left _ (by omega))
  dsimp only [budget]
  nlinarith

theorem pair_run (left right : List Bool) :
    ∃ out : Fin 30 → List Bool,
      ClockJoin.ReadyRun machine (budget left right) (input left right) out ∧
      out 26=frame (binary (width left right) (Nat.pair (value left) (value right))) := by
  have hinit : ReadyRun (programs 0) 1 (input left right) (initialized left right) :=
    initialized_run left right
  have hcompare : ReadyRun (programs 1) (4*width left right+4)
      (initialized left right) (compared left right) := compare_run left right
  have hstart := hinit.call sizes programs 0 next 0 1 (by intro q; rfl)
  by_cases hbranch : value right ≤ value left
  · obtain ⟨middle,hmul,h0,h1,_,_,h10,hfresh⟩ := square_run true left right
    obtain ⟨time,htime,hready⟩ := exact_time hmul
    have hsquare : ReadyRun (programs 2) time (compared left right) middle := hready
    obtain ⟨out,htail,hout⟩ := left_tail left right middle h0 h1 h10 hfresh hbranch
    have hchoose := hcompare.call sizes programs 0 next 1 2 (by
      intro q
      simp [next,compared,readTapeBit,hbranch])
    have hnext := hsquare.call sizes programs 0 next 2 3 (by intro q; rfl)
    have hfull := hstart.trans (hchoose.trans (hnext.trans htail))
    have he : 1+1+(4*width left right+4+1+(time+1+(8*width left right+10)))=
        time+12*width left right+18 := by omega
    rw [he] at hfull
    obtain ⟨r,hr,hf,hs⟩ := hfull.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hready : ClockJoin.ReadyRun machine (time+12*width left right+18)
        (input left right) out := by
      refine ⟨r,hr,?_,?_,hs.le⟩
      · rw [hf]
        rfl
      · intro i
        rw [hf]
        rfl
    exact ⟨out,ClockJoin.enlarge machine _ _ _ _ hready (clock_bound left right true time htime),hout⟩
  · obtain ⟨middle,hmul,h0,_,_,_,h10,hfresh⟩ := square_run false left right
    obtain ⟨time,htime,hready⟩ := exact_time hmul
    have hsquare : ReadyRun (programs 5) time (compared left right) middle := hready
    obtain ⟨out,htail,hout⟩ := right_tail left right middle h0 h10 hfresh hbranch
    have hchoose := hcompare.call sizes programs 0 next 1 5 (by
      intro q
      simp [next,compared,readTapeBit,hbranch])
    have hnext := hsquare.call sizes programs 0 next 5 6 (by intro q; rfl)
    have hfull := hstart.trans (hchoose.trans (hnext.trans htail))
    have he : 1+1+(4*width left right+4+1+(time+1+(4*width left right+5)))=
        time+8*width left right+13 := by omega
    rw [he] at hfull
    obtain ⟨r,hr,hf,hs⟩ := hfull.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hready : ClockJoin.ReadyRun machine (time+8*width left right+13)
        (input left right) out := by
      refine ⟨r,hr,?_,?_,hs.le⟩
      · rw [hf]
        rfl
      · intro i
        rw [hf]
        rfl
    have hb : time+8*width left right+13 ≤ budget left right :=
      (by omega : time+8*width left right+13 ≤ time+12*width left right+18).trans
        (clock_bound left right false time htime)
    exact ⟨out,ClockJoin.enlarge machine _ _ _ _ hready hb,hout⟩

end NearCubicWires.RepairOrdinary.PCPPair
