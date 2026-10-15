import Proof.Hierarchy.CompetitorRawScalarFieldEmit

/-! Retain the actual subtraction rewind word at the residue consumer. It
supplies the subsequent raw-cell emitter's reset counter without an input
padding assumption or a separate dimension-generation pass. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSignedResidue
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem subtract_reset_ready (w a b : ℕ) (ha : a<2^w) (hb : b<2^w) :
    ∃ out,ClockJoin.ReadyRun subtractProgram (4*w+4)
      ![frame (binary w a),frame (binary w b),[],[]] out ∧
      out 0=frame (binary w a) ∧ out 1=frame (binary w b) ∧
      out 2=frame (binary w (residue w w a b)) ∧ out 3=List.replicate (2*w+1) false := by
  obtain ⟨base,hr,ht,hs⟩ := raw_run (binary w a) (binary w b) (by simp)
  obtain ⟨r,hrun,hrt,hrc,hrh,hrs,_⟩ := Rewind.Workspace.reset_workspace Subtract.machine _ _ base hr 0
  have hs' : base.steps=2*w+1 := by simpa using hs
  have htime : 2*base.steps+2=4*w+4 := by omega
  rw [htime] at hrun
  have hin : (Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool)
      ![frame (binary w a),frame (binary w b),[]] (fun _ => List.replicate 0 false))=
      ![frame (binary w a),frame (binary w b),[],[]] := by funext i; fin_cases i <;> rfl
  rw [hin] at hrun
  refine ⟨r.final.tapes,⟨r,hrun,rfl,hrh,by omega⟩,(hrt 0).trans (congrFun ht 0),(hrt 1).trans (congrFun ht 1),?_,?_⟩
  · have hv := (hrt 2).trans (congrFun ht 2)
    change r.final.tapes 2=frame (Subtract.difference (binary w a) (binary w b) false) at hv
    rw [difference_binary w a b ha hb] at hv
    exact hv
  · change r.final.tapes 3=List.replicate (max 0 base.steps) false at hrc
    simpa only [hs',Nat.zero_max] using hrc

theorem residue_reset_run (w q a b : ℕ) (ha : a<2^w) (hb : b<2^w) (hq : q≤w) :
    ∃ out,ClockJoin.ReadyRun machine (4*w+4*q+9) (input w q a b) out ∧
      out 0=frame (binary w a) ∧ out 1=frame (binary w b) ∧ out 3=List.replicate (2*w+1) false ∧
      out 4=List.replicate q true ∧ out 5=frame (binary q (residue w q a b)) := by
  obtain ⟨sub,hsub,h0,h1,h2,h3⟩ := subtract_reset_ready w a b ha hb
  have hi : Function.Injective subtractSlots := by intro i j h; exact Fin.ext (congrArg (fun a : Fin 8 => a.val) h)
  have hin : ∀ i,input w q a b (subtractSlots i)=![frame (binary w a),frame (binary w b),[],[]] i := by intro i; fin_cases i <;> rfl
  have hfirst := CompetitorRationalProducts.bounded_focus subtractSlots hi _ _ _ hsub (input w q a b) hin
  let middle := install subtractSlots (input w q a b) sub
  obtain ⟨crop,hcrop,hc0,_,hc2,_,_,hch,hcs⟩ := ClockNormalize.normalize_run q (binary w (residue w w a b))
  have cropReady : ClockJoin.ReadyRun ClockNormalize.machine (4*q+4)
      (ClockNormalize.input q (binary w (residue w w a b))) crop.final.tapes := ⟨crop,hcrop,rfl,hch,hcs.le⟩
  have hcInput : ∀ i,middle (cropSlots i)=ClockNormalize.input q (binary w (residue w w a b)) i := by
    intro i
    fin_cases i
    · exact install_other subtractSlots _ _ 4 (by decide)
    · exact (install_slot subtractSlots hi (input w q a b) sub 2).trans h2
    · exact install_other subtractSlots _ _ 5 (by decide)
    · exact install_other subtractSlots _ _ 6 (by decide)
    · exact install_other subtractSlots _ _ 7 (by decide)
  have hlast := CompetitorRationalProducts.bounded_focus cropSlots (by decide) _ _ _ cropReady middle hcInput
  have hall := ClockJoin.join firstProgram lastProgram _ _ _ _ _ hfirst hlast
  have htime : (4*w+4)+1+(4*q+4)=4*w+4*q+9 := by omega
  rw [htime] at hall
  refine ⟨install cropSlots middle crop.final.tapes,hall,?_,?_,?_,?_,?_⟩
  · exact (install_other cropSlots _ _ 0 (by decide)).trans ((install_slot subtractSlots hi _ sub 0).trans h0)
  · exact (install_other cropSlots _ _ 1 (by decide)).trans ((install_slot subtractSlots hi _ sub 1).trans h1)
  · exact (install_other cropSlots _ _ 3 (by decide)).trans ((install_slot subtractSlots hi _ sub 3).trans h3)
  · exact (install_slot cropSlots (by decide) middle crop.final.tapes 0).trans hc0
  · have ho := (install_slot cropSlots (by decide) middle crop.final.tapes 2).trans hc2
    change install cropSlots middle crop.final.tapes 5=frame (ClockNormalize.resize q (binary w (residue w w a b))) at ho
    rw [crop_residue w q a b hq] at ho
    exact ho

end NearCubicWires.RepairOrdinary.CompetitorSignedResidue
