import Proof.MachineModel.OrdinaryMatrixCoefficientFields

/-! One actual coefficient extraction from the canonical cut stream: skip
both d-weight blocks, skip its threshold, then append exactly its framed
sign and magnitude. The same physical d-driver is reused throughout. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientGate
open LocalBitMultitape MatrixScoreBatch
open MatrixCoefficientFields (cfg)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def weights := Composition.machine MatrixCoefficientFields.skip MatrixCoefficientFields.skip
noncomputable def skipped := Composition.machine weights MatrixCoefficientFields.threshold
noncomputable def machine := Composition.machine skipped MatrixCoefficientFields.copy
def budget (d p : ℕ) := 2*d*(2*p+6)+4*p+15

theorem gate_run (d p : ℕ) (left right : List ℤ) (threshold coefficient : ℤ) (pre suffix out : List Bool)
    (hleft : left.length=d) (hright : right.length=d) : ∃ actual,
    runFrom machine (budget d p)
      (cfg machine.start (pre++MatrixScoreCanonical.fields p left++MatrixScoreCanonical.fields p right++
        frame (signMagnitude p threshold)++frame (signMagnitude p coefficient)++suffix) pre.length d out)=some actual ∧
    actual.final=cfg actual.final.control
      (pre++MatrixScoreCanonical.fields p left++MatrixScoreCanonical.fields p right++
        frame (signMagnitude p threshold)++frame (signMagnitude p coefficient)++suffix)
      (pre.length+(MatrixScoreCanonical.fields p left).length+(MatrixScoreCanonical.fields p right).length+
        (frame (signMagnitude p threshold)).length+(frame (signMagnitude p coefficient)).length)
      d (out++frame (signMagnitude p coefficient)) ∧ actual.steps≤budget d p := by
  let L := MatrixScoreCanonical.fields p left
  let R := MatrixScoreCanonical.fields p right
  let T := frame (signMagnitude p threshold)
  let C := frame (signMagnitude p coefficient)
  obtain ⟨first,hfirst,ff,fs⟩ := MatrixCoefficientFields.skip_run p left pre (R++T++C++suffix) out
  obtain ⟨second,hsecond,sf,ss⟩ := MatrixCoefficientFields.skip_run p right (pre++L) (T++C++suffix) out
  simp only [hleft] at hfirst ff fs
  simp only [hright] at hsecond sf ss
  have hi : Composition.restart first.final MatrixCoefficientFields.skip.start=
      cfg MatrixCoefficientFields.skip.start ((pre++L)++R++(T++C++suffix)) (pre++L).length d out := by
    rw [ff]
    simp only [Composition.restart,cfg,List.append_assoc,List.length_append,L]
  rw [←hi] at hsecond
  have firstJoin := Composition.run_join MatrixCoefficientFields.skip MatrixCoefficientFields.skip _ _ _ first second hfirst hsecond
  let pair := Composition.joinedReceipt first second
  obtain ⟨third,hthird,tf,ts⟩ := MatrixCoefficientFields.threshold_run (signMagnitude p threshold)
    (pre++L++R) (C++suffix) out d
  have ht : Composition.restart pair.final MatrixCoefficientFields.threshold.start=
      cfg MatrixCoefficientFields.threshold.start ((pre++L++R)++T++(C++suffix)) (pre++L++R).length d out := by
    change Composition.restart (Composition.rightConfig _ second.final) MatrixCoefficientFields.threshold.start=_
    rw [sf]
    simp only [Composition.restart,Composition.rightConfig,cfg,List.append_assoc,List.length_append,R,Nat.add_assoc]
  rw [←ht] at hthird
  have secondJoin := Composition.run_join weights MatrixCoefficientFields.threshold _ _ _ pair third firstJoin hthird
  let prepared := Composition.joinedReceipt pair third
  obtain ⟨last,hl,lf,ls⟩ := MatrixCoefficientFields.copy_run (signMagnitude p coefficient) (pre++L++R++T) suffix out d
  have hc : Composition.restart prepared.final MatrixCoefficientFields.copy.start=
      cfg MatrixCoefficientFields.copy.start ((pre++L++R++T)++C++suffix) (pre++L++R++T).length d out := by
    change Composition.restart (Composition.rightConfig _ third.final) MatrixCoefficientFields.copy.start=_
    rw [tf]
    simp only [Composition.restart,Composition.rightConfig,cfg,List.append_assoc,List.length_append,T,Nat.add_assoc]
  rw [←hc] at hl
  have finalJoin := Composition.run_join skipped MatrixCoefficientFields.copy _ _ _ prepared last secondJoin hl
  have hbits (z : ℤ) : (signMagnitude p z).length=p+1 := by simp [signMagnitude]
  have hbudget : (d*(2*p+6)+3)+1+(d*(2*p+6)+3)+1+(2*(signMagnitude p threshold).length+1)+
      1+(2*(signMagnitude p coefficient).length+1)=budget d p := by rw [hbits,hbits]; unfold budget; ring
  rw [hbudget] at finalJoin
  refine ⟨Composition.joinedReceipt prepared last,?_,?_,?_⟩
  · simpa only [L,R,T,C,List.append_assoc,Composition.leftConfig,cfg,machine,skipped,weights,Composition.machine] using finalJoin
  · change Composition.rightConfig _ last.final=_
    rw [lf]
    simp only [Composition.rightConfig,Composition.joinedReceipt,cfg,L,R,T,List.append_assoc,List.length_append,Nat.add_assoc]
  · change first.steps+1+second.steps+1+third.steps+1+last.steps≤budget d p
    rw [ts,ls]
    rw [←hbudget]
    omega

end NearCubicWires.RepairOrdinary.MatrixCoefficientGate
