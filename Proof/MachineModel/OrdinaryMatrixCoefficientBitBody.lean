import Proof.MachineModel.OrdinaryMatrixCoefficientBitScans

/-! Actual one-coefficient mask production. Read and test the sign, skip
exactly the physically supplied even byte offset, emit the selected
magnitude bit conjoined with the sign test, and consume the remaining frame.
The enclosing plane scheduler must produce the byte-offset sentinel. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientBitBody
open LocalBitMultitape
open MatrixCoefficientBitLeaf (cfg nextFlag nextOut)
open RecoveryRadixInput (framePrefix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def skipped (negative : Bool) := Composition.machine
  (MatrixCoefficientBitLeaf.machine false negative) MatrixCoefficientBitScans.skip
noncomputable def selected (negative : Bool) := Composition.machine (skipped negative) (MatrixCoefficientBitLeaf.machine true false)
noncomputable def machine (negative : Bool) := Composition.machine (selected negative) MatrixCoefficientBitScans.tail
def budget (before after : List Bool) := 4*before.length+2*after.length+12

theorem body_run (negative flag sign bit : Bool) (before after pre suffix out : List Bool) : ∃ actual,
    runFrom (machine negative) (budget before after)
      (cfg (machine negative).start
        (pre++[true,sign]++framePrefix before++[true,bit]++frame after++suffix) pre.length (2*before.length) flag out)=some actual ∧
    actual.final=cfg actual.final.control
      (pre++[true,sign]++framePrefix before++[true,bit]++frame after++suffix)
      (pre.length+2+2*before.length+2+(frame after).length) (2*before.length) (sign==negative)
      (out++[(sign==negative) && bit]) ∧ actual.steps=budget before after := by
  let B := framePrefix before
  let A := frame after
  obtain ⟨first,hfirst,ff,fs⟩ := MatrixCoefficientBitLeaf.read_run false negative flag sign pre
    (B++[true,bit]++A++suffix) out (2*before.length)
  simp only [nextFlag,nextOut,Bool.false_eq_true,if_false] at ff
  obtain ⟨second,hsecond,sf,ss⟩ := MatrixCoefficientBitScans.skip_run B (pre++[true,sign])
    ([true,bit]++A++suffix) out (sign==negative)
  have hB : B.length=2*before.length := RecoveryRadixInput.prefix_length before
  rw [hB] at hsecond sf ss
  have hi : Composition.restart first.final MatrixCoefficientBitScans.skip.start=
      cfg MatrixCoefficientBitScans.skip.start ((pre++[true,sign])++B++([true,bit]++A++suffix))
        (pre++[true,sign]).length (2*before.length) (sign==negative) out := by
    rw [ff]
    simp [Composition.restart,cfg,List.append_assoc]
  rw [←hi] at hsecond
  have firstJoin := Composition.run_join (MatrixCoefficientBitLeaf.machine false negative) MatrixCoefficientBitScans.skip
    _ _ _ first second hfirst hsecond
  let pair := Composition.joinedReceipt first second
  obtain ⟨third,hthird,tf,ts⟩ := MatrixCoefficientBitLeaf.read_run true false (sign==negative) bit
    (pre++[true,sign]++B) (A++suffix) out (2*before.length)
  simp only [nextFlag,nextOut,if_true] at tf
  have ht : Composition.restart pair.final (MatrixCoefficientBitLeaf.machine true false).start=
      cfg 0 ((pre++[true,sign]++B)++[true,bit]++(A++suffix))
        (pre++[true,sign]++B).length (2*before.length) (sign==negative) out := by
    change Composition.restart (Composition.rightConfig _ second.final) _=_
    rw [sf]
    simp [Composition.restart,Composition.rightConfig,cfg,List.append_assoc,hB,Nat.add_assoc,MatrixCoefficientBitLeaf.machine]
    omega
  rw [←ht] at hthird
  have secondJoin := Composition.run_join (skipped negative) (MatrixCoefficientBitLeaf.machine true false)
    _ _ _ pair third firstJoin hthird
  let prepared := Composition.joinedReceipt pair third
  obtain ⟨last,hl,lf,ls⟩ := MatrixCoefficientBitScans.tail_run after
    (pre++[true,sign]++B++[true,bit]) suffix (out++[(sign==negative) && bit]) (2*before.length) (sign==negative)
  have hc : Composition.restart prepared.final MatrixCoefficientBitScans.tail.start=
      cfg MatrixCoefficientBitScans.tail.start ((pre++[true,sign]++B++[true,bit])++A++suffix)
        (pre++[true,sign]++B++[true,bit]).length (2*before.length) (sign==negative)
        (out++[(sign==negative) && bit]) := by
    change Composition.restart (Composition.rightConfig _ third.final) _=_
    rw [tf]
    simp [Composition.restart,Composition.rightConfig,cfg,List.append_assoc,Nat.add_assoc]
  rw [←hc] at hl
  have finalJoin := Composition.run_join (selected negative) MatrixCoefficientBitScans.tail _ _ _ prepared last secondJoin hl
  have hbudget : 2+1+(2*(2*before.length)+4)+1+2+1+(2*after.length+1)=budget before after := by unfold budget; ring
  rw [hbudget] at finalJoin
  refine ⟨Composition.joinedReceipt prepared last,?_,?_,?_⟩
  · simpa only [B,A,List.append_assoc,Composition.leftConfig,cfg,machine,selected,skipped,Composition.machine,MatrixCoefficientBitLeaf.machine] using finalJoin
  · change Composition.rightConfig _ last.final=_
    rw [lf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.rightConfig,Composition.joinedReceipt,cfg,B]; omega
    · funext i; fin_cases i <;> simp [Composition.rightConfig,Composition.joinedReceipt,cfg,B,List.append_assoc]
  · change first.steps+1+second.steps+1+third.steps+1+last.steps=budget before after
    rw [fs,ss,ts,ls,hbudget]

theorem coefficient_run (negative flag sign bit : Bool) (before after pre suffix out : List Bool) : ∃ actual,
    runFrom (machine negative) (budget before after)
      (cfg (machine negative).start (pre++frame (sign::(before++bit::after))++suffix)
        pre.length (2*before.length) flag out)=some actual ∧
    actual.final=cfg actual.final.control (pre++frame (sign::(before++bit::after))++suffix)
      (pre.length+(frame (sign::(before++bit::after))).length) (2*before.length) (sign==negative)
      (out++[(sign==negative) && bit]) ∧ actual.steps=budget before after := by
  obtain ⟨actual,ha,hf,hs⟩ := body_run negative flag sign bit before after pre suffix out
  have hword : frame (sign::(before++bit::after))=
      [true,sign]++framePrefix before++[true,bit]++frame after := by
    simp [frame,RecoveryRadixInput.frame_append,List.append_assoc]
  refine ⟨actual,?_,?_,hs⟩
  · simpa only [hword,List.append_assoc] using ha
  · rw [hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [cfg,hword]; omega
    · funext i; fin_cases i <;> simp [cfg,hword,List.append_assoc]

end NearCubicWires.RepairOrdinary.MatrixCoefficientBitBody
