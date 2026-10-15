import Proof.MachineModel.UPreparedRun
import Proof.MachineModel.UInitializedRuntimeMetadata

/-! Actual numeric outputs at the prepared U endpoint. A common zero-tail
capacity relates the retained t counter to the canonical lookup counter;
the relation allocates no cells and preserves all observations. -/
namespace NearCubicWires.RepairOrdinary.UPrepared
open LocalBitMultitape RecoveryExecution RepairSource RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pad_pad (a b : ℕ) (tape : List Bool) :
    ZeroPadding.pad a (ZeroPadding.pad b tape)=ZeroPadding.pad (max a b) tape := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc,←List.replicate_add]
  congr 1
  congr 1
  omega

theorem counter_repad (tape : List Bool) (c d t : ℕ)
    (h : ZeroPadding.pad (c+2) tape=CapMachine.counter c t) :
    ZeroPadding.pad (max (c+2) (d+2)) tape=
      ZeroPadding.pad (max (c+2) (d+2)) (CapMachine.counter d t) := by
  have hc : max (max (c+2) (d+2)) (c+2)=max (c+2) (d+2) := max_eq_left (le_max_left _ _)
  have hd : max (max (c+2) (d+2)) (d+2)=max (c+2) (d+2) := max_eq_left (le_max_right _ _)
  have he := congrArg (ZeroPadding.pad (max (c+2) (d+2))) h
  simpa only [CapMachine.counter,pad_pad,hc,hd] using he

theorem counter_read_eq (tape : List Bool) (c d t : ℕ)
    (h : ZeroPadding.pad (c+2) tape=CapMachine.counter c t) (p : ℕ) :
    readTapeBit tape p=readTapeBit (CapMachine.counter d t) p := by
  have he := congrArg (fun xs => readTapeBit xs p) (counter_repad tape c d t h)
  simpa only [ZeroPadding.read_pad] using he

theorem numeric_drivers {s : ℕ} (w t j c : ℕ) (final : Configuration 139 s)
    (h : UWalkArray.Numeric w t j c (ZeroPadding.config (UWalkBootstrap.capacity c) final)) :
    final.tapes 20=List.replicate w true ∧
    ZeroPadding.pad (c+2) (final.tapes 50)=CapMachine.counter c t ∧
    final.tapes 58=CompareMachine.word j ∧ final.tapes 73=CompareMachine.word w ∧
    final.heads 20=0 ∧ final.heads 50=1 ∧ final.heads 58=1 ∧ final.heads 73=1 := by
  obtain ⟨hw,ht,hhw,hht⟩ := UWalkArray.numeric_inputs w t j c _ h
  have hj := h.1 2
  have hwidth := h.1 3
  have hj' : final.tapes 58=CompareMachine.word j := by
    simpa [ZeroPadding.config,UWalkBootstrap.capacity,UWalkArray.numbers,UWalkArray.old,UWalkOrdinary.slots,
      UWalkNumbers.afterUnit,UWalkNumbers.afterOne,UWalkNumbers.afterZ3,UWalkNumbers.afterZ2,
      UWalkNumbers.afterZ1,UWalkNumbers.afterC,UWalkNumbers.afterQ,UWalkNumbers.afterK,UWalkNumbers.afterP,
      UWalkNumbers.afterD,UWalkNumbers.afterW,UWalkNumbers.afterJ,UWalkNumbers.afterT,UWalkNumbers.input] using hj
  have hwidth' : final.tapes 73=CompareMachine.word w := by
    simpa [ZeroPadding.config,UWalkBootstrap.capacity,UWalkArray.numbers,UWalkArray.old,UWalkOrdinary.slots,
      UWalkNumbers.afterUnit,UWalkNumbers.afterOne,UWalkNumbers.afterZ3,UWalkNumbers.afterZ2,
      UWalkNumbers.afterZ1,UWalkNumbers.afterC,UWalkNumbers.afterQ,UWalkNumbers.afterK,UWalkNumbers.afterP,
      UWalkNumbers.afterD,UWalkNumbers.afterW,UWalkNumbers.afterJ,UWalkNumbers.afterT,UWalkNumbers.input] using hwidth
  exact ⟨by simpa [ZeroPadding.config,UWalkBootstrap.capacity] using hw,
    by simpa [ZeroPadding.config,UWalkBootstrap.capacity] using ht,hj',hwidth',hhw,hht,h.2 2,h.2 3⟩

structure NumericBuffers (w t j : ℕ) (tapes : Fin 139 → List Bool) : Prop where
  capacity : tapes 111=List.replicate (UWalkCapacity.amount w t j) true
  reset1 : tapes 112=List.replicate (UWalkCapacity.amount w t j) false
  reset2 : tapes 113=List.replicate (UWalkCapacity.amount w t j) false
  reset3 : tapes 114=List.replicate (UWalkCapacity.amount w t j) false
  reset4 : tapes 115=List.replicate (UWalkCapacity.amount w t j) false
  arrayReset : tapes 116=List.replicate (UWalkCapacity.amount w t j+1) false
  zero1 : tapes 119=frame (binary w 0)
  zero2 : tapes 123=frame (binary w 0)
  zero3 : tapes 127=frame (binary w 0)
  unit : tapes 132=frame (binary w 1)

theorem numeric_buffers {s : ℕ} (w t j c : ℕ) (final : Configuration 139 s)
    (h : UWalkArray.Numeric w t j c (ZeroPadding.config (UWalkBootstrap.capacity c) final)) :
    NumericBuffers w t j final.tapes := by
  obtain ⟨hc,h1,h2,h3,h4,ha,hz1,hz2,hz3,hu⟩ := UWalkOrdinary.output_fields w t j c
  have hv (k : Fin 42) (hk : k.val≠1) :
      final.tapes (UWalkArray.numbers k)=UWalkNumbers.afterUnit w t j c k := by
    have hn : (UWalkArray.numbers k).val≠50 := by
      rw [UWalkArray.numbers,UWalkArray.old]
      change (UWalkOrdinary.slots k).val≠50
      rw [UWalkOrdinary.slot_value]
      split_ifs <;> omega
    simpa [ZeroPadding.config,UWalkBootstrap.capacity,hn] using h.1 k
  exact ⟨(hv 18 (by decide)).trans hc,(hv 19 (by decide)).trans h1,(hv 20 (by decide)).trans h2,
    (hv 21 (by decide)).trans h3,(hv 22 (by decide)).trans h4,(hv 23 (by decide)).trans ha,
    (hv 26 (by decide)).trans hz1,(hv 30 (by decide)).trans hz2,(hv 34 (by decide)).trans hz3,
    (hv 39 (by decide)).trans hu⟩

theorem numeric_output_heads {s : ℕ} (w t j c : ℕ) (final : Configuration 139 s)
    (h : UWalkArray.Numeric w t j c (ZeroPadding.config (UWalkBootstrap.capacity c) final))
    (i : Fin 139) (hi : 97 ≤ i.val) (hi' : i.val<135) : final.heads i=0 := by
  let k : Fin 42 := ⟨i.val-93,by omega⟩
  have hk : 4≤k.val := by dsimp [k]; omega
  have he : UWalkArray.numbers k=i := by
    apply Fin.ext
    change (UWalkOrdinary.slots k).val=i.val
    rw [UWalkOrdinary.slot_value]
    dsimp only [k]
    split_ifs <;> omega
  rw [←he]
  have hh := h.2 k
  simpa [ZeroPadding.config,UWalkNumbers.heads,UWalkNumbers.selected,show k.val≠1 by omega,
    show k.val≠2 by omega,show k.val≠3 by omega] using hh

end NearCubicWires.RepairOrdinary.UPrepared
