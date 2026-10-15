import Proof.MachineModel.Layout
import Proof.MachineModel.FrameCopy
import Proof.MachineModel.Totals
import Proof.Amplification.RecoveryScratchErase

/-! P25: one complete occurrence round.

Framed native request → the SAME selected decomposition constructor → the actual
child count word, the actual child body and the running unary total, then the
paid masked head reset and the paid erase of the reusable source bank. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Tapes do not grow while every head stays inside them -/

theorem write_len (l : List Bool) (k : ℕ) (v : Bool) (h : k < l.length) :
    (writeTapeBit l k v).length = l.length := by
  induction l generalizing k with
  | nil => simp at h
  | cons b l ih =>
    cases k with
    | zero => simp [writeTapeBit]
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
      simp [writeTapeBit, ih k h]

theorem length_preserved {t s : ℕ} (p : Machine t s) (fuel : ℕ) (c : Configuration t s)
    (r : ExecutionReceipt t s) (i : Fin t) (hr : runFrom p fuel c = some r)
    (hfit : c.heads i + fuel < (c.tapes i).length) : (r.final.tapes i).length = (c.tapes i).length := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; rfl
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; rfl
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases he : runFrom p fuel d with
        | none => simp [hs, he] at hr
        | some tail =>
          simp only [hs, he, Option.some.injEq] at hr
          subst r
          obtain ⟨action, _, ha⟩ := Option.map_eq_some_iff.mp hs
          subst d
          have hlen : ((applyAction c action).tapes i).length = (c.tapes i).length := by
            simp only [applyAction]
            cases hw : action.write i with
            | none => rfl
            | some v => exact write_len _ _ _ (by omega)
          have hhead : (applyAction c action).heads i ≤ c.heads i + 1 := by
            simp only [applyAction]
            cases action.move i <;> simp only [HeadMove.apply] <;> omega
          have := ih (applyAction c action) tail he (by rw [hlen]; omega)
          rw [this, hlen]

variable (a : DecompositionAlgorithm)

/-! ## Slot maps -/

noncomputable def copySlots : Fin 3 → Fin (T a) :=
  fun i => if i.val = 0 then str a else if i.val = 1 then bin a else fcp a
noncomputable def fieldSlots : Fin 3 → Fin (T a) :=
  fun i => if i.val = 0 then bsrc a else if i.val = 1 then bfld a else cnt a
noncomputable def recSlots : Fin 5 → Fin (T a) :=
  fun i => if i.val = 0 then bsrc a else if i.val = 1 then bfld a else if i.val = 2 then bod a
    else if i.val = 3 then dom a else bcnt a
noncomputable def totSlots : Fin 2 → Fin (T a) :=
  fun i => if i.val = 0 then bcnt a else tot a

theorem sb_eq : SB a = 27 + (Call.sourceProgram a).tapeCount := by
  change Call.tapes a + 11 = _
  unfold Call.tapes
  omega

theorem bin_val : (bin a).val = 0 := rfl
theorem bfld_val : (bfld a).val = 14 := rfl
theorem bsrc_val : (bsrc a).val = 16 + (Call.sourceProgram a).outputTape.val := out_val a
theorem bcnt_val : (bcnt a).val = 25 + (Call.sourceProgram a).tapeCount := by
  change (Counted.fresh a 9).val = _
  rw [fresh_val a 9]
  change Call.tapes a + 9 = _
  unfold Call.tapes
  omega
theorem out_pos : 1 ≤ (Call.sourceProgram a).outputTape.val := by
  have hf := (Call.sourceProgram a).outputFresh
  omega

theorem port_facts :
    (bin a).val = 0 ∧ (bfld a).val = 14 ∧ (bsrc a).val = 16 + (Call.sourceProgram a).outputTape.val ∧
      (bcnt a).val = 25 + (Call.sourceProgram a).tapeCount ∧
      1 ≤ (Call.sourceProgram a).outputTape.val ∧
      (Call.sourceProgram a).outputTape.val < (Call.sourceProgram a).tapeCount ∧
      SB a = 27 + (Call.sourceProgram a).tapeCount ∧
      (str a).val = SB a ∧ (cnt a).val = SB a + 1 ∧ (bod a).val = SB a + 2 ∧
      (tot a).val = SB a + 3 ∧ (fcp a).val = SB a + 7 ∧ (dom a).val = SB a + 10 :=
  ⟨bin_val a, bfld_val a, bsrc_val a, bcnt_val a, out_pos a, out_lt a, sb_eq a,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem copy_injective : Function.Injective (copySlots a) := by
  intro i j h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := port_facts a
  have hv := congrArg (fun k : Fin (T a) => k.val) h
  simp only [copySlots] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

theorem field_injective : Function.Injective (fieldSlots a) := by
  intro i j h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := port_facts a
  have hv := congrArg (fun k : Fin (T a) => k.val) h
  simp only [fieldSlots] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

theorem rec_injective : Function.Injective (recSlots a) := by
  intro i j h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := port_facts a
  have hv := congrArg (fun k : Fin (T a) => k.val) h
  simp only [recSlots] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

theorem tot_injective : Function.Injective (totSlots a) := by
  intro i j h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := port_facts a
  have hv := congrArg (fun k : Fin (T a) => k.val) h
  simp only [totSlots] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-! ## The single-request input word, by tape value -/

theorem counted_input_val (r : ExactDecompositionRequest) (i : Fin (SB a)) :
    Counted.input a r i = if i.val = 0 then frame (natWord r.arity ++ Call.tail r) else [] := by
  refine Fin.addCases (m := Call.tapes a) (n := 11) (fun j => ?_) (fun j => ?_) i
  · simp only [Counted.input, Fin.addCases_left, Fin.val_castAdd]
    refine Fin.addCases (m := 16) (n := (Call.sourceProgram a).tapeCount) (fun k => ?_) (fun k => ?_) j
    · simp only [Call.input, Fin.addCases_left, Fin.val_castAdd, Prepare.input]
      split_ifs <;> rfl
    · simp only [Call.input, Fin.addCases_right, Fin.val_natAdd]
      rw [if_neg (by omega)]
  · simp only [Counted.input, Fin.addCases_right, Fin.val_natAdd]
    have h16 : 16 ≤ Call.tapes a := by unfold Call.tapes; omega
    rw [if_neg (by omega)]

end NearCubicWires.ExtDecompositionBatch
