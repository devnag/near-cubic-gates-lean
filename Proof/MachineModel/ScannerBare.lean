import Proof.CaseAnalysis.FinalRowScannerDock
import Proof.CaseAnalysis.RowsEstimatorBacking

/-! The paid scanner's exact bank is the common-D bare Warm entry, with
native-only C padding. The retained capacity word and C≤D are boundary facts;
this identity creates no tapes or metadata. -/
namespace NearCubicWires.P1Independent.ScannerBare
open LocalBitMultitape RepairRepresentation RepairOrdinary RepairSource.CloseoutFinal
open RepairOrdinary.CloseoutRowsEstimator RepairOrdinary.C10RowFrameJoin
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def paddedBare (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (i : Fin (WholePrefix.tapes p)) : List Bool :=
  ZeroPadding.pad (if i.val=52 then C else 0)
    (WarmReuse.padded p D (WarmFields.bare p row C) i)

/-- New worker-independent spelling of the existing entry_tapes_fun RHS. -/
noncomputable def bareBank (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (out : List Bool) : Fin (Reuse.tapes p) → List Bool :=
  Fin.addCases (m:=WholePrefix.tapes p+1) (n:=2) (motive:=fun _ => List Bool)
    (Fin.addCases (m:=WholePrefix.tapes p) (n:=1) (motive:=fun _ => List Bool)
      (paddedBare p row C D) (fun _ => List.replicate (D+1) false))
    ![out,List.replicate D true]

private theorem small_bare (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (j : Fin 64) :
    paddedBare p row C D ((j.castAdd 6).castAdd (CloseoutRowsRawRecord.tapes p)) =
      ZeroPadding.pad (C10RowScannerReload.caps C D j) (Prepare.output row j) := by
  have hn : j.val ≠ 68 := by have := j.isLt; omega
  simp only [paddedBare, WarmReuse.padded, Reset.caps, WarmFields.bare,
    Warm.supplied, Scanned.output, Fin.addCases_left, Fin.val_castAdd]
  change ZeroPadding.pad (if j.val=52 then C else 0)
    (ZeroPadding.pad (if j.val=52 ∨ j.val=68 then 0 else D)
      (Prepare.output row j)) = _
  by_cases h : j=52
  · subst j
    simp [C10RowScannerReload.caps]
  · have hv : j.val ≠ 52 := fun he => h (Fin.ext he)
    simp [C10RowScannerReload.caps,h,hv,hn]

private theorem extra_bare (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (hCD : C ≤ D) (j : Fin 6) :
    paddedBare p row C D ((j.natAdd 64).castAdd (CloseoutRowsRawRecord.tapes p)) =
      if 64+j.val=68 then List.replicate C true else List.replicate D false := by
  simp only [paddedBare,WarmReuse.padded,Reset.caps,WarmFields.bare,Warm.supplied,
    Scanned.output,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd]
  fin_cases j <;> simp [Scanned.extra,ZeroPadding.pad]
  omega

private theorem high_bare (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (hCD : C ≤ D) (i : Fin (WholePrefix.tapes p)) (hi : 64 ≤ i.val) :
    paddedBare p row C D i =
      if i.val=68 then List.replicate C true else List.replicate D false := by
  by_cases h70 : i.val<70
  · let j : Fin 6 := ⟨i.val-64,by omega⟩
    have he : i=(j.natAdd 64).castAdd (CloseoutRowsRawRecord.tapes p) := Fin.ext (by dsimp [j];omega)
    rw [he]
    exact extra_bare p row C D hCD j
  · let j : Fin (CloseoutRowsRawRecord.tapes p) := ⟨i.val-70,by have := i.isLt;unfold WholePrefix.tapes at this;omega⟩
    have he : i=j.natAdd 70 := Fin.ext (by dsimp [j];omega)
    rw [he]
    have h52 : 70+j.val ≠ 52 := by omega
    have h68 : 70+j.val ≠ 68 := by omega
    simp [paddedBare,WarmReuse.padded,Reset.caps,WarmFields.bare,Warm.supplied,
      WholePrefix.extra,Fin.val_natAdd,h52,h68,ZeroPadding.pad]

private theorem avoid_old (p : Program) (i : Fin (WholePrefix.tapes p))
    (hi : 64 ≤ i.val) :
    ∀ j,C10RowScannerDock.slots p j ≠ (Reuse.old p i).castAdd 3 := by
  intro j he
  have hv := congrArg Fin.val he
  have bound := i.isLt
  revert hv
  refine Fin.addCases (m:=64) (n:=5) (fun k => ?_) (fun k => ?_) j
  · intro hv
    have := k.isLt
    simp only [C10RowScannerDock.slots,Fin.addCases_left,C10RowScannerDock.small] at hv
    change k.val=i.val at hv
    omega
  · intro hv
    simp only [C10RowScannerDock.slots,Fin.addCases_right] at hv
    fin_cases k <;>
      dsimp [C10RowScannerDock.slots,Reuse.old,Reuse.driver,Reuse.log,Reuse.tapes] at hv <;> omega

theorem old_output (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool)
    (hcapacity : old (Retained.capacity p)=List.replicate C true) (hCD : C ≤ D)
    (i : Fin (WholePrefix.tapes p)) :
    install (C10RowScannerDock.slots p) (C10RowScannerDock.input p row C D old out)
      (C10RowScannerReload.output row C D) ((Reuse.old p i).castAdd 3) = paddedBare p row C D i := by
  by_cases hi : i.val<64
  · let j : Fin 64 := ⟨i.val,hi⟩
    have he : i=(j.castAdd 6).castAdd (CloseoutRowsRawRecord.tapes p) := Fin.ext rfl
    have hs : (Reuse.old p i).castAdd 3=C10RowScannerDock.slots p (j.castAdd 5) := by
      apply Fin.ext
      simp only [C10RowScannerDock.slots,Fin.addCases_left]
      rfl
    rw [hs,install_slot _ (C10RowScannerDock.injective p),he,small_bare]
    simp only [C10RowScannerReload.output,Fin.addCases_left]
  · rw [install_other _ _ _ _ (avoid_old p i (by omega)),high_bare p row C D hCD i (by omega)]
    simp only [C10RowScannerDock.input,Fin.addCases_left]
    have hn : Reuse.old p i ≠ Reuse.native p := by
      intro he;have hv := congrArg Fin.val he;change i.val=52 at hv;omega
    rw [Function.update_of_ne hn]
    have ho : Reuse.old p i ≠ Reuse.output p := by
      intro he;have hv := congrArg Fin.val he;have := i.isLt;dsimp [Reuse.old,Reuse.output] at hv;omega
    have hd : Reuse.old p i ≠ Reuse.driver p := by
      intro he;have hv := congrArg Fin.val he;have := i.isLt;dsimp [Reuse.old,Reuse.driver] at hv;omega
    have hl : Reuse.old p i ≠ Reuse.log p := by
      intro he;have hv := congrArg Fin.val he;have := i.isLt;dsimp [Reuse.old,Reuse.log] at hv;omega
    simp only [exitTapes,ho,hd,hl,hn,if_false]
    by_cases hc : i.val=68
    · have he : Reuse.old p i=Reuse.capacity p := Fin.ext hc
      simp only [he,hc,if_true,hcapacity]
    · have he : Reuse.old p i≠Reuse.capacity p := fun h => hc (congrArg Fin.val h)
      simp only [he,hc,if_false]

theorem tail (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) (j : Fin 5) :
      install (C10RowScannerDock.slots p) (C10RowScannerDock.input p row C D old out) (C10RowScannerReload.output row C D) (C10RowScannerDock.slots p (j.natAdd 64)) = C10RowScannerReload.extra row D j := by
    rw [install_slot _ (C10RowScannerDock.injective p)]
    exact Fin.addCases_right j
theorem log (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) : install (C10RowScannerDock.slots p) (C10RowScannerDock.input p row C D old out) (C10RowScannerReload.output row C D) ((Reuse.log p).castAdd 3)=List.replicate (D+1) false := by
    have hs : C10RowScannerDock.slots p ((4 : Fin 5).natAdd 64)=(Reuse.log p).castAdd 3 := by
      simp only [C10RowScannerDock.slots,Fin.addCases_right]
      rfl
    have h := tail p row C D old out 4
    rw [hs] at h
    exact h
theorem drv (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) : install (C10RowScannerDock.slots p) (C10RowScannerDock.input p row C D old out) (C10RowScannerReload.output row C D) ((Reuse.driver p).castAdd 3)=List.replicate D true := by
    have hs : C10RowScannerDock.slots p ((3 : Fin 5).natAdd 64)=(Reuse.driver p).castAdd 3 := by
      simp only [C10RowScannerDock.slots,Fin.addCases_right]
      rfl
    have h := tail p row C D old out 3
    rw [hs] at h
    exact h
theorem outT (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) : install (C10RowScannerDock.slots p) (C10RowScannerDock.input p row C D old out) (C10RowScannerReload.output row C D) ((Reuse.output p).castAdd 3)=out := by
    have avoid : ∀ j,C10RowScannerDock.slots p j ≠ (Reuse.output p).castAdd 3 := by
      intro j he
      have hv := congrArg Fin.val he
      have wide := tapes_ge p
      revert hv
      refine Fin.addCases (m:=64) (n:=5) (fun k => ?_) (fun k => ?_) j
      · intro hv
        have := k.isLt
        simp only [C10RowScannerDock.slots,Fin.addCases_left] at hv
        change k.val=WholePrefix.tapes p+1 at hv
        omega
      · intro hv
        simp only [C10RowScannerDock.slots,Fin.addCases_right] at hv
        fin_cases k <;> dsimp [Reuse.driver,Reuse.log,Reuse.output,Reuse.tapes] at hv <;> omega
    rw [install_other _ _ _ _ avoid]
    have hn : Reuse.output p ≠ Reuse.native p := by
      intro he
      have hv := congrArg Fin.val he
      rw [output_val,native_val] at hv
      have := tapes_ge p
      omega
    simp only [C10RowScannerDock.input,Fin.addCases_left,Function.update_of_ne hn]
    exact exitTapes_output p D old out
theorem fields (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) (j : Fin 3) :
    install (C10RowScannerDock.slots p) (C10RowScannerDock.input p row C D old out)
      (C10RowScannerReload.output row C D) (j.natAdd (Reuse.tapes p)) = C10RowScannerReload.fields row j := by
  have hs : C10RowScannerDock.slots p ((j.castAdd 2).natAdd 64)=j.natAdd (Reuse.tapes p) := by
    simp only [C10RowScannerDock.slots,Fin.addCases_right]
    fin_cases j <;> rfl
  have he : C10RowScannerReload.extra row D (j.castAdd 2)=C10RowScannerReload.fields row j := by
    fin_cases j <;> rfl
  have h := tail p row C D old out (j.castAdd 2)
  rw [hs,he] at h
  exact h

theorem output (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool)
    (hcapacity : old (Retained.capacity p)=List.replicate C true) (hCD : C ≤ D) :
    install (C10RowScannerDock.slots p) (C10RowScannerDock.input p row C D old out)
      (C10RowScannerReload.output row C D) =
      Fin.addCases (m:=Reuse.tapes p) (n:=3) (motive:=fun _ => List Bool)
        (bareBank p row C D out) (C10RowScannerReload.fields row) := by
  funext i
  refine Fin.addCases (m:=Reuse.tapes p) (n:=3) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.addCases (m:=WholePrefix.tapes p+1) (n:=2) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m:=WholePrefix.tapes p) (n:=1) (fun l => ?_) (fun l => ?_) k
      · simpa only [bareBank,Fin.addCases_left,Reuse.old] using old_output p row C D old out hcapacity hCD l
      · have he : l=0 := Subsingleton.elim _ _
        subst l
        simpa only [bareBank,Fin.addCases_left,Fin.addCases_right,Reuse.log] using log p row C D old out
    · simp only [bareBank,Fin.addCases_right]
      fin_cases k
      · exact outT p row C D old out
      · exact drv p row C D old out

  · simpa only [Fin.addCases_right] using fields p row C D old out j

/-- The actual scanner run ends at the complete padded bare bank. -/
theorem run (p : Program) (row : EquationRow.Input) (C D : ℕ)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool)
    (hcapacity : old (Retained.capacity p)=List.replicate C true) (hCD : C ≤ D)
    (hd : row.d ≤ D) (hp : row.p ≤ D) (hD : 1 ≤ D) :
    ExtDecompositionBatch.Step (RecoveryFocus.machine (C10RowScannerDock.slots p) C10RowScannerReload.machine)
      (C10RowScannerReload.budget row D) (C10RowScannerDock.heads p out)
      (C10RowScannerDock.input p row C D old out) (C10RowScannerDock.heads p out)
      (Fin.addCases (m:=Reuse.tapes p) (n:=3) (motive:=fun _ => List Bool)
        (bareBank p row C D out) (C10RowScannerReload.fields row)) :=
  (C10RowScannerDock.run p row C D old out hd hp hD).congr rfl
    (output p row C D old out hcapacity hCD)

end NearCubicWires.P1Independent.ScannerBare
