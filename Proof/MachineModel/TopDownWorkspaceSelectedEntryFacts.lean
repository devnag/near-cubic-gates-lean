import Proof.MachineModel.TopDownWorkspaceSelectedEntry

/-! Same-admission application and exact frame facts for the direct prologue.
No original-word premise is left on the public admission-to-entry theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryFacts
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal
open WorkspaceGuardedWorker (entry reference)
open WorkspaceSelectedAdmission (originalTapes preFuel coldCutoff)
open WorkspaceSelectedProgram (finalBank lengthFlag)
open WorkspaceSelectedEntry RecoveryRootRound
noncomputable section
attribute [local irreducible] WorkspaceSelectedProgram.admission

theorem output_public (sources : EightSources) (k r D n : Nat) (x bits : List Bool)
    (w : Nat→List Bool) (i : Fin (size sources k r D))
    (hi : i.val=0 ∨ i.val=1 ∨ i.val=216) :
    output sources k r D n x bits w i=
      if i.val=0 then RepairOrdinary.frame x else if i.val=1 then RepairOrdinary.frame bits else [true] := by
  let b := 218+(60+(engineTapes sources k r D+23))
  have hb : i.val<b := by dsimp only [b];rcases hi with h|h|h <;>omega
  let j : Fin b := ⟨i.val,hb⟩
  have he : i=j.castAdd 1 := Fin.ext rfl
  rw [he]
  simp only [output,Fin.addCases_left,C10SupplierCall.bank,C10SupplierCall.bankAt,Fin.val_castAdd]
  rcases hi with h|h|h
  · have hj:j.val=0:=h
    simp [hj]
  · have hj:j.val=1:=h
    simp [hj]
  · have hj:j.val=216:=h
    simp [hj]

theorem old_bank_retained (sources : EightSources) (k r D n t extra : Nat)
    (ht : 2≤t) (hspace : size sources k r D≤extra)
    (A : Fin t→List Bool) (L : Nat) (x bits : List Bool) (w : Nat→List Bool)
    (hx : A ⟨0,by omega⟩=RepairOrdinary.frame x)
    (hb : A ⟨1,by omega⟩=RepairOrdinary.frame bits) :
    ∀i:Fin t,install (slots ht hspace) (finalBank A L extra) (output sources k r D n x bits w)
      (((i.castAdd 1).castAdd 1).castAdd extra)=A i := by
  intro i
  by_cases h0:i.val=0
  · let j : Fin (size sources k r D) := ⟨0,by dsimp [size];omega⟩
    have he : slots ht hspace j=(((i.castAdd 1).castAdd 1).castAdd extra) := by
      apply Fin.ext;simp [slots,j,h0]
    rw [←he,install_slot _ (slots_injective ht hspace)]
    have hp:=output_public sources k r D n x bits w j (Or.inl rfl)
    have hi:i=⟨0,by omega⟩:=Fin.ext h0
    simpa only [j,if_true,hi] using hp.trans hx.symm
  by_cases h1:i.val=1
  · let j : Fin (size sources k r D) := ⟨1,by dsimp [size];omega⟩
    have he : slots ht hspace j=(((i.castAdd 1).castAdd 1).castAdd extra) := by
      apply Fin.ext;simp [slots,j,h1]
    rw [←he,install_slot _ (slots_injective ht hspace)]
    have hp:=output_public sources k r D n x bits w j (Or.inr (Or.inl rfl))
    have hi:i=⟨1,by omega⟩:=Fin.ext h1
    simpa only [j,show ¬(1:Nat)=0 by omega,if_false,if_true,hi] using hp.trans hb.symm
  · rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      have hi:=i.isLt
      dsimp only [slots,Fin.val_castAdd] at hv
      split_ifs at hv <;>omega)]
    exact WorkspaceSelectedProgram.finalBank_original A L extra i

theorem fresh_retained (sources : EightSources) (k r D n t extra : Nat)
    (ht : 2≤t) (hspace : size sources k r D≤extra)
    (A : Fin t→List Bool) (L : Nat) (x bits : List Bool) (w : Nat→List Bool)
    (j : Fin extra) (hj : size sources k r D≤j.val) :
    install (slots ht hspace) (finalBank A L extra) (output sources k r D n x bits w)
      (j.natAdd (t+1+1))=[] := by
  rw [install_other _ _ _ _ (by
    intro i he
    have hv:=congrArg Fin.val he
    have hi:=i.isLt
    dsimp only [slots,Fin.val_natAdd] at hv
    split_ifs at hv <;>omega)]
  exact Fin.addCases_right j

/-- Literal application from any exact selected admission receipt. The same
bank supplies the input words, and the prologue preserves every old tape. -/
theorem of_admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r extra : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (hspace : size sources k r p.clauseDegree≤extra)
    (n : Nat) (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k)→List Bool) (L : Nat)
    (hr : Step (WorkspaceSelectedProgram.admission sources p k clock extra)
      (preFuel sources p k clock n) (fun _=>0)
      (entry (lengthFlag sources p k extra) (List.ofFn x) bits) (fun _=>0) (finalBank A L extra))
    (admitted : C10LegalAdmission.passed sources p (reference k clock) (coldCutoff sources) n x bits=true) :
    let ht : 2≤originalTapes sources p k := by
      dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
      omega
    let port:=slots ht hspace
    ∃ w,Step (RecoveryFocus.machine port (program sources k r p.clauseDegree).2)
      (C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n) (fun _=>0) (finalBank A L extra)
      (dockH port (fun _=>0) (outputHeads sources k r p.clauseDegree))
      (install port (finalBank A L extra) (output sources k r p.clauseDegree n (List.ofFn x) bits w)) ∧
      (∀i:Fin (originalTapes sources p k),
        install port (finalBank A L extra) (output sources k r p.clauseDegree n (List.ofFn x) bits w)
          (((i.castAdd 1).castAdd 1).castAdd extra)=A i) ∧
      (∀j:Fin extra,size sources k r p.clauseDegree≤j.val →
        install port (finalBank A L extra) (output sources k r p.clauseDegree n (List.ofFn x) bits w)
          (j.natAdd (originalTapes sources p k+1+1))=[]) := by
  intro ht port
  have ho:=WorkspaceSelectedOriginals.originals_of_run sources p k clock extra n x bits A L hr admitted
  obtain ⟨w,hw,_hkeep⟩:=WorkspaceSelectedEntry.run sources p k r extra hspace n x bits A L ho
  exact ⟨w,hw,old_bank_retained sources k r p.clauseDegree n _ extra ht hspace A L (List.ofFn x) bits w
    ho.1 ho.2.1,fun j hj=>fresh_retained sources k r p.clauseDegree n _ extra ht hspace A L
      (List.ofFn x) bits w j hj⟩

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryFacts
