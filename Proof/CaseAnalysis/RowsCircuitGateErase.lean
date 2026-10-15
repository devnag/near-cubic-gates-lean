import Proof.CaseAnalysis.RowsCircuitNativePrefix

/-! The paid inner gate sweep is reused after top publication and after
count-header writing. It preserves all prefix, policy and append fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitGateErase
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuitAllocate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1050 → Fin 1703 := Fin.addCases (m:=1048) (n:=2) gate ![1694,1695]
noncomputable def machine:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1048)
noncomputable def output (C : ℕ) (A : Fin 1703 → List Bool):=
  install slots A (PCPTraversal.clearedLocal 1048 C (C+1))

theorem slots_val (i : Fin 1050) : (slots i).val=
    if i.val<1048 then 639+(if i.val<1035 then i.val else i.val+1)
    else if i.val=1048 then 1694 else 1695:=by
  refine Fin.addCases (m:=1048) (n:=2) ?_ ?_ i
  · intro j
    simp only [slots,Fin.addCases_left,gate_val,Fin.val_castAdd,if_pos j.isLt]
  · intro j;fin_cases j <;> rfl

theorem injective : Function.Injective slots:=by
  intro i j h;have hv:=congrArg Fin.val h
  rw [slots_val,slots_val] at hv
  apply Fin.ext;split_ifs at hv <;> omega

theorem output_gate (C : ℕ) (A : Fin 1703 → List Bool) (j : Fin 1048) :
    output C A (gate j)=List.replicate C false:=by
  have h:=install_slot slots injective A (PCPTraversal.clearedLocal 1048 C (C+1))
    ((j.castAdd 1).castAdd 1)
  have he:(j.castAdd 1).castAdd 1=j.castAdd 2:=Fin.ext rfl
  simp only [PCPTraversal.clearedLocal,Fin.addCases_left] at h
  simpa only [output,he,slots,Fin.addCases_left] using h

theorem output_driver (C : ℕ) (A : Fin 1703 → List Bool) :
    output C A 1694=List.replicate C true:=
  install_slot slots injective A (PCPTraversal.clearedLocal 1048 C (C+1)) 1048

theorem output_log (C : ℕ) (A : Fin 1703 → List Bool) :
    output C A 1695=List.replicate (C+1) false:=by
  have h:=install_slot slots injective A (PCPTraversal.clearedLocal 1048 C (C+1)) 1049
  change output C A 1695=List.replicate (max (C+1) (C+1)) false at h
  simpa only [Nat.max_self] using h

theorem outside (i : Fin 1703)
    (hi : (i.val < 639 ∨ 1687 < i.val ∨ i.val = 1674) ∧ i.val ≠ 1694 ∧ i.val ≠ 1695) :
    ∀ j,slots j≠i:=by
  intro j h;have hv:=congrArg Fin.val h
  rw [slots_val] at hv
  split_ifs at hv <;> omega

theorem output_other (C : ℕ) (A : Fin 1703 → List Bool) (i : Fin 1703)
    (hi : (i.val < 639 ∨ 1687 < i.val ∨ i.val = 1674) ∧ i.val ≠ 1694 ∧ i.val ≠ 1695) :
    output C A i=A i:=install_other _ _ _ _ (outside i hi)

theorem erase_run (C : ℕ) (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (hh : ∀ j,H (slots j)=0) (hb : ∀ j,(A (gate j)).length≤C)
    (hd : A 1694=List.replicate C true) (hl : A 1695=List.replicate (C+1) false) :
    PCPOuter.Exact machine (2*C+4) H A H (output C A):=by
  have base:=RecoveryScratchErase.erase_ready C (C+1) (fun j=>A (gate j)) hb
  obtain ⟨r,hr,rh,rt,rs⟩:=base.focus_at slots injective H A (by
    intro j
    refine Fin.addCases (m:=1049) (n:=1) ?_ ?_ j
    · intro k
      refine Fin.addCases (m:=1048) (n:=1) ?_ ?_ k
      · intro i
        simp only [Fin.addCases_left]
        have he:(i.castAdd 1).castAdd 1=i.castAdd 2:=Fin.ext rfl
        rw [he];simp only [slots,Fin.addCases_left]
      · intro i;have hi:i=0:=Fin.eq_zero i;subst i;exact hd
    · intro i;have hi:i=0:=Fin.eq_zero i;subst i;exact hl) hh
  exact ⟨r,hr,rh,rt,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitGateErase
