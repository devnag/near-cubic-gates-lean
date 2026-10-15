import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleClauseWidth
import Proof.CaseAnalysis.ScheduleScale
import Proof.Hierarchy.HierarchyFixedWord
import Proof.MachineModel.ClockUnarySum

namespace GR

/-! Complete cold arithmetic for the exact m_s used by the common language.
The actual native q is the only numerical input; copies and clause degree
are fixed finite-program parameters. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Width
open LocalBitMultitape RepairOrdinary RecoveryRootRound VerifierDecoding
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (D : Nat) := Clause.tapes D+14
def clauseSlots (D : Nat) : Fin (Clause.tapes D)→Fin (tapes D) := fun i=>i.castAdd 14
def fixedSlots (D : Nat) : Fin 2→Fin (tapes D) := fun i=>
  ⟨36+2*D+i.val,by have:=i.isLt;dsimp [tapes,Clause.tapes];omega⟩
def sumSlots (D : Nat) : Fin 4→Fin (tapes D) := fun i=>
  ⟨if i.val=0 then 0 else 36+2*D+(if i.val=1 then 0 else i.val),
    by have:=i.isLt;dsimp [tapes,Clause.tapes];split_ifs <;> omega⟩
def scaleSlots (D : Nat) : Fin 12→Fin (tapes D) := fun i=>
  ⟨if i.val=0 then 38+2*D else if i.val=1 then 24+2*D else 24+2*D+i.val,
    by have:=i.isLt;dsimp [tapes,Clause.tapes];split_ifs <;> omega⟩
theorem clause_injective (D : Nat) : Function.Injective (clauseSlots D) := by
  intro a b h
  have hv:=congrArg (fun i : Fin (tapes D)=>i.val) h
  exact Fin.ext hv
theorem fixed_injective (D : Nat) : Function.Injective (fixedSlots D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp only [fixedSlots] at hv
  omega
theorem sum_injective (D : Nat) : Function.Injective (sumSlots D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  have ha:=a.isLt
  have hb:=b.isLt
  apply Fin.ext
  dsimp only [sumSlots] at hv
  split_ifs at hv <;> omega
theorem scale_injective (D : Nat) : Function.Injective (scaleSlots D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp only [scaleSlots] at hv
  split_ifs at hv <;> omega
def clause (D : Nat) := RecoveryFocus.machine (clauseSlots D) (Clause.machine D)
def fixed (D ext : Nat) := RecoveryFocus.machine (fixedSlots D) (HierarchyFixedWord.machine (List.replicate ext true))
def sum (D : Nat) := RecoveryFocus.machine (sumSlots D) ClockUnarySum.machine
def scale (D copies : Nat) := RecoveryFocus.machine (scaleSlots D) (Scale.machine copies)
def machine (D copies ext : Nat) :=
  Composition.machine (Composition.machine (Composition.machine (clause D) (fixed D ext)) (sum D)) (scale D copies)
def input (D q : Nat) : Fin (tapes D)→List Bool := fun i=>if i.val=0 then List.replicate q true else []
def outputSlot (D : Nat) := scaleSlots D 10
def budget (D copies ext q : Nat) := Clause.budget D q+1+(2*ext+2)+1+(2*(q+1+ext)+6)+1+
  Scale.budget copies (q+1+ext) (CloseoutLanguage.clauseWidth D q)

theorem width_run (D copies ext q : Nat) (hD : 1 ≤ D) : ∃ out,
    ClockJoin.ReadyRun (machine D copies ext) (budget D copies ext q) (input D q) out ∧
      out (outputSlot D)=List.replicate (CloseoutLanguage.coreWidth copies ext D q) true := by
  obtain ⟨clauseOut,hc,hq,hr⟩:=Clause.clause_run D q hD
  have hcf:=hc.focus (clauseSlots D) (clause_injective D) (input D q) (by intro i;rfl)
  let m1:=install (clauseSlots D) (input D q) clauseOut
  change ClockJoin.ReadyRun (clause D) (Clause.budget D q) (input D q) m1 at hcf
  have m1_high (i : Fin (tapes D)) (hi : Clause.tapes D ≤ i.val) : m1 i=[] := by
    dsimp only [m1]
    rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
      dsimp [clauseSlots] at hv;omega)]
    simp only [input]
    split_ifs with h0
    · dsimp [Clause.tapes] at hi;omega
    · rfl
  have m1_q : m1 ⟨0,by dsimp [tapes,Clause.tapes];omega⟩=List.replicate (q+1) true := by
    have he : (⟨0,by dsimp [tapes,Clause.tapes];omega⟩ : Fin (tapes D))=clauseSlots D (Clause.qSlot D) := Fin.ext rfl
    rw [he]
    change install (clauseSlots D) _ _ (clauseSlots D (Clause.qSlot D))=_
    rw [install_slot _ (clause_injective D)]
    exact hq
  have m1_w : m1 ⟨24+2*D,by dsimp [tapes,Clause.tapes];omega⟩=
      CompareMachine.word (CloseoutLanguage.clauseWidth D q) := by
    have he : (⟨24+2*D,by dsimp [tapes,Clause.tapes];omega⟩ : Fin (tapes D))=clauseSlots D (Clause.widthSlot D) := by
      apply Fin.ext
      dsimp [clauseSlots,Clause.widthSlot,Clause.clogSlots]
      omega
    rw [he]
    change install (clauseSlots D) _ _ (clauseSlots D (Clause.widthSlot D))=_
    rw [install_slot _ (clause_injective D)]
    exact hr
  obtain ⟨r0,hr0,ht0,hh0,hs0⟩:=HierarchyFixedWord.word_ready (List.replicate ext true)
  simp only [List.length_replicate] at hr0 ht0 hs0
  have hff:=(show ClockJoin.ReadyRun (HierarchyFixedWord.machine (List.replicate ext true)) (2*ext+2)
      (fun _=>[]) ![List.replicate ext true,List.replicate ext false] from ⟨r0,hr0,ht0,hh0,hs0.le⟩).focus
    (fixedSlots D) (fixed_injective D) m1
    (by
      intro j
      exact m1_high _ (by dsimp [fixedSlots,Clause.tapes];omega))
  let m2:=install (fixedSlots D) m1 ![List.replicate ext true,List.replicate ext false]
  change ClockJoin.ReadyRun (fixed D ext) (2*ext+2) m1 m2 at hff
  have m2_other (i : Fin (tapes D)) (hi : i.val<36+2*D ∨ 38+2*D ≤ i.val) : m2 i=m1 i := by
    dsimp only [m2]
    rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
      dsimp [fixedSlots] at hv;omega)]
  have m2_a : m2 ⟨36+2*D,by dsimp [tapes,Clause.tapes];omega⟩=List.replicate ext true := by
    have he : (⟨36+2*D,by dsimp [tapes,Clause.tapes];omega⟩ : Fin (tapes D))=fixedSlots D 0 := Fin.ext rfl
    rw [he]
    change install (fixedSlots D) _ _ (fixedSlots D 0)=_
    rw [install_slot _ (fixed_injective D)]
    rfl
  have hsf:=(ClockUnarySum.sum_ready (q+1) ext).focus (sumSlots D) (sum_injective D) m2
    (by
      intro j
      fin_cases j
      · change m2 ⟨0,_⟩=_
        rw [m2_other _ (by left;show 0<36+2*D;omega)]
        exact m1_q
      · change m2 ⟨36+2*D+0,_⟩=_
        exact m2_a
      · change m2 ⟨36+2*D+2,_⟩=_
        rw [m2_other _ (by right;show 38+2*D ≤ 36+2*D+2;omega)]
        exact m1_high _ (by show 26+2*D ≤ 36+2*D+2;omega)
      · change m2 ⟨36+2*D+3,_⟩=_
        rw [m2_other _ (by right;show 38+2*D ≤ 36+2*D+3;omega)]
        exact m1_high _ (by show 26+2*D ≤ 36+2*D+3;omega))
  let m3:=install (sumSlots D) m2
    ![List.replicate (q+1) true,List.replicate ext true,List.replicate (q+1+ext) true,
      List.replicate (q+1+ext+2) false]
  change ClockJoin.ReadyRun (sum D) (2*(q+1+ext)+6) m2 m3 at hsf
  have m3_other (i : Fin (tapes D)) (hi : 0 < i.val ∧ i.val < 36+2*D) : m3 i=m2 i := by
    dsimp only [m3]
    rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
      dsimp [sumSlots] at hv;split_ifs at hv <;> omega)]
  have m3_s : m3 ⟨38+2*D,by dsimp [tapes,Clause.tapes];omega⟩=List.replicate (q+1+ext) true := by
    have he : (⟨38+2*D,by dsimp [tapes,Clause.tapes];omega⟩ : Fin (tapes D))=sumSlots D 2 := by
      apply Fin.ext
      simp [sumSlots]
      omega
    rw [he]
    change install (sumSlots D) _ _ (sumSlots D 2)=_
    rw [install_slot _ (sum_injective D)]
    rfl
  obtain ⟨scaleOut,hs,hw⟩:=Scale.scale_run copies (q+1+ext) (CloseoutLanguage.clauseWidth D q)
  have m3_scale (i : Fin 12) (hi : 2 ≤ i.val) : m3 (scaleSlots D i)=[] := by
    have hv : (scaleSlots D i).val=24+2*D+i.val := by
      simp only [scaleSlots]
      split_ifs <;> omega
    have hl := i.isLt
    rw [m3_other _ (by rw [hv];omega),m2_other _ (by left;rw [hv];omega)]
    exact m1_high _ (by rw [hv];dsimp [Clause.tapes];omega)
  have hsc:=hs.focus (scaleSlots D) (scale_injective D) m3 (by
    intro i
    fin_cases i
    · exact m3_s
    · change m3 ⟨24+2*D,_⟩=_
      rw [m3_other _ (show 0<24+2*D ∧ 24+2*D<36+2*D by omega),m2_other _ (by left;show 24+2*D<36+2*D;omega)]
      exact m1_w
    all_goals
      rw [m3_scale _ (by decide)]
      rfl)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hcf hff) hsf) hsc,?_⟩
  rw [outputSlot,install_slot _ (scale_injective D),hw]
  unfold CloseoutLanguage.coreWidth
  congr 2
  omega

end
end NearCubicWires.RepairSource.CloseoutSchedule.Width

end GR
