import Proof.CaseAnalysis.CaseTwoBlockScalars
import Proof.CaseAnalysis.ScheduleCoreWidth

/-! The original fixed clause-width schedule feeds the paid occurrence-block
scalars. The actual source q and native clause template are the only inputs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Widths
open LocalBitMultitape RecoveryRootRound RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (D : ℕ):=Width.tapes D+22
def widthSlots (D : ℕ) (i : Fin (Width.tapes D)) : Fin (tapes D):=
  ⟨if i.val=0 then 0 else i.val+1,by have h:=i.isLt;unfold tapes;split_ifs <;>omega⟩
def scalarSlots (D : ℕ) (i : Fin 22) : Fin (tapes D):=
  if i.val=0 then widthSlots D (Width.outputSlot D) else if i.val=1 then ⟨1,by simp [tapes]⟩
  else ⟨Width.tapes D+i.val,by have h:=i.isLt;unfold tapes;omega⟩
def width (D : ℕ):=RecoveryFocus.machine (widthSlots D) (Width.machine D 1)
def scalars (D block : ℕ):=RecoveryFocus.machine (scalarSlots D) (BlockScalars.machine block)
def machine (D block : ℕ):=Composition.machine (width D) (scalars D block)
def input (D q cb : ℕ) (i : Fin (tapes D)):=
  if i.val=0 then List.replicate q true else if i.val=1 then UnaryTemplate.tape cb else []
def budget (D block q cb : ℕ):=Width.budget D 1 q+1+
  BlockScalars.budget block (q+RepairSource.CloseoutLanguage.clauseWidth D q) cb
theorem width_injective (D : ℕ) : Function.Injective (widthSlots D):=by
  intro i j he
  have h:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [widthSlots] at h
  split_ifs at h <;>omega
theorem width_not_one (D : ℕ) (j : Fin (Width.tapes D)) : (widthSlots D j).val≠1:=by
  dsimp only [widthSlots]
  split_ifs <;>omega
theorem scalar_val (D : ℕ) (j : Fin 22) : (scalarSlots D j).val=
    if j.val=0 then (widthSlots D (Width.outputSlot D)).val
    else if j.val=1 then 1 else Width.tapes D+j.val:=by
  unfold scalarSlots
  split_ifs <;>rfl
theorem scalar_injective (D : ℕ) : Function.Injective (scalarSlots D):=by
  intro i j he
  have h:=congrArg Fin.val he
  have hw : (widthSlots D (Width.outputSlot D)).val ≤ Width.tapes D:=by
    have h:=(Width.outputSlot D).isLt
    dsimp only [widthSlots]
    split_ifs <;>omega
  have hw1:=width_not_one D (Width.outputSlot D)
  apply Fin.ext
  simp only [scalar_val] at h
  split_ifs at h <;>omega

theorem widths_run (D block q cb : ℕ) (hD : 1 ≤ D) : ∃ out,
    ClockJoin.ReadyRun (machine D block) (budget D block q cb) (input D q cb) out ∧
      out (scalarSlots D 2)=List.replicate (q+RepairSource.CloseoutLanguage.clauseWidth D q+1) true ∧
      out (scalarSlots D 8)=List.replicate (block*(q+RepairSource.CloseoutLanguage.clauseWidth D q+1)) true ∧
      out (scalarSlots D 14)=List.replicate (q+RepairSource.CloseoutLanguage.clauseWidth D q) true ∧
      out (scalarSlots D 18)=List.replicate cb true:=by
  obtain ⟨w,hw,wv⟩:=Width.width_run D 1 q hD
  simp only [RepairSource.CloseoutLanguage.coreWidth,one_mul] at wv
  have wf:=hw.focus (widthSlots D) (width_injective D) (input D q cb) (by
    intro j
    by_cases hj : j.val=0
    · simp only [widthSlots,hj,if_true,input,Fin.val_mk,Width.input]
    · have hn1:=width_not_one D j
      have hn0 : (widthSlots D j).val≠0:=by simp only [widthSlots,hj,if_false,Fin.val_mk];omega
      simp only [input,hn0,hn1,if_false,Width.input,hj])
  let A:=install (widthSlots D) (input D q cb) w
  obtain ⟨s,hs,s2,s8,s14,s18⟩:=BlockScalars.scalars_run block (q+RepairSource.CloseoutLanguage.clauseWidth D q) cb
  have sf:=hs.focus (scalarSlots D) (scalar_injective D) A (by
    intro j
    by_cases h0 : j.val=0
    · have hj : j=0:=Fin.ext h0
      subst j
      exact (install_slot (widthSlots D) (width_injective D) _ w _).trans wv
    · have ha : ∀ i,widthSlots D i≠scalarSlots D j:=by
        intro i he
        have h:=congrArg Fin.val he
        have hi:=i.isLt
        have hn:=width_not_one D i
        dsimp only [scalarSlots] at h
        rw [if_neg h0] at h
        split_ifs at h <;>dsimp only [widthSlots,Fin.val_mk] at h
        all_goals split_ifs at h <;>omega
      rw [show A (scalarSlots D j)=input D q cb (scalarSlots D j) from install_other _ _ _ _ ha]
      by_cases h1 : j.val=1
      · have hj : j=1:=Fin.ext h1
        subst j;rfl
      · have hW : 1<Width.tapes D:=by simp [Width.tapes,Clause.tapes]
        have hi0 : (scalarSlots D j).val≠0:=by simp only [scalarSlots,h0,h1,if_false,Fin.val_mk];omega
        have hi1 : (scalarSlots D j).val≠1:=by simp only [scalarSlots,h0,h1,if_false,Fin.val_mk];omega
        simp only [input,hi0,hi1,if_false,BlockScalars.input]
        have j0 : j≠0:=fun he=>h0 (congrArg Fin.val he)
        have j1 : j≠1:=fun he=>h1 (congrArg Fin.val he)
        simp only [j0,j1,if_false])
  exact ⟨_,ClockJoin.join _ _ _ _ _ _ _ wf sf,
    (install_slot (scalarSlots D) (scalar_injective D) _ s 2).trans s2,
    (install_slot (scalarSlots D) (scalar_injective D) _ s 8).trans s8,
    (install_slot (scalarSlots D) (scalar_injective D) _ s 14).trans s14,
    (install_slot (scalarSlots D) (scalar_injective D) _ s 18).trans s18⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Widths
