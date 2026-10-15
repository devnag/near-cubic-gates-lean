import Proof.CaseAnalysis.RowsDegreeReset
import Proof.Amplification.RecoveryScratchErase

/-! The actual degree call's reset is followed by a paid coarse sweep.
The native row context and append cursor survive; all 57 degree-work tapes
and both recording tapes are ready for the next metadata load. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeClean
open LocalBitMultitape RecoveryExecution RecoveryRootRound CloseoutRowsDegreeReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 59) : Fin 106 :=
  if i.val=0 then 44 else if i.val=1 then 47 else if i.val=2 then 48
  else if i.val<57 then ⟨i.val+46,by omega⟩ else ⟨i.val+47,by omega⟩
theorem slots_val (i : Fin 59) : (slots i).val=
    if i.val=0 then 44 else if i.val=1 then 47 else if i.val=2 then 48
    else if i.val<57 then i.val+46 else i.val+47 := by
  unfold slots
  split_ifs <;> rfl
theorem injective : Function.Injective slots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [slots_val,slots_val] at hv
  split_ifs at hv <;> omega
theorem work_slot (i : Fin 57) : slots (i.castAdd 2)=(work i).castAdd 3 := by
  apply Fin.ext
  simp [slots_val,work_val,i.isLt]
theorem selected_work (i : Fin 103) (hi : selected i=true) : ∃ j,work j=i := by
  simp only [selected,decide_eq_true_eq] at hi
  rcases hi with rfl|rfl|rfl|hi
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · let j : Fin 57 := ⟨i.val-46,by have hb:=i.isLt; omega⟩
    refine ⟨j,?_⟩
    apply Fin.ext
    rw [work_val]
    change (if i.val-46=0 then 44 else if i.val-46=1 then 47 else if i.val-46=2 then 48
      else i.val-46+46)=i.val
    split_ifs <;> omega
theorem outside (i : Fin 103) (hi : selected i=false) : ∀ j,slots j≠i.castAdd 3 := by
  intro j
  refine Fin.addCases (m := 57) (n := 2) (fun k => ?_) (fun k => ?_) j
  · rw [work_slot]
    intro he
    have hk : work k=i := Fin.ext (congrArg (fun x : Fin 106 => x.val) he)
    have hs := work_selected k
    rw [hk,hi] at hs
    contradiction
  · intro he
    have hv := congrArg Fin.val he
    have hb := i.isLt
    fin_cases k
    · change 104=i.val at hv
      omega
    · change 105=i.val at hv
      omega
theorem log_outside : ∀ j,slots j≠103 := by
  intro j he
  have hv := congrArg Fin.val he
  rw [slots_val] at hv
  change (if j.val=0 then 44 else if j.val=1 then 47 else if j.val=2 then 48
    else if j.val<57 then j.val+46 else j.val+47)=103 at hv
  split_ifs at hv <;> omega

def extra (C : ℕ) : Fin 2 → List Bool := ![List.replicate C true,List.replicate (C+1) false]
noncomputable def first {s : ℕ} (p : Machine 103 s) := TapeEmbedding.machine 2 (CloseoutRowsDegreeReset.machine p)
noncomputable def last := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 57)
noncomputable def machine {s : ℕ} (p : Machine 103 s) := Composition.machine (first p) last
noncomputable def input {s : ℕ} (c : Configuration 103 s) (C : ℕ) :=
  Composition.leftConfig 4 (TapeEmbedding.config (fun _ : Fin 2 => 0) (extra C)
    (CloseoutRowsDegreeReset.input c C))
def budget (fuel C : ℕ) := 2*fuel+2*C+7

theorem clean_run {s : ℕ} (p : Machine 103 s) (c : Configuration 103 s)
    (fuel C : ℕ) (raw : ExecutionReceipt 103 s) (hr : runFrom p fuel c=some raw)
    (hh : ∀ i,selected i=true → c.heads i=0)
    (ht : ∀ i,selected i=true → (c.tapes i).length≤C) (hc : fuel+1≤C) :
    ∃ actual,runFrom (machine p) (budget fuel C) (input c C)=some actual ∧
      (∀ i,actual.final.heads (i.castAdd 3)=if selected i then 0 else raw.final.heads i) ∧
      (∀ i,actual.final.tapes (i.castAdd 3)=if selected i then List.replicate C false else raw.final.tapes i) ∧
      actual.final.heads 103=0 ∧ actual.final.tapes 103=List.replicate C false ∧
      actual.final.heads 104=0 ∧ actual.final.tapes 104=List.replicate C true ∧
      actual.final.heads 105=0 ∧ actual.final.tapes 105=List.replicate (C+1) false ∧
      actual.steps≤budget fuel C := by
  obtain ⟨reset,hrst,rh,rt,rlogH,rlogT,rl,_⟩ := CloseoutRowsDegreeReset.reset_run p c fuel C raw hr hh ht hc
  let a := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (extra C) reset
  have ha := TapeEmbedding.run_embed (CloseoutRowsDegreeReset.machine p)
    (fun _ : Fin 2 => 0) (extra C) _ _ reset hrst
  let backing := fun i : Fin 57 => a.final.tapes ((work i).castAdd 3)
  have hb : ∀ i,(backing i).length≤C := by
    intro i
    change (a.final.tapes (((work i).castAdd 1).castAdd 2)).length≤C
    rw [TapeEmbedding.receipt_tapes_old]
    exact (rl (work i) (work_selected i)).le
  obtain ⟨erase,he,et,eh,_⟩ := RecoveryScratchErase.erase_ready C (C+1) backing hb
  have hiH : ∀ j,a.final.heads (slots j)=0 := by
    intro j
    refine Fin.addCases (m := 57) (n := 2) (fun i => ?_) (fun i => ?_) j
    · rw [work_slot]
      change a.final.heads (((work i).castAdd 1).castAdd 2)=0
      rw [TapeEmbedding.receipt_heads_old,rh,work_selected]
      simp only [↓reduceIte]
    · fin_cases i <;> rfl
  have hiT : ∀ j,a.final.tapes (slots j)=
      (Fin.addCases (m := 58) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 57) (n := 1) (motive := fun _ => List Bool)
          backing (fun _ => List.replicate C true)) (fun _ => List.replicate (C+1) false)) j := by
    intro j
    refine Fin.addCases (m := 57) (n := 2) (fun i => ?_) (fun i => ?_) j
    · rw [work_slot]
      change backing i=_
      change backing i=(Fin.addCases (m := 58) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 57) (n := 1) (motive := fun _ => List Bool)
          backing (fun _ => List.replicate C true)) (fun _ => List.replicate (C+1) false))
          ((i.castAdd 1).castAdd 1)
      simp only [Fin.addCases_left]
    · fin_cases i <;> rfl
  obtain ⟨b,hbRun,_,_,bh,bt,bkeep⟩ := RecoveryFocus.dock slots injective
    (RecoveryScratchErase.resetMachine 57) _ a.final.heads a.final.tapes _ hiH hiT erase he
  have hlast : runFrom last (2*C+4) (Composition.restart a.final last.start)=some b := hbRun
  have whole := Composition.run_join (first p) last _ _ _ a b ha hlast
  have htime : CloseoutRowsDegreeReset.budget fuel+1+(2*C+4)=budget fuel C := by
    unfold CloseoutRowsDegreeReset.budget budget
    omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_,?_,?_,?_,?_,?_,
    runFrom_steps_le (machine p) _ _ _ whole⟩
  · intro i
    change b.final.heads (i.castAdd 3)=_
    cases hs : selected i
    · change b.final.heads (i.castAdd 3)=raw.final.heads i
      rw [(bkeep _ (outside i hs)).1]
      change a.final.heads ((i.castAdd 1).castAdd 2)=_
      rw [TapeEmbedding.receipt_heads_old,rh,hs]
      simp only [Bool.false_eq_true,↓reduceIte]
    · obtain ⟨j,hj⟩ := selected_work i hs
      change b.final.heads (i.castAdd 3)=0
      rw [←hj,←work_slot,bh,eh]
  · intro i
    change b.final.tapes (i.castAdd 3)=_
    cases hs : selected i
    · change b.final.tapes (i.castAdd 3)=raw.final.tapes i
      rw [(bkeep _ (outside i hs)).2]
      change a.final.tapes ((i.castAdd 1).castAdd 2)=_
      rw [TapeEmbedding.receipt_tapes_old,rt]
      simp only [caps,hs,Bool.false_eq_true,if_false,ZeroPadding.pad_zero]
    · obtain ⟨j,hj⟩ := selected_work i hs
      change b.final.tapes (i.castAdd 3)=List.replicate C false
      rw [←hj,←work_slot,bt,et]
      change (Fin.addCases (m := 58) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 57) (n := 1) (motive := fun _ => List Bool)
          (fun _ => List.replicate C false) (fun _ => List.replicate C true))
          (fun _ => List.replicate (max (C+1) (C+1)) false)) ((j.castAdd 1).castAdd 1)=_
      simp only [Fin.addCases_left]
  · change b.final.heads 103=0
    rw [(bkeep 103 log_outside).1]
    exact rlogH
  · change b.final.tapes 103=List.replicate C false
    rw [(bkeep 103 log_outside).2]
    exact rlogT
  · change b.final.heads (slots 57)=0
    rw [bh,eh]
  · change b.final.tapes (slots 57)=List.replicate C true
    rw [bt,et]
    rfl
  · change b.final.heads (slots 58)=0
    rw [bh,eh]
  · change b.final.tapes (slots 58)=List.replicate (C+1) false
    rw [bt,et,max_self]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeClean
