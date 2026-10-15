import Proof.CaseAnalysis.WitnessLegalPolicyRun
import Proof.Amplification.RecoveryScratchErase

/-! The existing parallel erase allocates exactly a fixed selected bank.
Its driver and log are physical tapes; all other policy and output fields
remain untouched. Selection changes only the fixed tape embedding. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedErase
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev Private {t : ℕ} (mask : Fin t→Bool):={i : Fin t // mask i=true}
def count {t : ℕ} (mask : Fin t→Bool):=Fintype.card (Private mask)
def index {t : ℕ} (mask : Fin t→Bool) (j : Fin (count mask)) : Fin t:=
  ((Fintype.equivFin (Private mask)).symm j).val
def slots {t : ℕ} (mask : Fin t→Bool) (driver log : Fin t) : Fin (count mask+2)→Fin t:=
  Fin.addCases (index mask) (fun i : Fin 2=>if i.val=0 then driver else log)
def machine {t : ℕ} (mask : Fin t→Bool) (driver log : Fin t):=
  RecoveryFocus.machine (slots mask driver log) (RecoveryScratchErase.resetMachine (count mask))
def output {t : ℕ} (mask : Fin t→Bool) (log : Fin t) (cap : ℕ) (base : Fin t→List Bool) (i : Fin t):=
  if mask i then List.replicate cap false else if i=log then List.replicate (cap+1) false else base i

theorem index_mask {t : ℕ} (mask : Fin t→Bool) (j : Fin (count mask)) : mask (index mask j)=true:=
  ((Fintype.equivFin (Private mask)).symm j).property
theorem index_injective {t : ℕ} (mask : Fin t→Bool) : Function.Injective (index mask):=by
  intro i j h
  apply (Fintype.equivFin (Private mask)).symm.injective
  exact Subtype.ext h
theorem index_covers {t : ℕ} (mask : Fin t→Bool) (i : Fin t) (hi : mask i=true) :
    ∃ j,index mask j=i := ⟨(Fintype.equivFin (Private mask)) ⟨i,hi⟩,by
    simp only [index,Equiv.symm_apply_apply]⟩
theorem slot_index {t : ℕ} (mask : Fin t→Bool) (driver log : Fin t) (j : Fin (count mask)) :
    slots mask driver log (j.castAdd 2)=index mask j:=by rw [slots,Fin.addCases_left]
theorem slot_driver {t : ℕ} (mask : Fin t→Bool) (driver log : Fin t) :
    slots mask driver log ((0 : Fin 2).natAdd (count mask))=driver:=by simp [slots]
theorem slot_log {t : ℕ} (mask : Fin t→Bool) (driver log : Fin t) :
    slots mask driver log ((1 : Fin 2).natAdd (count mask))=log:=by simp [slots]
private theorem driver_index (n : ℕ) : (0 : Fin 2).natAdd n=((0 : Fin 1).natAdd n).castAdd 1:=Fin.ext rfl
private theorem log_index (n : ℕ) : (1 : Fin 2).natAdd n=(0 : Fin 1).natAdd (n+1):=Fin.ext (by simp [Fin.val_natAdd])

private theorem two (i : Fin 2) : i=0 ∨ i=1:=by
  have h:i.val=0 ∨ i.val=1:=by omega
  rcases h with h|h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem slots_injective {t : ℕ} (mask : Fin t→Bool) (driver log : Fin t)
    (hd : mask driver=false) (hl : mask log=false) (hne : driver≠log) :
    Function.Injective (slots mask driver log):=by
  intro i j
  refine Fin.addCases (m:=count mask) (n:=2) ?_ ?_ i
  · intro i
    refine Fin.addCases (m:=count mask) (n:=2) ?_ ?_ j
    · intro j h
      have he:index mask i=index mask j:=by simpa only [slot_index] using h
      exact congrArg (Fin.castAdd 2) (index_injective mask he)
    · intro j h
      rcases two j with rfl|rfl
      · have he:index mask i=driver:=by simpa only [slot_index,slot_driver,slot_log] using h
        have hm:=index_mask mask i;rw [he,hd] at hm;cases hm
      · have he:index mask i=log:=by simpa only [slot_index,slot_driver,slot_log] using h
        have hm:=index_mask mask i;rw [he,hl] at hm;cases hm
  · intro i
    refine Fin.addCases (m:=count mask) (n:=2) ?_ ?_ j
    · intro j h
      rcases two i with rfl|rfl
      · have he:driver=index mask j:=by simpa only [slot_index,slot_driver,slot_log] using h
        have hm:=index_mask mask j;rw [←he,hd] at hm;cases hm
      · have he:log=index mask j:=by simpa only [slot_index,slot_driver,slot_log] using h
        have hm:=index_mask mask j;rw [←he,hl] at hm;cases hm
    · intro j h
      rcases two i with rfl|rfl <;> rcases two j with rfl|rfl
      · rfl
      · exact False.elim (hne (by simpa only [slot_driver,slot_log] using h))
      · exact False.elim (hne (by simpa only [slot_driver,slot_log] using h.symm))
      · rfl

theorem erase_run {t : ℕ} (mask : Fin t→Bool) (driver log : Fin t)
    (hd : mask driver=false) (hl : mask log=false) (hne : driver≠log)
    (cap : ℕ) (heads : Fin t→ℕ) (base : Fin t→List Bool)
    (hh : ∀ i,mask i=true ∨ i=driver ∨ i=log → heads i=0)
    (hb : ∀ i,mask i=true → (base i).length≤cap)
    (hdriver : base driver=List.replicate cap true) (hlog : base log=[]) :
    ∃ r,runFrom (machine mask driver log) (2*cap+4)
      ⟨(machine mask driver log).start,heads,base⟩=some r ∧ r.steps≤2*cap+4 ∧
      r.final.heads=heads ∧ r.final.tapes=output mask log cap base:=by
  let ss:=slots mask driver log
  have inj:=slots_injective mask driver log hd hl hne
  obtain ⟨small,hr,st,sh,steps⟩:=RecoveryScratchErase.erase_ready cap 0 (fun j=>base (index mask j))
    (by intro j;exact hb _ (index_mask mask j))
  have sloth (j : Fin (count mask+2)):heads (ss j)=0:=by
    refine Fin.addCases (m:=count mask) (n:=2) ?_ ?_ j
    · intro j
      simpa only [ss,slot_index] using hh _ (Or.inl (index_mask mask j))
    · intro j;rcases two j with rfl|rfl
      · simpa only [ss,slot_driver,slot_log] using hh driver (Or.inr (Or.inl rfl))
      · simpa only [ss,slot_driver,slot_log] using hh log (Or.inr (Or.inr rfl))
  have slott (j : Fin (count mask+1+1)):base (ss j)=
      (Fin.addCases (m:=count mask+1) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=count mask) (n:=1) (motive:=fun _=>List Bool)
          (fun j=>base (index mask j)) (fun _ : Fin 1=>List.replicate cap true))
        (fun _ : Fin 1=>List.replicate 0 false)) j:=by
    refine Fin.addCases (m:=count mask) (n:=2) ?_ ?_ j
    · intro j
      have he:j.castAdd 2=(j.castAdd 1).castAdd 1:=Fin.ext rfl
      rw [show ss (j.castAdd 2)=index mask j from slot_index mask driver log j,he,Fin.addCases_left,Fin.addCases_left]
    · intro j;rcases two j with rfl|rfl
      · rw [show ss ((0 : Fin 2).natAdd (count mask))=driver from slot_driver mask driver log]
        simpa only [driver_index,Fin.addCases_left,Fin.addCases_right] using hdriver
      · rw [show ss ((1 : Fin 2).natAdd (count mask))=log from slot_log mask driver log]
        simpa only [log_index,Fin.addCases_right,List.replicate_zero] using hlog
  obtain ⟨r,run,_rf,rs,rh,rt,away⟩:=RecoveryFocus.dock ss inj _ _ heads base _ sloth slott small hr
  have selected (j : Fin (count mask)):r.final.tapes (index mask j)=List.replicate cap false:=by
    have he:j.castAdd 2=(j.castAdd 1).castAdd 1:=Fin.ext rfl
    have ht:=rt (j.castAdd 2)
    rw [show ss (j.castAdd 2)=index mask j from slot_index mask driver log j] at ht
    simpa only [st,he,Fin.addCases_left] using ht
  have d:r.final.tapes driver=List.replicate cap true:=by
    have ht:=rt ((0 : Fin 2).natAdd (count mask))
    rw [show ss ((0 : Fin 2).natAdd (count mask))=driver from slot_driver mask driver log] at ht
    simpa only [st,driver_index,Fin.addCases_left,Fin.addCases_right] using ht
  have l:r.final.tapes log=List.replicate (cap+1) false:=by
    have ht:=rt ((1 : Fin 2).natAdd (count mask))
    rw [show ss ((1 : Fin 2).natAdd (count mask))=log from slot_log mask driver log] at ht
    simpa only [st,log_index,Fin.addCases_right,Nat.zero_max] using ht
  refine ⟨r,run,rs.trans_le steps.le,?_,?_⟩
  · funext i
    by_cases his:∃ j,ss j=i
    · obtain ⟨j,rfl⟩:=his
      rw [rh,sh,sloth]
    · exact (away i (by simpa using his)).1
  · funext i
    by_cases hm:mask i=true
    · obtain ⟨j,rfl⟩:=index_covers mask i hm
      simp only [output,index_mask,if_true]
      exact selected j
    have hfalse:mask i=false:=Bool.eq_false_iff.mpr hm
    simp only [output,hfalse]
    by_cases hil:i=log
    · subst i;rw [if_pos rfl];exact l
    rw [if_neg hil]
    by_cases hid:i=driver
    · subst i;exact d.trans hdriver.symm
    exact (away i (by
      intro j
      refine Fin.addCases (m:=count mask) (n:=2) ?_ ?_ j
      · intro j h
        have he:index mask j=i:=by simpa only [ss,slot_index] using h
        apply hm;rw [←he];exact index_mask mask j
      · intro j h;rcases two j with rfl|rfl
        · exact hid (by simpa only [ss,slot_driver] using h.symm)
        · exact hil (by simpa only [ss,slot_log] using h.symm))).2

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedErase
