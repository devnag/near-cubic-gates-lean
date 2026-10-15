import Proof.CaseAnalysis.RowsEstimatorDriverCleanLog
import Proof.MachineModel.ClockUnarySum

/-! Copy the actual D word, then clear its bounded private producer bank.
Ports 0/1/2/3 are D, an empty zero summand, the new D copy, and its log;
the private producer words follow. Every operation is an original machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverCleanBank
open LocalBitMultitape RecoveryRootRound StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input {t : ℕ} (D : ℕ) (data : Fin t → List Bool) : Fin (4+t) → List Bool :=
  Fin.addCases (![List.replicate D true,[],[],[]] : Fin 4 → List Bool) data
def middle {t : ℕ} (D : ℕ) (data : Fin t → List Bool) : Fin (4+t) → List Bool :=
  Fin.addCases (![List.replicate D true,[],List.replicate D true,List.replicate (D+2) false] : Fin 4 → List Bool) data
def slots (t : ℕ) (i : Fin (t+1+2)) : Fin (4+t) :=
  if hi : i.val<t then ⟨4+i.val,by omega⟩
  else ⟨if i.val=t then 0 else if i.val=t+1 then 2 else 3,by split_ifs <;> omega⟩
theorem slots_val (t : ℕ) (i : Fin (t+1+2)) :
    (slots t i).val=if i.val<t then 4+i.val else if i.val=t then 0 else if i.val=t+1 then 2 else 3 := by
  unfold slots
  split_ifs <;> rfl
theorem injective (t : ℕ) : Function.Injective (slots t) := by
  intro i j he
  have hi:=i.isLt
  have hj:=j.isLt
  have hv:=congrArg (fun z : Fin (4+t) => z.val) he
  apply Fin.ext
  rw [slots_val,slots_val] at hv
  split_ifs at hv <;> omega
theorem work_slot {t : ℕ} (j : Fin t) : slots t ((j.castAdd 1).castAdd 2)=j.natAdd 4 := by
  simp [slots,j.isLt]
  rfl
theorem driver_slot (t : ℕ) : slots t (((0 : Fin 1).natAdd t).castAdd 2)=(0 : Fin 4).castAdd t := by
  apply Fin.ext
  rw [slots_val]
  simp
theorem copy_slot (t : ℕ) : slots t ((0 : Fin 2).natAdd (t+1))=(2 : Fin 4).castAdd t := by
  apply Fin.ext
  rw [slots_val]
  simp
theorem log_slot (t : ℕ) : slots t ((1 : Fin 2).natAdd (t+1))=(3 : Fin 4).castAdd t := by
  apply Fin.ext
  rw [slots_val]
  simp only [Fin.val_natAdd,Fin.val_one,Fin.val_castAdd]
  split_ifs <;> omega
theorem avoids (t : ℕ) : ∀ i,slots t i≠(1 : Fin 4).castAdd t := by
  intro i he
  have hv:=congrArg (fun z : Fin (4+t) => z.val) he
  change (slots t i).val=1 at hv
  rw [slots_val] at hv
  split_ifs at hv <;> omega

def first (t : ℕ) := TapeEmbedding.machine t ClockUnarySum.machine
noncomputable def last (t K : ℕ) := RecoveryFocus.machine (slots t) (DriverClean.machine t K)
noncomputable def machine (t K : ℕ) := Composition.machine (first t) (last t K)

theorem copy_ready {t : ℕ} (D : ℕ) (data : Fin t → List Bool) :
    ClockJoin.ReadyRun (first t) (2*D+6) (input D data) (middle D data) := by
  obtain ⟨base,hb,bt,bh,bs⟩:=ClockUnarySum.sum_ready D 0
  have hr:=TapeEmbedding.run_embed ClockUnarySum.machine (fun _ : Fin t => 0) data _ _ base hb
  have hi : TapeEmbedding.config (fun _ : Fin t => 0) data
      (initialConfiguration ClockUnarySum.machine ![List.replicate D true,List.replicate 0 true,[],[]])=
      initialConfiguration (first t) (input D data) := by
    apply configuration_ext
    · rfl
    · funext i;refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hi] at hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin t => 0) data base,hr,?_,?_,by change base.steps≤_;simpa using bs⟩
  · change (Fin.addCases base.final.tapes data : Fin (4+t) → List Bool)=_
    rw [bt]
    rfl
  · intro i
    refine Fin.addCases (m:=4) (n:=t) (fun j => ?_) (fun j => ?_) i
    · simpa [TapeEmbedding.receipt,TapeEmbedding.config] using bh j
    · simp [TapeEmbedding.receipt,TapeEmbedding.config]

theorem clean_ready {t : ℕ} (D K : ℕ) (data : Fin t → List Bool)
    (bound : ∀ i,(data i).length≤K*D) :
    ClockJoin.ReadyRun (last t K) (K*(5*D+10)+1) (middle D data)
      (middle D (fun _ : Fin t => List.replicate (K*D) false)) := by
  obtain ⟨base,hb,bt,bh,bs⟩:=DriverClean.logged_run D K (D+2) data bound (by omega)
  obtain ⟨r,hr,_rc,rs,rh,rt,keep⟩:=RecoveryFocus.dock (slots t) (injective t)
    (DriverClean.machine t K) _ (fun _=>0) (middle D data) _
    (by intro i;rfl)
    (by
      intro i
      refine Fin.addCases (m:=t+1) (n:=2) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) j
        · rw [work_slot];simp [middle,DriverClean.logged,RecoveryScratchErase.tapes,overlay,initialConfiguration]
        · fin_cases j;erw [driver_slot];simp [middle,DriverClean.logged,RecoveryScratchErase.tapes,initialConfiguration]
      · fin_cases j
        · erw [copy_slot];simp [middle,DriverClean.logged,initialConfiguration]
        · erw [log_slot];simp [middle,DriverClean.logged,initialConfiguration]) base hb
  refine ⟨r,hr,?_,?_,rs.trans_le bs⟩
  · funext i
    refine Fin.addCases (m:=4) (n:=t) (fun j=>?_) (fun j=>?_) i
    · fin_cases j
      · simpa [driver_slot,bt,DriverClean.logged,RecoveryScratchErase.tapes,middle] using rt (((0 : Fin 1).natAdd t).castAdd 2)
      · simpa [middle] using (keep _ (avoids t)).2
      · simpa [copy_slot,bt,DriverClean.logged,middle] using rt ((0 : Fin 2).natAdd (t+1))
      · simpa [log_slot,bt,DriverClean.logged,middle] using rt ((1 : Fin 2).natAdd (t+1))
    · simpa [work_slot,bt,DriverClean.logged,RecoveryScratchErase.tapes,middle,overlay] using rt ((j.castAdd 1).castAdd 2)
  · intro i
    refine Fin.addCases (m:=4) (n:=t) (fun j=>?_) (fun j=>?_) i
    · fin_cases j
      · simpa [driver_slot,bh] using rh (((0 : Fin 1).natAdd t).castAdd 2)
      · exact (keep _ (avoids t)).1
      · simpa [copy_slot,bh] using rh ((0 : Fin 2).natAdd (t+1))
      · simpa [log_slot,bh] using rh ((1 : Fin 2).natAdd (t+1))
    · simpa [work_slot,bh] using rh ((j.castAdd 1).castAdd 2)

theorem ready {t : ℕ} (D K : ℕ) (data : Fin t → List Bool)
    (bound : ∀ i,(data i).length≤K*D) :
    ClockJoin.ReadyRun (machine t K) (2*D+6+1+(K*(5*D+10)+1)) (input D data)
      (middle D (fun _ : Fin t => List.replicate (K*D) false)) :=
  ClockJoin.join _ _ _ _ _ _ _ (copy_ready D data) (clean_ready D K data bound)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverCleanBank
