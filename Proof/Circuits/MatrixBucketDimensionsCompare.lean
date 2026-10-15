import Proof.Circuits.MatrixBucketDimensionsBounds

namespace NearCubicWires.RepairOrdinary.MatrixBucketDimensions.Compare
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
      some ⟨1,fun _ => none,![.right,.stay,.stay]⟩
    else if q.val=1 then
      if bits 0 && bits 1 then some ⟨1,fun _ => none,![.right,.right,.stay]⟩
      else some ⟨2,![none,none,some (!bits 0)],fun _ => .stay⟩
    else none
def cfg (q : Fin 3) (U p pos : ℕ) (flag : List Bool) : Configuration 3 3 :=
  ⟨q,![pos+1,pos,0],![UnaryTemplate.tape U,List.replicate p true,flag]⟩
def input (U p : ℕ) : Fin 3→List Bool := ![UnaryTemplate.tape U,List.replicate p true,[]]

theorem boot_step (U p : ℕ) : step raw (initialConfiguration raw (input U p))=some (cfg 1 U p 0 []) := by
  simp [step,raw,initialConfiguration,input,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl
theorem scan_step (U p pos : ℕ) (hU : pos<U) (hp : pos<p) :
    step raw (cfg 1 U p pos [])=some (cfg 1 U p (pos+1) []) := by
  have hleft := UnaryTemplate.tape_mark U pos hU
  have hright : readTapeBit (List.replicate p true) pos=true := by simp [readTapeBit,List.getD,hp]
  simp [step,raw,cfg,Configuration.scanned,hleft,hright]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem stop_step (U p : ℕ) : step raw (cfg 1 U p (min U p) [])=
    some (cfg 2 U p (min U p) [decide (U≤p)]) := by
  by_cases h : U≤p
  · rw [min_eq_left h]
    have hz := UnaryTemplate.tape_end U
    simp [step,raw,cfg,Configuration.scanned,hz,h]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  · rw [min_eq_right (by omega : p≤U)]
    have hleft := UnaryTemplate.tape_mark U p (by omega)
    have hz : readTapeBit (List.replicate p true) p=false := by simp [readTapeBit,List.getD]
    simp [step,raw,cfg,Configuration.scanned,hleft,hz,h]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

theorem scan (U p pos remaining : ℕ) (hu : pos+remaining≤U) (hp : pos+remaining≤p) :
    Timed raw remaining (cfg 1 U p pos []) (cfg 1 U p (pos+remaining) []) := by
  induction remaining generalizing pos with
  | zero => simp; exact Timed.refl _ _
  | succ remaining ih =>
    have ht := ih (pos+1) (by omega) (by omega)
    have hs := Timed.single (by rfl) (scan_step U p pos (by omega) (by omega))
    have h := hs.trans ht
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem raw_run (U p : ℕ) :
    ∃ r,run raw (min U p+2) (input U p)=some r ∧
      r.final=cfg 2 U p (min U p) [decide (U≤p)] ∧ r.steps=min U p+2 := by
  have h0 := Timed.single (by rfl) (boot_step U p)
  have h1 := scan U p 0 (min U p) (by omega) (by omega)
  simp only [Nat.zero_add] at h1
  have h2 := Timed.single (by rfl) (stop_step U p)
  have hall := (h0.trans h1).trans h2
  have ht : 1+min U p+1=min U p+2 := by omega
  rw [ht] at hall
  exact hall.run (by rfl)

def machine := Rewind.machine raw
def capacities (C : ℕ) : Fin 4→ℕ := ![0,C,C,C]
def paddedInput (U p C : ℕ) : Fin 4→List Bool :=
  ![UnaryTemplate.tape U,ZeroPadding.pad C (List.replicate p true),List.replicate C false,List.replicate C false]
def paddedOutput (U p C : ℕ) : Fin 4→List Bool :=
  ![UnaryTemplate.tape U,ZeroPadding.pad C (List.replicate p true),
    ZeroPadding.pad C [decide (U≤p)],List.replicate C false]

theorem compare_run (U p C : ℕ) (hC : min U p+2≤C) :
    RecoveryRootRound.ReadyRun machine (2*min U p+6) (paddedInput U p C) (paddedOutput U p C) := by
  obtain ⟨base,hb,hbf,hbs⟩ := raw_run U p
  obtain ⟨reset,hr,hreset,hs,_⟩ := Rewind.recorded_run raw _ _ base hb 0 (by intro i; rfl)
  have htime : 0+2*base.steps+2=2*min U p+6 := by rw [hbs]; omega
  rw [htime] at hr hs
  obtain ⟨r,hp,hf,hsteps,_⟩ := ZeroPadding.run_config machine (capacities C) _ _ reset hr
  have hi : ZeroPadding.config (capacities C)
      (Rewind.recording (initialConfiguration raw (input U p)) 0)=
      initialConfiguration machine (paddedInput U p C) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,Rewind.recording,Rewind.config,initialConfiguration,Fin.addCases]
    · funext i; fin_cases i <;> simp [ZeroPadding.config,capacities,initialConfiguration,
        input,paddedInput,Fin.addCases,ZeroPadding.pad,Rewind.recording,Rewind.config]
  rw [hi] at hp
  refine ⟨r,hp,?_,?_,hsteps.trans hs⟩
  · rw [hf]
    rw [hreset,hbf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,capacities,Rewind.finished,Rewind.config,
      cfg,paddedOutput,Fin.addCases,hbs,ZeroPadding.pad,Nat.add_sub_of_le hC]
  · intro i; rw [hf,hreset]
    fin_cases i <;> simp [ZeroPadding.config,Rewind.finished,Rewind.config,Fin.addCases]

end NearCubicWires.RepairOrdinary.MatrixBucketDimensions.Compare
