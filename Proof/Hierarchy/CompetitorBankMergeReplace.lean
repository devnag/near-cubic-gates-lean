import Proof.Hierarchy.CompetitorBankMergeWorkspace
import Proof.Amplification.RecoveryBoundedTapeCopy

/-! Paid replacement of the retained P/N bank using the existing native D
and reset tapes. The raw copier reads false beyond its finite source, so a
short raw result is copied into exactly the original D-cell padded bank. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMergeReplace
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copied_pad (source : List Bool) (d : ℕ) (hd : source.length≤d) :
    RecoveryBoundedTapeCopy.copied source d=ZeroPadding.pad d source := by
  apply List.ext_getElem
  · simp [RecoveryBoundedTapeCopy.copied,ZeroPadding.pad_length,max_eq_left hd]
  · intro i hi hj
    simp only [RecoveryBoundedTapeCopy.copied,List.getElem_map,List.getElem_range]
    have hp := (ZeroPadding.read_pad d source i).symm
    simp only [readTapeBit,List.getD] at hp
    rw [List.getElem?_eq_getElem hj] at hp
    exact hp

def copyInput (source : List Bool) (d : ℕ) : Fin 4 → List Bool :=
  ![source,List.replicate d false,List.replicate d true,List.replicate (d+1) false]
def copyOutput (source : List Bool) (d : ℕ) : Fin 4 → List Bool :=
  ![source,ZeroPadding.pad d source,List.replicate d true,List.replicate (d+1) false]

theorem padded_copy_ready (source : List Bool) (d : ℕ) (hd : source.length≤d) :
    ReadyRun RecoveryBoundedTapeCopy.machine (2*d+4) (copyInput source d) (copyOutput source d) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryBoundedTapeCopy.copy_ready source d (d+1)
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config RecoveryBoundedTapeCopy.machine ![0,d,0,0] _ _ base hr
  have hin : ZeroPadding.config ![0,d,0,0]
      (initialConfiguration RecoveryBoundedTapeCopy.machine ![source,[],List.replicate d true,List.replicate (d+1) false])=
      initialConfiguration RecoveryBoundedTapeCopy.machine (copyInput source d) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,copyInput,ZeroPadding.pad]
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hf]
    have hp : ZeroPadding.pad d (RecoveryBoundedTapeCopy.copied source d)=RecoveryBoundedTapeCopy.copied source d := by
      simp [ZeroPadding.pad]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,ht,copyOutput,hp]
    exact copied_pad source d hd
  · intro i
    rw [hf]
    exact hh i

def eraseInput (backing : List Bool) (d : ℕ) : Fin 3 → List Bool :=
  ![backing,List.replicate d true,List.replicate (d+1) false]
def eraseOutput (d : ℕ) : Fin 3 → List Bool :=
  ![List.replicate d false,List.replicate d true,List.replicate (d+1) false]

theorem erase_ready (backing : List Bool) (d : ℕ) (hd : backing.length≤d) :
    ReadyRun (RecoveryScratchErase.resetMachine 1) (2*d+4) (eraseInput backing d) (eraseOutput d) := by
  have h := RecoveryScratchErase.erase_ready d (d+1) (fun _ : Fin 1 => backing) (fun _ => hd)
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  refine ⟨r,?_,?_,hh,hs⟩
  · convert hr using 2
    funext i
    fin_cases i <;> rfl
  · funext i
    have hi := congrFun ht i
    fin_cases i <;> simpa [eraseOutput,Fin.addCases] using hi

def clearSlots {t : ℕ} (target driver reset : Fin t) : Fin 3 → Fin t := ![target,driver,reset]
def copySlots {t : ℕ} (source target driver reset : Fin t) : Fin 4 → Fin t := ![source,target,driver,reset]
noncomputable def clearProgram {t : ℕ} (target driver reset : Fin t) :=
  RecoveryFocus.machine (clearSlots target driver reset) (RecoveryScratchErase.resetMachine 1)
noncomputable def copyProgram {t : ℕ} (source target driver reset : Fin t) :=
  RecoveryFocus.machine (copySlots source target driver reset) RecoveryBoundedTapeCopy.machine
noncomputable def program {t : ℕ} (source target driver reset : Fin t) :=
  Composition.machine (clearProgram target driver reset) (copyProgram source target driver reset)

theorem replace_run {t : ℕ} (source target driver reset : Fin t)
    (hi : Function.Injective (copySlots source target driver reset))
    (word backing : List Bool) (d : ℕ) (heads : Fin t → ℕ) (ambient : Fin t → List Bool)
    (hw : word.length≤d) (hb : backing.length≤d)
    (hh : ∀ i,heads (copySlots source target driver reset i)=0)
    (ht : ∀ i,ambient (copySlots source target driver reset i)=
      ![word,backing,List.replicate d true,List.replicate (d+1) false] i) :
    ∃ r,runFrom (program source target driver reset) (4*d+9)
      (RecoveryCalls.restarted (program source target driver reset) heads ambient)=some r ∧
      r.final.heads=heads ∧ r.final.tapes=Function.update ambient target (ZeroPadding.pad d word) ∧ r.steps=4*d+9 := by
  have hc : Function.Injective (clearSlots target driver reset) := by
    intro i j he
    have hh' : copySlots source target driver reset i.succ=copySlots source target driver reset j.succ := he
    apply Fin.ext
    have hv := congrArg Fin.val (hi hh')
    change i.val+1=j.val+1 at hv
    omega
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := HierarchyBinary.focused_run (clearSlots target driver reset) hc
    _ _ _ (erase_ready backing d hb) heads ambient (fun i => hh i.succ) (fun i => ht i.succ)
  let middle := install (clearSlots target driver reset) ambient (eraseOutput d)
  have middleSource : middle source=word := by
    have hn : ∀ j,clearSlots target driver reset j≠source := by
      intro j he
      have he' : copySlots source target driver reset j.succ=copySlots source target driver reset 0 := he
      have hf := hi he'
      have hv := congrArg (fun k : Fin 4 => k.val) hf
      change j.val+1=0 at hv
      omega
    exact (install_other (clearSlots target driver reset) ambient (eraseOutput d) source hn).trans (ht 0)
  have hcopy : ∀ i,middle (copySlots source target driver reset i)=copyInput word d i := by
    intro i
    refine Fin.cases middleSource ?_ i
    intro j
    exact install_slot (clearSlots target driver reset) hc ambient (eraseOutput d) j
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := HierarchyBinary.focused_run (copySlots source target driver reset) hi
    _ _ _ (padded_copy_ready word d hw) heads middle hh hcopy
  have he : Composition.restart first.final (copyProgram source target driver reset).start=
      RecoveryCalls.restarted (copyProgram source target driver reset) heads middle := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom (copyProgram source target driver reset) (2*d+4)
      (Composition.restart first.final (copyProgram source target driver reset).start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join (clearProgram target driver reset) (copyProgram source target driver reset)
    _ _ _ first last hfirst hl'
  have htime : (2*d+4)+1+(2*d+4)=4*d+9 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,hlh,?_,?_⟩
  · change last.final.tapes=_
    rw [hlt]
    funext i
    by_cases hit : i=target
    · subst i
      rw [Function.update_self]
      exact install_slot (copySlots source target driver reset) hi middle (copyOutput word d) 1
    · rw [Function.update_of_ne hit]
      by_cases hin : ∃ j,copySlots source target driver reset j=i
      · obtain ⟨j,hj⟩ := hin
        subst i
        rw [install_slot _ hi]
        have hti := ht j
        fin_cases j
        · exact hti.symm
        · exact False.elim (hit rfl)
        · exact hti.symm
        · exact hti.symm
      · rw [install_other _ middle _ i (fun j he' => hin ⟨j,he'⟩)]
        exact install_other (clearSlots target driver reset) ambient (eraseOutput d) i
          (fun j he' => hin ⟨j.succ,he'⟩)
  · change first.steps+1+last.steps=4*d+9
    omega

end NearCubicWires.RepairOrdinary.CompetitorBankMergeReplace
