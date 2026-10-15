import Proof.PCP.PCPPRequestNodeErase
import Proof.MachineModel.OrdinaryWilliamsSourceCropLayout

/-! The node caller physically appends the framed canonical node result and
then erases its bank. Its original source cursor and global unary
capacity survive; the append cursor alone advances. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeReuse
open LocalBitMultitape RecoveryRootRound
open PCPSerializerReuse (copyMachine copyEntry copy_run)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 3 → Fin 646 := ![630,643,642]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copyProgram := RecoveryFocus.machine copySlots copyMachine
noncomputable def tailMachine := Composition.machine copyProgram eraseMachine
def appendHeads (heads : Fin 646 → ℕ) (pos : ℕ) (i : Fin 646) : ℕ :=
  if i=643 then pos else heads i

theorem scratch_small (j : Fin 642) : (scratchSlots j).val<643 := by
  unfold scratchSlots
  have hj := j.isLt
  dsimp
  omega
theorem tail_run (capacity log : ℕ) (bits suffix out : List Bool)
    (heads : Fin 646 → ℕ) (ambient : Fin 646 → List Bool)
    (hbits : 2*bits.length+1 ≤ capacity)
    (hb : ∀ j,(ambient (scratchSlots j)).length ≤ capacity)
    (hh : ∀ j,heads (scratchSlots j)=0)
    (hsource : ambient 630=frame bits++suffix)
    (hout : ambient 643=out) (houtHead : heads 643=out.length)
    (hcopyLog : ambient 642=List.replicate capacity false)
    (hd : ambient 644=List.replicate capacity true) (hhd : heads 644=0)
    (hl : ambient 645=List.replicate log false) (hhl : heads 645=0) :
    ∃ r,runFrom tailMachine (4*bits.length+2*capacity+9)
      ⟨tailMachine.start,heads,ambient⟩=some r ∧
      r.final.heads=appendHeads heads (out++frame bits).length ∧
      r.final.tapes 0=ambient 0 ∧
      r.final.tapes 643=out++frame bits ∧
      r.final.tapes 644=List.replicate capacity true ∧
      r.final.tapes 645=List.replicate (max log (capacity+1)) false ∧
      (∀ j,r.final.tapes (scratchSlots j)=List.replicate capacity false) ∧
      r.steps ≤ 4*bits.length+2*capacity+9 := by
  have h630 : heads 630=0 := hh 629
  have h642 : heads 642=0 := hh 641
  obtain ⟨base,hbase,bh,bt,bs⟩ := copy_run [] bits suffix out capacity hbits
  obtain ⟨copied,hcopy,cf,cs⟩ := RecoveryFocus.run_config copySlots copySlots_injective
    copyMachine heads ambient _ _ base hbase
  have hi : RecoveryFocus.config copySlots heads ambient (copyEntry [] bits suffix out capacity)=
      (⟨copyProgram.start,heads,ambient⟩ : Configuration 646 5) := by
    have he := WilliamsSourceCrop.focus_same copySlots
      (⟨copyProgram.start,heads,ambient⟩ : Configuration 646 5)
      (copyEntry [] bits suffix out capacity)
      (by intro j; fin_cases j; exact h630; exact houtHead; exact h642)
      (by intro j; fin_cases j; exact hsource; exact hout; exact hcopyLog)
    exact he
  rw [hi] at hcopy
  have localH (j : Fin 3) : copied.final.heads (copySlots j)=
      (![0,(out++frame bits).length,0] : Fin 3 → ℕ) j := by
    rw [cf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot copySlots copySlots_injective,
      List.length_nil] using congrFun bh j
  have localT (j : Fin 3) : copied.final.tapes (copySlots j)=
      (![frame bits++suffix,out++frame bits,List.replicate capacity false] : Fin 3 → List Bool) j := by
    rw [cf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot copySlots copySlots_injective,List.nil_append] using congrFun bt j
  have other (i : Fin 646) (h630i : 630≠i) (h643i : 643≠i) (h642i : 642≠i) :
      copied.final.heads i=heads i ∧ copied.final.tapes i=ambient i := by
    have hn : ¬∃ j,copySlots j=i := by
      rintro ⟨j,hj⟩
      fin_cases j
      · exact h630i hj
      · exact h643i hj
      · exact h642i hj
    have hp : RecoveryFocus.pick copySlots i=none := by
      classical
      simp only [RecoveryFocus.pick,dif_neg hn]
    rw [cf]
    simp only [RecoveryFocus.config,hp,and_self]
  have copiedHeads : copied.final.heads=appendHeads heads (out++frame bits).length := by
    funext i
    by_cases hi643 : i=643
    · subst i; exact localH 1
    by_cases hi630 : i=630
    · subst i; exact (localH 0).trans h630.symm
    by_cases hi642 : i=642
    · subst i; exact (localH 2).trans h642.symm
    simpa only [appendHeads,hi643,ite_false] using
      (other i (Ne.symm hi630) (Ne.symm hi643) (Ne.symm hi642)).1
  have copyBound (j : Fin 642) : (copied.final.tapes (scratchSlots j)).length ≤ capacity := by
    by_cases hj630 : scratchSlots j=630
    · have ht : copied.final.tapes 630=frame bits++suffix := localT 0
      rw [hj630,ht,←hsource]
      have h := hb 629
      exact h
    by_cases hj642 : scratchSlots j=642
    · have ht : copied.final.tapes 642=List.replicate capacity false := localT 2
      rw [hj642,ht,List.length_replicate]
    have hj643 : 643≠scratchSlots j := by
      intro he; have he' := congrArg Fin.val he; have hj := scratch_small j; omega
    rw [(other _ (Ne.symm hj630) hj643 (Ne.symm hj642)).2]
    exact hb j
  have copyHeads (j : Fin 642) : copied.final.heads (scratchSlots j)=0 := by
    rw [copiedHeads]
    have hn : scratchSlots j≠643 := by
      intro he; have he' := congrArg Fin.val he; have hj := scratch_small j; omega
    simp only [appendHeads,hn,ite_false,hh j]
  obtain ⟨erasedRun,he,eh,et,es⟩ := erase_run capacity log copied.final.heads copied.final.tapes
    copyBound ((other 644 (by decide) (by decide) (by decide)).2.trans hd)
    ((other 645 (by decide) (by decide) (by decide)).2.trans hl) copyHeads
    ((other 644 (by decide) (by decide) (by decide)).1.trans hhd)
    ((other 645 (by decide) (by decide) (by decide)).1.trans hhl)
  have joined := Composition.run_join copyProgram eraseMachine _ _ _ copied erasedRun hcopy he
  have heq : (4*bits.length+4)+1+(2*capacity+4)=4*bits.length+2*capacity+9 := by omega
  rw [heq] at joined
  refine ⟨Composition.joinedReceipt copied erasedRun,joined,?_,?_,?_,?_,?_,?_,?_⟩
  · exact eh.trans copiedHeads
  · change erasedRun.final.tapes 0=ambient 0
    rw [et,erased_live capacity log copied.final.tapes 0 (by simp)]
    exact (other 0 (by decide) (by decide) (by decide)).2
  · change erasedRun.final.tapes 643=out++frame bits
    rw [et,erased_live capacity log copied.final.tapes 643 (by simp)]
    exact localT 1
  · change erasedRun.final.tapes 644=_
    rw [et,erased_driver]
  · change erasedRun.final.tapes 645=_
    rw [et,erased_log]
  · intro j
    change erasedRun.final.tapes (scratchSlots j)=_
    rw [et,erased_slot]
  · change copied.steps+1+erasedRun.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.PCPPRequestNodeReuse
