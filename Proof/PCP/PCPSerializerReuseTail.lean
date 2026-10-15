import Proof.PCP.PCPSerializerReuseErase
import Proof.MachineModel.OrdinaryWilliamsSourceCropLayout

/-! The repeated caller physically appends the framed serializer result and
then erases the shared bank. Its source/count cursors and global unary
capacity survive; the append cursor alone advances. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerReuse
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 3 → Fin 132 := ![77,129,128]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copyProgram := RecoveryFocus.machine copySlots copyMachine
noncomputable def tailMachine := Composition.machine copyProgram eraseMachine
def appendHeads (heads : Fin 132 → ℕ) (pos : ℕ) (i : Fin 132) : ℕ :=
  if i=129 then pos else heads i

theorem scratch_small (j : Fin 127) : (scratchSlots j).val<129 := by
  unfold scratchSlots
  split <;> dsimp <;> omega
theorem scratch_not_live (j : Fin 127) : scratchSlots j≠0 ∧ scratchSlots j≠2 := by
  constructor <;> intro h <;> have hv := congrArg Fin.val h
  all_goals simp only [scratchSlots] at hv
  all_goals split at hv <;> dsimp at hv <;> omega

theorem tail_run (capacity log : ℕ) (bits suffix out : List Bool)
    (heads : Fin 132 → ℕ) (ambient : Fin 132 → List Bool)
    (hbits : 2*bits.length+1 ≤ capacity)
    (hb : ∀ j,(ambient (scratchSlots j)).length ≤ capacity)
    (hh : ∀ j,heads (scratchSlots j)=0)
    (hsource : ambient 77=frame bits++suffix)
    (hout : ambient 129=out) (houtHead : heads 129=out.length)
    (hcopyLog : ambient 128=List.replicate capacity false)
    (hd : ambient 130=List.replicate capacity true) (hhd : heads 130=0)
    (hl : ambient 131=List.replicate log false) (hhl : heads 131=0) :
    ∃ r,runFrom tailMachine (4*bits.length+2*capacity+9)
      ⟨tailMachine.start,heads,ambient⟩=some r ∧
      r.final.heads=appendHeads heads (out++frame bits).length ∧
      r.final.tapes 0=ambient 0 ∧ r.final.tapes 2=ambient 2 ∧
      r.final.tapes 129=out++frame bits ∧
      r.final.tapes 130=List.replicate capacity true ∧
      r.final.tapes 131=List.replicate (max log (capacity+1)) false ∧
      (∀ j,r.final.tapes (scratchSlots j)=List.replicate capacity false) ∧
      r.steps ≤ 4*bits.length+2*capacity+9 := by
  have h77 : heads 77=0 := hh 75
  have h128 : heads 128=0 := hh 126
  obtain ⟨base,hbase,bh,bt,bs⟩ := copy_run [] bits suffix out capacity hbits
  obtain ⟨copied,hcopy,cf,cs⟩ := RecoveryFocus.run_config copySlots copySlots_injective
    copyMachine heads ambient _ _ base hbase
  have hi : RecoveryFocus.config copySlots heads ambient (copyEntry [] bits suffix out capacity)=
      (⟨copyProgram.start,heads,ambient⟩ : Configuration 132 5) := by
    have he := WilliamsSourceCrop.focus_same copySlots
      (⟨copyProgram.start,heads,ambient⟩ : Configuration 132 5)
      (copyEntry [] bits suffix out capacity)
      (by intro j; fin_cases j; exact h77; exact houtHead; exact h128)
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
  have other (i : Fin 132) (h77i : 77≠i) (h129i : 129≠i) (h128i : 128≠i) :
      copied.final.heads i=heads i ∧ copied.final.tapes i=ambient i := by
    have hn : ¬∃ j,copySlots j=i := by
      rintro ⟨j,hj⟩
      fin_cases j
      · exact h77i hj
      · exact h129i hj
      · exact h128i hj
    have hp : RecoveryFocus.pick copySlots i=none := by
      classical
      simp only [RecoveryFocus.pick,dif_neg hn]
    rw [cf]
    simp only [RecoveryFocus.config,hp,and_self]
  have copiedHeads : copied.final.heads=appendHeads heads (out++frame bits).length := by
    funext i
    by_cases hi129 : i=129
    · subst i; exact localH 1
    by_cases hi77 : i=77
    · subst i; exact (localH 0).trans h77.symm
    by_cases hi128 : i=128
    · subst i; exact (localH 2).trans h128.symm
    simpa only [appendHeads,hi129,ite_false] using
      (other i (Ne.symm hi77) (Ne.symm hi129) (Ne.symm hi128)).1
  have copyBound (j : Fin 127) : (copied.final.tapes (scratchSlots j)).length ≤ capacity := by
    by_cases hj77 : scratchSlots j=77
    · have ht : copied.final.tapes 77=frame bits++suffix := localT 0
      rw [hj77,ht,←hsource]
      have h := hb 75
      exact h
    by_cases hj128 : scratchSlots j=128
    · have ht : copied.final.tapes 128=List.replicate capacity false := localT 2
      rw [hj128,ht,List.length_replicate]
    have hj129 : 129≠scratchSlots j := by
      intro he; have he' := congrArg Fin.val he; have hj := scratch_small j; omega
    rw [(other _ (Ne.symm hj77) hj129 (Ne.symm hj128)).2]
    exact hb j
  have copyHeads (j : Fin 127) : copied.final.heads (scratchSlots j)=0 := by
    rw [copiedHeads]
    have hn : scratchSlots j≠129 := by
      intro he; have he' := congrArg Fin.val he; have hj := scratch_small j; omega
    simp only [appendHeads,hn,ite_false,hh j]
  obtain ⟨erasedRun,he,eh,et,es⟩ := erase_run capacity log copied.final.heads copied.final.tapes
    copyBound ((other 130 (by decide) (by decide) (by decide)).2.trans hd)
    ((other 131 (by decide) (by decide) (by decide)).2.trans hl) copyHeads
    ((other 130 (by decide) (by decide) (by decide)).1.trans hhd)
    ((other 131 (by decide) (by decide) (by decide)).1.trans hhl)
  have joined := Composition.run_join copyProgram eraseMachine _ _ _ copied erasedRun hcopy he
  have heq : (4*bits.length+4)+1+(2*capacity+4)=4*bits.length+2*capacity+9 := by omega
  rw [heq] at joined
  refine ⟨Composition.joinedReceipt copied erasedRun,joined,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact eh.trans copiedHeads
  · change erasedRun.final.tapes 0=ambient 0
    rw [et,erased_live capacity log copied.final.tapes 0 (by simp)]
    exact (other 0 (by decide) (by decide) (by decide)).2
  · change erasedRun.final.tapes 2=ambient 2
    rw [et,erased_live capacity log copied.final.tapes 2 (by simp)]
    exact (other 2 (by decide) (by decide) (by decide)).2
  · change erasedRun.final.tapes 129=out++frame bits
    rw [et,erased_live capacity log copied.final.tapes 129 (by simp)]
    exact localT 1
  · change erasedRun.final.tapes 130=_
    rw [et,erased_driver]
  · change erasedRun.final.tapes 131=_
    rw [et,erased_log]
  · intro j
    change erasedRun.final.tapes (scratchSlots j)=_
    rw [et,erased_slot]
  · change copied.steps+1+erasedRun.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.PCPSerializerReuse
