import Proof.Supplier.EquationScalarStreamErase

/-! Exact framed append followed by an actual thirteen-tape erase sweep. -/
namespace NearCubicWires.RepairOrdinary.EquationScalarStream
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem tail_run (C pos : Nat) (bits suffix out : List Bool) (a : Fin 17→List Bool)
    (hcap : 2*bits.length+1 ≤ C) (hbound : ∀ j,(a (scratchSlots j)).length ≤ C)
    (h10 : a 10=frame bits++suffix) (h13 : a 13=List.replicate C false)
    (h14 : a 14=out) (h15 : a 15=List.replicate C true) (h16 : a 16=List.replicate (C+1) false) :
    ∃ r,runFrom tail (4*bits.length+2*C+9)
      ⟨tail.start,heads pos out.length,a⟩=some r ∧
      r.final.heads=heads pos (out++frame bits).length ∧
      r.final.tapes=tapes C (a 0) (out++frame bits) ∧ r.steps ≤ 4*bits.length+2*C+9 := by
  obtain ⟨base,hb,bh,bt,bs⟩ := PCPSerializerReuse.copy_run [] bits suffix out C hcap
  obtain ⟨copied,hcopy,cf,cs⟩ := RecoveryFocus.run_config copySlots (by decide)
    PCPSerializerReuse.copyMachine (heads pos out.length) a _ _ base hb
  have hi : RecoveryFocus.config copySlots (heads pos out.length) a
      (PCPSerializerReuse.copyEntry [] bits suffix out C)=
      (⟨copyProgram.start,heads pos out.length,a⟩ : Configuration 17 5) := by
    apply WilliamsSourceCrop.focus_same copySlots (⟨copyProgram.start,heads pos out.length,a⟩ : Configuration 17 5)
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j
      · change a 10=[]++frame bits++suffix
        simpa only [List.nil_append] using h10
      · exact h14
      · exact h13
  rw [hi] at hcopy
  let b := Function.update a 14 (out++frame bits)
  have ch : copied.final.heads=heads pos (out++frame bits).length := by
    rw [cf]
    simp only [RecoveryFocus.config,bh,List.length_nil]
    funext i; fin_cases i <;> simp [pick_copy,heads]
  have ct : copied.final.tapes=b := by
    rw [cf]
    change install copySlots a base.final.tapes=b
    rw [bt]
    funext i; fin_cases i <;>
      simp [install,pick_copy,b,List.nil_append,h10,h13]
  have bb (j : Fin 13) : (b (scratchSlots j)).length ≤ C := by
    have hn : scratchSlots j≠14 := by intro he; have hv:=congrArg Fin.val he; dsimp [scratchSlots] at hv; omega
    simpa only [b,Function.update_of_ne hn] using hbound j
  obtain ⟨last,hl,lh,lt,ls⟩ := erase_run C pos (out++frame bits) b bb
    (by simp [b,h15]) (by simp [b,h16])
  have he : Composition.restart copied.final eraseProgram.start=
      (⟨eraseProgram.start,heads pos (out++frame bits).length,b⟩ : Configuration 17 4) := by
    apply configuration_ext
    · rfl
    · exact ch
    · exact ct
  rw [←he] at hl
  have joined := Composition.run_join copyProgram eraseProgram _ _ _ copied last hcopy hl
  have ht : (4*bits.length+4)+1+(2*C+4)=4*bits.length+2*C+9 := by omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt copied last,joined,lh,?_,?_⟩
  · change last.final.tapes=_
    rw [lt,erased_tapes]
    simp [b]
  · change copied.steps+1+last.steps ≤ _
    rw [cs,ls]
    omega

end
end NearCubicWires.RepairOrdinary.EquationScalarStream
