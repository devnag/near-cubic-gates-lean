import Proof.Amplification.RecoveryProjectionFieldErase

/-! One projected output bit is physically appended and the evaluator bank
is physically erased, preserving all external source/randomness cursors. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionField
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def emitSlots : Fin 2→Fin 34 := ![26,31]
theorem emit_injective : Function.Injective emitSlots := by decide
noncomputable def emitMachine := RecoveryFocus.machine emitSlots RecoveryProjectionEmitBit.machine
noncomputable def tailMachine := Composition.machine emitMachine eraseMachine
def appendHeads (hs : Fin 34→Nat) (pos : Nat) (i : Fin 34) := if i=31 then pos else hs i

theorem emit_run (cap : Nat) (bit : Bool) (out : List Bool)
    (hs : Fin 34→Nat) (data : Fin 34→List Bool)
    (hb : data 26=ZeroPadding.pad cap [bit]) (hh : hs 26=0)
    (ho : data 31=out) (hho : hs 31=out.length) : ∃ r,
    runFrom emitMachine 2 ⟨emitMachine.start,hs,data⟩=some r ∧
      r.final.heads=appendHeads hs (out++[true,bit]).length ∧
      r.final.tapes=Function.update data 31 (out++[true,bit]) ∧ r.steps=2 := by
  obtain ⟨base,hr,hf,bs⟩ := RecoveryProjectionEmitBit.padded_emit cap bit out
  obtain ⟨r,hrr,_hcontrol,rsteps,rh,rt,other⟩ := RecoveryFocus.dock emitSlots emit_injective
    RecoveryProjectionEmitBit.machine 2 hs data _
    (by intro j; fin_cases j; exact hh; exact hho)
    (by intro j; fin_cases j; exact hb; exact ho) base hr
  have localH (j : Fin 2) : r.final.heads (emitSlots j)=![0,(out++[true,bit]).length] j := by
    rw [rh,hf]; rfl
  have localT (j : Fin 2) : r.final.tapes (emitSlots j)=![ZeroPadding.pad cap [bit],out++[true,bit]] j := by
    rw [rt,hf]; rfl
  refine ⟨r,hrr,?_,?_,rsteps.trans bs⟩
  · funext i
    by_cases h31 : i=31
    · subst i; exact localH 1
    by_cases h26 : i=26
    · subst i; exact (localH 0).trans hh.symm
    have hn : ∀ j,emitSlots j≠i := by intro j; fin_cases j; exact Ne.symm h26; exact Ne.symm h31
    simpa only [appendHeads,h31,ite_false] using (other i hn).1
  · funext i
    by_cases h31 : i=31
    · subst i; simpa [emitSlots] using localT 1
    by_cases h26 : i=26
    · subst i; simpa [emitSlots] using (localT 0).trans hb.symm
    have hn : ∀ j,emitSlots j≠i := by intro j; fin_cases j; exact Ne.symm h26; exact Ne.symm h31
    simpa only [Function.update_of_ne h31] using (other i hn).2

theorem tail_run (cap log : Nat) (bit : Bool) (out : List Bool)
    (hs : Fin 34→Nat) (data : Fin 34→List Bool)
    (hb : ∀ j,(data (bankSlots j)).length ≤ cap) (hh : ∀ j,hs (bankSlots j)=0)
    (hbit : data 26=ZeroPadding.pad cap [bit]) (ho : data 31=out) (hho : hs 31=out.length)
    (hd : data 32=List.replicate cap true) (hhd : hs 32=0)
    (hl : data 33=List.replicate log false) (hhl : hs 33=0) : ∃ r,
    runFrom tailMachine (2*cap+7) ⟨tailMachine.start,hs,data⟩=some r ∧
      r.final.heads=appendHeads hs (out++[true,bit]).length ∧
      (∀ j,r.final.tapes (bankSlots j)=List.replicate cap false) ∧
      r.final.tapes 28=data 28 ∧ r.final.tapes 29=data 29 ∧ r.final.tapes 30=data 30 ∧
      r.final.tapes 31=out++[true,bit] ∧ r.final.tapes 32=List.replicate cap true ∧
      r.final.tapes 33=List.replicate (max log (cap+1)) false ∧ r.steps=2*cap+7 := by
  obtain ⟨first,hfirst,fh,ft,fs⟩ := emit_run cap bit out hs data hbit (hh 26) ho hho
  have hn (j : Fin 28) : bankSlots j≠31 := by
    intro h; have hv:=congrArg Fin.val h; have hj:=j.isLt; dsimp [bankSlots] at hv; omega
  have fb : ∀ j,(first.final.tapes (bankSlots j)).length ≤ cap := by
    intro j; rw [ft,Function.update_of_ne (hn j)]; exact hb j
  have fheads : ∀ j,first.final.heads (bankSlots j)=0 := by
    intro j; rw [fh]; simp only [appendHeads,hn j,ite_false,hh j]
  obtain ⟨last,hlast,lh,bank,other,driver,logResult,ls⟩ := erase_run cap log first.final.heads first.final.tapes
    fb fheads (by simpa [ft] using hd) (by simpa [fh,appendHeads] using hhd)
    (by simpa [ft] using hl) (by simpa [fh,appendHeads] using hhl)
  have hall := Composition.run_join emitMachine eraseMachine 2 (2*cap+4) _ first last hfirst hlast
  have htime : 2+1+(2*cap+4)=2*cap+7 := by omega
  rw [htime] at hall
  refine ⟨_,hall,lh.trans fh,bank,?_,?_,?_,?_,driver,logResult,?_⟩
  · change last.final.tapes 28=data 28
    simpa [ft] using other 28 (by decide) (by decide)
  · change last.final.tapes 29=data 29
    simpa [ft] using other 29 (by decide) (by decide)
  · change last.final.tapes 30=data 30
    simpa [ft] using other 30 (by decide) (by decide)
  · change last.final.tapes 31=out++[true,bit]
    simpa [ft] using other 31 (by decide) (by decide)
  · change first.steps+1+last.steps=_
    omega

end NearCubicWires.RepairSource.RecoveryProjectionField
