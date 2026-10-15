import Proof.Amplification.RecoveryTseitinBank

/-! Abstract state and budget carrier for the exact cold stream join. This
avoids normalizing either finite controller while proving tape transport. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def streamSlots (i : Fin 242) : Fin 262 := i.castAdd 20
theorem stream_injective : Function.Injective streamSlots := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 262=>k.val) he)
theorem join_run {s t : Nat} (driver : Machine 262 s) (stream : Machine 242 t)
    (startData : Fin 262→List Bool) (cap count driverBudget streamBudget : Nat) (word : List Bool)
    (hd : ∃ out,ClockJoin.ReadyRun driver (driverBudget) (startData) out ∧
      out 3=List.replicate (cap) true ∧
      out 241=CompareMachine.word count ∧ out 242=List.replicate count true ∧
      (∀ i : Fin 242,i≠3 → i≠241 → out (i.castAdd 20)=[]))
    (ho : ∃ r,runFrom stream (streamBudget)
      ⟨stream.start,fun _=>0,bankInput (cap) count []⟩=some r ∧
      r.final.tapes 239=word ∧
      r.final.heads 239=(word).length ∧
      r.final.tapes 241=CompareMachine.word count ∧ r.final.heads 241=1 ∧
      r.steps ≤ streamBudget) : ∃ r,
    run (Composition.machine driver (RecoveryFocus.machine streamSlots stream)) ((driverBudget+1+streamBudget)) (startData)=some r ∧
      r.final.tapes 239=word ∧
      r.final.heads 239=(word).length ∧
      r.final.tapes 241=CompareMachine.word count ∧ r.final.heads 241=1 ∧
      r.final.tapes 242=List.replicate count true ∧ r.final.heads 242=0 ∧
      r.steps≤(driverBudget+1+streamBudget) := by
  obtain ⟨drivers,⟨first,hf,ft,fh,fs⟩,d3,d241,d242,db⟩ := hd
  obtain ⟨base,hb,b239,bh239,b241,bh241,bs⟩ := ho
  obtain ⟨last,hl,_lc,ls,lh,lt,lo⟩ := RecoveryFocus.dock streamSlots stream_injective
    stream _ first.final.heads first.final.tapes _
    (by intro i; exact fh _)
    (by
      intro i
      rw [ft]
      by_cases h3 : i=3
      · subst i; exact d3
      by_cases h241 : i=241
      · subst i; exact d241
      have hblank:=db i h3 h241
      simpa [bankInput,h3,h241,streamSlots] using hblank) base hb
  have hwhole := Composition.run_join driver (RecoveryFocus.machine streamSlots stream) _ _ _ first last hf hl
  refine ⟨_,hwhole,?_,?_,?_,?_,?_,?_,?_⟩
  · change last.final.tapes (streamSlots 239)=_
    exact (lt 239).trans b239
  · change last.final.heads (streamSlots 239)=_
    exact (lh 239).trans bh239
  · change last.final.tapes (streamSlots 241)=_
    exact (lt 241).trans b241
  · change last.final.heads (streamSlots 241)=_
    exact (lh 241).trans bh241
  · have hn : ∀ j,streamSlots j≠242 := by
      intro j he
      have hv:=congrArg Fin.val he
      have hj:=j.isLt
      change j.val=242 at hv
      omega
    exact (lo 242 hn).2.trans (by rw [ft]; exact d242)
  · have hn : ∀ j,streamSlots j≠242 := by
      intro j he
      have hv:=congrArg Fin.val he
      have hj:=j.isLt
      change j.val=242 at hv
      omega
    exact (lo 242 hn).1.trans (fh 242)
  · change first.steps+1+last.steps≤_
    exact Nat.add_le_add (Nat.add_le_add_right fs 1) (ls.le.trans bs)

end NearCubicWires.RepairSource.RecoveryTseitinTautology.Cold
