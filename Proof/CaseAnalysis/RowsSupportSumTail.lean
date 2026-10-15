import Proof.CaseAnalysis.RowsSupportSumEnter
import Proof.CaseAnalysis.WitnessSumStorage

/-! A false term or mass verdict halts immediately. Only the successful
whole sum body enters the single rewind/erase tail and returns the exact
next-sum layout, with all three retained output cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumTail
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
open CloseoutWitness.SupportDock (lift)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def ending:=TapeEmbedding.machine 1 SumCleanup.machine
noncomputable def machine {s : ℕ} (body : Machine 3062 s):=
  RecoveryGatedSequence.machine body ending 724
def budget (H fuel : ℕ):=fuel+SumCleanup.budget H+2

theorem tail_run {s : ℕ} (body : Machine 3062 s) (P H b B core W L K T fuel position : ℕ)
    (source arity out native counts nextOut nextNative supports nextSupport : List Bool) (flag : Bool)
    (ambient : Fin 94 → List Bool) (bank : Fin 528 → List Bool) (first : ExecutionReceipt 3062 s)
    (hr : runFrom body fuel
      ⟨body.start,lift (CloseoutWitness.SumWork.heads 0 0 out native counts) supports.length,
        lift (CloseoutWitness.SumWork.data P H b core W L K source out native ambient bank) supports⟩=some first)
    (hh : first.final.heads 724=0) (ht : first.final.tapes 724=[flag])
    (good : flag=true → ∃ after,
      first.final.heads=lift (CloseoutWitness.SumWork.heads position 1 nextOut nextNative counts) nextSupport.length ∧
      first.final.tapes=lift (CloseoutWitness.SumWork.data P H b core W L K source nextOut nextNative after bank) nextSupport ∧
      Store B zero [] after)
    (hpos : position ≤ H) (hsource : source.length ≤ H)
    (hcount : (ZeroPadding.pad H (CompareMachine.word K)).length ≤ H)
    (h501 : bank 501=frame arity) (h502 : bank 502=List.replicate T true) (h526 : bank 526=counts)
    (hbank : ∀ i : Fin 528,i≠501 → i≠502 → i≠526 → (bank i).length ≤ H)
    (holes : ∀ i : Fin 528,(i.val=357 ∨ i.val=368 ∨ i.val=499) → bank i=List.replicate H false) :
    ∃ r,runFrom (machine body) (budget H fuel)
      ⟨(machine body).start,lift (CloseoutWitness.SumWork.heads 0 0 out native counts) supports.length,
        lift (CloseoutWitness.SumWork.data P H b core W L K source out native ambient bank) supports⟩=some r ∧
      r.steps ≤ budget H fuel ∧ r.final.heads 724=0 ∧ r.final.tapes 724=[flag] ∧
      (flag=true → ∃ after,
        r.final.heads=lift (SumDock.heads nextOut nextNative counts) nextSupport.length ∧
        r.final.tapes=lift (SumStorage.data P H b core W L T arity nextOut nextNative counts after) nextSupport ∧
        Store B zero [] after) := by
  cases hf:flag with
  | false =>
    obtain ⟨r,run,rs,rh,rt⟩:=SumControl.reject_run body ending 724 fuel _ first hr hh (by rw [ht,hf])
    have hb:fuel+1 ≤ budget H fuel:=by unfold budget;omega
    have more:=runFrom_moreFuel (machine body) _ (budget H fuel-(fuel+1)) _ r run
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨r,more,rs.trans hb,by rw [rh];exact hh,by rw [rt,ht,hf],?_⟩
    intro impossible;cases impossible
  | true =>
    obtain ⟨after,ah,atapes,store⟩:=good hf
    obtain ⟨base,baseRun,_ls,bh,bt,bd,bl,bk⟩:=SumCleanup.cleanup_run H position nextOut nextNative counts
      (CloseoutWitness.SumWork.data P H b core W L K source nextOut nextNative after bank) hpos rfl rfl
      (SumStorage.scratch_bounds P H b core W L K source nextOut nextNative after bank hsource hcount hbank)
    let last:=TapeEmbedding.receipt (fun _ : Fin 1=>nextSupport.length) (fun _=>nextSupport) base
    have lastRun:=TapeEmbedding.run_embed SumCleanup.machine (fun _ : Fin 1=>nextSupport.length)
      (fun _=>nextSupport) _ _ base baseRun
    have actualLast : runFrom ending (SumCleanup.budget H)
        (RecoveryCalls.restarted ending first.final.heads first.final.tapes)=some last:=by
      rw [ah,atapes];exact lastRun
    obtain ⟨r,run,rs,rh,rt⟩:=SumControl.accept_run body ending 724 fuel (SumCleanup.budget H)
      _ first last hr hh (by rw [ht,hf]) actualLast
    have restored:=SumStorage.restored P H b core W L K T source arity nextOut nextNative counts after bank
      base.final.tapes h501 h502 h526 holes bt bd bl bk
    have lh:last.final.heads=lift (SumDock.heads nextOut nextNative counts) nextSupport.length:=by
      change lift base.final.heads nextSupport.length=_
      rw [bh]
      rfl
    have lt:last.final.tapes=lift (SumStorage.data P H b core W L T arity nextOut nextNative counts after) nextSupport:=by
      change lift base.final.tapes nextSupport=_
      rw [restored]
    refine ⟨r,run,rs,?_,?_,?_⟩
    · rw [rh,lh];rfl
    · rw [rt,lt];rfl
    · intro _
      exact ⟨after,rh.trans lh,rt.trans lt,store⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumTail
