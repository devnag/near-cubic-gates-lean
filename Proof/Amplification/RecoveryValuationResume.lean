import Proof.Amplification.RecoveryValuationRetainedWhole

/-! Successful cold valuation return with a paid reset of its three unary
heads. The certificate cursor is retained while scalar preparation resumes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resumeMachine : Machine 32 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if moves i then .left else .stay⟩ else none
def resumedHeads (h : Fin 32→Nat) (i : Fin 32) :=
  if moves i then h i-1 else h i
noncomputable def resumedMachine := Composition.machine coldMachine resumeMachine
def resumedBudget (bits word : List Bool) := coldBudget bits word+2

theorem resume_run (h : Fin 32→Nat) (ts : Fin 32→List Bool) :
    ∃ r,runFrom resumeMachine 1 ⟨resumeMachine.start,h,ts⟩=some r ∧
      r.final.heads=resumedHeads h ∧ r.final.tapes=ts := by
  have hs : step resumeMachine ⟨resumeMachine.start,h,ts⟩=
      some ⟨1,resumedHeads h,ts⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      simp only [applyAction,resumedHeads]
      split <;> rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf]⟩

theorem returned_heads (bits word : List Bool) (c s count : Nat)
    (base : NativeReceipt) (out : RecoveryValuationStream.Data)
    (hp : ZeroPadding.config (caps bits) base.final=RecoveryValuationCount.cfg out count (cap bits)
      (RecoveryCalls.controlCode RecoveryValuationCount.graphSizes none)) :
    resumedHeads (RecoveryFocus.config slots positioned (after bits word c s) base.final).heads=
      Function.update (fun _ : Fin 32=>0) 23 out.pos := by
  have hh := congrArg Configuration.heads hp
  change base.final.heads=(RecoveryValuationCount.cfg out count (cap bits)
    (RecoveryCalls.controlCode RecoveryValuationCount.graphSizes none)).heads at hh
  funext i
  by_cases hi : ∃ j,slots j=i
  · obtain ⟨j,rfl⟩ := hi
    simp only [resumedHeads,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,hh]
    fin_cases j <;> rfl
  · have hm : ¬moves i := by
      rintro (h|h|h)
      · exact hi ⟨2,Fin.ext h.symm⟩
      · exact hi ⟨9,Fin.ext h.symm⟩
      · exact hi ⟨8,Fin.ext h.symm⟩
    have hn : i≠23 := by intro he; exact hi ⟨0,he.symm⟩
    simp only [resumedHeads,hm,if_false,RecoveryFocus.config,RecoveryFocus.pick,hi,↓reduceDIte,
      positioned,Function.update_of_ne hn]

theorem returned_tape (bits : List Bool) (base : NativeReceipt)
    (out : RecoveryValuationStream.Data) (count : Nat)
    (hp : ZeroPadding.config (caps bits) base.final=RecoveryValuationCount.cfg out count (cap bits)
      (RecoveryCalls.controlCode RecoveryValuationCount.graphSizes none))
    (j : Fin 10) (hj : j.val≠6) :
    base.final.tapes j=(RecoveryValuationCount.cfg out count (cap bits)
      (RecoveryCalls.controlCode RecoveryValuationCount.graphSizes none)).tapes j := by
  have h := congrArg (fun c=>c.tapes j) hp
  simpa only [ZeroPadding.config,caps,hj,if_false,ZeroPadding.pad_zero] using h

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
