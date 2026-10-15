import Proof.Amplification.RecoveryPrefixLayout

/-! Exact cold call boundaries: outer unframing followed by the complete
input-derived workspace producer. These fields are consequences of actual
ordinary runs, not assumptions of the public search operation. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open RecoveryPrefixBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlot (i : Fin 360) : Fin 389 := ⟨i.val+1,by have h:=i.isLt; omega⟩
def Prepared (C payload total : Nat) (ambient : Fin 389→List Bool) : Prop :=
  Inv (RecoveryPrefixColdPrepare.capacity C payload total) payload
    (RecoveryPrefixColdPrepare.capacity C payload total+1) [] false
    (frame (List.replicate total true)) (ambient ∘ nativeSlot) ∧
  ambient 361=VerifierDecoding.CompareMachine.word total ∧
  ∀ i : Fin 389,382 ≤ i.val → ambient i=[]

theorem ordinary_ready {o : Nat→Bool} {t s fuel : Nat} (ports : Ports t)
    (p : Machine t s) (input output : Fin t→List Bool) (h : ClockJoin.ReadyRun p fuel input output) :
    ∃ cost≤fuel,Ready o (ports.program (ordinary p)) cost input output := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r.steps,hs,r.final,ordinary_trace ports p fuel _ r hr,
    (prefix_of_run p fuel _ r hr).2,hh,ht⟩

theorem unwrap_ready (payload total : Nat) :
    ClockJoin.ReadyRun unwrap (4*(RecoveryPrefixMeasure.request payload total).length+2)
      (input payload total) (unwrapped payload total) :=
  (UInputFields.unwrap_ready (RecoveryPrefixMeasure.request payload total)).focus unwrapSlots unwrap_injective
    (input payload total) (by intro i; fin_cases i <;> rfl)

theorem unwrapped_cold (payload total : Nat) (i : Fin 380) :
    unwrapped payload total (coldSlots i)=RecoveryPrefixColdPrepare.cold payload total i := by
  classical
  by_cases hi : i.val=0
  · have he : i=0 := Fin.ext hi
    subst i
    change install unwrapSlots _ _ (unwrapSlots 1)=_
    rw [install_slot _ unwrap_injective]
    rfl
  · rw [unwrapped,install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg (fun k : Fin 389=>k.val) he
      have hl:=i.isLt
      fin_cases j <;> dsimp [unwrapSlots,coldSlots] at hv <;> omega)]
    simp [input,coldSlots,RecoveryPrefixColdPrepare.cold,hi]

theorem unwrapped_fresh (payload total : Nat) (i : Fin 389) (hi : 382 ≤ i.val) :
    unwrapped payload total i=[] := by
  classical
  rw [unwrapped,install_other _ _ _ _ (by
    intro j he
    have hv:=congrArg (fun k : Fin 389=>k.val) he
    fin_cases j <;> dsimp [unwrapSlots] at hv <;> omega)]
  simp [input,show i.val≠0 by omega]

theorem prepare_ready (C payload total : Nat) (hC : 1073741824≤C) : ∃ out,
    ClockJoin.ReadyRun (prepare C) (RecoveryPrefixColdPrepare.budget C payload total)
      (unwrapped payload total) out ∧ Prepared C payload total out := by
  classical
  obtain ⟨localOut,hlocal,hinv,hdriver⟩ := RecoveryPrefixColdPrepare.prepare C payload total (capacity_large C payload total hC)
  have h := hlocal.focus coldSlots cold_injective (unwrapped payload total) (unwrapped_cold payload total)
  refine ⟨_,h,?_,?_,?_⟩
  · have he : (install coldSlots (unwrapped payload total) localOut) ∘ nativeSlot=
        localOut ∘ RecoveryPrefixColdPrepare.nativeSlots := by
      funext i
      change install coldSlots _ _ (coldSlots (RecoveryPrefixColdPrepare.nativeSlots i))=_
      exact install_slot coldSlots cold_injective _ _ _
    rw [he]
    exact hinv
  · change install coldSlots _ _ (coldSlots 360)=_
    rw [install_slot _ cold_injective]
    exact hdriver
  · intro i hi
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg (fun k : Fin 389=>k.val) he
      have hj:=j.isLt
      dsimp [coldSlots] at hv
      omega)]
    exact unwrapped_fresh payload total i hi

end NearCubicWires.RepairSource.RecoveryPrefixCold
