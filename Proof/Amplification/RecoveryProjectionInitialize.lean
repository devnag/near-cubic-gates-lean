import Proof.Amplification.RecoveryProjectionInitializeRandom

/-! The whole actual row initializer allocates scratch, writes all R random
bits, and positions both finite repeat drivers. Its input contains only the
source and physically produced capacity and dimension words. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionInitialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readyHeads (i : Fin 36) := if i.val=34 ∨ i.val=35 then 1 else 0
def position : Machine 36 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if i.val=34 ∨ i.val=35 then .right else .stay⟩ else none

theorem position_step (data : Fin 36→List Bool) :
    step position (initialConfiguration position data)=some ⟨1,readyHeads,data⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val=34 ∨ i.val=35 <;> simp [applyAction,readyHeads,hi,HeadMove.apply,initialConfiguration]
  · rfl

noncomputable def prepareMachine := Composition.machine eraseMachine randomMachine
noncomputable def machine := Composition.machine prepareMachine position

theorem prepared_tapes (cap R Q : Nat) (source : List Bool) :
    randomized cap R Q source=
      (RecoveryProjectionRows.cfg 0 cap R source (List.replicate R false) [] [] 0 Q 1).tapes := by
  funext i
  fin_cases i <;> try rfl
  change RepairOrdinary.frame (List.replicate R false)=RepairOrdinary.frame (List.replicate R false)++[]
  exact (List.append_nil _).symm

theorem prepared_heads (cap R Q : Nat) (source : List Bool) :
    readyHeads=(RecoveryProjectionRows.cfg 0 cap R source (List.replicate R false) [] [] 0 Q 1).heads := by
  funext i
  fin_cases i <;> rfl

theorem initialize_run (cap R Q : Nat) (source : List Bool) (hc : 2*R+3≤cap) : ∃ r,
    run machine (2*cap+4*R+15) (cold cap R Q source)=some r ∧
      r.final.heads=(RecoveryProjectionRows.cfg 0 cap R source (List.replicate R false) [] [] 0 Q 1).heads ∧
      r.final.tapes=(RecoveryProjectionRows.cfg 0 cap R source (List.replicate R false) [] [] 0 Q 1).tapes ∧
      r.steps≤2*cap+4*R+15 := by
  have hfirst := ClockJoin.join _ _ _ _ _ _ _ (erase_ready cap R Q source) (random_ready cap R Q source hc)
  obtain ⟨first,hfirst,ft,fh,fs⟩ := hfirst
  obtain ⟨last,hlast,lf,ls⟩ := (Timed.single (by rfl) (position_step first.final.tapes)).run (by rfl)
  have he : Composition.restart first.final position.start=initialConfiguration position first.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext fh
    · rfl
  rw [←he] at hlast
  have hall := Composition.run_join prepareMachine position _ 1 _ first last hfirst hlast
  have htime : ((2*cap+4)+1+(4*R+8))+1+1=2*cap+4*R+15 := by omega
  rw [htime] at hall
  refine ⟨_,hall,?_,?_,?_⟩
  · change last.final.heads=_
    rw [lf]
    exact prepared_heads cap R Q source
  · change last.final.tapes=_
    rw [lf]
    exact ft.trans (prepared_tapes cap R Q source)
  · change first.steps+1+last.steps≤_
    omega

end NearCubicWires.RepairSource.RecoveryProjectionInitialize
