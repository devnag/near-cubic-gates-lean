import Proof.Amplification.RecoveryFocusDock
import Proof.Amplification.RecoveryUnpair
import Proof.PCP.ProjectionNormalizationUnary
import Proof.PCP.PCPPRequestNodeFieldsJoin

/-! Actual raw projection-code field to its two bounded unary components.
The existing binary unpair and unary producers are the only arithmetic. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeProjectionRead
open LocalBitMultitape RadixSemantics RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftSlots : Fin 5 → Fin 24 := ![2,16,17,18,19]
def rightSlots : Fin 5 → Fin 24 := ![3,20,21,22,23]
theorem left_injective : Function.Injective leftSlots := by decide
theorem right_injective : Function.Injective rightSlots := by decide
noncomputable def first := TapeEmbedding.machine 8 RecoveryUnpair.machine
noncomputable def left := RecoveryFocus.machine leftSlots Unary.machine
noncomputable def right := RecoveryFocus.machine rightSlots Unary.machine
noncomputable def machine := Composition.machine (Composition.machine first left) right
def input (bits : List Bool) : Fin 24 → List Bool := fun i => if i=0 then frame bits else []
def budget (bits : List Bool) := RecoveryUnpair.budget bits+1+
  Unary.budget (RecoveryUnpair.leftWord bits)+1+Unary.budget (RecoveryUnpair.rightWord bits)

theorem read_run (bits : List Bool) :
    ∃ r,run machine (budget bits) (input bits)=some r ∧ r.steps≤budget bits ∧
      r.final.tapes 18=RepairSource.VerifierDecoding.CompareMachine.word (Nat.unpair (value bits)).1 ∧
      r.final.tapes 22=RepairSource.VerifierDecoding.CompareMachine.word (Nat.unpair (value bits)).2 ∧
      r.final.heads 18=1 ∧ r.final.heads 22=1 := by
  obtain ⟨base,hb,b2,b3,bh,bs⟩ := RecoveryUnpair.unpair_run bits
  let paired := TapeEmbedding.receipt (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) base
  have hp := TapeEmbedding.run_embed RecoveryUnpair.machine
    (fun _ : Fin 8 => 0) (fun _ : Fin 8 => []) _ _ base hb
  obtain ⟨lb,hlb,lout,lh,ls⟩ := Unary.unary_run (RecoveryUnpair.leftWord bits)
  obtain ⟨l,hl,_,lsteps,lhsel,ltsel,lkeep⟩ := RecoveryFocus.dock leftSlots left_injective
    Unary.machine _ paired.final.heads paired.final.tapes
    (initialConfiguration Unary.machine (Unary.input (RecoveryUnpair.leftWord bits)))
    (by intro j; fin_cases j
        · exact bh 2
        all_goals rfl)
    (by intro j; fin_cases j
        · exact b2
        all_goals rfl) lb hlb
  obtain ⟨rb,hrb,rout,rh,rs⟩ := Unary.unary_run (RecoveryUnpair.rightWord bits)
  have right_old : ∀ j : Fin 5,l.final.heads (rightSlots j)=paired.final.heads (rightSlots j) ∧
      l.final.tapes (rightSlots j)=paired.final.tapes (rightSlots j) := by
    intro j
    exact lkeep _ (by fin_cases j <;> decide)
  obtain ⟨last,hlast,_,rsteps,rhsel,rtsel,rkeep⟩ := RecoveryFocus.dock rightSlots right_injective
    Unary.machine _ l.final.heads l.final.tapes
    (initialConfiguration Unary.machine (Unary.input (RecoveryUnpair.rightWord bits)))
    (by intro j; rw [(right_old j).1]; fin_cases j
        · exact bh 3
        all_goals rfl)
    (by intro j; rw [(right_old j).2]; fin_cases j
        · exact b3
        all_goals rfl) rb hrb
  obtain ⟨result,hresult,hheads,htapes,hsteps⟩ := PCPPRequestNodeFields.join_three_run
    first left right _ _ _ _ paired l last hp hl hlast
  have hin : Composition.leftConfig _ (Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 8 => 0) (fun _ : Fin 8 => [])
        (initialConfiguration RecoveryUnpair.machine (fun i => if i.val=0 then frame bits else []))))=
      initialConfiguration machine (input bits) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=16) (n:=8) (fun j => ?_) (fun j => ?_) i
      all_goals simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,
        Fin.addCases_left,Fin.addCases_right]
    · funext i
      refine Fin.addCases (m:=16) (n:=8) (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,
          Fin.addCases_left,input,Fin.ext_iff,Fin.val_castAdd]
        rfl
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,
          Fin.addCases_right,input,Fin.ext_iff,Fin.val_natAdd]
        change [] = if 16+j.val=0 then frame bits else []
        rw [if_neg (by omega)]
  rw [hin] at hresult
  obtain ⟨lv,rv⟩ := RecoveryUnpair.word_values bits
  refine ⟨result,hresult,?_,?_,?_,?_,?_⟩
  · rw [hsteps,lsteps,rsteps]
    change base.steps+1+lb.steps+1+rb.steps≤_
    unfold budget
    omega
  · rw [htapes,(rkeep 18 (by decide)).2]
    exact (ltsel 3).trans (by simpa only [lv] using lout)
  · rw [htapes]
    exact (rtsel 3).trans (by simpa only [rv] using rout)
  · rw [hheads,(rkeep 18 (by decide)).1]
    exact (lhsel 3).trans (lh 3)
  · rw [hheads]
    exact (rhsel 3).trans (rh 3)

end NearCubicWires.RepairOrdinary.PCPPNativeProjectionRead
