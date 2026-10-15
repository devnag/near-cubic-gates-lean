import Proof.Circuits.DecompositionMagnitudeSerializer

/-! Four actual transitions frame a retained sign bit and restore the
destination head. The sign is read from its tape, not chosen by the proof. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSignFrame
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==5
  rule := fun q bs => if q.val=0 then
      some ⟨if bs 0 then 2 else 1,![none,some true],![.stay,.right]⟩
    else if q.val=1 ∨ q.val=2 then
      some ⟨3,![none,some (q.val==2)],![.stay,.right]⟩
    else if q.val=3 then some ⟨4,![none,some false],![.stay,.left]⟩
    else if q.val=4 then some ⟨5,fun _ => none,![.stay,.left]⟩ else none
def cfg (q : Fin 6) (b : Bool) (out : List Bool) (head : ℕ) : Configuration 2 6 :=
  ⟨q,![0,head],![[b],out]⟩

theorem ready (b : Bool) : ClockJoin.ReadyRun machine 4 ![[b],[]] ![[b],frame [b]] := by
  have h0 : step machine (cfg 0 b [] 0)=some (cfg (if b then 2 else 1) b [true] 1) := by
    cases b <;> simp [step,machine,cfg,Configuration.scanned,readTapeBit]
    all_goals apply configuration_ext
    all_goals try rfl
    all_goals funext i; fin_cases i <;> rfl
  have h1 : step machine (cfg (if b then 2 else 1) b [true] 1)=some (cfg 3 b [true,b] 2) := by
    cases b <;> simp [step,machine,cfg]
    all_goals apply configuration_ext
    all_goals try rfl
    all_goals funext i; fin_cases i <;> rfl
  have h2 : step machine (cfg 3 b [true,b] 2)=some (cfg 4 b [true,b,false] 1) := by
    simp [step,machine,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h3 : step machine (cfg 4 b [true,b,false] 1)=some (cfg 5 b (frame [b]) 0) := by
    simp [step,machine,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h := ((Timed.single (by rfl) h0).trans (Timed.single (by cases b <;> rfl) h1)).trans
    ((Timed.single (by rfl) h2).trans (Timed.single (by rfl) h3))
  obtain ⟨r,hr,rf,rs⟩ := h.run (by rfl)
  refine ⟨r,?_,?_,?_,rs.le⟩
  · have he : initialConfiguration machine ![[b],[]]=cfg 0 b [] 0 := by
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    change runFrom machine 4 (initialConfiguration machine ![[b],[]])=some r
    rw [he]
    exact hr
  · rw [rf]; rfl
  · intro i; rw [rf]; fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.DecompositionSignFrame
