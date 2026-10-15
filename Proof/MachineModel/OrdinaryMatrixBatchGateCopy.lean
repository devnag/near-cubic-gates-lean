import Proof.MachineModel.OrdinaryMatrixBatchGateNativeLoop
import Proof.MachineModel.OrdinaryMatrixBatchWorkspace

/-! The cold full-request caller pays for its independent id-zero word and
the `U`-sentinel head adjustment, retaining every other tape and cursor.

The weight-count sentinel comes from the width setup (`MatrixBatchWidthSetup`) with its head already at
cell 1, so the linear front end's `d`-sentinel (tape 92) is not advanced: it is gate scratch now. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGateColdCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 166 := ![103,147,106,107]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def copy := RecoveryFocus.machine slots copyMachine
def output (r : Request) : Fin 4 → List Bool :=
  ![frame (binary r.M 0),frame (binary r.M 0),List.replicate (C r) false,List.replicate (C r+1) false]
def updated (r : Request) (tapes : Fin 166 → List Bool) (i : Fin 166) :=
  if i=147 then frame (binary r.M 0) else tapes i
def shifted (heads : Fin 166 → ℕ) (i : Fin 166) :=
  if i=39 then heads i+1 else heads i
def advance : Machine 166 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=39 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine copy advance
def budget (r : Request) := 8*r.M+10

theorem install_output (r : Request) (tapes : Fin 166 → List Bool)
    (h103 : tapes 103=frame (binary r.M 0))
    (h106 : tapes 106=List.replicate (C r) false)
    (h107 : tapes 107=List.replicate (C r+1) false) :
    install slots tapes (output r)=updated r tapes := by
  funext i
  unfold install
  cases hp : RecoveryFocus.pick slots i with
  | none =>
    have hi : i≠147 := by
      intro he
      subst i
      have hh := RecoveryFocus.pick_slot slots slots_injective 1
      change RecoveryFocus.pick slots 147=some 1 at hh
      rw [hp] at hh
      contradiction
    simp only [updated,hi,ite_false]
  | some j =>
    have hi := RecoveryFocus.slot_of_pick slots hp
    change output r j=updated r tapes i
    rw [←hi]
    fin_cases j <;> simp [slots,output,updated,h103,h106,h107]

theorem copy_run (r : Request) (heads : Fin 166 → ℕ) (tapes : Fin 166 → List Bool)
    (hh : ∀ i,heads (slots i)=0)
    (h103 : tapes 103=frame (binary r.M 0)) (h147 : tapes 147=[])
    (h106 : tapes 106=List.replicate (C r) false)
    (h107 : tapes 107=List.replicate (C r+1) false) :
    ∃ actual,runFrom copy (8*r.M+8) (RecoveryCalls.restarted copy heads tapes)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=updated r tapes ∧ actual.steps=8*r.M+8 := by
  have hc : 2*r.M+1≤C r := by unfold C; omega
  have hr : 4*r.M+3≤C r+1 := by unfold C; omega
  have ready := copy_ready (binary r.M 0) [] (C r) (C r+1) (by simp)
  simp only [binary_length,Nat.max_eq_left hc,Nat.max_eq_left hr] at ready
  obtain ⟨actual,ha,ah,atapes,as⟩ := HierarchyBinary.focused_run slots slots_injective copyMachine _ _ ready heads tapes hh
    (by intro i; fin_cases i; exact h103; exact h147; exact h106; exact h107)
  exact ⟨actual,ha,ah,atapes.trans (install_output r tapes h103 h106 h107),as⟩

theorem advance_run (heads : Fin 166 → ℕ) (tapes : Fin 166 → List Bool) :
    ∃ actual,runFrom advance 1 ⟨0,heads,tapes⟩=some actual ∧
      actual.final=⟨1,shifted heads,tapes⟩ ∧ actual.steps=1 := by
  have hs : step advance ⟨0,heads,tapes⟩=some ⟨1,shifted heads,tapes⟩ := by
    simp only [step,advance,Fin.val_zero,ite_true,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=39 <;> simp [applyAction,shifted,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem prepare_run (r : Request) (heads : Fin 166 → ℕ) (tapes : Fin 166 → List Bool)
    (hh : ∀ i,heads (slots i)=0)
    (h103 : tapes 103=frame (binary r.M 0)) (h147 : tapes 147=[])
    (h106 : tapes 106=List.replicate (C r) false)
    (h107 : tapes 107=List.replicate (C r+1) false) :
    ∃ actual,runFrom machine (budget r) (RecoveryCalls.restarted machine heads tapes)=some actual ∧
      actual.final.heads=shifted heads ∧ actual.final.tapes=updated r tapes ∧ actual.steps=budget r := by
  obtain ⟨copied,hc,ch,ct,cs⟩ := copy_run r heads tapes hh h103 h147 h106 h107
  obtain ⟨moved,hm,mf,ms⟩ := advance_run copied.final.heads copied.final.tapes
  have joined := Composition.run_join copy advance _ _ _ copied moved hc hm
  refine ⟨Composition.joinedReceipt copied moved,joined,?_,?_,?_⟩
  · change moved.final.heads=_
    rw [mf]
    exact congrArg shifted ch
  · change moved.final.tapes=_
    rw [mf]
    exact ct
  · change copied.steps+1+moved.steps=budget r
    rw [cs,ms]
    rfl

end NearCubicWires.RepairOrdinary.MatrixBatchGateColdCopy
