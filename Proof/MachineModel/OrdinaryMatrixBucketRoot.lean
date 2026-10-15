import Proof.MachineModel.OrdinaryMatrixBucketRootLoop

namespace NearCubicWires.RepairOrdinary.MatrixBucketRootCold
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBucketRootClear (tapes)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2 → Fin 27 := ![0,26]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := RecoveryFocus.machine slots (HierarchyFixedWord.machine (UnaryTemplate.tape 1))
noncomputable def machine := Composition.machine first MatrixBucketRootCalls.machine
def input (r : Request) : Fin 27 → List Bool := fun i =>
  if i=22 then UnaryTemplate.tape r.U else if i=25 then List.replicate (D r) true else []
def budget (r : Request) := 8+1+MatrixBucketRootLoop.budget r

theorem prepare_ready (r : Request) : ReadyRun first 8 (input r) (tapes r 1 3 (fun _ => [])) := by
  have ready := (HierarchyFixedWord.word_ready (UnaryTemplate.tape 1)).focus slots slots_injective (input r)
    (by intro i; fin_cases i <;> rfl)
  have ht : install slots (input r) ![UnaryTemplate.tape 1,List.replicate 3 false]=tapes r 1 3 (fun _ => []) := by
    funext i
    by_cases h0 : i=0
    · subst i
      exact install_slot slots slots_injective _ _ 0
    by_cases h26 : i=26
    · subst i
      exact install_slot slots slots_injective _ _ 1
    have hn : RecoveryFocus.pick slots i=none := by
      have no : ¬ ∃ j,slots j=i := by
        rintro ⟨j,hj⟩
        fin_cases j
        · exact h0 hj.symm
        · exact h26 hj.symm
      simp [RecoveryFocus.pick,no]
    simp only [install,hn]
    fin_cases i <;> first | contradiction | rfl
  change ReadyRun first 8 (input r) (install slots (input r) ![UnaryTemplate.tape 1,List.replicate 3 false]) at ready
  rw [ht] at ready
  exact ready

theorem root_run (r : Request) :
    ∃ work : Fin 23 → List Bool,(∀ i,(work i).length≤D r) ∧
      ∃ actual,run machine (budget r) (input r)=some actual ∧
        actual.final.heads=(fun _ => 0) ∧
        actual.final.tapes=tapes r (MatrixBucketDimensions.capacity r.U) (D r+1) work ∧
        actual.steps≤budget r := by
  obtain ⟨prepared,hp,pt,ph,ps⟩ := prepare_ready r
  obtain ⟨work,hw,body,hb,hbf,bs⟩ := MatrixBucketRootLoop.search_run r 3 (fun _ => []) (by intro i; simp)
  have hi : MatrixBucketRootCalls.boundary 0 r 1 3 (fun _ => [])=
      Composition.restart prepared.final MatrixBucketRootCalls.machine.start := by
    apply configuration_ext
    · rfl
    · exact (funext ph).symm
    · exact pt.symm
  rw [hi] at hb
  have joined := Composition.run_join first MatrixBucketRootCalls.machine _ _ _ prepared body hp hb
  have hD : 104000*(r.U+1)≤D r := (MatrixBatchCapacity.request_capacity r).2
  have hcap : max 3 (D r+1)=D r+1 := Nat.max_eq_right (by omega)
  refine ⟨work,hw,Composition.joinedReceipt prepared body,joined,?_,?_,?_⟩
  · change body.final.heads=_
    rw [hbf]
    rfl
  · change body.final.tapes=_
    rw [hbf]
    change tapes r (MatrixBucketDimensions.capacity r.U) (max 3 (D r+1)) work=_
    rw [hcap]
  · change prepared.steps+1+body.steps≤budget r
    rw [ps]
    exact Nat.add_le_add_left bs 9

end NearCubicWires.RepairOrdinary.MatrixBucketRootCold
