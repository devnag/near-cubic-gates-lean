import Proof.MachineModel.OrdinaryMatrixBucketBudgetPrepare

/-! Whole canonical budget computation, including the executed Gates=0
branch which prints one instead of calling positive-divisor division. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketBudget
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def divideSlots : Fin 4 → Fin 9 := ![2,1,7,8]
def oneSlots : Fin 2 → Fin 9 := ![7,8]
noncomputable def divide := RecoveryFocus.machine divideSlots MatrixBucketDivide.machine
noncomputable def one := RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine [true])
def sizes : Fin 3 → ℕ := ![11,6,4]
noncomputable def programs : (j : Fin 3) → Machine 9 (sizes j)
  | ⟨0,_⟩ => MatrixBucketBudgetPrepare.machine
  | ⟨1,_⟩ => divide
  | ⟨2,_⟩ => one
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 9 → Bool) : Option (Fin 3) :=
  if j=0 then if bits 6 then some 1 else some 2 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def value (C G : ℕ) := if G=0 then 1 else C/G
def budget (C : ℕ) := 12*C+24

theorem divide_run (C G : ℕ) (ambient : Fin 9 → List Bool) (hG : 0<G)
    (h1 : ambient 1=UnaryTemplate.tape G) (h2 : ambient 2=List.replicate C true)
    (h7 : ambient 7=[]) (h8 : ambient 8=[]) :
    ∃ actual,runFrom divide (8*C+6) (RecoveryCalls.restarted divide (fun _ => 0) ambient)=some actual ∧
      actual.final.heads=(fun _ => 0) ∧ actual.final.tapes 0=ambient 0 ∧ actual.final.tapes 1=ambient 1 ∧
      actual.final.tapes 7=List.replicate (C/G) true ∧ actual.steps≤8*C+6 := by
  obtain ⟨base,hb,b0,b1,b2,bh,bs⟩ := MatrixBucketDivide.divide_run C G hG
  have ready : ClockJoin.ReadyRun MatrixBucketDivide.machine (8*C+6) (MatrixBucketDivide.resetInput C G) base.final.tapes :=
    ⟨base,hb,rfl,bh,bs⟩
  obtain ⟨actual,ha,ah,atapes,as⟩ := CompetitorReusableDecision.bounded_focused_run divideSlots (by decide)
    MatrixBucketDivide.machine _ _ ready (fun _ => 0) ambient (by intro i; rfl)
    (by intro i; fin_cases i; exact h2; exact h1; exact h7; exact h8)
  have localT (i : Fin 4) : actual.final.tapes (divideSlots i)=base.final.tapes i := by
    rw [atapes]
    exact install_slot divideSlots (by decide) _ _ i
  refine ⟨actual,ha,ah,?_,(localT 1).trans (b1.trans h1.symm),(localT 2).trans b2,as⟩
  rw [atapes]
  exact install_other divideSlots _ _ 0 (by decide)

theorem one_run (ambient : Fin 9 → List Bool) (h7 : ambient 7=[]) (h8 : ambient 8=[]) :
    ∃ actual,runFrom one 4 (RecoveryCalls.restarted one (fun _ => 0) ambient)=some actual ∧
      actual.final.heads=(fun _ => 0) ∧ actual.final.tapes 0=ambient 0 ∧ actual.final.tapes 1=ambient 1 ∧
      actual.final.tapes 7=[true] ∧ actual.steps≤4 := by
  have ready := HierarchyFixedWord.word_ready [true]
  obtain ⟨actual,ha,ah,atapes,as⟩ := HierarchyBinary.focused_run oneSlots (by decide)
    (HierarchyFixedWord.machine [true]) _ _ ready (fun _ => 0) ambient (by intro i; rfl)
    (by intro i; fin_cases i; exact h7; exact h8)
  refine ⟨actual,ha,ah,?_,?_,?_,as.le⟩
  · rw [atapes]; exact install_other oneSlots _ _ 0 (by decide)
  · rw [atapes]; exact install_other oneSlots _ _ 1 (by decide)
  · rw [atapes]; exact install_slot oneSlots (by decide) _ _ 0

theorem budget_run (C G : ℕ) :
    ∃ actual,run machine (budget C) (MatrixBucketBudgetPrepare.input C G)=some actual ∧
      actual.final.tapes 0=UnaryTemplate.tape C ∧ actual.final.tapes 1=UnaryTemplate.tape G ∧
      actual.final.tapes 7=List.replicate (value C G) true ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget C := by
  obtain ⟨prepared,hp,ph,p0,p1,p2,p6,p7,p8,_⟩ := MatrixBucketBudgetPrepare.prepare_run C G
  have flag : prepared.final.scanned 6=decide (0<G) := by
    simp only [Configuration.scanned,ph,p6]
    rfl
  by_cases hz : G=0
  · obtain ⟨t0,h0,hfirst⟩ := call_receipt sizes programs 0 next 0 2 (MatrixBucketBudgetPrepare.budget C)
      (initialConfiguration (programs 0) (MatrixBucketBudgetPrepare.input C G)) prepared hp
      (by simp [next]; exact flag.trans (by simp [hz]))
    rw [ph] at hfirst
    obtain ⟨body,hb,bh,b0,b1,b7,_⟩ := one_run prepared.final.tapes p7 p8
    obtain ⟨t1,h1,hlast⟩ := stop_receipt sizes programs 0 next 2 4
      (RecoveryCalls.restarted (programs 2) (fun _ => 0) prepared.final.tapes) body hb (by rfl)
    have path := hfirst.trans hlast
    obtain ⟨actual,ha,hf,hs⟩ := path.run
      (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have ht : t0+t1≤budget C := by unfold MatrixBucketBudgetPrepare.budget budget at *; omega
    have he := run_moreFuel machine _ (budget C-(t0+t1)) (MatrixBucketBudgetPrepare.input C G) actual ha
    rw [Nat.add_sub_of_le ht] at he
    refine ⟨actual,he,?_,?_,?_,?_,hs.trans_le ht⟩
    · rw [hf]; exact b0.trans p0
    · rw [hf]; exact b1.trans p1
    · rw [hf]
      change body.final.tapes 7=List.replicate (value C G) true
      simpa only [value,hz,ite_true,List.replicate_one] using b7
    · intro i; rw [hf]; exact congrFun bh i
  · have hG : 0<G := by omega
    obtain ⟨t0,h0,hfirst⟩ := call_receipt sizes programs 0 next 0 1 (MatrixBucketBudgetPrepare.budget C)
      (initialConfiguration (programs 0) (MatrixBucketBudgetPrepare.input C G)) prepared hp
      (by simp [next]; exact flag.trans (by simp [hG]))
    rw [ph] at hfirst
    obtain ⟨body,hb,bh,b0,b1,b7,_⟩ := divide_run C G prepared.final.tapes hG p1 p2 p7 p8
    obtain ⟨t1,h1,hlast⟩ := stop_receipt sizes programs 0 next 1 (8*C+6)
      (RecoveryCalls.restarted (programs 1) (fun _ => 0) prepared.final.tapes) body hb (by rfl)
    have path := hfirst.trans hlast
    obtain ⟨actual,ha,hf,hs⟩ := path.run
      (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have ht : t0+t1≤budget C := by unfold MatrixBucketBudgetPrepare.budget budget at *; omega
    have he := run_moreFuel machine _ (budget C-(t0+t1)) (MatrixBucketBudgetPrepare.input C G) actual ha
    rw [Nat.add_sub_of_le ht] at he
    refine ⟨actual,he,?_,?_,?_,?_,hs.trans_le ht⟩
    · rw [hf]; exact b0.trans p0
    · rw [hf]; exact b1.trans p1
    · rw [hf]
      change body.final.tapes 7=List.replicate (value C G) true
      simpa only [value,hz,ite_false] using b7
    · intro i; rw [hf]; exact congrFun bh i

end NearCubicWires.RepairOrdinary.MatrixBucketBudget
