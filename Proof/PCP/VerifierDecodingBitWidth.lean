import Proof.PCP.VerifierDecodingBitWidthLayout

/-! Enclosing bit-width construction on the actual decoder state counter. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.BitWidthMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def first : Machine 6 19 := Composition.machine frameProgram binaryProgram
def machine : Machine 6 25 := Composition.machine first widthProgram
def input (n : ℕ) : Configuration 6 25 :=
  Composition.leftConfig 6 (Composition.leftConfig 14 (frameInput n))
def output (n a b : ℕ) : Configuration 6 25 := Composition.rightConfig 19 (finished n a b)
def budget (n : ℕ) := 4*n+binaryBudget n+4*width n+7

theorem width_eq (n : ℕ) (hn : 0 < n) : width n = natBitLength n :=
  ClockBinary.length_log n hn

theorem budget_bound (c n : ℕ) (hn : n ≤ c) : budget n ≤ 8*c^2+34*c+11 := by
  have hw : width n ≤ n := ClockBinary.length_bound n n Nat.lt_two_pow_self
  have he : PCPResourceLedger.ell n ≤ n := Nat.clog_le_of_le_pow (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  simp only [budget,binaryBudget,ClockLengthReady.budget,ClockInputLength.cost,List.length_replicate]
  nlinarith

/-- From the physically produced unary state count, construct both its exact
binary value and the unary width used by the frozen flat verifier encoding.
Every scratch tape starts blank; every caller-facing head is restored. -/
theorem bit_width_run (n : ℕ) (hn : 0 < n) :
    ∃ a b, a ≤ 2*PCPResourceLedger.ell n+3 ∧
      b ≤ ClockInputLength.cost n (List.replicate n true) ∧
      ∃ receipt : ExecutionReceipt 6 25,
        runFrom machine (budget n) (input n) = some receipt ∧
        receipt.final = output n a b ∧ receipt.steps ≤ budget n := by
  obtain ⟨rf,hrf,hff,hsf⟩ := frame_layout n
  obtain ⟨a,b,ha,hb,rb,hrb,hfb,hsb⟩ := binary_layout n hn
  have hrb' : runFrom binaryProgram (binaryBudget n) (Composition.restart rf.final binaryProgram.start) = some rb := by
    rw [hff]
    exact hrb
  have hj := Composition.run_join frameProgram binaryProgram (4*n+2) (binaryBudget n) _ rf rb hrf hrb'
  let rfirst := Composition.joinedReceipt rf rb
  obtain ⟨rw,hrw,hfw,hsw⟩ := width_layout n a b
  have hrw' : runFrom widthProgram (4*width n+3) (Composition.restart rfirst.final widthProgram.start) = some rw := by
    change runFrom widthProgram (4*width n+3)
      (Composition.restart (Composition.rightConfig 5 rb.final) widthProgram.start) = some rw
    rw [hfb]
    exact hrw
  have hwhole := Composition.run_join first widthProgram ((4*n+2)+1+binaryBudget n) (4*width n+3)
    _ rfirst rw hj hrw'
  let result := Composition.joinedReceipt rfirst rw
  have hclock : ((4*n+2)+1+binaryBudget n)+1+(4*width n+3) = budget n := by
    dsimp only [budget]
    omega
  rw [hclock] at hwhole
  refine ⟨a,b,ha,hb,result,hwhole,?_,?_⟩
  · change Composition.rightConfig 19 rw.final = output n a b
    rw [hfw]
    rfl
  · change rf.steps+1+rb.steps+1+rw.steps ≤ budget n
    dsimp only [budget]
    omega

/-- Consumer form matching exactly j = natBitLength s and fixedBits j s. -/
theorem state_width_run (c s : ℕ) (hs : 0 < s) (hsc : s ≤ c) :
    ∃ receipt : ExecutionReceipt 6 25,
      runFrom machine (8*c^2+34*c+11) (input s) = some receipt ∧
      receipt.final.tapes 0 = CompareMachine.word s ∧
      receipt.final.tapes 2 = frame (VerifierEncoding.fixedBits (natBitLength s) s) ∧
      receipt.final.tapes 5 = CompareMachine.word (natBitLength s) ∧
      receipt.final.heads = ![1,0,0,0,0,1] ∧ receipt.steps ≤ 8*c^2+34*c+11 := by
  obtain ⟨a,b,_,_,r,hr,hf,hsteps⟩ := bit_width_run s hs
  have hbound := budget_bound c s hsc
  have hmore := runFrom_moreFuel machine (budget s) (8*c^2+34*c+11-budget s) _ r hr
  rw [Nat.add_sub_of_le hbound] at hmore
  have he : VerifierEncoding.fixedBits (natBitLength s) s = ClockBinary.word s := by
    rw [fixedBits_binary,←width_eq s hs]
    exact ClockBinary.word_binary s
  refine ⟨r,hmore,?_,?_,?_,?_,hsteps.trans hbound⟩
  · simp [hf,output,Composition.rightConfig,finished]
  · simp [hf,output,Composition.rightConfig,finished,dimension,he]
  · simp [hf,output,Composition.rightConfig,finished,width_eq s hs]
  · simp [hf,output,Composition.rightConfig,finished]

end NearCubicWires.RepairSource.VerifierDecoding.BitWidthMachine
