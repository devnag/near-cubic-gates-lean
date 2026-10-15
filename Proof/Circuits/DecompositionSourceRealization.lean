import Proof.Circuits.DecompositionSourceEntry

/-! Literal ordinary source-entry realization, with a polynomial envelope
derived from the selected constructor's own coefficient and degree. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def parameter (r : ExactDecompositionRequest) := r.arity+r.gate.encodingBits+1
def coefficient (a : DecompositionAlgorithm) := 1024*(a.coefficient+2)^2
def degree (a : DecompositionAlgorithm) := 2*a.degree+2

theorem entry_budget_coarse (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    Entry.budget a r ≤ 1024*(sourceBudget a r+parameter r+1)^2 := by
  let n := r.arity
  let m := (a.output r).children.length
  let S := parameter r
  let B := sourceBudget a r
  let W := B+S+1
  have hn : n+1 ≤ S := by dsimp [n,S,parameter]; omega
  have hm : m ≤ B := children_bound a r
  have hout := output_length a r
  have hbody : ((a.output r).children.flatMap exactWord).length ≤ B := by
    have hx : (natWord m).length+((a.output r).children.flatMap exactWord).length ≤ B := by
      simpa only [exactListWord,List.length_append] using hout
    omega
  have hinput := thresholdWord_bound r.gate
  have hinput' : (natWord n++Call.tail r).length ≤ 8*S := by
    simpa only [thresholdWord,Call.tail,List.append_assoc,n,S,parameter] using hinput
  have harity := Count.budget_bound n
  have hchildren := Count.budget_bound m
  have hnbit : natBitLength n ≤ n+1 := by unfold natBitLength; have := Nat.log_le_self 2 n; omega
  have hmbit : natBitLength m ≤ m+1 := by unfold natBitLength; have := Nat.log_le_self 2 m; omega
  have hNW : n+1 ≤ W := by dsimp [W]; omega
  have hMW : m+1 ≤ W := by dsimp [W]; omega
  have hBW : B ≤ W := by dsimp [W]; omega
  have hSW : S ≤ W := by dsimp [W]; omega
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hn2 : (n+1)^2 ≤ W^2 := Nat.pow_le_pow_left hNW 2
  have hm2 : (m+1)^2 ≤ W^2 := Nat.pow_le_pow_left hMW 2
  have hnm : n*m ≤ W^2 := by
    calc n*m ≤ W*W := Nat.mul_le_mul (by omega) (by omega)
         _ = W^2 := by ring
  have hW2 : W ≤ W^2 := by nlinarith
  change Entry.budget a r ≤ 1024*W^2
  unfold Entry.budget Counted.budget Call.budget Prepare.budget PCPPQueryField.fieldCost
  change 4*(natWord n++Call.tail r).length+Count.budget n+(2*natBitLength n+3)+4+
      2*B+3+Count.budget m+1+(2*natBitLength m+3)+
      ((a.output r).children.flatMap exactWord).length+(6*n+10)*m+5 ≤ _
  nlinarith

theorem entry_budget (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    Entry.budget a r ≤ coefficient a*(r.arity+r.gate.encodingBits+1)^degree a := by
  let S := parameter r
  have hS : 1 ≤ S := by dsimp [S,parameter]; omega
  have hpow : S^a.degree ≤ S^(a.degree+1) := Nat.pow_le_pow_right hS (by omega)
  have hlinear : S ≤ S^(a.degree+1) := by
    calc S=S^1 := by simp
         _ ≤ S^(a.degree+1) := Nat.pow_le_pow_right hS (by omega)
  have hone : 1 ≤ S^(a.degree+1) := Nat.one_le_pow _ _ hS
  have hB : sourceBudget a r ≤ a.coefficient*S^(a.degree+1) := Nat.mul_le_mul_left _ hpow
  have hsum : sourceBudget a r+parameter r+1 ≤ (a.coefficient+2)*S^(a.degree+1) := by
    change sourceBudget a r+S+1 ≤ _
    nlinarith
  calc
    Entry.budget a r ≤ 1024*(sourceBudget a r+parameter r+1)^2 := entry_budget_coarse a r
    _ ≤ 1024*((a.coefficient+2)*S^(a.degree+1))^2 := by gcongr
    _ = coefficient a*(r.arity+r.gate.encodingBits+1)^degree a := by
      rw [mul_pow,← pow_mul]
      have hdegree : (a.degree+1)*2=degree a := by unfold degree; omega
      rw [hdegree]
      simp [coefficient,S,parameter,Nat.mul_assoc]

noncomputable def program (a : DecompositionAlgorithm) : Program where
  tapeCount := Counted.tapes a
  stateCount := _
  twoTapes := by unfold Counted.tapes Call.tapes; omega
  machine := Entry.machine a
  outputTape := Counted.localTape a 15
  outputFresh := by change (15 : ℕ)≠0; decide

theorem input_eq (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    (program a).inputTapes (thresholdWord r.gate)=Counted.input a r := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp [program,Program.inputTapes,Counted.input,Call.input,Prepare.input,thresholdWord,
        Call.tail,List.append_assoc]
    · simp [program,Program.inputTapes,Counted.input,Call.input]
  · simp [program,Program.inputTapes,Counted.input]

noncomputable def realization (a : DecompositionAlgorithm) :
    RepairSource.OrdinaryWordFunction ExactDecompositionRequest
      (fun r => thresholdWord r.gate)
      (fun r => natWord r.arity++exactListWord (a.output r).children)
      (fun r => coefficient a*(r.arity+r.gate.encodingBits+1)^degree a) where
  program := program a
  realizes := by
    intro r
    obtain ⟨receipt,hr,_,hout,_,_,_,_,_⟩ := Entry.entry_run a r
    have hm := run_moreFuel (Entry.machine a) (Entry.budget a r)
      (coefficient a*(r.arity+r.gate.encodingBits+1)^degree a-Entry.budget a r) _ receipt hr
    rw [Nat.add_sub_of_le (entry_budget a r)] at hm
    refine ⟨receipt,?_,hout⟩
    rw [input_eq]
    exact hm

theorem coefficient_positive (a : DecompositionAlgorithm) : 0<coefficient a := by unfold coefficient; positivity

end NearCubicWires.RepairOrdinary.DecompositionSource
