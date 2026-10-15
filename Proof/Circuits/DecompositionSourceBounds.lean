import Proof.PCP.PCPPQueryNatural
import Proof.Amplification.RecoveryTapeSupport

/-! The child count is bounded by the actual fresh output of the SAME
ordinary decomposition constructor. No quantitative source field is added. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource
open LocalBitMultitape RepairRepresentation SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem one_tape_support {t s : ℕ} (p : Machine t s) (fuel : ℕ)
    (c : Configuration t s) (r : ExecutionReceipt t s) (i : Fin t) (k : ℕ)
    (hr : runFrom p fuel c=some r) (hh : c.heads i ≤ k)
    (ht : (c.tapes i).length ≤ k) : (r.final.tapes i).length ≤ k+r.steps := by
  induction fuel generalizing c r k with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; simpa using ht
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; simpa using ht
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases he : runFrom p fuel d with
        | none => simp [hs,he] at hr
        | some tail =>
          simp only [hs,he,Option.some.injEq] at hr
          subst r
          have hh' : d.heads i ≤ k+1 := by
            unfold step at hs
            obtain ⟨action,_,ha⟩ := Option.map_eq_some_iff.mp hs
            subst d
            simp only [applyAction]
            cases action.move i <;> simp only [HeadMove.apply] <;> omega
          have ht' : (d.tapes i).length ≤ k+1 := by
            unfold step at hs
            obtain ⟨action,_,ha⟩ := Option.map_eq_some_iff.mp hs
            subst d
            simp only [applyAction]
            cases action.write i <;> simp only [RecoveryTapeSupport.write_length] <;> omega
          have h := ih d tail (k+1) he hh' ht'
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def sourceBudget (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :=
  a.coefficient*(r.arity+r.gate.encodingBits+1)^a.degree

theorem output_length (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    (exactListWord (a.output r).children).length ≤ sourceBudget a r := by
  obtain ⟨receipt,hr,ho⟩ := a.constructor.realizes r
  have h := one_tape_support a.constructor.program.machine _ _ receipt
    a.constructor.program.outputTape 0 hr (by rfl)
    (by simp [initialConfiguration,Program.inputTapes,a.constructor.program.outputFresh])
  rw [ho] at h
  simpa only [Nat.zero_add,sourceBudget] using h.trans
    (by simpa only [Nat.zero_add] using runFrom_steps_le _ _ _ _ hr)

@[simp] theorem natWord_length (n : ℕ) : (natWord n).length=2*natBitLength n+1 := by
  simpa [PCPPQueryField.fieldBits] using PCPPQueryField.fieldBits_length n

@[simp] theorem intWord_length (z : ℤ) : (intWord z).length=2*intBitLength z+2 := by
  simp [intWord,natBitLength,intBitLength]

theorem exactWord_nonempty {n : ℕ} (g : ExactThresholdGate n) : 1 ≤ (exactWord g).length := by
  simp only [exactWord,List.length_append,intWord_length]
  omega

theorem children_le_output {n : ℕ} (gs : List (ExactThresholdGate n)) :
    gs.length ≤ (exactListWord gs).length := by
  have h : gs.length ≤ (gs.flatMap exactWord).length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      have hg := exactWord_nonempty g
      omega
  simp only [exactListWord,List.length_append]
  omega

theorem children_bound (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) :
    (a.output r).children.length ≤ a.coefficient*(r.arity+r.gate.encodingBits+1)^a.degree :=
  (children_le_output _).trans (output_length a r)

theorem thresholdWord_length {n : ℕ} (g : NormalizedThresholdGate n) :
    (thresholdWord g).length=2*natBitLength n+2*g.encodingBits+2*n+3 := by
  simp only [thresholdWord,List.length_append,natWord_length,List.length_flatMap,
    intWord_length,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  simp only [NormalizedThresholdGate.encodingBits,Finset.sum_add_distrib,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem thresholdWord_bound {n : ℕ} (g : NormalizedThresholdGate n) :
    (thresholdWord g).length ≤ 8*(n+g.encodingBits+1) := by
  rw [thresholdWord_length]
  have hb : natBitLength n ≤ n+1 := by unfold natBitLength; have := Nat.log_le_self 2 n; omega
  omega

end NearCubicWires.RepairOrdinary.DecompositionSource
