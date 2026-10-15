import Proof.Assembly.ClosureHardwireReusable

/-! A.12's hardwired-child preparation, including reusable scratch, has a
uniform quadratic source-size budget. The whole copied source suffix and
backing are bounded; the append output is deliberately outside that bound.
All C/D/E/R workspace premises of the executed reusable call are discharged. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireBudget
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open VerifierDecoding SignedSortKey
open scoped BigOperators

def C (w : Nat) := 8*w+12
def D (q w : Nat) := q*(28*w+2*C w+50)+3
def E (B q : Nat) := B+10*q+3
def R (B q w : Nat) := 1024*(B+q+w+1)^2
def budget (B q w : Nat) := 8192*(B+q+w+1)^2

theorem score_loop {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (w : Nat) :
    C10NaturalHardwireScore.loopBudget (C10NaturalHardwireScore.items live g y) w (C w)=D q w := by
  simp only [C10NaturalHardwireScore.loopBudget,C10NaturalHardwireScore.items,List.length_ofFn,
    CloseoutRowsPoolMinimum.uniformBudget,D]

theorem negative_loop {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (w : Nat) :
    CloseoutRowsPoolMinimum.loopBudget (C10NaturalHardwireScore.items live g y) w (C w)=D q w := by
  simp only [CloseoutRowsPoolMinimum.loopBudget,C10NaturalHardwireScore.items,List.length_ofFn,
    CloseoutRowsPoolMinimum.uniformBudget,D]

theorem weight_loop {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (tail : List Bool) (B : Nat) (hsource : (exactWord g++tail).length≤B) :
    C10NaturalHardwireWeights.loopBudget (C10NaturalHardwireWeights.gateItems g live)≤E B q := by
  unfold C10NaturalHardwireWeights.loopBudget
  rw [C10NaturalHardwireWeights.gateItems_word]
  simp only [C10NaturalHardwireWeights.gateItems,List.length_ofFn,E]
  simp only [exactWord,List.length_append] at hsource
  unfold C10NaturalHardwireWeights.weightWord
  omega

theorem child_bound {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (tail : List Bool) (B w : Nat)
    (hsource : (exactWord g++tail).length≤B) (hw : 0<w)
    (hm : g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) :
    HardwireChild.budget live g y w (C w) ≤ 512*(B+q+w+1)^2 := by
  have he := weight_loop live g tail B hsource
  have ht : natBitLength g.target.natAbs≤w := CompactCacheCost.bit_bound g.target w hw (by omega)
  have target := C10NaturalHardwireTarget.budget_le g.target w ht
  have linear : HardwireChild.budget live g y w (C w) ≤
      2*B+132*q*w+242*q+76*w+144 := by
    unfold HardwireChild.budget HardwireChild.scoreTargetBudget C10NaturalHardwireScoreInputs.budget
    rw [score_loop,negative_loop]
    unfold D C E at *
    nlinarith
  exact linear.trans (by nlinarith)

theorem reserve {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (tail : List Bool) (B w : Nat)
    (hsource : (exactWord g++tail).length≤B) (hw : 0<w)
    (hm : g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) :
    HardwireChild.budget live g y w (C w)+2≤R B q w := by
  have h := child_bound live g y tail B w hsource hw hm
  have one : 1≤(B+q+w+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold R
  omega

theorem masters_fit {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (tail backing : List Bool) (B w : Nat)
    (hsource : (exactWord g++tail).length≤B) (hback : backing.length≤B) :
    ∀ j,(HardwireReusable.masters live g y tail backing w (C w) (D q w) (E B q) j).length≤R B q w := by
  have square : B+q+w+1≤(B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  have hB : B≤R B q w := by unfold R; omega
  have hc : C w+1≤R B q w := by unfold C R; omega
  have hd : D q w≤R B q w := by unfold D C R; nlinarith
  have he : E B q≤R B q w := by unfold E R; omega
  have hq : q+1≤R B q w := by unfold R; omega
  have hw : 2*w+1≤R B q w := by unfold R; omega
  have hs := hsource.trans hB
  simp only [List.length_append] at hs
  have hb := hback.trans hB
  intro j
  fin_cases j <;>
    simp [HardwireReusable.masters,HardwireReusable.work,HardwireChild.data,HardwireChild.extra,
      C10NaturalHardwireScoreInputs.data,C10NaturalHardwireScoreInputs.extra,
      C10NaturalHardwireTarget.input,C10NaturalHardwireTarget.pairInput,C10NaturalHardwireTarget.pairExtra,
      C10NaturalHardwireTarget.extra,CloseoutRowsPoolMagnitude.input,CloseoutRowsGateSupport.gateMembers,
      Fin.addCases,MatrixScoreWeight.scalar,ZeroPadding.pad_length,
      frame_length,binary_length,List.length_replicate,List.length_ofFn,CompareMachine.word,
      List.length_cons] <;> omega

theorem reusable_bound {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (tail : List Bool) (B w : Nat)
    (hsource : (exactWord g++tail).length≤B) (hw : 0<w)
    (hm : g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) :
    HardwireReusable.budget live g y w (C w) (R B q w)≤budget B q w := by
  have h := child_bound live g y tail B w hsource hw hm
  have one : 1≤(B+q+w+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold HardwireReusable.budget R budget
  omega

theorem run {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (tail backing out : List Bool) (B w : Nat)
    (hsource : (exactWord g++tail).length≤B) (hback : backing.length≤B)
    (hw : 0<w) (hm : g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) :
    Step HardwireReusable.machine (budget B q w) (HardwireReusable.heads out 1)
      (HardwireReusable.input live g y tail backing w (C w) (D q w) (E B q) out (R B q w))
      (HardwireReusable.heads (out++exactWord (C10SupplierRowInput.hardwire live g y)) 1)
      (HardwireReusable.input live g y tail backing w (C w) (D q w) (E B q)
        (out++exactWord (C10SupplierRowInput.hardwire live g y)) (R B q w)) := by
  have h := HardwireReusable.run live g y tail backing w (C w) (D q w) (E B q) out (R B q w)
    hw hm le_rfl (score_loop live g y w).le (weight_loop live g tail B hsource)
    (masters_fit live g y tail backing B w hsource hback) (reserve live g y tail B w hsource hw hm)
  exact h.enlarge (reusable_bound live g y tail B w hsource hw hm)

end NearCubicWires.P1Closure.HardwireBudget
