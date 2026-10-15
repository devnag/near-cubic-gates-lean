import Proof.MachineModel.OrdinaryMatrixScoreLeftFields

/-! Complete physical left score: negate the actual left-weight fold, skip
all original right fields, load the actual threshold, and subtract. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreLeft
open LocalBitMultitape SignedSortKey MatrixScoreLeftFields
open MatrixScoreWeight (zeros scalar nextPositive nextNegative)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positive (z : ℤ) := if z<0 then 0 else z.natAbs
def negative (z : ℤ) := if z<0 then z.natAbs else 0
theorem sign_identity (z : ℤ) : z=(positive z : ℤ)-negative z := by
  cases z <;> simp [positive,negative]
  omega

theorem next_positive (P : ℕ) (z : ℤ) : nextPositive P z.natAbs (decide (z<0)) true=P+positive z := by
  by_cases h : z<0 <;> simp [nextPositive,positive,h]
theorem next_negative (N : ℕ) (z : ℤ) : nextNegative N z.natAbs (decide (z<0)) true=N+negative z := by
  by_cases h : z<0 <;> simp [nextNegative,negative,h]

noncomputable def negate := TapeEmbedding.machine 2 MatrixScoreNegativeFold.machine
noncomputable def first := Composition.machine negate MatrixScoreLeftFields.skip
noncomputable def updated := Composition.machine first MatrixScoreLeftFields.threshold
noncomputable def finish := TapeEmbedding.machine 2 MatrixScoreFinish.machine
noncomputable def machine := Composition.machine updated finish
def budget (d p s c : ℕ) :=
  ((MatrixScoreFoldEntry.budget d c p (s+1)+1+(d*(2*p+6)+3))+1+
    MatrixScoreThresholdDriver.budget c p (s+1))+1+MatrixScoreFinish.budget s c

theorem left_run (weights right : List ℤ) (pre suffix apre asuffix : List Bool)
    (p n s c cap : ℕ) (theta : ℤ) (work : Fin 12 → List Bool)
    (hlen : right.length=weights.length)
    (hf : ∀ z ∈ weights,z.natAbs<2^p) (htheta : theta.natAbs<2^p)
    (hw : p≤ s+1) (hc : 4*(s+1)+5≤c) (hcap : cap≤c+1) (hs : ∀ i,(work i).length≤c)
    (hp : MatrixScoreBatch.part true weights n+theta.natAbs<2^s)
    (hn : MatrixScoreBatch.part false weights n+theta.natAbs<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      finalWork 0=scalar c (s+1) (shifted s (theta-MatrixScoreBatch.linearForm weights n)) ∧
      ∃ actual,runFrom machine (budget weights.length p s c)
        (RecoveryCalls.restarted machine (heads pre.length apre.length)
          (tapes (pre++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++
              frame (MatrixScoreBatch.signMagnitude p theta)++suffix)
            (apre++frame (binary weights.length n)++asuffix) weights.length c cap (s+1) (2^s) 0 work [] []))=some actual ∧
        actual.final.heads=heads
          (pre.length+(MatrixScoreCanonical.fields p weights).length+(MatrixScoreCanonical.fields p right).length+2*p+3)
          (apre.length+2*weights.length) ∧
        actual.final.tapes=tapes
          (pre++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++
            frame (MatrixScoreBatch.signMagnitude p theta)++suffix)
          (apre++frame (binary weights.length n)++asuffix) weights.length c (c+1) (s+1) (2^s) 0 finalWork [true,true] (zeros 2) ∧
        actual.steps≤budget weights.length p s c := by
  let source := pre++MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++
    frame (MatrixScoreBatch.signMagnitude p theta)++suffix
  let assignment := apre++frame (binary weights.length n)++asuffix
  let leftPre := pre++MatrixScoreCanonical.fields p weights
  let thetaPre := leftPre++MatrixScoreCanonical.fields p right
  let apos := apre.length+2*weights.length
  let P := MatrixScoreBatch.part true weights n
  let N := MatrixScoreBatch.part false weights n
  have hP : P<2^s := by dsimp [P]; omega
  have hN : N<2^s := by dsimp [N]; omega
  obtain ⟨scratch,hss,base,hb,bh,bt,bs⟩ := MatrixScoreNegativeFold.negative_run weights pre
    (MatrixScoreCanonical.fields p right++frame (MatrixScoreBatch.signMagnitude p theta)++suffix)
    apre asuffix p n s c cap work hf hw (by omega) hcap hs hN hP
  have he := TapeEmbedding.run_embed MatrixScoreNegativeFold.machine (fun _ : Fin 2 => 0) ![[],[]] _ _ base hb
  let negated := TapeEmbedding.receipt (fun _ : Fin 2 => 0) ![[],[]] base
  have nh : negated.final.heads=heads leftPre.length apos := by
    funext i
    fin_cases i <;> simp [negated,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bh,heads,
      MatrixScoreFoldEntry.heads,leftPre,apos]
  have nt : negated.final.tapes=tapes source assignment weights.length c (c+1) (s+1) (2^s) 0
      (MatrixScoreFoldEntry.accumulators c (s+1) (2^s+P) N scratch) [] [] := by
    funext i
    fin_cases i <;> simp [negated,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bt,tapes,
      MatrixScoreFoldEntry.tapes,source,assignment,P,N,List.append_assoc]
  obtain ⟨skipped,hk,kh,kt,ks⟩ := MatrixScoreLeftFields.skip_run right leftPre
    (frame (MatrixScoreBatch.signMagnitude p theta)++suffix) assignment [] [] p apos c (c+1) (s+1) (2^s) 0
    (MatrixScoreFoldEntry.accumulators c (s+1) (2^s+P) N scratch)
  simp only [hlen] at hk kh kt ks
  have sourceSkip : leftPre++MatrixScoreCanonical.fields p right++(frame (MatrixScoreBatch.signMagnitude p theta)++suffix)=source := by
    simp [source,leftPre,List.append_assoc]
  rw [sourceSkip] at hk kt
  have ki : Composition.restart negated.final MatrixScoreLeftFields.skip.start=
      RecoveryCalls.restarted MatrixScoreLeftFields.skip (heads leftPre.length apos)
        (tapes source assignment weights.length c (c+1) (s+1) (2^s) 0
          (MatrixScoreFoldEntry.accumulators c (s+1) (2^s+P) N scratch) [] []) := by
    apply configuration_ext
    · rfl
    · exact nh
    · exact nt
  rw [← ki] at hk
  have hkJoin := Composition.run_join negate MatrixScoreLeftFields.skip _ _ _ negated skipped he hk
  have hfit : theta.natAbs+(if theta<0 then N else 2^s+P)<2^(s+1) := by
    have pow : 2^(s+1)=2*2^s := by rw [Nat.pow_succ]; omega
    rw [pow]
    dsimp [P,N]
    split <;> omega
  obtain ⟨afterScratch,has,applied,ha,ah,appliedTapes,aas⟩ := MatrixScoreLeftFields.threshold_run thetaPre suffix assignment
    apos weights.length p c (s+1) (2^s) 0 (2^s+P) N theta scratch hss htheta hw (by omega) hfit
  have sourceTheta : thetaPre++frame (MatrixScoreBatch.signMagnitude p theta)++suffix=source := by rfl
  rw [sourceTheta] at ha appliedTapes
  have ai : Composition.restart (Composition.joinedReceipt negated skipped).final MatrixScoreLeftFields.threshold.start=
      RecoveryCalls.restarted MatrixScoreLeftFields.threshold (heads thetaPre.length apos)
        (tapes source assignment weights.length c (c+1) (s+1) (2^s) 0
          (MatrixScoreFoldEntry.accumulators c (s+1) (2^s+P) N scratch) [] []) := by
    apply configuration_ext
    · rfl
    · change skipped.final.heads=_
      rw [kh]
      simp only [thetaPre,List.length_append,RecoveryCalls.restarted]
    · exact kt
  rw [← ai] at ha
  have haJoin := Composition.run_join first MatrixScoreLeftFields.threshold _ _ _
    (Composition.joinedReceipt negated skipped) applied hkJoin ha
  have hp' : P+positive theta<2^s := by
    have ht : positive theta≤theta.natAbs := by unfold positive; split <;> omega
    dsimp [P]; omega
  have hn' : N+negative theta<2^s := by
    have ht : negative theta≤theta.natAbs := by unfold negative; split <;> omega
    dsimp [N]; omega
  rw [next_positive,next_negative] at appliedTapes
  rw [Nat.add_assoc (2^s) P (positive theta)] at appliedTapes
  obtain ⟨finalWork,hws,hw0,ended,hg,gh,gt,gs⟩ := MatrixScoreFinish.finish_run source assignment
    (thetaPre.length+2*p+3) apos weights.length c s (P+positive theta) (N+negative theta) (2^s) 0 afterScratch has hp' hn' hc
  have ge := TapeEmbedding.run_embed MatrixScoreFinish.machine (fun _ : Fin 2 => 0)
    ![[true,true],zeros 2] _ _ ended hg
  let finished := TapeEmbedding.receipt (fun _ : Fin 2 => 0) ![[true,true],zeros 2] ended
  have gi : TapeEmbedding.config (fun _ : Fin 2 => 0) ![[true,true],zeros 2]
      (RecoveryCalls.restarted MatrixScoreFinish.machine
        (MatrixScoreFoldEntry.heads (thetaPre.length+2*p+3) apos)
        (MatrixScoreFoldEntry.tapes source assignment weights.length c (c+1) (s+1) (2^s) 0
          (MatrixScoreFoldEntry.accumulators c (s+1) (2^s+(P+positive theta)) (N+negative theta) afterScratch)))=
      Composition.restart (Composition.joinedReceipt (Composition.joinedReceipt negated skipped) applied).final finish.start := by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact appliedTapes.symm
  rw [gi] at ge
  have joined := Composition.run_join updated finish _ _ _
    (Composition.joinedReceipt (Composition.joinedReceipt negated skipped) applied) finished haJoin ge
  have initial : Composition.leftConfig _ (Composition.leftConfig _ (Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 2 => 0) ![[],[]]
        (RecoveryCalls.restarted MatrixScoreNegativeFold.machine (MatrixScoreFoldEntry.heads pre.length apre.length)
          (MatrixScoreFoldEntry.tapes (pre++MatrixScoreCanonical.fields p weights++
              (MatrixScoreCanonical.fields p right++frame (MatrixScoreBatch.signMagnitude p theta)++suffix))
            assignment weights.length c cap (s+1) (2^s) 0 work)))))=
      RecoveryCalls.restarted machine (heads pre.length apre.length)
        (tapes source assignment weights.length c cap (s+1) (2^s) 0 work [] []) := by
    apply configuration_ext
    · rfl
    · rfl
    · simp only [source,List.append_assoc]
      rfl
  rw [initial] at joined
  have hvalue : ((P+positive theta : ℕ) : ℤ)-((N+negative theta : ℕ) : ℤ)=theta-MatrixScoreBatch.linearForm weights n := by
    have sig := sign_identity theta
    rw [MatrixScoreBatch.linearForm_parts]
    dsimp [P,N]
    omega
  rw [hvalue] at hw0
  refine ⟨finalWork,hws,hw0,Composition.joinedReceipt
    (Composition.joinedReceipt (Composition.joinedReceipt negated skipped) applied) finished,joined,?_,?_,?_⟩
  · change finished.final.heads=_
    funext i
    fin_cases i <;> simp [finished,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,gh,heads,
      MatrixScoreFoldEntry.heads,thetaPre,leftPre,apos,Nat.add_assoc]
  · change finished.final.tapes=_
    funext i
    fin_cases i <;> simp [finished,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,gt,tapes,
      MatrixScoreFoldEntry.tapes,source,assignment]
  · change ((base.steps+1+skipped.steps)+1+applied.steps)+1+ended.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreLeft
