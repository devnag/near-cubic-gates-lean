import Proof.PCP.PCPPNativeClauseOracleLayout

/-! The original Q-loop and its retained oracle physically supply every
raw-count clause-entry port, including both original-output offsets. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseOracle
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def beforeClauses := Composition.machine first second
def prefixBudget {R : ℕ} (oracle : BooleanCircuit R) (Q M Lq Lc : ℕ) :=
  PCPPNativeQueryConjunction.budget R Q oracle.size M Lq Lc+1+PCPPNativeOracleScalars.budget oracle

theorem prefix_run (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width≤R) (hQ : p.queries≤Q) {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit R) (suffix clauseFields : List Bool) (M : ℕ) :
    let Lq := (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length
    let Lc := clauseFields.length
    let W := PCPPNativeResources.W R Q oracle.size M Lq Lc
    let out := PCPPNativeQueryConjunction.queryBytes p R Q hR hQ x oracle++PCPPNativeConjunctionStart.trueBits
    ∃ result,run beforeClauses (prefixBudget oracle Q M Lq Lc)
      (input (PCPPNativeQueryConjunction.input (PCPPNative.descriptor oracle)
        (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) R Q oracle.size M Lq Lc) clauseFields)=some result ∧
      result.steps≤prefixBudget oracle Q M Lq Lc ∧
      (∀ i : Fin 58,result.final.heads (clauseSlots i)=
        (PCPPNativeClauseRawRun.entry clauseFields 0 (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size)
          (PCPPNativeCapacityReady.C W) (Q*(2*oracle.size+1)+1) (Q*(2*oracle.size+1)) out M).heads i ∧
        result.final.tapes (clauseSlots i)=
        (PCPPNativeClauseRawRun.entry clauseFields 0 (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size)
          (PCPPNativeCapacityReady.C W) (Q*(2*oracle.size+1)+1) (Q*(2*oracle.size+1)) out M).tapes i) ∧
      result.final.heads 14=0 ∧ result.final.tapes 14=List.replicate (PCPPNativeCount.outputIndex Q oracle.size M) true ∧
      result.final.heads 16=0 ∧ result.final.tapes 16=List.replicate (PCPPNativeCount.nativeSize Q oracle.size M) true := by
  intro Lq Lc W out
  obtain ⟨a,ar,as,aoh,ao,abh,ab,aah,aa,aCh,aC,aMh,aM,ash,ast,a14h,a14,a16h,a16,a95h,a95,a1h,a1⟩:=
    PCPPNativeQueryConjunction.query_conjunction_retained_run p R Q hR hQ x oracle suffix M Lc
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 85=>0) (extra clauseFields) a
  have firstRun:=TapeEmbedding.run_embed PCPPNativeQueryConjunction.machine (fun _ : Fin 85=>0)
    (extra clauseFields) _ _ a ar
  obtain ⟨scalars,⟨b,br,bt,bh,bs⟩,_,bn,bp⟩:=PCPPNativeOracleScalars.scalar_run oracle
  obtain ⟨c,cr,_,cs,ch,ct,other⟩:=RecoveryFocus.dock scalarSlots scalar_injective PCPPNativeOracleScalars.machine _
    lifted.final.heads lifted.final.tapes
    (initialConfiguration PCPPNativeOracleScalars.machine (PCPPNativeOracleScalars.input (PCPPNative.descriptor oracle) oracle.size))
    (scalar_heads a.final.heads a95h a1h)
    (scalar_data a.final.tapes clauseFields (PCPPNative.descriptor oracle) oracle.size a95 a1) b br
  have joined:=Composition.run_join first second _ _ _ lifted c firstRun cr
  have init : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 85=>0) (extra clauseFields)
      (initialConfiguration PCPPNativeQueryConjunction.machine (PCPPNativeQueryConjunction.input
        (PCPPNative.descriptor oracle) (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix)
        R Q oracle.size M Lq Lc)))=initialConfiguration beforeClauses
      (input (PCPPNativeQueryConjunction.input (PCPPNative.descriptor oracle)
        (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) R Q oracle.size M Lq Lc) clauseFields) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=278) (n:=85) (fun _=>?_) (fun _=>?_) i <;>
        simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases_left,Fin.addCases_right]
    · rfl
  rw [init] at joined
  refine ⟨Composition.joinedReceipt lifted c,joined,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps≤prefixBudget oracle Q M Lq Lc
    rw [cs]
    exact Nat.add_le_add (Nat.add_le_add_right as 1) bs
  · intro i
    change c.final.heads (clauseSlots i)=_ ∧ c.final.tapes (clauseSlots i)=_
    by_cases hi5 : i=5
    · subst i
      constructor
      · exact (ch 25).trans (bh 25)
      · rw [PCPPNativeClauseRawRun.input_data]
        exact (ct 25).trans ((congrFun bt 25).trans bp)
    by_cases hi6 : i=6
    · subst i
      constructor
      · exact (ch 22).trans (bh 22)
      · rw [PCPPNativeClauseRawRun.input_data]
        exact (ct 22).trans ((congrFun bt 22).trans bn)
    have keep:=other (clauseSlots i) (clause_away i hi5 hi6)
    have oldH:=PCPPNativeClauseQuery.clause_heads a.final.heads clauseFields (2*oracle.size+1)
      (2*oracle.output.val+1) (2*oracle.size) (PCPPNativeCapacityReady.C W)
      (Q*(2*oracle.size+1)+1) (Q*(2*oracle.size+1)) M out ash abh aah aoh aCh aMh i
    have oldT:=PCPPNativeClauseQuery.clause_data a.final.tapes clauseFields (2*oracle.size+1)
      (2*oracle.output.val+1) (2*oracle.size) (PCPPNativeCapacityReady.C W)
      (Q*(2*oracle.size+1)+1) (Q*(2*oracle.size+1)) M out ast ab aa ao aC aM i
    exact ⟨keep.1.trans ((clause_head a.final.heads i).trans oldH),
      keep.2.trans ((clause_other a.final.tapes clauseFields (2*oracle.output.val+1) (2*oracle.size) i hi5 hi6).trans oldT)⟩
  · change c.final.heads 14=0
    exact (other 14 scalar_away14).1.trans a14h
  · change c.final.tapes 14=_
    exact (other 14 scalar_away14).2.trans a14
  · change c.final.heads 16=0
    exact (other 16 scalar_away16).1.trans a16h
  · change c.final.tapes 16=_
    exact (other 16 scalar_away16).2.trans a16

end NearCubicWires.RepairOrdinary.PCPPNativeClauseOracle
