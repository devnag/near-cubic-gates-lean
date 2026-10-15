import Proof.CaseAnalysis.WitnessNativePolicyCall
import Proof.Amplification.RecoveryCursorCalls

/-! One original stream traversal reaches the exact size test. The native
node/source/cache/policy continuation runs only on its successful branch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev base (G : ℕ):=125+OracleCap.Call.extra G
def counter (G : ℕ):=NativeScreen.slots G
def localSlots (a : PointwisePCPPAlgorithm) (D G : ℕ):=NativePolicy.Call.slots a D (counter G)
def cacheSlots (a : PointwisePCPPAlgorithm) (D G : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  localSlots a D G (NativePolicy.cacheSlots a D j)
def flagSlot (a : PointwisePCPPAlgorithm) (D G : ℕ):=NativePolicy.Call.old a D (NativeScreen.flagSlot G)
def first (a : PointwisePCPPAlgorithm) (D G : ℕ):=
  TapeEmbedding.machine (NativePolicy.Call.extra a D) (NativeScreen.machine G)
def second (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ):=
  NativePolicy.Call.machine a D copies delta (counter G)
def test (a : PointwisePCPPAlgorithm) (D G : ℕ) (scan : Fin (base G+NativePolicy.Call.extra a D)→Bool):=
  scan (flagSlot a D G)
def machine (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ):=
  CloseoutRowsGateColdPair.machine (first a D G) (second a D G copies delta) (test a D G)
def input (a : PointwisePCPPAlgorithm) (D G : ℕ) {R : ℕ}
    (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ):=
  NativePolicy.Call.input a D (NativeScreen.input G oracle p Q)
def budget (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ)
    (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R):=
  NativeScreen.budget G p R Q oracle.size+1+
    (if oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R then
      NativePolicy.budget a D copies delta p R Q hR hQ x oracle+1 else 0)

private theorem flag_outside (G : ℕ) : ∀ j,counter G j≠NativeScreen.flagSlot G:=by
  intro j he
  have h0:(OracleCap.Core.flagSlot (OracleCap.degree G)).val≠0:=by
    change OracleCap.Core.P (OracleCap.degree G)+4≠0
    omega
  have h1:(OracleCap.Core.flagSlot (OracleCap.degree G)).val≠1:=by
    change OracleCap.Core.P (OracleCap.degree G)+4≠1
    omega
  simp only [counter,NativeScreen.slots,NativeScreen.flagSlot,OracleCap.Call.flagSlot,
    OracleCap.Call.slots,if_neg h0,if_neg h1] at he
  have hv:=congrArg Fin.val he
  have hj:=(NativeMeasured.slots j).isLt
  simp only [OracleCap.Call.old,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem pipeline_run (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ)
    (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) (hD : 1≤D) :
    let r:=NativeCache.request a p R Q hR hQ x oracle
    ∃ actual,run (machine a D G copies delta) (budget a D G copies delta p R Q hR hQ x oracle)
      (input a D G oracle p Q)=some actual ∧
      actual.steps≤budget a D G copies delta p R Q hR hQ x oracle ∧
      actual.final.heads (flagSlot a D G)=0 ∧
      actual.final.tapes (flagSlot a D G)=[decide (oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R)] ∧
      (oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R →
        (∀ j : Fin 19,actual.final.tapes (cacheSlots a D G (PCPPSourceCache.cacheSlots a j))=
          PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
            (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
        (∀ j : Fin 19,actual.final.heads (cacheSlots a D G (PCPPSourceCache.cacheSlots a j))=
          PCPPQueryClauseReuse.heads j) ∧
        SourcePolicy.Call.Fields D copies delta (NativePolicy.fields a) r (a.output r)
          (NativePolicy.Call.project a D (counter G) actual.final)):=by
  intro r
  obtain ⟨s,hs,_,sf,srh,srt,sh,st⟩:=NativeScreen.screen_run G oracle p Q hR hQ
  let lifted:=TapeEmbedding.receipt (fun _ : Fin (NativePolicy.Call.extra a D)=>0) (fun _=>[]) s
  have hfirst:=TapeEmbedding.run_embed (NativeScreen.machine G)
    (fun _ : Fin (NativePolicy.Call.extra a D)=>0) (fun _=>[]) _ _ s hs
  rw [StreamPrepare.embed_initial] at hfirst
  have lh:lifted.final.heads (flagSlot a D G)=0:=
    (TapeEmbedding.receipt_heads_old _ _ s _).trans sh
  have lt:lifted.final.tapes (flagSlot a D G)=
      [decide (oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R)]:=
    (TapeEmbedding.receipt_tapes_old _ _ s _).trans st
  have scanned:test a D G lifted.final.scanned=decide (oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R):=by
    change readTapeBit (lifted.final.tapes (flagSlot a D G)) (lifted.final.heads (flagSlot a D G))=_
    rw [lh,lt]
    rfl
  by_cases live:oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G R
  · obtain ⟨last,hl,_,lct,lch,lf,away⟩:=NativePolicy.Call.call_run a D copies delta (counter G)
      (NativeScreen.slots_injective G) s.final.tapes s.final.heads p R Q hR hQ x oracle hD sf srh srt
    have he:=MatrixPacketBranch.restart_fields (second a D G copies delta) lifted.final
      (NativePolicy.Call.heads a D s.final.heads) (NativePolicy.Call.input a D s.final.tapes) rfl rfl
    dsimp only [second,RecoveryCalls.restarted] at he
    rw [he] at hl
    obtain ⟨u,hu,initial⟩:=call_receipt _
      (CloseoutRowsGateColdPair.programs (first a D G) (second a D G copies delta)) 0
      (CloseoutRowsGateColdPair.next (test a D G)) 0 1 (NativeScreen.budget G p R Q oracle.size) _ lifted hfirst (by
        change (if test a D G lifted.final.scanned then some (1 : Fin 2) else none)=some 1
        rw [scanned,decide_eq_true live];rfl)
    obtain ⟨v,hv,terminal⟩:=stop_receipt _
      (CloseoutRowsGateColdPair.programs (first a D G) (second a D G copies delta)) 0
      (CloseoutRowsGateColdPair.next (test a D G)) 1
      (NativePolicy.budget a D copies delta p R Q hR hQ x oracle) _ last hl (by rfl)
    obtain ⟨actual,ha,hfinal,hsteps⟩:=(initial.trans terminal).run (by
      simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
    have hb:u+v≤budget a D G copies delta p R Q hR hQ x oracle:=by
      unfold budget
      rw [if_pos live]
      omega
    have more:=run_moreFuel (machine a D G copies delta) (u+v)
      (budget a D G copies delta p R Q hR hQ x oracle-(u+v)) (input a D G oracle p Q) actual ha
    rw [Nat.add_sub_of_le hb] at more
    have keep:=away (NativeScreen.flagSlot G) (NativePolicy.Call.outside a D (counter G) _ (flag_outside G))
    refine ⟨actual,more,hsteps.le.trans hb,?_,?_,fun _=>?_⟩
    · rw [hfinal]
      exact keep.1.trans sh
    · rw [hfinal]
      exact keep.2.trans st
    · refine ⟨?_,?_,?_⟩
      · intro j
        rw [hfinal]
        exact lct j
      · intro j
        rw [hfinal]
        exact lch j
      · exact ⟨by simpa only [hfinal,NativePolicy.Call.project,RecoveryCalls.stopped] using lf.count,
          by simpa only [hfinal,NativePolicy.Call.project,RecoveryCalls.stopped] using lf.clause,
          by simpa only [hfinal,NativePolicy.Call.project,RecoveryCalls.stopped] using lf.q0,
          by simpa only [hfinal,NativePolicy.Call.project,RecoveryCalls.stopped] using lf.cap,
          by intro i;simpa only [hfinal,NativePolicy.Call.project,RecoveryCalls.stopped] using lf.cursor i⟩
  · obtain ⟨u,hu,terminal⟩:=stop_receipt _
      (CloseoutRowsGateColdPair.programs (first a D G) (second a D G copies delta)) 0
      (CloseoutRowsGateColdPair.next (test a D G)) 0 (NativeScreen.budget G p R Q oracle.size) _ lifted hfirst (by
        change (if test a D G lifted.final.scanned then some (1 : Fin 2) else none)=none
        rw [scanned,decide_eq_false live];rfl)
    obtain ⟨actual,ha,hfinal,hsteps⟩:=terminal.run (by
      simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
    have hb:u≤budget a D G copies delta p R Q hR hQ x oracle:=by
      unfold budget
      rw [if_neg live]
      omega
    have more:=run_moreFuel (machine a D G copies delta) u
      (budget a D G copies delta p R Q hR hQ x oracle-u) (input a D G oracle p Q) actual ha
    rw [Nat.add_sub_of_le hb] at more
    exact ⟨actual,more,hsteps.le.trans hb,by rw [hfinal];exact lh,
      by rw [hfinal];exact lt,fun h=>False.elim (live h)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline
