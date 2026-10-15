import Proof.CaseAnalysis.WitnessMassStoredDecision

/-! Complete mass cap comparison with the exact native store retained for
the next paid sum reset. This is the original threshold-tail machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassReusableCheck
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open CompetitorSumFold CompetitorThresholdAmbient
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem check_run (B k : ℕ) (q : ℚ) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool) (h : Store B a source ambient)
    (ha : a.Valid B) (hq : 0≤q) (hk : k≤B)
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k) : ∃ output,
    ClockJoin.ReadyRun (MassCheck.machine k q) (MassCheck.budget B k) (MassCheck.input ambient) output ∧
      Store B a source (project output) ∧
      (readTapeBit (output 65) 0=true ↔ a.value≤q):=by
  have he:project (MassCheck.input ambient)=ambient:=by
    funext i;simp [project,native,MassCheck.input]
  have hs:Store B a source (project (MassCheck.input ambient)):=by rw [he];exact h
  have hheads:∀ i,(fun _ : Fin 110=>0) (native i)=heads 0 i:=by
    intro i;simp only [heads,ite_self]
  obtain ⟨f,constants,hf,fs,fh,ft,fp,fn,fz,fd⟩:=constants_run B k 0 q a source
    (fun _=>0) (MassCheck.input ambient) hs hheads (by intros;rfl)
    (by intro i hi;simp [MassCheck.input,Fin.addCases,show ¬i.val<94 by omega]) hk hp hd
  have hfs:ClockJoin.ReadyRun (constantsProgram k q) (CompetitorThresholdConstants.budget B k)
      (MassCheck.input ambient) constants:=by
    refine ⟨f,hf,ft,?_,fs⟩
    intro i;rw [fh]
  have hconstant:Store B a source (project constants):=by rw [fp];exact hs
  obtain ⟨c,hc,cs,ch,ct⟩:=CompetitorThresholdAmbient.clear_run B 0 a source
    (fun _=>0) constants hconstant hheads
  have hcr:ClockJoin.ReadyRun CompetitorThresholdAmbient.clearProgram
      (2*CompetitorReusableDecision.capacity B+4) constants (cleaned B constants):=by
    refine ⟨c,hc,ct,?_,cs.le⟩
    intro i;rw [ch]
  have hpow:(2:ℕ)^k ≤ 2^B:=Nat.pow_le_pow_right (by decide) hk
  obtain ⟨out,hr,hstore,hflag⟩:=MassStoredDecision.decision_run B q a source constants hconstant
    fn fz fd ha hq (hp.trans_le hpow) (hd.trans_le hpow)
  have htail:=ClockJoin.join CompetitorThresholdAmbient.clearProgram
    (CompetitorThresholdAmbient.decisionProgram false) _ _ _ _ _ hcr hr
  have hall:=ClockJoin.join (constantsProgram k q) (decisionTail false) _ _ _ _ _ hfs htail
  have hb:CompetitorThresholdConstants.budget B k+1+
      ((2*CompetitorReusableDecision.capacity B+4)+1+2000*(B+1)^2)=MassCheck.budget B k:=by
    unfold MassCheck.budget CompetitorThresholdAmbient.budget
    omega
  rw [hb] at hall
  exact ⟨out,hall,hstore,hflag⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassReusableCheck
