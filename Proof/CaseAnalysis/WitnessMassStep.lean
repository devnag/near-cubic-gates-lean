import Proof.CaseAnalysis.WitnessMassPrepare

/-! One complete direct absolute-mass update: clear, widen the retained
coefficient fields, add, and copy the exact accumulator back. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassStep
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def lastProgram:=RecoveryFocus.machine MassPrepare.old bodyTail
def machine:=Composition.machine MassPrepare.machine lastProgram
def budget (B : ℕ):=MassPrepare.budget B+1+Mass.tailBudget B

theorem step_run (B b n d : ℕ) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool) (h : Store B a source ambient)
    (ha : a.Valid B) (hb : b ≤ B) (hn : n<2^b) (hd : d<2^b) (hpos : 0<d) : ∃ output,
    ClockJoin.ReadyRun machine (budget B)
      (MassPrepare.input ambient (binary b n) (binary b d)) output ∧
      Store B (CompetitorRationalNumerators.add a ⟨n,0,d⟩) source (MassPrepare.project output) ∧
      output 94=frame (binary b n) ∧ output 95=frame (binary b d):=by
  obtain ⟨p,hp,pp,pn,pd⟩:=MassPrepare.prepare_run B b n d a source ambient h hb hn hd
  have hpow:(2:ℕ)^b ≤ 2^B:=Nat.pow_le_pow_right (by decide) hb
  have hc:(⟨n,0,d⟩ : Estimate).Valid B:=
    ⟨hn.trans_le hpow,Nat.two_pow_pos _,hd.trans_le hpow,hpos⟩
  obtain ⟨r,hr,rt,rh,rs⟩:=Mass.tail_run B 0 a ⟨n,0,d⟩ source ambient h ha hc
  have hi:cfg bodyTail.start 0 (prepared B ⟨n,0,d⟩ ambient)=
      initialConfiguration bodyTail (prepared B ⟨n,0,d⟩ ambient):=by
    apply configuration_ext
    · rfl
    · funext i;simp only [cfg,heads,initialConfiguration,ite_self]
    · rfl
  rw [hi] at hr
  have ready:ClockJoin.ReadyRun bodyTail (Mass.tailBudget B)
      (prepared B ⟨n,0,d⟩ ambient) r.final.tapes:=by
    refine ⟨r,hr,rfl,?_,rt⟩
    intro i;rw [rh];simp only [heads,ite_self]
  have hf:=ready.focus MassPrepare.old MassPrepare.old_injective p (congrFun pp)
  refine ⟨_,ClockJoin.join MassPrepare.machine lastProgram _ _ _ _ _ hp hf,?_,?_,?_⟩
  · have he:MassPrepare.project (install MassPrepare.old p r.final.tapes)=r.final.tapes:=by
      funext i;exact install_slot MassPrepare.old MassPrepare.old_injective p r.final.tapes i
    rw [he]
    exact rs
  · exact (install_other MassPrepare.old p r.final.tapes 94
      (MassPrepare.old_outside 94 (by decide))).trans pn
  · exact (install_other MassPrepare.old p r.final.tapes 95
      (MassPrepare.old_outside 95 (by decide))).trans pd

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassStep
