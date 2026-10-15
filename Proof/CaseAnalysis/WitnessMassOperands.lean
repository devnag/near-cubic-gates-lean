import Proof.CaseAnalysis.WitnessTermPadded
import Proof.CaseAnalysis.WitnessMassReusableStep

/-! The reusable mass round consumes the coefficient reader's existing
allocated fields. Only its two coefficient operands receive zero padding;
the native store and the paid scratch reset are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassOperands
open LocalBitMultitape RecoveryRootRound SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pads (C : ℕ) (i : Fin 105):=if i.val=94 ∨ i.val=95 then C else 0
def input (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) (i : Fin 105):=
  ZeroPadding.pad (pads C i) (MassReusableStep.input C ambient nb db i)

theorem input_native (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) (i : Fin 94) :
    input C ambient nb db (MassReusableStep.native i)=ambient i:=by
  rw [input,pads,if_neg (show ¬((MassReusableStep.native i).val=94 ∨
    (MassReusableStep.native i).val=95) by change ¬(i.val=94 ∨ i.val=95);omega),
    ZeroPadding.pad_zero,MassReusableStep.input_native]
theorem input_num (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) :
    input C ambient nb db 94=ZeroPadding.pad C (frame nb):=by
  change ZeroPadding.pad C (MassReusableStep.input C ambient nb db 94)=_
  rw [MassReusableStep.input_num]
theorem input_den (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) :
    input C ambient nb db 95=ZeroPadding.pad C (frame db):=by
  change ZeroPadding.pad C (MassReusableStep.input C ambient nb db 95)=_
  rw [MassReusableStep.input_den]

theorem step_run (C B b n d : ℕ) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool) (h : Store B a source ambient)
    (ha : a.Valid B) (hb : b≤B) (hn : n<2^b) (hd : d<2^b) (hpos : 0<d)
    (hc : MassStep.budget B+1≤C)
    (hi : ∀ i,(MassPrepare.input ambient (binary b n) (binary b d) i).length≤C) : ∃ next,
    ClockJoin.ReadyRun MassReusableStep.machine (MassReusableStep.budget C B)
      (input C ambient (binary b n) (binary b d)) (input C next (binary b n) (binary b d)) ∧
      Store B (CompetitorRationalNumerators.add a ⟨n,0,d⟩) source next:=by
  obtain ⟨next,⟨base,hr,ht,hh,hs⟩,hstore⟩:=
    MassReusableStep.step_run C B b n d a source ambient h ha hb hn hd hpos hc hi
  obtain ⟨r,hrun,rf,rt,_⟩:=ZeroPadding.run_config MassReusableStep.machine (pads C) _ _ base hr
  refine ⟨next,⟨r,hrun,?_,?_,rt.trans_le hs⟩,hstore⟩
  · funext i
    rw [rf]
    change ZeroPadding.pad (pads C i) (base.final.tapes i)=_
    rw [ht]
    rfl
  · intro i;rw [rf];exact hh i

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassOperands
