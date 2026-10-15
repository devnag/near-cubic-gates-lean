import Proof.CaseAnalysis.WitnessMassStep

/-! Reuse only the normalizer scratch under the already-paid enclosing
parser capacity. Coefficients and the exact native store stay unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassPaddedStep
open LocalBitMultitape RecoveryRootRound SignedSortKey
open CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pads (C : ℕ) (i : Fin 103):=if 96 ≤ i.val then C else 0
def input (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) (i : Fin 103):=
  ZeroPadding.pad (pads C i) (MassPrepare.input ambient nb db i)

theorem step_run (C B b n d : ℕ) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool) (h : Store B a source ambient)
    (ha : a.Valid B) (hb : b≤B) (hn : n<2^b) (hd : d<2^b) (hpos : 0<d)
    (hc : MassStep.budget B+1≤C)
    (hi : ∀ i,(MassPrepare.input ambient (binary b n) (binary b d) i).length≤C) : ∃ output,
    ClockJoin.ReadyRun MassStep.machine (MassStep.budget B)
      (input C ambient (binary b n) (binary b d)) output ∧
      Store B (CompetitorRationalNumerators.add a ⟨n,0,d⟩) source (MassPrepare.project output) ∧
      output 94=frame (binary b n) ∧ output 95=frame (binary b d) ∧
      (∀ i,(output i).length≤C):=by
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,hstore,hnum,hden⟩:=MassStep.step_run B b n d a source ambient h ha hb hn hd hpos
  have hbnd:=RecoveryTapeSupport.run_support MassStep.machine _ _ base hr C 0
    (by intro i;exact Nat.zero_le _) (fun i=>(hi i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 103) : (base.final.tapes i).length≤C:=by
    have hmax:base.steps+1≤C:=by omega
    simpa only [Nat.zero_add,max_eq_left hmax] using hbnd i
  obtain ⟨r,hrun,rf,rt,_⟩:=ZeroPadding.run_config MassStep.machine (pads C) _ _ base hr
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,rt.trans_le hs⟩,?_,?_,?_,?_⟩
  · intro i;rw [rf];exact hh i
  · have hp:MassPrepare.project r.final.tapes=MassPrepare.project out:=by
      funext i
      rw [rf]
      change ZeroPadding.pad (pads C (MassPrepare.old i))
        (base.final.tapes (MassPrepare.old i))=out (MassPrepare.old i)
      rw [pads,if_neg (show ¬96 ≤ (MassPrepare.old i).val by change ¬96 ≤ i.val;omega),
        ZeroPadding.pad_zero,ht]
    rw [hp]
    exact hstore
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 94)=_
    rw [ZeroPadding.pad_zero,ht]
    exact hnum
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 95)=_
    rw [ZeroPadding.pad_zero,ht]
    exact hden
  · intro i;rw [rf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold pads;split <;> omega) (hbound i)

theorem input_native (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool) (i : Fin 94) :
    input C ambient nb db (MassPrepare.old i)=ambient i:=by
  rw [input,pads,if_neg (show ¬96 ≤ (MassPrepare.old i).val by change ¬96 ≤ i.val;omega),
    ZeroPadding.pad_zero,MassPrepare.input_old]
theorem input_scratch (C : ℕ) (ambient : Fin 94→List Bool) (nb db : List Bool)
    (i : Fin 103) (hi : 96 ≤ i.val) : input C ambient nb db i=List.replicate C false:=by
  rw [input,pads,if_pos hi]
  have he:MassPrepare.input ambient nb db i=[]:=by
    have hv:i=96 ∨ i=97 ∨ i=98 ∨ i=99 ∨ i=100 ∨ i=101 ∨ i=102:=by
      simp only [Fin.ext_iff]
      omega
    rcases hv with hv|hv|hv|hv|hv|hv|hv <;> subst i <;> rfl
  rw [he]
  simp [ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassPaddedStep
