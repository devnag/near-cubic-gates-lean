import Proof.CaseAnalysis.WitnessTermCommit
import Proof.CaseAnalysis.WitnessMassActual

/-! The actual mass comparator reuses sixteen cleared parser tapes for its
constant scratch. Native mass storage remains exactly the existing Store. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassPaddedCheck
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorThresholdAmbient
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pads (P : ℕ) (i : Fin 110):=if 94 ≤ i.val then P else 0
def input (P : ℕ) (ambient : Fin 94→List Bool) (i : Fin 110):=
  ZeroPadding.pad (pads P i) (MassCheck.input ambient i)
theorem input_native (P : ℕ) (ambient : Fin 94→List Bool) (i : Fin 94) :
    input P ambient (native i)=ambient i:=by
  rw [input,pads,if_neg (show ¬94 ≤ (native i).val by change ¬94 ≤ i.val;omega),ZeroPadding.pad_zero]
  change MassCheck.input ambient (i.castAdd 16)=ambient i
  rw [MassCheck.input,Fin.addCases_left]
theorem input_scratch (P : ℕ) (ambient : Fin 94→List Bool) (i : Fin 16) :
    input P ambient (i.natAdd 94)=List.replicate P false:=by
  rw [input,pads,if_pos (show 94 ≤ (i.natAdd 94).val by change 94 ≤ 94+i.val;omega),
    MassCheck.input,Fin.addCases_right]
  simp [ZeroPadding.pad]

theorem check_run (P B k : ℕ) (q : ℚ) (a : Estimate) (source : List Bool)
    (ambient : Fin 94→List Bool) (h : Store B a source ambient)
    (ha : a.Valid B) (hq : 0≤q) (hk : k≤B)
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k)
    (hc : MassCheck.budget B k+1≤P) (hi : ∀ i,(ambient i).length≤P) : ∃ output,
    ClockJoin.ReadyRun (MassCheck.machine k q) (MassCheck.budget B k) (input P ambient) output ∧
      Store B a source (project output) ∧
      (readTapeBit (output 65) 0=true ↔ a.value≤q) ∧
      (∀ i,(output i).length≤P):=by
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,hstore,hflag⟩:=MassReusableCheck.check_run B k q a source ambient
    h ha hq hk hp hd
  have hin (i : Fin 110) : (MassCheck.input ambient i).length≤P:=by
    refine Fin.addCases (m:=94) (n:=16) ?_ ?_ i
    · intro j;simpa only [MassCheck.input,Fin.addCases_left] using hi j
    · intro j;simp only [MassCheck.input,Fin.addCases_right,List.length_nil];omega
  have hbnd:=RecoveryTapeSupport.run_support (MassCheck.machine k q) _ _ base hr P 0
    (by intro i;exact Nat.zero_le _) (fun i=>(hin i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 110) : (base.final.tapes i).length≤P:=by
    have hmax:base.steps+1≤P:=by omega
    simpa only [Nat.zero_add,max_eq_left hmax] using hbnd i
  obtain ⟨r,hrun,rf,rs,_⟩:=ZeroPadding.run_config (MassCheck.machine k q) (pads P) _ _ base hr
  have hn (i : Fin 94) : r.final.tapes (native i)=out (native i):=by
    rw [rf]
    change ZeroPadding.pad (pads P (native i)) (base.final.tapes (native i))=out (native i)
    rw [pads,if_neg (show ¬94 ≤ (native i).val by change ¬94 ≤ i.val;omega),
      ZeroPadding.pad_zero,ht]
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,rs.trans_le hs⟩,?_,?_,?_⟩
  · intro i;rw [rf];exact hh i
  · have he:project r.final.tapes=project out:=funext hn
    rw [he];exact hstore
  · have he:r.final.tapes 65=out 65:=hn 65
    rw [he];exact hflag
  · intro i;rw [rf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold pads;split <;> omega) (hbound i)

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassPaddedCheck
