import Proof.CaseAnalysis.WitnessSumFinish

/-! The reusable Store itself bounds every native tape. No per-iteration
workspace promise is needed after choosing the shared actual capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCapacity
open LocalBitMultitape CompetitorSumFold CompetitorReusableDecision SignedSortKey
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem store_length (B : ℕ) (a : Estimate) (ambient : Fin 94→List Bool)
    (h : Store B a [] ambient) (i : Fin 94) : (ambient i).length≤capacity B+1:=by
  refine Fin.addCases (m:=88) (n:=6) ?_ ?_ i
  · intro j;exact (h.support j).trans (Nat.le_succ _)
  · intro j;fin_cases j
    · change (ambient 88).length≤capacity B+1;rw [h.source];simp
    · change (ambient 89).length≤capacity B+1;rw [h.loaderReset,List.length_replicate];omega
    · change (ambient 90).length≤capacity B+1;rw [h.eraseDriver,List.length_replicate];omega
    · change (ambient 91).length≤capacity B+1;rw [h.eraseReset,List.length_replicate]
    · change (ambient 92).length≤capacity B+1;rw [h.copyCounter,List.length_replicate];omega
    · change (ambient 93).length≤capacity B+1;rw [h.copyReset,List.length_replicate];omega

theorem prepare_length (P B b n d : ℕ) (a : Estimate) (ambient : Fin 94→List Bool)
    (h : Store B a [] ambient) (hcap : capacity B+1≤P) (hb : 2*b+1≤P)
    (i : Fin 103) : (MassPrepare.input ambient (binary b n) (binary b d) i).length≤P:=by
  refine Fin.addCases (m:=94) (n:=9) ?_ ?_ i
  · intro j
    rw [MassPrepare.input,Fin.addCases_left]
    exact (store_length B a ambient h j).trans hcap
  · intro j;fin_cases j
    all_goals first
      | (change (frame (binary b n)).length≤P;simpa only [frame_length,binary_length] using hb)
      | (change (frame (binary b d)).length≤P;simpa only [frame_length,binary_length] using hb)
      | (change 0≤P;omega)

theorem actual_sum_run (P position : ℕ) (delta : ℚ) (hd : 0<delta) (hh : delta<1/2)
    (copies q0 clauseBits T : ℕ) (hc : 1≤copies) (a : Estimate)
    (source out : List Bool) (flag : Bool) (ambient : Fin 94→List Bool)
    (h : Store (MassActual.width delta copies q0 clauseBits T) a [] ambient)
    (ha : a.Valid (MassActual.width delta copies q0 clauseBits T))
    (hcheck : MassActual.budget delta copies q0 clauseBits T+1≤P)
    (hcapacity : capacity (MassActual.width delta copies q0 clauseBits T)+1≤P) :
    let B:=MassActual.width delta copies q0 clauseBits T
    let b:=natBitLength (RepairSource.CloseoutXor.cap delta q0 copies*max 1 (2*2^clauseBits))
    ∃ next,SumFinish.Ready
      (SumFinish.machine (RepairSource.CloseoutMassThreshold.literalWidth delta copies)
        (RepairSource.CloseoutSampledWitness.massCap delta copies))
      (SumFinish.budget P B (RepairSource.CloseoutMassThreshold.literalWidth delta copies)) position out
      (TermCommit.data P (TermRead.data P b [] source flag) ambient out)
      (TermCommit.data P (TermRead.data P b [] source
        (flag && decide (a.value≤RepairSource.CloseoutSampledWitness.massCap delta copies))) next out) ∧
      Store B CompetitorSumWidth.zero [] next:=by
  dsimp only
  obtain ⟨_,hp,hden⟩:=RepairSource.CloseoutMassThreshold.threshold_fits delta hd hh copies q0 clauseBits hc
  exact SumFinish.finish_run P (MassActual.width delta copies q0 clauseBits T) _
    (RepairSource.CloseoutMassThreshold.literalWidth delta copies) position
    (RepairSource.CloseoutSampledWitness.massCap delta copies) a source out flag ambient h ha
    (by unfold MassActual.width CompetitorSumWidth.width;nlinarith)
    (RepairSource.CloseoutSampledWitness.mass_nonneg delta hd hh copies)
    (RepairSource.CloseoutMassThreshold.shared_fits delta hd hh copies q0 clauseBits T hc)
    hp hden hcheck (fun i=>(store_length _ a ambient h i).trans hcapacity)

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCapacity
