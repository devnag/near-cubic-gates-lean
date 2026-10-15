import Proof.CaseAnalysis.WitnessNodeErase

/-! Advance the shared strict-earlier-node bound in framed binary. Its
already-allocated reset log is reused, independently of the numeric value. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
open LocalBitMultitape RadixSemantics SignedSortKey RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem data_right_other (cap w : ℕ) (left right nextRight out source : List Bool) (flag : Bool)
    (hcap : 1 ≤ cap) (i : Fin 755) (hi : i≠671) :
    data cap w left right [] out source flag i=data cap w left nextRight [] out source flag i:=by
  classical
  revert hi
  refine Fin.addCases (m:=749) (n:=6) ?_ ?_ i
  · intro j hi
    simp only [data,Fin.addCases_left]
    by_cases hj:j=747
    · subst j
      rw [NodeReady.entry_output,NodeReady.entry_output]
    by_cases hc:∃ k : Fin 4,(NodeGuard.common k).castAdd 3=j
    · obtain ⟨k,rfl⟩:=hc
      rw [NodeReady.entry_common,NodeReady.entry_common]
      fin_cases k
      · rfl
      · rfl
      · rfl
      · exact False.elim (hi (Fin.ext rfl))
    · have hn:∀ k : Fin 4,(NodeGuard.common k).castAdd 3≠j:=by intro k h;exact hc ⟨k,h⟩
      rw [NodeReady.entry_blank _ _ _ _ _ hcap j hj hn,NodeReady.entry_blank _ _ _ _ _ hcap j hj hn]
  · intro j _
    simp only [data,Fin.addCases_right]

noncomputable def increment:=RecoveryFocus.machine incrementSlots FramedIncrement.machine
def incrementPads (cap : ℕ) : Fin 2 → ℕ:=![cap,0]
theorem increment_ready (cap w index : ℕ) (hi : index+1<2^w) (hcap : 2*w ≤ cap) :
    ClockJoin.ReadyRun FramedIncrement.machine (4*w+2)
      ![ZeroPadding.pad cap (frame (binary w index)),List.replicate cap false]
      ![ZeroPadding.pad cap (frame (binary w (index+1))),List.replicate cap false]:=by
  obtain ⟨r,hr,rt,rl,rh,rs,_⟩:=FramedIncrement.increment_run w index cap hi hcap
  obtain ⟨p,hp,pf,ps,_⟩:=ZeroPadding.run_config FramedIncrement.machine (incrementPads cap) _ _ r hr
  have he:ZeroPadding.config (incrementPads cap)
      (initialConfiguration FramedIncrement.machine
        (Fin.addCases (motive:=fun _ : Fin (1+1)=>List Bool)
          (fun _ : Fin 1=>frame (binary w index)) (fun _ : Fin 1=>List.replicate cap false)))=
      initialConfiguration FramedIncrement.machine
        ![ZeroPadding.pad cap (frame (binary w index)),List.replicate cap false]:=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i
      · rfl
      · exact ZeroPadding.pad_zero _
  rw [he] at hp
  refine ⟨p,hp,?_,?_,ps.trans_le rs⟩
  · funext i
    rw [pf]
    fin_cases i
    · change ZeroPadding.pad cap (r.final.tapes 0)=_
      rw [rt]
      simp
    · change ZeroPadding.pad 0 (r.final.tapes 1)=_
      rw [ZeroPadding.pad_zero,rl]
      simp
  · intro i
    rw [pf]
    exact rh i

theorem increment_run (cap w index position : ℕ) (left out source : List Bool) (flag : Bool)
    (hi : index+1<2^w) (hcap : 2*w ≤ cap) (hC : 1 ≤ cap) : ∃ result,
    runFrom increment (4*w+2)
      (cfg increment.start cap w position left (binary w index) [] out source flag)=some result ∧
      result.steps ≤ 4*w+2 ∧ result.final.heads=heads out position ∧
      result.final.tapes=data cap w left (binary w (index+1)) [] out source flag:=by
  obtain ⟨r,hr,rh,rt,rs⟩:=(increment_ready cap w index hi hcap).focus_at incrementSlots (by decide)
    (heads out position) (data cap w left (binary w index) [] out source flag)
    (by
      intro i;fin_cases i
      · exact NodeReady.entry_common cap w left (binary w index) [] out 3
      · rfl) (by intro i;fin_cases i <;> rfl)
  refine ⟨r,hr,rs,rh,?_⟩
  rw [rt]
  funext i
  by_cases h0:i=671
  · subst i
    rw [show (671 : Fin 755)=incrementSlots 0 by decide,install_slot _ (by decide)]
    exact (NodeReady.entry_common cap w left (binary w (index+1)) [] out 3).symm
  by_cases h1:i=753
  · subst i
    rw [show (753 : Fin 755)=incrementSlots 1 by decide,install_slot _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by
      intro j;fin_cases j
      · exact Ne.symm h0
      · exact Ne.symm h1)]
    exact data_right_other cap w left (binary w index) (binary w (index+1)) out source flag hC i h0

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
