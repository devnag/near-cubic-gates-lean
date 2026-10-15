import Proof.CaseAnalysis.RowsCircuitBottomParse

/-! Load the next literal bottom field into the SAME paid gate bank. The
canonical source cursor advances once; every global output remains live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loader:=RecoveryFocus.machine loadSlots FrameLoad.machine

theorem data_bits_other (cap core : ℕ) (bits next out source membership : List Bool)
    (description wires : ℕ) (flag : Bool) (i : Fin 1059) (hi : i.val≠1) :
    data cap core bits out source membership description wires flag i=
      data cap core next out source membership description wires flag i := by
  revert hi
  refine Fin.addCases (m:=1049) (n:=10) ?_ ?_ i
  · intro j hj
    simp only [data,Fin.addCases_left,CloseoutRowsGateBank.input,CloseoutRowsGateBank.padded,
      CloseoutRowsGateBank.input_eq,Fin.val_castAdd] at *
    rw [if_neg hj,if_neg hj]
  · intro j _
    simp only [data,Fin.addCases_right]

theorem load_run (cap core memberPos : ℕ) (bits out pre tail membership : List Bool)
    (description wires : ℕ) (flag : Bool) (hc : 2*bits.length+1 ≤ cap) : ∃ r,
    runFrom loader (4*bits.length+3)
      (cfg loader.start cap core pre.length memberPos [] out (pre++frame bits++tail) membership description wires flag)=some r ∧
      r.steps=4*bits.length+3 ∧
      r.final.heads=heads (pre.length+2*bits.length+1) memberPos out description wires ∧
      r.final.tapes=data cap core bits out (pre++frame bits++tail) membership description wires flag := by
  let source:=pre++frame bits++tail
  obtain ⟨base,hb,bs,bh,bt⟩:=CloseoutRowsIntegerRound.padded_load_run cap bits pre tail hc
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock loadSlots (by decide) FrameLoad.machine _
    (heads pre.length memberPos out description wires) (data cap core [] out source membership description wires flag) _
    (by intro i;fin_cases i <;> rfl)
    (by
      intro i;fin_cases i
      · exact (ZeroPadding.pad_zero source).symm
      · change ZeroPadding.pad cap (CloseoutRowsGateMeasured.input core [] 1)=ZeroPadding.pad cap []
        rw [CloseoutRowsGateBank.input_eq]
        change ZeroPadding.pad cap (frame [])=ZeroPadding.pad cap []
        rw [CloseoutRowsIntegerReady.pad_empty_frame cap (by omega)]
        simp [ZeroPadding.pad]
      · change List.replicate cap false=ZeroPadding.pad cap []
        simp [ZeroPadding.pad]) base hb
  refine ⟨r,hr,rs.trans bs,?_,?_⟩
  · funext i
    by_cases h0:i=1052
    · subst i;exact (rh 0).trans (bh 0)
    by_cases h1:i=1
    · subst i;exact (rh 1).trans (bh 1)
    by_cases h2:i=1057
    · subst i;exact (rh 2).trans (bh 2)
    rw [(keep i (by intro j;fin_cases j <;> first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2)).1]
    have hv:i.val≠1052:=by intro h;exact h0 (Fin.ext h)
    simp only [heads,if_neg hv]
  · funext i
    by_cases h0:i=1052
    · subst i;exact (rt 0).trans (bt 0)
    by_cases h1:i=1
    · subst i
      change r.final.tapes (loadSlots 1)=_
      rw [rt 1,bt 1]
      change ZeroPadding.pad cap (frame bits)=ZeroPadding.pad cap (CloseoutRowsGateMeasured.input core bits 1)
      rw [CloseoutRowsGateBank.input_eq];rfl
    by_cases h2:i=1057
    · subst i;exact (rt 2).trans (bt 2)
    exact ((keep i (by intro j;fin_cases j <;> first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2)).2).trans
      (data_bits_other cap core [] bits out source membership description wires flag i (by
        intro h;exact h1 (Fin.ext h)))

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
