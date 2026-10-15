import Proof.CaseAnalysis.RowsCircuitTraversalCaps

/-! The actual returned bottom bank and resource projections bound every
private tape by C+1. The extra cell is the paid erase log; neither policy
word nor the native append prefix is part of this scratch bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTailSupport
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit CloseoutRowsCircuitBottomDock
open CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem local_support (C core n : ℕ) (out source members : List Bool) (D W : ℕ) (flag : Bool)
    (hd : D ≤ C) (hw : W ≤ C) (hs : source.length ≤ C) (hm : members.length ≤ C+1)
    (hn : n+2 ≤ C+1) (i : Fin 1060) (hcore : i.val≠1035) (hnative : i.val≠1049) :
    (localTapes C core n out source members D W flag i).length ≤ C+1:=by
  refine Fin.addCases (m:=1059) (n:=1) ?_ ?_ i hcore hnative
  · intro j jc jn
    simp only [localTapes,Fin.addCases_left,data]
    refine Fin.addCases (m:=1049) (n:=10) ?_ ?_ j jc jn
    · intro k kc _kn
      simp only [Fin.addCases_left,CloseoutRowsGateBank.input,CloseoutRowsGateBank.padded,
        CloseoutRowsGateBank.input_eq,CloseoutRowsGateBank.pads,Fin.val_castAdd] at kc ⊢
      rw [if_neg kc,if_neg kc,ZeroPadding.pad_length]
      apply max_le (by omega)
      split_ifs
      · rw [frame_length];simp
      · exact Nat.zero_le _
    · intro k _kc kn
      have nk:k.val≠0:=by intro h;apply kn;change 1049+k.val=1049;omega
      simp only [Fin.addCases_right]
      fin_cases k
      · exact False.elim (nk rfl)
      · change (List.replicate D true).length ≤ C+1
        simpa only [List.length_replicate] using hd.trans (Nat.le_succ C)
      · change (List.replicate W true).length ≤ C+1
        simpa only [List.length_replicate] using hw.trans (Nat.le_succ C)
      · exact hs.trans (Nat.le_succ C)
      · exact hm
      · change 1 ≤ C+1;omega
      · simp [extra]
      · simp [extra]
      · simp [extra]
      · simp [extra,ZeroPadding.pad_length]
  · intro j _jc _jn
    have hj:j=0:=Fin.eq_zero j;subst j
    simpa only [localTapes,Fin.addCases_right,UnaryTemplate.tape_length] using hn

theorem final_support (C core n : ℕ) (out source members : List Bool) (D W : ℕ) (flag : Bool)
    (A mid final : Fin 1703 → List Bool) (hc : 1 ≤ C)
    (hd : D ≤ C) (hw : W ≤ C) (hs : source.length ≤ C) (hm : members.length ≤ C+1)
    (hn : n+2 ≤ C+1)
    (mt : ∀ i,mid (bottomSlots i)=localTapes C core n out source members D W flag i)
    (mkeep : ∀ i,(∀ j,bottomSlots j≠i) → mid i=A i)
    (kept : ∀ i,(i.val<639 ∨ 665 ≤ i.val) → i≠1700 → final i=mid i)
    (small : ∀ i,CloseoutRowsCircuitColdEntry.heads out i=0 → (mid i).length ≤ C → (final i).length ≤ C)
    (hflag : A 1700=[])
    (initial : ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (A i).length ≤ C+1) :
    ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (final i).length ≤ C+1:=by
  intro i nr nc nd nw nl no
  have ih:CloseoutRowsCircuitColdEntry.heads out i=0:=by
    simp only [CloseoutRowsCircuitColdEntry.heads,if_neg no,CloseoutRowsCircuit.heads,
      if_neg (show i.val≠1674 from fun h=>nc (Fin.ext h))]
  by_cases hflagPort:i=1700
  · subst i
    apply (small 1700 ih _).trans (Nat.le_succ C)
    rw [mkeep 1700 (by
      intro j h
      have hv:=congrArg Fin.val h
      rw [bottom_val] at hv;split_ifs at hv <;> omega),hflag]
    exact Nat.zero_le _
  by_cases modified:639 ≤ i.val ∧ i.val ≤ 664
  · apply (small i ih _).trans (Nat.le_succ C)
    rw [CloseoutRowsCircuitTraversalCaps.blank C core n out source members D W flag mid hc mt i modified,List.length_replicate]
  · rw [kept i (by omega) hflagPort]
    by_cases hit:∃ j,bottomSlots j=i
    · obtain ⟨j,hj⟩:=hit
      rw [←hj,mt]
      apply local_support C core n out source members D W flag hd hw hs hm hn j
      · intro h
        have he:j=1035:=Fin.ext h
        subst j;exact nc hj.symm
      · intro h
        have he:j=1049:=Fin.ext h
        subst j;exact no hj.symm
    · rw [mkeep i (by simpa only [not_exists] using hit)]
      exact initial i nr nc nd nw nl no

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTailSupport
