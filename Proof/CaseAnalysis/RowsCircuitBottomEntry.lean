import Proof.CaseAnalysis.RowsCircuitBottomPosition
import Proof.CaseAnalysis.RowsCircuitBottomDock

/-! The physically prepared native prefix and original canonical bottom
stream are exactly the input of the counted bottom traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomEntry
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit CloseoutRowsCircuitBottomDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (threshold : Bool) (out : List Bool) (D W : ℕ) (i : Fin 1703):=
  if i=1674 then 1 else if i=1688 then out.length else if i=1689 then D else if i=1690 then W
  else if i=624 then (if threshold then 1 else 0) else 0

theorem heads_ready (threshold : Bool) (out : List Bool) (D W : ℕ) (i : Fin 1060) :
    CloseoutRowsCircuitBottomPosition.output (heads threshold out D W) (bottomSlots i)=localHeads 0 1 out D W i:=by
  refine Fin.addCases (m:=1059) (n:=1) ?_ ?_ i
  · intro j
    by_cases h1035:j=1035
    · subst j;rfl
    by_cases h1049:j=1049
    · subst j;rfl
    by_cases h1050:j=1050
    · subst j;rfl
    by_cases h1051:j=1051
    · subst j;rfl
    by_cases h1052:j=1052
    · subst j;rfl
    by_cases h1053:j=1053
    · subst j;rfl
    have h1059:j.val≠1059:=by omega
    have valueFacts:j.val≠1035 ∧ j.val≠1049 ∧ j.val≠1050 ∧ j.val≠1051 ∧ j.val≠1052 ∧ j.val≠1053:=by
      exact ⟨fun h=>h1035 (Fin.ext h),fun h=>h1049 (Fin.ext h),fun h=>h1050 (Fin.ext h),
        fun h=>h1051 (Fin.ext h),fun h=>h1052 (Fin.ext h),fun h=>h1053 (Fin.ext h)⟩
    simp only [localHeads,Fin.addCases_left,CloseoutRowsCircuitBottom.heads,
      if_neg valueFacts.1,if_neg valueFacts.2.1,if_neg valueFacts.2.2.1,if_neg valueFacts.2.2.2.1,
      if_neg valueFacts.2.2.2.2.1,if_neg valueFacts.2.2.2.2.2]
    have slotValue:(bottomSlots (j.castAdd 1)).val=639+j.val:=by
      rw [bottom_val]
      simp only [Fin.val_castAdd,if_neg valueFacts.2.2.2.2.1,if_neg h1059]
    have ne (target : Fin 1703) (ht : target.val≠639+j.val) : bottomSlots (j.castAdd 1)≠target:=by
      intro h;have hv:=congrArg Fin.val h
      rw [slotValue] at hv;exact ht hv.symm
    simp only [CloseoutRowsCircuitBottomPosition.output,Function.update_of_ne (ne 624 (by omega)),
      Function.update_of_ne (ne 1692 (by omega)),heads,if_neg (ne 1674 (by omega)),
      if_neg (ne 1688 (by omega)),if_neg (ne 1689 (by omega)),if_neg (ne 1690 (by omega)),
      if_neg (ne 624 (by omega))]
  · intro j;have hj:j=0:=Fin.eq_zero j;subst j
    rfl

theorem tapes_ready (C core n : ℕ) (out source members : List Bool) (D W : ℕ) (flag : Bool)
    (A : Fin 1703 → List Bool) (hc : 1 ≤ C)
    (blank : ∀ i,639 ≤ i.val ∧ i.val ≤ 1687 ∧ i.val≠1674 → A i=List.replicate C false)
    (domain : A 1674=UnaryTemplate.tape core)
    (extra : ∀ i : Fin 10,A (![1688,1689,1690,297,1692,1693,1694,1695,1696,1697] i)=
      CloseoutRowsCircuitBottom.extra C out source members D W flag i)
    (count : A 624=UnaryTemplate.tape n) :
    ∀ i,A (bottomSlots i)=localTapes C core n out source members D W flag i:=by
  intro i
  refine Fin.addCases (m:=1059) (n:=1) ?_ ?_ i
  · intro j
    simp only [localTapes,Fin.addCases_left,CloseoutRowsCircuitBottom.data]
    refine Fin.addCases (m:=1049) (n:=10) ?_ ?_ j
    · intro k
      simp only [Fin.addCases_left,CloseoutRowsGateBank.input,CloseoutRowsGateBank.padded,
        CloseoutRowsGateBank.input_eq,CloseoutRowsGateBank.pads]
      have val:(bottomSlots (k.castAdd 11)).val=639+k.val:=by
        rw [bottom_val]
        simp only [Fin.val_castAdd,if_neg (show k.val≠1052 by omega),if_neg (show k.val≠1059 by omega)]
      have same:((k.castAdd 10).castAdd 1)=k.castAdd 11:=Fin.ext rfl
      rw [same]
      by_cases hk:k.val=1035
      · rw [if_pos hk,if_pos hk,ZeroPadding.pad_zero]
        have he:bottomSlots (k.castAdd 11)=1674:=Fin.ext (by rw [val,hk];rfl)
        rw [he];exact domain
      · rw [if_neg hk,if_neg hk]
        rw [blank _ (by rw [val];omega)]
        by_cases h1:k.val=1
        · rw [if_pos h1]
          change List.replicate C false=ZeroPadding.pad C [false]
          cases C
          · omega
          · simp [ZeroPadding.pad,List.replicate_succ]
        · rw [if_neg h1];simp [ZeroPadding.pad]
    · intro k
      simp only [Fin.addCases_right]
      fin_cases k
      · exact extra 0
      · exact extra 1
      · exact extra 2
      · exact extra 3
      · exact extra 4
      · exact extra 5
      · exact extra 6
      · exact extra 7
      · exact extra 8
      · exact extra 9
  · intro j;have hj:j=0:=Fin.eq_zero j;subst j
    exact count

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomEntry
