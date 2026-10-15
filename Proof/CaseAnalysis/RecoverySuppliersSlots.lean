import Proof.CaseAnalysis.RecoverySuppliersLayout

/-! Injective physical banks and their exact retained projections for the
three original cold suppliers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem old_injective (k d : ℕ) : Function.Injective (old source k d):=by
  intro i j he;exact Fin.ext (congrArg (fun x : Fin (tapes source k d)=>x.val) he)
theorem count_injective (k d : ℕ) : Function.Injective (countSlots source k d):=Fin.castAdd_injective _ _
theorem count_old (k d : ℕ) (i : Fin 158) :
    countSlots source k d (RecoveryBoundedColdHierarchyDock.Count.old source k i)=old source k d i:=rfl

theorem capacity_injective (k d : ℕ) : Function.Injective (capacitySlots source k d):=by
  intro i j he
  have hb:=base_large source k
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [capacitySlots,wPort,old,capacityWork] at hv
  split_ifs at hv <;>dsimp at hv <;>omega

private def projectionIndex (B R Q : ℕ) (i : Fin 113):=
  if i.val<37 then 78+i.val else if i.val=37 then R else if i.val=65 then Q
  else if i.val=104 then 76 else if i.val=106 then 115
  else if i.val=109 then 153 else if i.val=111 then 156 else B+1+49+i.val
private def projectionUndo (B R Q value : ℕ):=
  if 78≤value ∧ value<115 then value-78 else if value=R then 37 else if value=Q then 65
  else if value=76 then 104 else if value=115 then 106
  else if value=153 then 109 else if value=156 then 111 else value-(B+1+49)
private theorem projectionUndo_index (B R Q : ℕ) (hB : 158<B)
    (hr : 158≤R) (hrB : R<B) (hq : 158≤Q) (hqB : Q<B) (hne : R≠Q) :
    ∀ i : Fin 113,projectionUndo B R Q (projectionIndex B R Q i)=i.val:=by
  intro i
  unfold projectionIndex
  split_ifs with h37 hR hQ h76 h115 h153 h156
  · simp only [projectionUndo,if_pos (show 78≤78+i.val ∧ 78+i.val<115 by omega)]
    omega
  · simp only [projectionUndo,if_neg (show ¬(78≤R ∧ R<115) by omega),if_pos]
    omega
  · simp only [projectionUndo,if_neg (show ¬(78≤Q ∧ Q<115) by omega),if_neg hne.symm,if_pos]
    omega
  · norm_num only [projectionUndo]
    simp only [if_neg (show (76 : ℕ)≠R by omega),if_neg (show (76 : ℕ)≠Q by omega)]
    simpa using h76.symm
  · norm_num only [projectionUndo]
    simp only [if_neg (show (115 : ℕ)≠R by omega),if_neg (show (115 : ℕ)≠Q by omega)]
    simpa using h115.symm
  · norm_num only [projectionUndo]
    simp only [if_neg (show (153 : ℕ)≠R by omega),if_neg (show (153 : ℕ)≠Q by omega)]
    simpa using h153.symm
  · norm_num only [projectionUndo]
    simp only [if_neg (show (156 : ℕ)≠R by omega),if_neg (show (156 : ℕ)≠Q by omega)]
    simpa using h156.symm
  · simp only [projectionUndo,
      if_neg (show ¬(78≤B+1+49+i.val ∧ B+1+49+i.val<115) by omega),
      if_neg (show B+1+49+i.val≠R by omega),if_neg (show B+1+49+i.val≠Q by omega),
      if_neg (show B+1+49+i.val≠76 by omega),if_neg (show B+1+49+i.val≠115 by omega),
      if_neg (show B+1+49+i.val≠153 by omega),if_neg (show B+1+49+i.val≠156 by omega)]
    omega
private theorem projectionIndex_injective (B R Q : ℕ) (hB : 158<B)
    (hr : 158≤R) (hrB : R<B) (hq : 158≤Q) (hqB : Q<B) (hne : R≠Q) :
    Function.Injective (projectionIndex B R Q):=by
  intro i j he
  apply Fin.ext
  rw [←projectionUndo_index B R Q hB hr hrB hq hqB hne i,
    ←projectionUndo_index B R Q hB hr hrB hq hqB hne j]
  exact congrArg (projectionUndo B R Q) he
private theorem projection_value (k d : ℕ) (i : Fin 113) :
    (projectionSlots source k d i).val=
      projectionIndex (base source k) (rBitsPort source k d).val (qBitsPort source k d).val i:=by
  unfold projectionSlots projectionIndex
  split_ifs <;>rfl
theorem projection_injective (k d : ℕ) : Function.Injective (projectionSlots source k d):=by
  intro i j he
  obtain ⟨hr,hrB,hq,hqB⟩:=bits_range source k d
  apply projectionIndex_injective _ _ _ (base_large source k) hr hrB hq hqB (bits_distinct source k d)
  simpa only [projection_value] using congrArg Fin.val he

theorem full_injective (k d : ℕ) : Function.Injective (fullSlots source k d):=by
  intro i j he
  have hb:=base_large source k
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [fullSlots,old,fullWork] at hv
  split_ifs at hv <;>dsimp at hv <;>subst_vars <;>omega

theorem capacity_away (k d : ℕ) (i : Fin (tapes source k d))
    (hw : i≠wPort source k d) (h154 : i≠old source k d 154)
    (h76 : i≠old source k d 76) (h77 : i≠old source k d 77)
    (hrange : i.val<base source k+1 ∨ base source k+1+49 ≤ i.val) :
    ∀ j,capacitySlots source k d j≠i:=by
  intro j he
  have hj:=j.isLt
  dsimp only [capacitySlots] at he
  split_ifs at he
  · exact hw he.symm
  · exact h154 he.symm
  · exact h76 he.symm
  · exact h77 he.symm
  · have hv:=congrArg Fin.val he
    change base source k+1+j.val=i.val at hv
    omega

theorem projection_bank (k d : ℕ) (i : Fin 37) :
    projectionSlots source k d (RecoveryProjectionCold.bankSlots i)=old source k d ⟨78+i.val,by omega⟩:=by
  simp only [projectionSlots,RecoveryProjectionCold.bankSlots,Fin.val_castAdd,dif_pos i.isLt]

theorem projection_away (k d : ℕ) (i : Fin (tapes source k d))
    (hbank : i.val<78 ∨ 115 ≤ i.val) (hr : i≠rBitsPort source k d) (hq : i≠qBitsPort source k d)
    (h76 : i≠old source k d 76) (h115 : i≠old source k d 115)
    (h153 : i≠old source k d 153) (h156 : i≠old source k d 156)
    (hrange : i.val<base source k+1+49 ∨ base source k+1+49+113 ≤ i.val) :
    ∀ j,projectionSlots source k d j≠i:=by
  intro j he
  have hj:=j.isLt
  dsimp only [projectionSlots] at he
  split_ifs at he
  · have hv:=congrArg Fin.val he
    change 78+j.val=i.val at hv
    omega
  · exact hr he.symm
  · exact hq he.symm
  · exact h76 he.symm
  · exact h115 he.symm
  · exact h153 he.symm
  · exact h156 he.symm
  · have hv:=congrArg Fin.val he
    change base source k+1+49+j.val=i.val at hv
    omega

theorem full_away (k d : ℕ) (i : Fin (tapes source k d))
    (h153 : i≠old source k d 153) (h155 : i≠old source k d 155) (h152 : i≠old source k d 152)
    (hrange : i.val<base source k+1+49+113) : ∀ j,fullSlots source k d j≠i:=by
  intro j he
  dsimp only [fullSlots] at he
  split_ifs at he
  · exact h153 he.symm
  · exact h155 he.symm
  · exact h152 he.symm
  · have hv:=congrArg Fin.val he
    change base source k+1+49+113+j.val=i.val at hv
    omega

theorem full_source (k d : ℕ) : fullSlots source k d (RecoveryFullBound.sourceSlot d)=old source k d 153:=by
  simp only [fullSlots,if_pos]
theorem full_raw (k d : ℕ) : fullSlots source k d (RecoveryFullBound.rawSlot d)=old source k d 155:=by
  have hn : RecoveryFullBound.rawSlot d≠RecoveryFullBound.sourceSlot d:=RecoveryFullBound.copy_away_source d 1
  simp only [fullSlots,if_neg hn,if_pos]
theorem full_compare (k d : ℕ) : fullSlots source k d (RecoveryFullBound.compareSlot d)=old source k d 152:=by
  have hn : RecoveryFullBound.compareSlot d≠RecoveryFullBound.rawSlot d:=
    RecoveryFullBound.old_away d 0 (DimensionPolynomial.rawSlot (RecoveryFullBound.exponent d))
  have hs : RecoveryFullBound.compareSlot d≠RecoveryFullBound.sourceSlot d:=RecoveryFullBound.copy_away_source d 0
  simp only [fullSlots,if_neg hs,if_neg hn,if_pos]

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
