import Proof.CaseAnalysis.CaseTwoWholeBlockLayout

/-! Exact shared entry ports of the whole original block. Fresh occurrence
scratch is blank; all source and query data come from the paid producer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBlock
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
theorem cache_slot (k D : ℕ) (j : Fin 19) :
    slots source a k D (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39)))=
      old source a k D (SourceBlock.cacheSlots source a k j):=by
  have hshared : shared (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39))):=Or.inl j.isLt
  rw [slots,if_pos hshared]
  have hk : key (Occurrence.old D a (OccurrenceAddress.base D (j.castAdd 39)))=j.castAdd 2:=by
    apply Fin.ext
    rw [key_value]
    change (if j.val<19 then j.val else if j.val=56 then 19 else 20)=j.val
    rw [if_pos j.isLt]
  rw [hk]
  exact congrArg (old source a k D) (Fin.append_left _ _ j)
theorem request_slot (k D : ℕ) :
    slots source a k D (Occurrence.old D a (OccurrenceAddress.base D 56))=
      old source a k D (SourceBlock.requestSlot source a k):=rfl

theorem input_flat (D : ℕ) (r : PCPPRequest a.minimumArity) (address : List Bool)
    (j : Fin (Occurrence.tapes D a)) :
    Occurrence.input D a r address j=
      if h : j.val<19 then OccurrenceAddress.cache a r ⟨j.val,h⟩
      else if j.val=56 then frame (pcppInput r) else if j.val=57 then frame address else []:=by
  refine Fin.addCases (motive:=fun j=>Occurrence.input D a r address j=
      if h : j.val<19 then OccurrenceAddress.cache a r ⟨j.val,h⟩
      else if j.val=56 then frame (pcppInput r) else if j.val=57 then frame address else [])
    (fun j : Fin (OccurrenceAddress.tapes D)=>?_) (fun j : Fin (OccurrenceBit.tapes a)=>?_) j
  · simp only [Occurrence.input,Fin.addCases_left,Fin.val_castAdd]
    rfl
  · have hb : 58≤OccurrenceAddress.tapes D:=by unfold OccurrenceAddress.tapes;omega
    simp only [Occurrence.input,Fin.addCases_right,Fin.val_natAdd]
    rw [dif_neg (by omega),if_neg (by omega),if_neg (by omega)]
theorem heads_flat (D : ℕ) (j : Fin (Occurrence.tapes D a)) :
    Occurrence.heads D a j=if j.val=13 ∨ j.val=14 then 1 else 0:=by
  refine Fin.addCases (motive:=fun j=>Occurrence.heads D a j=if j.val=13 ∨ j.val=14 then 1 else 0)
    (fun j : Fin (OccurrenceAddress.tapes D)=>?_) (fun j : Fin (OccurrenceBit.tapes a)=>?_) j
  · simp only [Occurrence.heads,Fin.addCases_left,Fin.val_castAdd]
    rfl
  · have hb : 58≤OccurrenceAddress.tapes D:=by unfold OccurrenceAddress.tapes;omega
    simp only [Occurrence.heads,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]
theorem fresh_input (D : ℕ) (r : PCPPRequest a.minimumArity) (address : List Bool)
    (j : Fin (Occurrence.tapes D a)) (hj : ¬shared j) :
    Occurrence.input D a r address j=[] ∧ Occurrence.heads D a j=0:=by
  have h19 : ¬j.val<19:=fun h=>hj (Or.inl h)
  have h56 : j.val≠56:=fun h=>hj (Or.inr (Or.inl h))
  have h57 : j.val≠57:=fun h=>hj (Or.inr (Or.inr h))
  rw [input_flat,heads_flat,dif_neg h19,if_neg h56,if_neg h57,if_neg (by omega)]
  exact ⟨rfl,rfl⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBlock
