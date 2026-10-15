import Proof.CaseAnalysis.RecoveryGrammarRowState

/-! One uniform paid room contract serves every original grammar atom.
The enclosing C.12 ledger discharges these loose bounds once. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Room (W C D L S B P : ℕ) : Prop where
  originalC : C=RecoveryBoundedSelectorLoop.capacity W
  cB : C+1≤B
  dB : D≤B
  lB : L≤B
  wB : W≤B
  positive : 1≤S
  reference : 2*W+2≤B
  packet : 4*C+10*W+20≤B
  unaryLog : ∀ limit,limit≤W → RecoveryBoundedNativeUnaryJoin.budget limit C≤D
  lessLog : RecoveryBoundedSelectorFinish.logCapacity W≤L
  unaryRun : ∀ limit,limit≤W → S+RecoveryBoundedUnaryReuse.budget limit C+3≤B
  lessRun : ∀ upper,upper≤W → S+RecoveryBoundedAddressReuse.resetBudget upper W+3≤B
  foldRun : ∀ conjunction count,count≤W → S+RecoveryBoundedGrammarFold.budget conjunction count C+3≤B
  stack : S+W*(2*W+1)≤P

structure ScalarFits (q bound row W : ℕ) : Prop where
  index : ∀ j,rowIndex q bound row j≤W
  limit : ∀ j,rowLimit q bound j≤W
  upper : ∀ j,rowUpper q row j≤W
  value : 6≤W

theorem Room.capacity {W C D L S B P : ℕ} (h : Room W C D L S B P) :
    16384*(W+1)^2≤C := by rw [h.originalC];rfl

theorem Room.packet_fits {W C D L S B P q bound row : ℕ} (h : Room W C D L S B P)
    (hs : ScalarFits q bound row W) (p : Selection) :
    2*(rowIndex q bound row p.index)+4≤B ∧
    2*(rowLimit q bound p.limit)+4≤B ∧ 2*p.value.val+4≤B ∧
    2*(rowUpper q row p.upper)+4≤B ∧ 2*C+4≤B ∧
    (selectedWord p q bound row C).length≤B ∧
    ∀ j∈RecoveryBoundedRowReload.ports,(selectedFields p q bound row C j).length≤B := by
  have hi:=hs.index p.index
  have hl:=hs.limit p.limit
  have hu:=hs.upper p.upper
  have hv : p.value.val≤W:=by have hh:=p.value.isLt;have h6:=hs.value;omega
  have hb:=h.packet
  refine ⟨by omega,by omega,by omega,by omega,by omega,?_,?_⟩
  · unfold selectedWord selectedFields
    rw [RecoveryBoundedGrammarPrototype.packet_length]
    omega
  · intro j _
    exact RecoveryBoundedGrammarBank.fields_support C _ _ _ _ B
      (by omega) (by omega) (by omega) (by omega) (by omega) j

theorem Room.pad_packet_length {W C D L S B P q bound row : ℕ} (h : Room W C D L S B P)
    (hs : ScalarFits q bound row W) (p : Selection) :
    (ZeroPadding.pad B (selectedWord p q bound row C)).length≤B := by
  have hp:=(h.packet_fits hs p).2.2.2.2.2.1
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate]
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
