import Proof.CaseAnalysis.RecoveryGraphSerializeReady

/-! The output-only reset uses the abandoned fresh graph alias as its
actual trace tape. The enclosing bank therefore stays at 1659 tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerialize
open LocalBitMultitape RecoveryRootRound
open RepairSource.RecoveryTseitinNative CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem serializer_hole (i : Fin 1506) : serializerSlots i≠1215 := by
  intro he
  have hv := congrArg Fin.val he
  by_cases h1 : i=1062
  · subst i;change 20=1215 at hv;omega
  by_cases h2 : i=1339
  · subst i;change 25=1215 at hv;omega
  by_cases h3 : i=1342
  · subst i;change 145=1215 at hv;omega
  simp only [serializerSlots,if_neg h1,if_neg h2,if_neg h3,Fin.val_natAdd] at hv
  have hi : i=1062 := Fin.ext (by change 153+i.val=1215 at hv;omega)
  exact h1 hi

def readySlots (i : Fin 1507) : Fin 1659 :=
  if h : i.val<1506 then serializerSlots ⟨i.val,h⟩ else 1215

theorem ready_old (i : Fin 1506) : readySlots (i.castAdd 1)=serializerSlots i := by
  simp only [readySlots,Fin.val_castAdd,dif_pos i.isLt]
theorem ready_last : readySlots 1506=1215 := rfl
theorem ready_injective : Function.Injective readySlots := by
  intro i j he
  apply Fin.ext
  dsimp only [readySlots] at he
  split_ifs at he with hi hj
  · exact congrArg (fun k : Fin 1506=>k.val) (serializer_injective he)
  · exact False.elim (serializer_hole _ he)
  · exact False.elim (serializer_hole _ he.symm)
  · have hib := i.isLt
    have hjb := j.isLt
    omega

theorem ready_old_away (i : Fin 1659) (hi : i.val<153) (h20 : i≠20) (h25 : i≠25) (h145 : i≠145) :
    ∀ j,readySlots j≠i := by
  intro j he
  dsimp only [readySlots] at he
  split_ifs at he
  · exact serializer_old i hi h20 h25 h145 _ he
  · have hv := congrArg Fin.val he
    change 1215=i.val at hv
    omega

noncomputable def serialize := RecoveryFocus.machine readySlots RecoveryBoundedGraphSerializeReady.machine

theorem serialize_run {n : ℕ} (B : ℕ) (c : BooleanCircuit n)
    (H : Fin 1659→ℕ) (A : Fin 1659→List Bool)
    (hH : ∀ j,H (readySlots j)=0)
    (hA : ∀ j,A (readySlots j)=RecoveryBoundedGraphSerializeReady.input B c j) :
    ∃ r,runFrom serialize (RecoveryBoundedGraphSerializeReady.budget c) ⟨serialize.start,H,A⟩=some r ∧
      r.final.tapes 1657=frame (balancedCNFPayload (CircuitInputCNF.circuitInputFormula c)).bits ∧
      r.final.heads 1657=0 ∧ r.steps≤RecoveryBoundedGraphSerializeReady.budget c ∧
      (∀ i,(∀ j,readySlots j≠i) → r.final.heads i=H i ∧ r.final.tapes i=A i) := by
  obtain ⟨p,hp,pt,ph,_pl,ps⟩ := RecoveryBoundedGraphSerializeReady.serialize_ready B c
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩ := RecoveryFocus.dock readySlots ready_injective
    RecoveryBoundedGraphSerializeReady.machine _ H A
    (initialConfiguration RecoveryBoundedGraphSerializeReady.machine (RecoveryBoundedGraphSerializeReady.input B c))
    hH hA p hp
  exact ⟨r,hr,(rt 1504).trans pt,(rh 1504).trans ph,rs.le.trans ps,rkeep⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerialize
