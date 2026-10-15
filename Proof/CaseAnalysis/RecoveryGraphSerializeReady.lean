import Proof.CaseAnalysis.RecoveryGraphSerializeLayout
import Proof.MachineModel.OrdinaryMaskedReset

/-! The unchanged cold serializer is followed by the existing paid masked
head return on its output alone. The actual trace starts empty and is erased;
no serializer time driver or postulated output-head invariant is supplied. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerializeReady
open LocalBitMultitape RecoveryRootRound
open RepairSource.RecoveryTseitinNative CanonicalRecoveryLanguage BalancedCNFSATEncoding
open RecoveryBoundedGraphSerialize (serializerCaps)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 1506) : Bool := decide (i=1504)
noncomputable def machine := MaskedReset.machine Serialize.machine selected
def input {n : ℕ} (B : ℕ) (c : BooleanCircuit n) : Fin 1507→List Bool :=
  Fin.addCases (m:=1506) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (serializerCaps B i) (Serialize.input c i)) (fun _=>[])
def budget {n : ℕ} (c : BooleanCircuit n) := 2*Serialize.budget c+2

theorem serialize_ready {n : ℕ} (B : ℕ) (c : BooleanCircuit n) :
    ∃ r,run machine (budget c) (input B c)=some r ∧
      r.final.tapes 1504=frame (balancedCNFPayload (CircuitInputCNF.circuitInputFormula c)).bits ∧
      r.final.heads 1504=0 ∧ r.final.heads 1506=0 ∧ r.steps≤budget c := by
  obtain ⟨a,ha,atapes,asteps⟩ := Serialize.serialize_run c
  obtain ⟨p,hp,pf,ps,_⟩ := ZeroPadding.run_config Serialize.machine (serializerCaps B) _ _ a ha
  have paddedEntry : ZeroPadding.config (serializerCaps B) (initialConfiguration Serialize.machine (Serialize.input c))=
      initialConfiguration Serialize.machine (fun i=>ZeroPadding.pad (serializerCaps B i) (Serialize.input c i)) := by
    apply configuration_ext <;> rfl
  rw [paddedEntry] at hp
  have hhead : ∀ i,selected i=true → p.final.heads i≤p.steps := by
    intro i _
    have h := SelectiveReset.prefix_head (prefix_of_run Serialize.machine _ _ p hp).1 i
    simpa only [initialConfiguration,Nat.zero_add] using h
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.reset_run Serialize.machine selected _ _ p hp hhead
  have entry : Rewind.recording
      (initialConfiguration Serialize.machine (fun i=>ZeroPadding.pad (serializerCaps B i) (Serialize.input c i))) 0=
      initialConfiguration machine (input B c) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=1506) (n:=1) (fun j=>?_) (fun j=>?_) i
      all_goals simp only [Rewind.recording,Rewind.config,initialConfiguration,Fin.addCases_left,Fin.addCases_right]
    · rfl
  rw [entry] at hr
  have hb : 2*p.steps+2≤budget c := by
    unfold budget
    omega
  have more := runFrom_moreFuel machine (2*p.steps+2) (budget c-(2*p.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,?_,?_,?_,rs.le.trans hb⟩
  · rw [rf]
    change p.final.tapes (1504 : Fin 1506)=_
    rw [pf]
    change ZeroPadding.pad (serializerCaps B 1504) (a.final.tapes 1504)=_
    rw [atapes]
    exact ZeroPadding.pad_zero _
  · rw [rf]
    change (if selected (1504 : Fin 1506) then 0 else p.final.heads 1504)=0
    simp only [selected,decide_true,↓reduceIte]
  · rw [rf]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerializeReady
