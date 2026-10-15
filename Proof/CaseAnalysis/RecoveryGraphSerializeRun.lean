import Proof.CaseAnalysis.RecoveryGraphSerializeEntry

/-! The original completed graph physically enters the unchanged cold
Tseitin/balanced-CNF serializer. The emitted frame is returned to head zero,
and old search/hierarchy metadata is preserved outside the three consumed ports. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerialize
open LocalBitMultitape RecoveryRootRound
open RepairSource.RecoveryTseitinNative CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prepare := RecoveryFocus.machine prepareSlots RecoveryBoundedGraphSerializePrepare.machine
noncomputable def machine := Composition.machine prepare serialize
def budget {n : ℕ} (B : ℕ) (c : BooleanCircuit n) :=
  RecoveryBoundedGraphSerializePrepare.budget n c.output.val B+1+RecoveryBoundedGraphSerializeReady.budget c

theorem original_run {n : ℕ} (B : ℕ) (c : BooleanCircuit n)
    (H : Fin 1659→ℕ) (A : Fin 1659→List Bool) (entry : Entry B c H A)
    (hlast : c.nodes.length=c.output.val+1)
    (hg : (graph c).length≤B) (ho : c.output.val+1≤B) (ha : n+1≤B) :
    ∃ r,runFrom machine (budget B c) ⟨machine.start,H,A⟩=some r ∧
      r.final.tapes 1657=frame (balancedCNFPayload (CircuitInputCNF.circuitInputFormula c)).bits ∧
      r.final.heads 1657=0 ∧ r.steps≤budget B c ∧
      (∀ i : Fin 1659,i.val<153 → i≠20 → i≠25 → i≠145 →
        r.final.heads i=H i ∧ r.final.tapes i=A i) := by
  obtain ⟨base,br,bh,bt,bs⟩ := RecoveryBoundedGraphSerializePrepare.prepare_run n c.output.val B (graph c) hg ho ha
  obtain ⟨p,pr,_,ps,ph,pt,pk⟩ := RecoveryFocus.dock prepareSlots prepare_injective
    RecoveryBoundedGraphSerializePrepare.machine _ H A
    ⟨RecoveryBoundedGraphSerializePrepare.machine.start,
      RecoveryBoundedGraphSerializePrepare.heads (graph c),
      RecoveryBoundedGraphSerializePrepare.input n c.output.val B (graph c)⟩
    entry.heads entry.tapes base br
  have ph' : ∀ j,p.final.heads (prepareSlots j)=0 := fun j=>(ph j).trans (congrFun bh j)
  have pt' : ∀ j,p.final.tapes (prepareSlots j)=
      RecoveryBoundedGraphSerializePrepare.result n c.output.val B (graph c) j := fun j=>(pt j).trans (congrFun bt j)
  have projection := prepared_projection B c H p.final.heads A p.final.tapes entry hlast ph' pt' pk
  obtain ⟨q,qr,qt,qh,qs,qk⟩ := serialize_run B c p.final.heads p.final.tapes
    (fun j=>(projection j).1) (fun j=>(projection j).2)
  have whole := Composition.run_join prepare serialize _ _ _ p q pr qr
  refine ⟨Composition.joinedReceipt p q,whole,qt,qh,?_,?_⟩
  · change p.steps+1+q.steps≤budget B c
    unfold budget
    omega
  · intro i hi h20 h25 h145
    have first := prepared_old B c H p.final.heads A p.final.tapes entry ph' pt' pk i hi h20 h25 h145
    have last := qk i (ready_old_away i hi h20 h25 h145)
    exact ⟨last.1.trans first.1,last.2.trans first.2⟩

theorem budget_le {n : ℕ} (B : ℕ) (c : BooleanCircuit n)
    (ho : c.output.val+1≤B) (ha : n+1≤B) :
    budget B c≤16*(B+2)+2*Serialize.budget c+3 := by
  have h := RecoveryBoundedGraphSerializePrepare.budget_le n c.output.val B ho ha
  unfold budget RecoveryBoundedGraphSerializeReady.budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerialize
