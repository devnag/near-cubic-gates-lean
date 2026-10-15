import Proof.CaseAnalysis.WitnessNativePolicyDock

/-! The literal measured-counter bank executes the complete native cache
and policy continuation. All nonaliased old fields and cursors are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy.Call
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def project (a : PointwisePCPPAlgorithm) (D : ℕ) {t s : ℕ} (counter : Fin 75→Fin t)
    (cfg : Configuration (t+extra a D) s) : Configuration (extra a D) s:=
  ⟨cfg.control,cfg.heads ∘ slots a D counter,cfg.tapes ∘ slots a D counter⟩

theorem outside (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (counter : Fin 75→Fin t)
    (i : Fin t) (hi : ∀ j,counter j≠i) : ∀ j,slots a D counter j≠old a D i:=by
  have away : ∀ k,bank a D counter k≠old a D i:=by
    intro k
    refine Fin.addCases (m:=75) (n:=extra a D) (fun j=>?_) (fun j=>?_) k
    · intro he
      have hv:=congrArg Fin.val he
      simp only [bank,Fin.addCases_left,old,Fin.val_castAdd] at hv
      exact hi j (Fin.ext hv)
    · intro he
      have hv:=congrArg Fin.val he
      simp only [bank,Fin.addCases_right,old,Fin.val_castAdd,Fin.val_natAdd] at hv
      have ht:=i.isLt
      omega
  exact fun j=>away (remap a D j)

theorem call_run (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ)
    {t : ℕ} (counter : Fin 75→Fin t) (hc : Function.Injective counter)
    (data : Fin t→List Bool) (cursor : Fin t→ℕ)
    (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) (hD : 1≤D)
    (hf : ∀ j,cursor (counter (PCPPNativeColdCounters.ports j))=0 ∧
      data (counter (PCPPNativeColdCounters.ports j))=PCPPNativeMetadataMass.values oracle p Q j)
    (hrh : cursor (counter 72)=0) (hrt : data (counter 72)=List.replicate R true) :
    let r:=NativeCache.request a p R Q hR hQ x oracle
    ∃ actual,runFrom (machine a D copies delta counter) (NativePolicy.budget a D copies delta p R Q hR hQ x oracle)
      ⟨(machine a D copies delta counter).start,heads a D cursor,input a D data⟩=some actual ∧
      actual.steps≤NativePolicy.budget a D copies delta p R Q hR hQ x oracle ∧
      (∀ j : Fin 19,actual.final.tapes (slots a D counter (NativePolicy.cacheSlots a D (PCPPSourceCache.cacheSlots a j)))=
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
      (∀ j : Fin 19,actual.final.heads (slots a D counter (NativePolicy.cacheSlots a D (PCPPSourceCache.cacheSlots a j)))=
        PCPPQueryClauseReuse.heads j) ∧
      SourcePolicy.Call.Fields D copies delta (NativePolicy.fields a) r (a.output r)
        (project a D counter actual.final) ∧
      (∀ i,(∀ j,slots a D counter j≠old a D i) →
        actual.final.heads (old a D i)=cursor i ∧ actual.final.tapes (old a D i)=data i):=by
  intro r
  obtain ⟨base,hb,bs,bt,bh,bf⟩:=NativePolicy.policy_run a D copies delta p R Q hR hQ x oracle hD
  have hdata:=input_fields a D counter data cursor oracle p Q hf hrh hrt
  obtain ⟨actual,ha,_,asteps,ah,atape,away⟩:=RecoveryFocus.dock (slots a D counter) (slots_injective a D counter hc)
    (NativePolicy.machine a D copies delta) _ (heads a D cursor) (input a D data)
    (initialConfiguration (NativePolicy.machine a D copies delta) (NativePolicy.input a D oracle p Q))
    (fun i=>(hdata i).1) (fun i=>(hdata i).2) base hb
  refine ⟨actual,ha,asteps.trans_le bs,fun j=>(atape _).trans (bt j),fun j=>(ah _).trans (bh j),
    ⟨(atape _).trans bf.count,(atape _).trans bf.clause,(atape _).trans bf.q0,
      (atape _).trans bf.cap,fun i=>(ah _).trans (bf.cursor i)⟩,?_⟩
  intro i hi
  obtain ⟨ih,it⟩:=away (old a D i) hi
  simpa only [heads,input,old,Fin.addCases_left] using And.intro ih it

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy.Call
