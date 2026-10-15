import Proof.CaseAnalysis.WitnessBoundedFamilyPreHierarchy

/-! Execute the existing capacity constructor and then the actual supplied
strengthened family receipt. All policy aliases come from the real prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupportFromPolicy
open LocalBitMultitape FamilyFromPolicy
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem family_run {s t : ℕ} (supplier : Machine 3244 s)
    (e E K N den copies R q0 cb V C fuel : ℕ) (delta : ℚ) (sym : Bool)
    (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t)
    (data : Fin t→List Bool) (cursor : Fin t→ℕ) (bits supports : List Bool)
    (hK:0<K) (injective:Function.Injective policy) (hne:count≠raw)
    (hc:∀ i,count≠policy i) (hr:∀ i,raw≠policy i)
    (hN:data source=List.replicate N true) (hNh:cursor source=0)
    (hV:data count=List.replicate V true) (hVh:cursor count=0)
    (hraw:data raw=frame bits) (hrawh:cursor raw=0)
    (hpolicy:LegalTemplate.Call.Fields e den delta copies sym R q0 cb (natBitLength C) (data ∘ policy))
    (hph:∀ i,cursor (policy i)=LegalTemplate.heads e i)
    (inner : ExecutionReceipt 3244 s)
    (actual:runFrom supplier fuel
      ⟨supplier.start,SupportDock.lift (FamilyPrepare.heads FamilyHeads.heads) supports.length,
        SupportDock.lift (FamilyCold.input (FamilyCapacity.value E K N) (FamilyCapacity.value E K N+1)
          V C (LegalPolicy.T delta copies q0 cb) R (LegalPolicy.W e den R)
          (DescriptionPolicy.value sym R q0 (LegalPolicy.W e den R)) bits
          (SignedSortKey.binary (natBitLength R) R) (LegalTemplate.project e (data ∘ policy))) supports⟩=some inner) :
    ∃ final,runFrom (machine supplier e E K source count raw policy)
      (FamilyCapacity.budget E K N+1+fuel)
      ⟨(machine supplier e E K source count raw policy).start,heads E cursor supports,input E data supports⟩=some final ∧
      final.steps≤FamilyCapacity.budget E K N+1+fuel ∧
      (∀ i,final.final.heads (FamilySupportCall.slots (fields e E source count raw policy) i)=inner.final.heads i ∧
        final.final.tapes (FamilySupportCall.slots (fields e E source count raw policy) i)=inner.final.tapes i) ∧
      (∀ i,(∀ j,fields e E source count raw policy j≠FamilyCapacity.Call.old E i)→
        final.final.heads (FamilySupportCall.old (FamilyCapacity.Call.old E i))=cursor i ∧
        final.final.tapes (FamilySupportCall.old (FamilyCapacity.Call.old E i))=data i) := by
  let P:=FamilyCapacity.value E K N
  let T:=LegalPolicy.T delta copies q0 cb
  let W:=LegalPolicy.W e den R
  let L:=DescriptionPolicy.value sym R q0 W
  let arity:=SignedSortKey.binary (natBitLength R) R
  let ambient:=LegalTemplate.project e (data ∘ policy)
  obtain ⟨cap,run,steps,cheads,ctapes,htapes,keep⟩:=FamilyCapacity.Call.call_run E K N hK source data cursor hN hNh
  have ex (i : Fin 4):cap.final.tapes (external E source count raw i)=
      FamilyPolicyPorts.externalValues P (P+1) V bits i:=by
    fin_cases i
    · exact ctapes
    · exact htapes
    · exact (keep count).2.trans hV
    · exact (keep raw).2.trans hraw
  have loc (i : Fin 100):cap.final.tapes (inside e E policy i)=
      FamilyPolicyPorts.localValues R W L T (natBitLength C) arity ambient i:=
    (keep (policy (FamilyPolicyPorts.port e i))).2.trans
      (FamilyPolicyPorts.local_values e den delta copies sym R q0 cb (natBitLength C) (data ∘ policy) hpolicy i)
  have exh (i : Fin 4):cap.final.heads (external E source count raw i)=0:=by
    fin_cases i
    · exact cheads (FamilyCapacity.pSlot E)
    · exact cheads (FamilyCapacity.hSlot E)
    · exact (keep count).1.trans hVh
    · exact (keep raw).1.trans hrawh
  have loch (i : Fin 100):cap.final.heads (inside e E policy i)=if i.val=0 then 1 else 0:=
    (keep (policy (FamilyPolicyPorts.port e i))).1.trans
      ((hph _).trans (FamilyPolicyPorts.head_port e i))
  obtain ⟨last,lr,_ls,localFields,away⟩:=FamilySupportCall.call_run supplier
    (fields e E source count raw policy) (fields_injective e E source count raw policy injective hne hc hr)
    P (P+1) V C T R W L fuel bits arity supports ambient cap.final.tapes cap.final.heads
    (FamilyPolicyPorts.join_values _ _ _ P (P+1) V C T R W L bits arity ambient ex loc)
    (FamilyPolicyPorts.join_heads _ _ _ exh loch) inner actual
  let lifted:=FamilySupportPrefix.receipt supports cap
  have firstRun:=FamilySupportPrefix.run_lift (FamilyCapacity.Call.machine E K source)
    (FamilyCapacity.budget E K N) (FamilyCapacity.Call.heads E cursor)
    (FamilyCapacity.Call.input E data) supports cap run
  have secondRun:runFrom (second supplier e E source count raw policy) fuel
      ⟨(second supplier e E source count raw policy).start,lifted.final.heads,lifted.final.tapes⟩=some last:=by
    simpa only [second,lifted,FamilySupportPrefix.receipt_heads,FamilySupportPrefix.receipt_tapes] using lr
  obtain ⟨final,fr,fs,fh,ft⟩:=joined (first E K source) (second supplier e E source count raw policy)
    (FamilyCapacity.budget E K N) fuel (heads E cursor supports) (input E data supports)
    lifted last firstRun secondRun steps (runFrom_steps_le _ _ _ last secondRun)
  refine ⟨final,fr,fs,fun i=>⟨(congrFun fh _).trans (localFields i).1,
    (congrFun ft _).trans (localFields i).2⟩,?_⟩
  intro i hi
  have retained:=away (FamilyCapacity.Call.old E i) hi
  exact ⟨(congrFun fh _).trans (retained.1.trans (keep i).1),
    (congrFun ft _).trans (retained.2.trans (keep i).2)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupportFromPolicy
