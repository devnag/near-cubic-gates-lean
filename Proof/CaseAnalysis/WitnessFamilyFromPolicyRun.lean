import Proof.CaseAnalysis.WitnessFamilyFromPolicyLayout

/-! The retained actual source policy pays P/H and immediately executes
the complete family verifier, including all raw rejection branches. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFromPolicy
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth FamilyResources
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem family_run (e E K N den copies R q0 cb S V C k : ℕ) (delta q : ℚ) (sym : Bool)
    {t : ℕ} (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t)
    (data : Fin t→List Bool) (cursor : Fin t→ℕ) (bits : List Bool)
    (hK : 0<K) (injective : Function.Injective policy) (hne : count≠raw)
    (hc : ∀ i,count≠policy i) (hr : ∀ i,raw≠policy i)
    (hN : data source=List.replicate N true) (hNh : cursor source=0)
    (hV : data count=List.replicate V true) (hVh : cursor count=0)
    (hraw : data raw=frame bits) (hrawh : cursor raw=0)
    (hpolicy : LegalTemplate.Call.Fields e den delta copies sym R q0 cb (natBitLength C) (data ∘ policy))
    (hph : ∀ i,cursor (policy i)=LegalTemplate.heads e i)
    (hf : Fits (FamilyCapacity.value E K N) V C (LegalPolicy.T delta copies q0 cb) k bits
      (SignedSortKey.binary (natBitLength R) R))
    (hlen : bits.length≤S) (hv : V≤S) (hC : 0<C) (hq : 0≤q)
    (hk : k≤width (LegalPolicy.T delta copies q0 cb) (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k) :
    let P:=FamilyCapacity.value E K N
    let T:=LegalPolicy.T delta copies q0 cb
    let W:=LegalPolicy.W e den R
    let L:=DescriptionPolicy.value sym R q0 W
    let arity:=SignedSortKey.binary (natBitLength R) R
    ∃ extra actual,runFrom (machine e E K source count raw policy sym k q)
      (FamilyCapacity.budget E K N+1+FamilyCold.budget P (P+1) V (sumCost S P) bits)
      ⟨(machine e E K source count raw policy sym k q).start,heads E cursor,input E data⟩=some actual ∧
      actual.steps≤FamilyCapacity.budget E K N+1+totalCost S P ∧
      actual.final.heads (FamilyCold.Call.slots (fields e E source count raw policy) 724)=0 ∧
      actual.final.tapes (FamilyCold.Call.slots (fields e E source count raw policy) 724)=
        [FamilyCold.passed sym V C T R W L q bits arity] ∧
      extra 174=List.replicate V true ∧
      (∀ i,(∀ j,fields e E source count raw policy j≠FamilyCapacity.Call.old E i)→
        actual.final.heads (FamilyCold.Call.old (FamilyCapacity.Call.old E i))=cursor i ∧
        actual.final.tapes (FamilyCold.Call.old (FamilyCapacity.Call.old E i))=data i) ∧
      (FamilyCold.passed sym V C T R W L q bits arity=true→∃ after,
        actual.final.heads ∘ FamilyCold.Call.slots (fields e E source count raw policy)=
          FamilyPrepare.heads (FamilyWork.heads
            (FamilyLoop.entry (FamilyMode.machine sym) P (P+1) C T R W L k q
              (FamilyFields.words bits) arity [] (FamilyFields.tail (P+1) bits)
              [] [] [] (FamilyMode.native sym R) V after) 1) ∧
        actual.final.tapes ∘ FamilyCold.Call.slots (fields e E source count raw policy)=
          FamilyPrepare.tapes (natBitLength C) bits (FamilyWork.tapes (P+1) V
            (FamilyLoop.entry (FamilyMode.machine sym) P (P+1) C T R W L k q
              (FamilyFields.words bits) arity [] (FamilyFields.tail (P+1) bits)
              [] [] [] (FamilyMode.native sym R) V after) extra) ∧
        Store (width T (natBitLength C)) zero [] after):=by
  let P:=FamilyCapacity.value E K N
  let T:=LegalPolicy.T delta copies q0 cb
  let W:=LegalPolicy.W e den R
  let L:=DescriptionPolicy.value sym R q0 W
  let arity:=SignedSortKey.binary (natBitLength R) R
  let ambient:=LegalTemplate.project e (data ∘ policy)
  have capExists:=FamilyCapacity.Call.call_run E K N hK source data cursor hN hNh
  let cap:=Classical.choose capExists
  have cf:=Classical.choose_spec capExists
  have keep:=cf.2.2.2.2.2
  have ex (i : Fin 4):cap.final.tapes (external E source count raw i)=
      FamilyPolicyPorts.externalValues P (P+1) V bits i:=by
    fin_cases i
    · exact cf.2.2.2.1
    · exact cf.2.2.2.2.1
    · exact (keep count).2.trans hV
    · exact (keep raw).2.trans hraw
  have loc (i : Fin 100):cap.final.tapes (inside e E policy i)=
      FamilyPolicyPorts.localValues R W L T (natBitLength C) arity ambient i:=
    (keep (policy (FamilyPolicyPorts.port e i))).2.trans
      (FamilyPolicyPorts.local_values e den delta copies sym R q0 cb (natBitLength C) (data ∘ policy) hpolicy i)
  have exh (i : Fin 4):cap.final.heads (external E source count raw i)=0:=by
    fin_cases i
    · exact cf.2.2.1 (FamilyCapacity.pSlot E)
    · exact cf.2.2.1 (FamilyCapacity.hSlot E)
    · exact (keep count).1.trans hVh
    · exact (keep raw).1.trans hrawh
  have loch (i : Fin 100):cap.final.heads (inside e E policy i)=if i.val=0 then 1 else 0:=
    (keep (policy (FamilyPolicyPorts.port e i))).1.trans
      ((hph _).trans (FamilyPolicyPorts.head_port e i))
  obtain ⟨extra,last,lr,ls,lh,lt,lV,lkeep,good⟩:=FamilyCold.Call.call_run sym S P V C T R W L k q
    bits arity ambient (fields e E source count raw policy)
    (fields_injective e E source count raw policy injective hne hc hr) cap.final.tapes cap.final.heads
    (FamilyPolicyPorts.join_values _ _ _ P (P+1) V C T R W L bits arity ambient ex loc)
    (FamilyPolicyPorts.join_heads _ _ _ exh loch) hf hlen hv hC hpolicy.store hq hk hp hd
  let lifted:=TapeEmbedding.receipt (fun _ : Fin FamilyCold.Call.extra=>0) (fun _=>[]) cap
  have firstRun:=TapeEmbedding.run_embed (FamilyCapacity.Call.machine E K source)
    (fun _ : Fin FamilyCold.Call.extra=>0) (fun _=>[]) _ _ cap cf.1
  obtain ⟨actual,run,steps,ah,atapes⟩:=joined (first E K source) (second e E source count raw policy sym k q)
    (FamilyCapacity.budget E K N) (FamilyCold.budget P (P+1) V (sumCost S P) bits)
    (heads E cursor) (input E data) lifted last firstRun lr cf.2.1 (runFrom_steps_le _ _ _ last lr)
  have bound:=FamilyResources.total_cost S P V C T k bits arity hf hv
  refine ⟨extra,actual,run,steps.trans (Nat.add_le_add_left bound _),
    (congrFun ah _).trans lh,(congrFun atapes _).trans lt,lV,?_,?_⟩
  · intro i hi
    have ret:=lkeep (FamilyCapacity.Call.old E i) hi
    exact ⟨(congrFun ah _).trans (ret.1.trans (keep i).1),
      (congrFun atapes _).trans (ret.2.trans (keep i).2)⟩
  · intro accepted
    obtain ⟨after,hh,ht,hs⟩:=good accepted
    exact ⟨after,(congrArg (fun hs=>hs ∘ FamilyCold.Call.slots (fields e E source count raw policy)) ah).trans hh,
      (congrArg (fun ts=>ts ∘ FamilyCold.Call.slots (fields e E source count raw policy)) atapes).trans ht,hs⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFromPolicy
