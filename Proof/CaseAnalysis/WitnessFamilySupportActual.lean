import Proof.CaseAnalysis.WitnessFamilySupportSupplier
import Proof.CaseAnalysis.WitnessFamilySupportFromPolicyRun
import Proof.CaseAnalysis.WitnessSupportBudgetRatio

/-! The actual source policy constructs capacity and runs the strengthened
family. Its fuel is twice the original literal family continuation budget. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupportActual
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth FamilyResources FamilyFromPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem family_run (e E K N den copies R q0 cb S V C k : ℕ) (delta q : ℚ) (sym : Bool)
    {t : ℕ} (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t)
    (data : Fin t→List Bool) (cursor : Fin t→ℕ) (bits supports : List Bool)
    (hK:0<K) (injective:Function.Injective policy) (hne:count≠raw)
    (hc:∀ i,count≠policy i) (hr:∀ i,raw≠policy i)
    (hN:data source=List.replicate N true) (hNh:cursor source=0)
    (hV:data count=List.replicate V true) (hVh:cursor count=0)
    (hraw:data raw=frame bits) (hrawh:cursor raw=0)
    (hpolicy:LegalTemplate.Call.Fields e den delta copies sym R q0 cb (natBitLength C) (data ∘ policy))
    (hph:∀ i,cursor (policy i)=LegalTemplate.heads e i)
    (hf:Fits (FamilyCapacity.value E K N) V C (LegalPolicy.T delta copies q0 cb) k bits
      (SignedSortKey.binary (natBitLength R) R))
    (hP:capacity S≤FamilyCapacity.value E K N)
    (hlen:bits.length≤S) (hv:V≤S) (hcore:R≤S) (hC:0<C) (hq:0≤q)
    (hk:k≤width (LegalPolicy.T delta copies q0 cb) (natBitLength C))
    (hp:CompetitorThresholdDecision.numerator q<2^k) (hd:q.den<2^k) :
    let P:=FamilyCapacity.value E K N
    let T:=LegalPolicy.T delta copies q0 cb
    let W:=LegalPolicy.W e den R
    let L:=DescriptionPolicy.value sym R q0 W
    let arity:=SignedSortKey.binary (natBitLength R) R
    let fuel:=2*(FamilyCapacity.budget E K N+1+FamilyCold.budget P (P+1) V (sumCost S P) bits)
    ∃ actual,runFrom (FamilySupportFromPolicy.machine (FamilySupport.Actual sym k q) e E K source count raw policy)
      fuel ⟨(FamilySupportFromPolicy.machine (FamilySupport.Actual sym k q) e E K source count raw policy).start,
        FamilySupportFromPolicy.heads E cursor supports,FamilySupportFromPolicy.input E data supports⟩=some actual ∧
      actual.steps≤fuel ∧
      actual.final.heads (FamilySupportCall.slots (fields e E source count raw policy) 724)=0 ∧
      actual.final.tapes (FamilySupportCall.slots (fields e E source count raw policy) 724)=
        [FamilyCold.passed sym V C T R W L q bits arity] ∧
      (∀ i,(∀ j,fields e E source count raw policy j≠FamilyCapacity.Call.old E i)→
        actual.final.heads (FamilySupportCall.old (FamilyCapacity.Call.old E i))=cursor i ∧
        actual.final.tapes (FamilySupportCall.old (FamilyCapacity.Call.old E i))=data i) ∧
      (FamilyCold.passed sym V C T R W L q bits arity=true→
        FamilySupport.retained sym P V C T R W L k q bits supports
          (actual.final.heads ∘ FamilySupportCall.slots (fields e E source count raw policy))
          (actual.final.tapes ∘ FamilySupportCall.slots (fields e E source count raw policy))) := by
  let P:=FamilyCapacity.value E K N
  let T:=LegalPolicy.T delta copies q0 cb
  let W:=LegalPolicy.W e den R
  let L:=DescriptionPolicy.value sym R q0 W
  let arity:=SignedSortKey.binary (natBitLength R) R
  let ambient:=LegalTemplate.project e (data ∘ policy)
  let oldFuel:=FamilyCapacity.budget E K N+1+FamilyCold.budget P (P+1) V (sumCost S P) bits
  obtain ⟨inner,ir,_is,ih,it,good⟩:=FamilySupport.family_run sym S P V C T R W L k q bits supports ambient
    hf hlen hv hcore hC hpolicy.store hq hk hp hd
  obtain ⟨actual,run,steps,localFields,away⟩:=FamilySupportFromPolicy.family_run (FamilySupport.Actual sym k q)
    e E K N den copies R q0 cb V C
    (FamilyCold.budget P (P+1) V (CloseoutRowsSupportStream.FamilyCosts.sumCost S P) bits) delta sym
    source count raw policy data cursor bits supports hK injective hne hc hr hN hNh hV hVh hraw hrawh
    hpolicy hph inner ir
  have bound:=SupportCostRatio.cold_budget_le S P (P+1) V (FamilyCapacity.budget E K N+1) bits hP
  let newFuel:=FamilyCapacity.budget E K N+1+FamilyCold.budget P (P+1) V
    (CloseoutRowsSupportStream.FamilyCosts.sumCost S P) bits
  have paid:=runFrom_moreFuel _ newFuel (2*oldFuel-newFuel) _ actual run
  rw [Nat.add_sub_of_le bound] at paid
  refine ⟨actual,paid,steps.trans bound,(localFields 724).1.trans ih,(localFields 724).2.trans it,away,?_⟩
  intro accepted
  have heads:actual.final.heads ∘ FamilySupportCall.slots (fields e E source count raw policy)=inner.final.heads:=
    funext (fun i=>(localFields i).1)
  have tapes:actual.final.tapes ∘ FamilySupportCall.slots (fields e E source count raw policy)=inner.final.tapes:=
    funext (fun i=>(localFields i).2)
  rw [heads,tapes]
  exact good accepted

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupportActual
