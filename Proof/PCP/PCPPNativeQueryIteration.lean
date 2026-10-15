import Proof.PCP.PCPPNativeQueryIterationLoad

/-! One complete iteration loads its original projection row, emits the
exact query DAG, advances its actual base, and clears all local work. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryIteration
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n r : ℕ} (base C F G : ℕ) (oracle : BooleanCircuit n) (projection : Fin n → ProjectedRandomBit r) : Prop :=
  PCPPNativeNodeLoop.workspace base 0 C F projection oracle.nodes ∧
    PCPPNativeAddressAppend.budget base oracle.output.val+1 ≤ C ∧ base+2*oracle.size+1 ≤ F ∧
    PCPPNativeQueryStep.budget base C F oracle+1 ≤ G ∧ (rowCache projection).length+3*n+4 ≤ G
def budget {n r : ℕ} (base C F G : ℕ) (oracle : BooleanCircuit n) (projection : Fin n → ProjectedRandomBit r) :=
  PCPPNativeQueryRowLoad.budget (rowFields projection)+1+PCPPNativeQueryReusable.budget base C F G oracle

theorem iteration_run {n r : ℕ} (pre suffix : List Bool) (base C F G : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hFG : F+1 ≤ G) (hcap : capacity base C F G oracle projection) :
    ∃ result,runFrom machine (budget base C F G oracle projection)
      (entry (PCPPNative.descriptor oracle) (pre++rowCache projection++suffix) pre.length base C F G out n)=some result ∧
      result.steps ≤ budget base C F G oracle projection ∧
      result.final.heads=heads (pre.length+(rowCache projection).length) (out++PCPPNativeQuery.emitted base oracle projection) ∧
      result.final.tapes=data (PCPPNative.descriptor oracle) [] (pre++rowCache projection++suffix)
        (base+2*oracle.size+1) C F G (out++PCPPNativeQuery.emitted base oracle projection) n := by
  rcases hcap with ⟨hw,hC,hF,hG,hload⟩
  obtain ⟨a,ha,as,alow,ap,atapes,an,ant⟩ := load_run pre suffix (PCPPNative.descriptor oracle) base C F G projection out hload
  obtain ⟨raw,hr,rs,rh,rt⟩ := PCPPNativeQueryReusable.query_run base C F G oracle projection out hCF hw hC hF hG hFG (by omega)
  obtain ⟨b,hb,_,bs,bh,bt,bkeep⟩ := RecoveryFocus.dock querySlots query_injective PCPPNativeQueryReusable.machine _
    a.final.heads a.final.tapes _ (fun j => (alow j).1) (fun j => (alow j).2) raw hr
  let result := Composition.joinedReceipt a b
  have run := Composition.run_join load query _ _ _ a b ha hb
  have keep171 := bkeep 171 (by intro j; apply Fin.ne_of_val_ne; change j.val≠171; omega)
  have keep172 := bkeep 172 (by intro j; apply Fin.ne_of_val_ne; change j.val≠172; omega)
  refine ⟨result,run,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega
  · change b.final.heads=_
    funext i
    refine Fin.addCases (m := 171) (n := 2) (fun j => ?_) (fun j => ?_) i
    · simp only [heads,Fin.addCases_left]
      exact (bh j).trans (congrFun rh j)
    · fin_cases j
      · exact keep171.1.trans ap
      · exact keep172.1.trans an
  · change b.final.tapes=_
    funext i
    refine Fin.addCases (m := 171) (n := 2) (fun j => ?_) (fun j => ?_) i
    · simp only [data,Fin.addCases_left]
      exact (bt j).trans (congrFun rt j)
    · fin_cases j
      · exact keep171.2.trans atapes
      · exact keep172.2.trans ant

theorem budget_bound {n r : ℕ} (base C F G : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (hcap : capacity base C F G oracle projection) :
    budget base C F G oracle projection ≤ 6*G+6 := by
  rcases hcap with ⟨_hw,_hC,_hF,hG,hload⟩
  have hlen : (rowFields projection).length=n := by simp only [rowFields,List.length_ofFn]
  unfold budget PCPPNativeQueryRowLoad.budget PCPPNativeQueryReusable.budget
  rw [hlen]
  change 2*((rowCache projection).length+3*n+3)+2+1+
    (2*PCPPNativeQueryStep.budget base C F oracle+2*G+7) ≤ 6*G+6
  omega

end NearCubicWires.RepairOrdinary.PCPPNativeQueryIteration
