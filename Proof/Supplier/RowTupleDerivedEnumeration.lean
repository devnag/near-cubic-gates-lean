import Proof.Supplier.RowTupleLimit

/-! The complete tuple enumerator now derives its terminal field and extent
from the runtime width and degree. The only supplied metadata are width,
degree and the actual cache-size bound; no exponential-length driver is input. -/
namespace NearCubicWires.RepairOrdinary.RowTupleDerivedEnumeration
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w k M : ℕ) : Fin 40→List Bool := fun i=>
  if i=2 then CompareMachine.word w else
  if i=3 then frame (binary w (M-1)) else
  if i=12 then CompareMachine.word k else
  if i=18 then List.replicate w true else []
def productSlots : Fin 4→Fin 40 := ![18,12,29,30]
def limitSlots : Fin 12→Fin 40 := ![29,14,31,32,33,34,35,36,37,38,25,39]
def rowSlots (i : Fin 29) : Fin 40 := i.castAdd 11
theorem product_injective : Function.Injective productSlots := by decide
theorem limit_injective : Function.Injective limitSlots := by decide
theorem row_injective : Function.Injective rowSlots := by
  intro i j h; exact Fin.ext (congrArg (fun a : Fin 40=>a.val) h)
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def limit := RecoveryFocus.machine limitSlots RowTupleLimit.machine
noncomputable def metadata := Composition.machine product limit
noncomputable def enumeration := RecoveryFocus.machine rowSlots RowTupleColdEnumeration.machine
noncomputable def machine := Composition.machine metadata enumeration
def productTime (w k : ℕ) := 2*(w*(2*k+3)+2)+2
def metadataTime (w k : ℕ) := productTime w k+1+RowTupleLimit.budget (w*k)
def budget (w k : ℕ) := metadataTime w k+1+RowTupleColdEnumeration.budget w k
def productInput (w k : ℕ) : Fin 4→List Bool :=
  ![List.replicate w true,CompareMachine.word k,[],[]]
def productOutput (w k : ℕ) : Fin 4→List Bool :=
  ![List.replicate w true,CompareMachine.word k,List.replicate (w*k) true,
    List.replicate (w*(2*k+3)+2) false]

theorem product_ready (w k : ℕ) : ClockJoin.ReadyRun ClockUnaryProduct.machine
    (productTime w k) (productInput w k) (productOutput w k) := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run w k
  have hi : Fin.addCases (motive := fun _ : Fin (3+1)=>List Bool)
      ![List.replicate w true,false::List.replicate k true,[]] (fun _ : Fin 1=>[])=productInput w k := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i; fin_cases i <;> simp [productOutput,h0,h1,h2,h3,CompareMachine.word]

theorem metadata_run (w k M : ℕ) : ∃ out,
    ClockJoin.ReadyRun metadata (metadataTime w k) (input w k M) out ∧
      ∀ i,out (rowSlots i)=RowTupleColdFields.input w k M i := by
  obtain ⟨p,hp,_,p1,p10⟩ := RowTupleLimit.limit_run (w*k)
  have h1 := bounded_focus productSlots product_injective _ _ _ (product_ready w k) (input w k M)
    (by intro i; fin_cases i <;> rfl)
  let a := install productSlots (input w k M) (productOutput w k)
  have h2 := bounded_focus limitSlots limit_injective _ _ _ hp a (by
    intro i; fin_cases i
    · exact install_slot productSlots product_injective _ _ 2
    all_goals
      change install productSlots (input w k M) (productOutput w k) (limitSlots _) = []
      rw [install_other _ _ _ _ (by decide)]
      rfl)
  have hwhole := ClockJoin.join product limit _ _ _ _ _ h1 h2
  refine ⟨install limitSlots a p,hwhole,?_⟩
  intro i
  fin_cases i
  all_goals first
    | exact (install_slot limitSlots limit_injective a p 1).trans p1
    | exact (install_slot limitSlots limit_injective a p 10).trans p10
    | (rw [install_other _ _ _ _ (by decide)]
       first
         | exact install_slot productSlots product_injective _ _ 0
         | exact install_slot productSlots product_injective _ _ 1
         | (change install productSlots (input w k M) (productOutput w k) (rowSlots _)=_
            rw [install_other _ _ _ _ (by decide)]
            rfl))

theorem enumerate_run (w k M : ℕ) (hM : 0<M) (hMw : M≤2^w) :
    ∃ r,run machine (budget w k) (input w k M)=some r ∧
      r.final.tapes 17=RowTupleEnumeration.word w k M ∧
      r.final.heads 17=(RowTupleEnumeration.word w k M).length ∧ r.steps≤budget w k := by
  obtain ⟨middle,⟨a,ha,atapes,ah,as⟩,hcore⟩ := metadata_run w k M
  obtain ⟨base,hbase,_,b17,_,bh17,_⟩ := RowTupleColdEnumeration.enumerate_run w k M hM hMw
  obtain ⟨b,hb,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective RowTupleColdEnumeration.machine
    (fun _=>0) middle _ _ base hbase
  have hi : RecoveryFocus.config rowSlots (fun _=>0) middle
      (initialConfiguration RowTupleColdEnumeration.machine (RowTupleColdFields.input w k M))=
      Composition.restart a.final enumeration.start := by
    rw [show Composition.restart a.final enumeration.start=initialConfiguration enumeration middle from by
      apply configuration_ext
      · rfl
      · funext i; exact ah i
      · exact atapes]
    apply WilliamsSourceCrop.focus_same rowSlots (initialConfiguration enumeration middle)
    · intro i; rfl
    · exact hcore
  rw [hi] at hb
  have hwhole := Composition.run_join metadata enumeration _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,hwhole,?_,?_,runFrom_steps_le machine _ _ _ hwhole⟩
  · change b.final.tapes (rowSlots 17)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    exact b17
  · change b.final.heads (rowSlots 17)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    exact bh17

end NearCubicWires.RepairOrdinary.RowTupleDerivedEnumeration
