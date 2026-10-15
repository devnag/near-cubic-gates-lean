import Proof.PCP.PCPSerializerReuseBudget
import Proof.PCP.ProjectionNormalizationProduct

namespace NearCubicWires.RepairOrdinary.PCPTripleCount
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (M : ℕ) : Fin 5 → List Bool := ![CompareMachine.word M,[],[],[],[]]
def firstHeads : Fin 5 → ℕ := ![1,0,0,0,0]
def finalHeads : Fin 5 → ℕ := ![1,0,0,1,0]
def retreat : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some
    ⟨1,fun _ => none,fun i => if i=0 then .left else .stay⟩ else none
def printSlots : Fin 2 → Fin 5 := ![1,2]
def productSlots : Fin 4 → Fin 5 := ![1,0,3,4]
theorem print_injective : Function.Injective printSlots := by decide
theorem product_injective : Function.Injective productSlots := by decide
noncomputable def printer := RecoveryFocus.machine printSlots (HierarchyFixedWord.machine [true,true,true])
noncomputable def product := RecoveryFocus.machine productSlots Product.machine
noncomputable def tail := Composition.machine printer product
noncomputable def machine := Composition.machine retreat tail
noncomputable def entry (M : ℕ) :=
  (⟨machine.start,firstHeads,input M⟩ : Configuration 5 _)
def printed (M : ℕ) : Fin 5 → List Bool :=
  ![CompareMachine.word M,[true,true,true],[false,false,false],[],[]]

theorem retreat_run (M : ℕ) : ∃ r,runFrom retreat 1 ⟨0,firstHeads,input M⟩=some r ∧
    r.final=⟨1,fun _ => 0,input M⟩ ∧ r.steps=1 := by
  have hs : step retreat ⟨0,firstHeads,input M⟩=some ⟨1,fun _ => 0,input M⟩ := by
    simp only [step,retreat,Fin.val_zero,ite_true,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem print_run (M : ℕ) : ∃ r,run printer 8 (input M)=some r ∧
    r.final.heads=(fun _ => 0) ∧ r.final.tapes=printed M ∧ r.steps=8 := by
  obtain ⟨r,hr,ht,hh,hs⟩ := (HierarchyFixedWord.word_ready [true,true,true]).focus
    printSlots print_injective (input M) (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,funext hh,?_,hs⟩
  rw [ht]
  funext i
  fin_cases i
  · exact install_other printSlots _ _ 0 (by decide)
  · exact install_slot printSlots print_injective _ _ 0
  · exact install_slot printSlots print_injective _ _ 1
  · exact install_other printSlots _ _ 3 (by decide)
  · exact install_other printSlots _ _ 4 (by decide)

theorem product_run (M : ℕ) : ∃ r,run product (Product.budget 3 M) (printed M)=some r ∧
    r.final.heads=finalHeads ∧ r.final.tapes 0=CompareMachine.word M ∧
    r.final.tapes 3=CompareMachine.word (3*M) ∧ r.steps=Product.budget 3 M := by
  obtain ⟨base,hb,_,b1,b2,bh,bs⟩ := Product.product_run 3 M
  obtain ⟨r,hr,hf,hs⟩ := RecoveryFocus.run_config productSlots product_injective Product.machine
    (fun _ => 0) (printed M) _ _ base hb
  have hi : RecoveryFocus.config productSlots (fun _ => 0) (printed M)
      (initialConfiguration Product.machine (Product.input 3 M))=
      initialConfiguration product (printed M) := by
    exact WilliamsSourceCrop.focus_same productSlots (initialConfiguration product (printed M))
      (initialConfiguration Product.machine (Product.input 3 M))
      (by intro j; rfl) (by intro j; fin_cases j <;> rfl)
  rw [hi] at hr
  have localT (j : Fin 4) : r.final.tapes (productSlots j)=base.final.tapes j := by
    simp only [hf,RecoveryFocus.config,RecoveryFocus.pick_slot productSlots product_injective]
  refine ⟨r,hr,?_,(localT 1).trans b1,(localT 2).trans b2,hs.trans bs⟩
  funext i
  cases hp : RecoveryFocus.pick productSlots i with
  | none =>
    have hn0 : i≠0 := by
      intro he; subst i
      have h : RecoveryFocus.pick productSlots 0=some 1 :=
        RecoveryFocus.pick_slot productSlots product_injective 1
      rw [hp] at h; contradiction
    have hn3 : i≠3 := by
      intro he; subst i
      have h : RecoveryFocus.pick productSlots 3=some 2 :=
        RecoveryFocus.pick_slot productSlots product_injective 2
      rw [hp] at h; contradiction
    simp only [hf,RecoveryFocus.config,hp]
    fin_cases i <;> first | contradiction | rfl
  | some j =>
    have he := RecoveryFocus.slot_of_pick productSlots hp
    rw [←he,hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot productSlots product_injective,bh]
    fin_cases j <;> rfl

theorem count_run (M : ℕ) : ∃ r,runFrom machine (12*M+41) (entry M)=some r ∧
    r.final.heads=finalHeads ∧ r.final.tapes 0=CompareMachine.word M ∧
    r.final.tapes 3=CompareMachine.word (3*M) ∧ r.steps=12*M+41 := by
  obtain ⟨a,ha,af,as⟩ := retreat_run M
  obtain ⟨b,hb,bh,bt,bs⟩ := print_run M
  obtain ⟨c,hc,ch,c0,c3,cs⟩ := product_run M
  have hc' : runFrom product (Product.budget 3 M) (Composition.restart b.final product.start)=some c := by
    have he : Composition.restart b.final product.start=initialConfiguration product (printed M) := by
      apply configuration_ext
      · rfl
      · exact bh
      · exact bt
    rw [he]
    exact hc
  have hbc := Composition.run_join printer product _ _ _ b c hb hc'
  have he : Composition.leftConfig _ (initialConfiguration printer (input M))=
      Composition.restart a.final tail.start := by rw [af]; rfl
  rw [he] at hbc
  have joined := Composition.run_join retreat tail _ _ _ a (Composition.joinedReceipt b c) ha hbc
  have ht : 1+1+(8+1+Product.budget 3 M)=12*M+41 := by unfold Product.budget; omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt a (Composition.joinedReceipt b c),joined,ch,c0,c3,?_⟩
  change a.steps+1+(b.steps+1+c.steps)=_
  rw [as,bs,cs]
  exact ht

end NearCubicWires.RepairOrdinary.PCPTripleCount
