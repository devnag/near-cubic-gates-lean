import Proof.CaseAnalysis.WitnessDAGFields
import Proof.PCP.PCPPNativeHeader

/-! The actual hierarchy arity and the same literal traversal count supply
the original oracle's native header. Reuse the total existing header writer;
no binary count conversion or new natural serializer is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGHeader
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 3→Fin 37:=![1,2,3]
def headerSlots (i : Fin 35) : Fin 37:=if i=0 then 0 else if i=1 then 2 else ⟨i.val+2,by omega⟩
theorem copy_injective : Function.Injective copySlots:=by decide
theorem header_injective : Function.Injective headerSlots:=by decide
def input (arity count : ℕ) (i : Fin 37) : List Bool:=
  if i=0 then List.replicate arity true
  else if i=1 then RepairSource.VerifierDecoding.CompareMachine.word count else []
noncomputable def copied (arity count : ℕ):=
  install copySlots (input arity count) (UWalkUnary.result false false 0 count)
noncomputable def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
noncomputable def header:=RecoveryFocus.machine headerSlots PCPPNativeColdHeader.machine
noncomputable def machine:=Composition.machine copy header
def budget (arity count : ℕ):=2*count+6+1+PCPPNativeColdHeader.budget arity count

theorem copy_ready (arity count : ℕ) :
    ClockJoin.ReadyRun copy (2*count+6) (input arity count) (copied arity count):=
  (UWalkUnary.ready false false 0 count).focus copySlots copy_injective (input arity count)
    (by intro i;fin_cases i <;> simp [input,copySlots,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero])

theorem header_input (arity count : ℕ) :
    ∀ i,copied arity count (headerSlots i)=PCPPNativeColdHeader.data arity count [] i:=by
  intro i
  by_cases h0:i=0
  · subst i
    rw [copied,install_other _ _ _ _ (by decide)]
    rfl
  by_cases h1:i=1
  · subst i
    change install copySlots _ _ (copySlots 1)=_
    rw [install_slot _ copy_injective]
    simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,PCPPNativeColdHeader.data]
  have hv:(headerSlots i).val=i.val+2:=by simp [headerSlots,h0,h1]
  have hi0:i.val≠0:=by intro h;exact h0 (Fin.ext h)
  have hi1:i.val≠1:=by intro h;exact h1 (Fin.ext h)
  rw [copied,install_other _ _ _ _ (by
    intro j h
    have he:=congrArg Fin.val h
    rw [hv] at he
    fin_cases j <;> simp [copySlots] at he <;> omega)]
  simp [input,PCPPNativeColdHeader.data,h0,h1,show headerSlots i≠0 by apply Fin.ne_of_val_ne;omega,
    show headerSlots i≠1 by apply Fin.ne_of_val_ne;omega]

theorem header_run (arity count : ℕ) : ∃ actual,
    run machine (budget arity count) (input arity count)=some actual ∧
      actual.steps≤budget arity count ∧
      actual.final.tapes 20=natWord arity++natWord count ∧
      actual.final.heads 20=(natWord arity++natWord count).length ∧
      actual.final.tapes 1=RepairSource.VerifierDecoding.CompareMachine.word count ∧
      actual.final.heads 1=0 ∧
      actual.final.tapes 4=List.replicate arity true ∧ actual.final.heads 4=0 ∧
      actual.final.tapes 21=List.replicate count true ∧ actual.final.heads 21=0:=by
  obtain ⟨a,ha,atape,ah,as⟩:=copy_ready arity count
  obtain ⟨base,hbase,bs,bo,bh,bq,bqh,bk,bkh⟩:=PCPPNativeColdHeader.append_run arity count []
  obtain ⟨b,hb,_,bt,bheads,btapes,bkeep⟩:=RecoveryFocus.dock headerSlots header_injective
    PCPPNativeColdHeader.machine _ a.final.heads a.final.tapes _
    (by intro j;rw [ah];simp [PCPPNativeColdHeader.entry,PCPPNativeColdHeader.heads])
    (by intro j;rw [atape];exact header_input arity count j) base hbase
  have h:=Composition.run_join copy header _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤budget arity count
    unfold budget
    omega
  · exact (btapes 18).trans (by simpa only [PCPPNativeColdHeader.emitted,List.nil_append] using bo)
  · exact (bheads 18).trans (by simpa only [PCPPNativeColdHeader.emitted,List.nil_append] using bh)
  · change b.final.tapes 1=RepairSource.VerifierDecoding.CompareMachine.word count
    rw [(bkeep 1 (by decide)).2,atape]
    change install copySlots _ _ (copySlots 0)=_
    rw [install_slot _ copy_injective]
    simp [UWalkUnary.result,UWalkUnary.source,ZeroPadding.pad_zero]
  · exact ((bkeep 1 (by decide)).1).trans (ah 1)
  · exact (btapes 2).trans bq
  · exact (bheads 2).trans bqh
  · exact (btapes 19).trans bk
  · exact (bheads 19).trans bkh

theorem budget_bound (arity count : ℕ) : budget arity count≤2048*(arity+count+1)^2:=by
  have h:=PCPPNativeColdHeader.budget_bound arity count
  unfold budget
  nlinarith [Nat.zero_le (arity*count),Nat.zero_le (arity*arity),Nat.zero_le (count*count)]

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGHeader
