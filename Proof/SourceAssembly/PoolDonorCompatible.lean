import Proof.Rows.RowsPoolMinimumPaper
import Proof.Rows.RowsPoolRequestWriter
import Proof.Rows.ClosureConstantGate
import Proof.Rows.ClosureReusable48
import Proof.Rows.ClosureConstantGateReusable
import Proof.MachineModel.Semantics
import Proof.Assembly.RowsPoolMinimumLoop
import Proof.Assembly.ClosureHardwireChild
import Proof.Assembly.ClosureHardwireReusable
import Proof.Assembly.AppendOutputFrame
import Proof.CaseAnalysis.CaseTwoTraversalForward
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsTupleSeekFrame
import Proof.CaseAnalysis.RowsUniversalPool
import Proof.Hierarchy.CompetitorFrameAppend
import Proof.Circuits.DecompositionSourceRecords
import Proof.Amplification.RecoveryScratchErase
import Proof.MachineModel.UInputFields

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGateFrame
open LocalBitMultitape RepairOrdinary RepairSource.ProjectionNormalization
open RepairSource.CloseoutFinal

theorem field_forward (keep : Bool) : CursorRestore.NoLeft (PCPPQueryField.machine keep) 2 := by
  intro q bs a ha
  fin_cases q <;> simp [PCPPQueryField.machine] at ha
  all_goals first
    | (split at ha <;> cases ha <;> cases keep <;> simp)
    | (cases ha; cases keep <;> simp)

theorem signed_field_forward : CursorRestore.NoLeft DecompositionSource.Fields.machine 2 := by
  apply CursorRestore.composition_forward
  · intro q bs a ha
    cases ha
    change HeadMove.right ≠ HeadMove.left
    decide
  · exact field_forward true

theorem skipped_field_forward : CursorRestore.NoLeft RowNativeFieldSkip.machine 2 := by
  apply CursorRestore.composition_forward
  · intro q bs a ha
    cases ha
    decide
  · exact field_forward false

theorem weight_choice_forward : CursorRestore.NoLeft CloseoutRowsPoolWeight.choice 2 := by
  apply EquationCut.calls_forward
  intro j
  fin_cases j
  · intro q bs a ha; cases ha
  · exact EquationRowCuts.embedded_forward 1 _ 2 signed_field_forward
  · apply CursorRestore.composition_forward
    · exact EquationRowCuts.embedded_forward 1 _ 2 skipped_field_forward
    · exact CursorRestore.focus_forward CloseoutRowsPoolWeight.zeroSlots (by decide)
        _ 0 (PCPPNativeForward.literal _)

theorem weight_body_forward : CursorRestore.NoLeft CloseoutRowsPoolWeight.body 2 := by
  apply CursorRestore.composition_forward
  · exact weight_choice_forward
  · intro q bs a ha
    cases ha
    decide

theorem weights_forward : CursorRestore.NoLeft ConstantGate.weights 34 :=
  CursorRestore.focus_forward HardwireChild.weightSlots (by decide) _ 2
    (PCPPNativeForward.masked CloseoutRowsPoolWeight.loop HardwireChild.resetWeights 2 (by decide)
      (CursorRestore.repeat_forward CloseoutRowsPoolWeight.body (fun _ _=>true) 2 weight_body_forward))

theorem target_writer_forward : CursorRestore.NoLeft C10NaturalHardwireTarget.writer 15 := by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · apply CursorRestore.composition_forward
      · exact EquationRowRaw.embedded_extra_forward CloseoutRowsPoolSigned.machine (0 : Fin 5)
      · exact EquationRowCuts.unselected_forward C10NaturalHardwireTarget.frameSlots _ 15 (by decide)
    · apply CursorRestore.focus_forward C10NaturalHardwireTarget.signSlots (by decide) _ 3
      intro q bs a ha
      fin_cases q <;> simp [CloseoutRowsSignedAppend.sign] at ha <;> cases ha <;> simp
  · exact CursorRestore.focus_forward C10NaturalHardwireTarget.copySlots (by decide) _ 2
      CloseoutCaseTwo.Traversal.native_copy_forward

theorem target_forward : CursorRestore.NoLeft C10NaturalHardwireTarget.machine 34 := by
  apply CursorRestore.composition_forward
  · exact EquationRowRaw.embedded_extra_forward C10NaturalHardwireTarget.pairMachine (13 : Fin 18)
  · exact CursorRestore.focus_forward C10NaturalHardwireTarget.writerSlots (by decide) _ 15
      target_writer_forward

theorem forward : CursorRestore.NoLeft ConstantGate.machine 34 := by
  apply CursorRestore.composition_forward
  · exact weights_forward
  · apply EquationRowCuts.embedded_forward 4 _ 34
    apply CursorRestore.composition_forward
    · exact EquationRowCuts.unselected_forward C10NaturalHardwireScoreInputs.negativeSlots _ 34 (by decide)
    · exact EquationRowCuts.embedded_forward 5 _ 34 target_forward

end NearCubicWires.P1Closure.ConstantGateFrame

end

section

/-! The actual framed frozen native gate request. The arity prefix is
copied from its runtime native field, and the shifted strict threshold is
computed from original signed fields and membership. The existing measured
output framer physically writes the outer frame and restores every head. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGateFrame
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization CloseoutRowsPoolWeight
open SupplierPipeline

def aritySlots : Fin 4 → Fin 51 := ![48,49,34,50]
noncomputable def arity := RecoveryFocus.machine aritySlots CloseoutCaseTwo.NativeCopy.machine
def extra (q C : Nat) : Fin 3 → List Bool :=
  ![ZeroPadding.pad C (natWord q),List.replicate C false,List.replicate C false]
def copiedExtra (q C : Nat) : Fin 3 → List Bool :=
  ![ZeroPadding.pad C (natWord q),StablePartition.Workspace.overlay
    (UnaryTemplate.tape (natBitLength q)) (List.replicate C false),List.replicate C false]
def input (xs : List Item) (z : Int) (tail backing : List Bool) (w C D E : Nat) : Fin 51 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool) (ConstantGate.data xs z tail backing [] w C D E)
    (extra xs.length C)
def middle (xs : List Item) (z : Int) (tail backing : List Bool) (w C D E : Nat) : Fin 51 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (ConstantGate.data xs z tail backing (natWord xs.length) w C D E) (copiedExtra xs.length C)
def rawHeads (out : List Bool) (pos mpos : Nat) : Fin 51 → Nat :=
  Fin.addCases (motive:=fun _=>Nat) (HardwireChild.heads out pos mpos) (fun _ : Fin 3=>0)
def position : Machine 51 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>decide (q=1)
  rule := fun q _=>if q=0 then
    some ⟨1,fun _=>none,fun i=>if i=42 ∨ i=46 then .right else .stay⟩ else none
noncomputable def raw := Composition.machine (Composition.machine position arity)
  (TapeEmbedding.machine 3 ConstantGate.machine)
def rawBudget (xs : List Item) (z : Int) (w C : Nat) :=
  CloseoutCaseTwo.NativeCopy.budget xs.length+ConstantGate.budget xs z w C+3
def native (xs : List Item) (z : Int) := natWord xs.length++emitted xs++
  intWord (z+CloseoutRowsPoolMinimum.liveSum xs)

theorem position_run (A : Fin 51 → List Bool) :
    Step position 1 (fun _=>0) A (rawHeads [] 0 0) A := by
  have h : step position (⟨position.start,fun _=>0,A⟩ : Configuration 51 2)=
      some ⟨1,rawHeads [] 0 0,A⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) h).run rfl
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

set_option maxHeartbeats 800000 in
theorem arity_run (xs : List Item) (z : Int) (tail backing : List Bool) (w C D E : Nat)
    (hC : 2*natBitLength xs.length+3≤C) :
    Step arity (CloseoutCaseTwo.NativeCopy.budget xs.length)
      (rawHeads [] 0 0) (input xs z tail backing w C D E)
      (rawHeads (natWord xs.length) 0 0) (middle xs z tail backing w C D E) := by
  obtain ⟨r,hr,ht,hh,_⟩ := CloseoutCaseTwo.NativeCopy.append_run xs.length C [] hC
  have h := (Step.of_run hr hh ht).dock aritySlots (by decide)
    (rawHeads [] 0 0) (input xs z tail backing w C D E)
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl)
  refine h.congr ?_ ?_
  · funext i
    fin_cases i <;> first
      | exact dockH_slot aritySlots (by decide) _ _ 0
      | exact dockH_slot aritySlots (by decide) _ _ 1
      | exact dockH_slot aritySlots (by decide) _ _ 2
      | exact dockH_slot aritySlots (by decide) _ _ 3
      | exact dockH_other aritySlots _ _ _ (by decide)
  · apply HierarchyAllocation.install_eq aritySlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact False.elim (hi 2 rfl) | exact False.elim (hi 1 rfl)

theorem raw_run (xs : List Item) (z : Int) (tail backing : List Bool) (w C D E : Nat)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hn : CloseoutRowsPoolMinimum.negSum xs<2^w) (hz : natBitLength z.natAbs≤w)
    (hp : C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs)<2^w)
    (hneg : C10NaturalHardwireTarget.nPart z 0<2^w)
    (hE : CloseoutRowsPoolWeight.loopBudget xs≤E) (hC : 2*natBitLength xs.length+3≤C) :
    ∃ result : Fin 51 → List Bool,
      Step raw (rawBudget xs z w C) (fun _=>0) (input xs z tail backing w C D E)
        (rawHeads (native xs z) ((word xs).length+(intWord z).length) xs.length) result ∧
      result 34=native xs z := by
  obtain ⟨result,last,_,ho⟩ := ConstantGate.run xs z tail backing (natWord xs.length) w C D E
    hw hc hn hz hp hneg hE
  have last := last.embed (fun _ : Fin 3=>0) (copiedExtra xs.length C)
  have whole := ((position_run _).seq (arity_run xs z tail backing w C D E hC)).seq last
  have hb : 1+1+CloseoutCaseTwo.NativeCopy.budget xs.length+1+ConstantGate.budget xs z w C=
      rawBudget xs z w C := by unfold rawBudget;omega
  refine ⟨_,by simpa only [raw,hb,rawHeads,native] using whole,?_⟩
  exact ho

theorem raw_forward : CursorRestore.NoLeft raw 34 := by
  apply CursorRestore.composition_forward
  · apply CursorRestore.composition_forward
    · intro q bs a ha
      fin_cases q <;> simp [position] at ha
      cases ha
      decide
    · exact CursorRestore.focus_forward aritySlots (by decide) _ 2
        CloseoutCaseTwo.Traversal.native_copy_forward
  · exact EquationRowCuts.embedded_forward 3 _ 34 forward

noncomputable def machine := AppendOutputFrame.machine raw (34 : Fin 51)
def budget (xs : List Item) (z : Int) (w C : Nat) :=
  6*rawBudget xs z w C+7

theorem frame_run (xs : List Item) (z : Int) (tail backing : List Bool) (w C D E : Nat)
    (hw : ∀ x∈xs,natBitLength x.1.natAbs≤w) (hc : 8*w+12≤C)
    (hn : CloseoutRowsPoolMinimum.negSum xs<2^w) (hz : natBitLength z.natAbs≤w)
    (hp : C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs)<2^w)
    (hneg : C10NaturalHardwireTarget.nPart z 0<2^w)
    (hE : CloseoutRowsPoolWeight.loopBudget xs≤E) (hC : 2*natBitLength xs.length+3≤C) :
    ∃ result : Fin 55 → List Bool,
      Step machine (budget xs z w C) (fun _=>0)
        (AppendOutputFrame.input (input xs z tail backing w C D E)) (fun _=>0) result ∧
      result 53=RepairOrdinary.frame (native xs z) := by
  obtain ⟨_,⟨source,hs,hh,ht,ss⟩,ho⟩ := raw_run xs z tail backing w C D E hw hc hn hz hp hneg hE hC
  obtain ⟨r,hr,rf,rh,_⟩ := AppendOutputFrame.frame_run raw 34 raw_forward
    (rawBudget xs z w C) (input xs z tail backing w C D E) source hs (native xs z)
    ((congrFun ht 34).trans ho) (by rw [hh];rfl)
  have len := SelectiveReset.prefix_head (prefix_of_run raw (rawBudget xs z w C) _ source hs).1
    (34 : Fin 51)
  rw [hh] at len
  change (native xs z).length≤0+source.steps at len
  have small : 2*source.steps+4*(native xs z).length+7≤budget xs z w C := by unfold budget;omega
  exact ⟨r.final.tapes,(Step.of_run hr (funext rh) rfl).enlarge small,rf⟩

theorem constant_native {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    native (CloseoutRowsPoolMinimum.items g.gate live) (g.gate.threshold-1)=
      CloseoutRowsCircuitBottom.nativeWord (RepairSource.CloseoutRowsUniversal.constantSupportedGate live g) := by
  rw [ConstantGate.constant_fields]
  simp only [native,CloseoutRowsPoolMinimum.items_length]

theorem constant_run {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (tail backing : List Bool) (w C D E : Nat)
    (hw : ∀ x∈CloseoutRowsPoolMinimum.items g.gate live,natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C)
    (hn : CloseoutRowsPoolMinimum.negSum (CloseoutRowsPoolMinimum.items g.gate live)<2^w)
    (hz : natBitLength (g.gate.threshold-1).natAbs≤w)
    (hp : C10NaturalHardwireTarget.pPart (g.gate.threshold-1)
      (CloseoutRowsPoolMinimum.liveSum (CloseoutRowsPoolMinimum.items g.gate live))<2^w)
    (hneg : C10NaturalHardwireTarget.nPart (g.gate.threshold-1) 0<2^w)
    (hE : CloseoutRowsPoolWeight.loopBudget (CloseoutRowsPoolMinimum.items g.gate live)≤E)
    (hC : 2*natBitLength q+3≤C) :
    ∃ result : Fin 55 → List Bool,
      Step machine (budget (CloseoutRowsPoolMinimum.items g.gate live) (g.gate.threshold-1) w C)
        (fun _=>0) (AppendOutputFrame.input
          (input (CloseoutRowsPoolMinimum.items g.gate live) (g.gate.threshold-1) tail backing w C D E))
        (fun _=>0) result ∧
      result 53=RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord
        (RepairSource.CloseoutRowsUniversal.constantSupportedGate live g)) := by
  obtain ⟨result,hr,ho⟩ := frame_run (CloseoutRowsPoolMinimum.items g.gate live) (g.gate.threshold-1)
    tail backing w C D E hw hc hn hz hp hneg hE
    (by simpa only [CloseoutRowsPoolMinimum.items_length] using hC)
  exact ⟨result,hr,ho.trans (congrArg RepairOrdinary.frame (constant_native live g))⟩

end NearCubicWires.P1Closure.ConstantGateFrame

end

section

/-! Read one original framed native gate into its arity and signed-field
ports. The only semantic source word is the original frame; neither the
field slice nor a transformed gate is supplied as input advice. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryLoad
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource.VerifierDecoding

def word {q : Nat} (g : ExactThresholdGate q) := natWord q++exactWord g
def heads (pos arity fields count : Nat) : Fin 8 → Nat := fun i=>if i=1 then pos else if i=2 then arity else if i=5 then fields else if i=6 then count else 0
def data {q : Nat} (g : ExactThresholdGate q) (raw arity headerBack childBack fields log : List Bool) :
    Fin 8 → List Bool := fun i=>if i=0 then frame (word g) else if i=1 then raw else if i=2 then arity else if i=3 then headerBack else if i=4 then childBack else if i=5 then fields else if i=6 then CompareMachine.word q else if i=7 then log else []
def input {q : Nat} (g : ExactThresholdGate q) (C : Nat) :=
  data g [] (List.replicate C false) [] [] [] []
def output {q : Nat} (g : ExactThresholdGate q) (C : Nat) :=
  data g (word g) (ZeroPadding.pad C (natWord q)) (PCPPQueryField.saved q [])
    (DecompositionSource.Records.childSaved g []) (exactWord g) (List.replicate (word g).length false)
def unwrapSlots : Fin 3 → Fin 8 := ![0,1,7]
theorem unwrap_inj : Function.Injective unwrapSlots := by decide
def headerSlots : Fin 3 → Fin 8 := ![1,3,2]
def recordSlots : Fin 4 → Fin 8 := ![1,4,5,6]
noncomputable def unwrap := RecoveryFocus.machine unwrapSlots Streaming.machine
noncomputable def header := RecoveryFocus.machine headerSlots (PCPPQueryField.machine true)
noncomputable def records := RecoveryFocus.machine recordSlots DecompositionSource.Records.child
def move (right : Bool) : Machine 8 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if i=6 then if right then .right else .left else .stay⟩ else none
noncomputable def raw := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine unwrap header) (move true)) records) (move false)
def rawBudget {q : Nat} (g : ExactThresholdGate q) :=
  4*(word g).length+2*natBitLength q+(exactWord g).length+6*q+18

theorem move_run (right : Bool) (pos arity fields : Nat) (A : Fin 8 → List Bool) :
    Step (move right) 1 (heads pos arity fields (if right then 0 else 1)) A
      (heads pos arity fields (if right then 1 else 0)) A := by
  have h : step (move right)
      (⟨(move right).start,heads pos arity fields (if right then 0 else 1),A⟩ : Configuration 8 2)=
      some ⟨1,heads pos arity fields (if right then 1 else 0),A⟩ := by
    cases right <;> apply congrArg some
    all_goals apply configuration_ext
    all_goals first | rfl | (funext i;fin_cases i <;>rfl)
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by cases right <;>rfl) h).run rfl
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem unwrap_step (bits : List Bool) :
    Step Streaming.machine (4*bits.length+2) (fun _=>0) ![frame bits,[],[]]
      (fun _=>0) ![frame bits,bits,List.replicate bits.length false] := by
  obtain ⟨r,hr,ht,hh,_⟩ := UInputFields.unwrap_ready bits
  exact Step.of_run hr (funext hh) ht

theorem unwrap_run {q : Nat} (g : ExactThresholdGate q) (C : Nat) :
    Step unwrap (4*(word g).length+2) (heads 0 0 0 0) (input g C) (heads 0 0 0 0)
      (data g (word g) (List.replicate C false) [] [] [] (List.replicate (word g).length false)) := by
  have h := (unwrap_step (word g)).dock unwrapSlots unwrap_inj
    (heads 0 0 0 0) (input g C) (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl)
  refine h.congr (dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)) ?_
  apply HierarchyAllocation.install_eq unwrapSlots unwrap_inj
  · intro j;fin_cases j <;>rfl
  · intro i hi
    have h1 : i≠1 := by intro h;subst i;exact hi 1 rfl
    have h7 : i≠7 := by intro h;subst i;exact hi 2 rfl
    simp only [data,input,if_neg h1,if_neg h7]

theorem header_run {q : Nat} (g : ExactThresholdGate q) (C : Nat) :
    Step header (2*natBitLength q+3) (heads 0 0 0 0)
      (data g (word g) (List.replicate C false) [] [] [] (List.replicate (word g).length false))
      (heads (natWord q).length (natWord q).length 0 0)
      (data g (word g) (ZeroPadding.pad C (natWord q)) (PCPPQueryField.saved q []) [] []
        (List.replicate (word g).length false)) := by
  obtain ⟨r,hr,hf,_⟩ := PCPPQueryField.nat_run true [] (exactWord g) [] [] q
  have h := (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).pad
    (![0,0,C] : Fin 3→Nat)
  have small : Step (PCPPQueryField.machine true) (2*natBitLength q+3) (![0,0,0] : Fin 3→Nat)
      ![word g,[],List.replicate C false]
      ![(natWord q).length,0,(natWord q).length]
      ![word g,PCPPQueryField.saved q [],ZeroPadding.pad C (natWord q)] := by
    refine (h.congr_in ?_ ?_).congr ?_ ?_
    all_goals funext i;fin_cases i <;>
      simp [PCPPQueryField.cfg,PCPPQueryField.payload,PCPPQueryField.selected,PCPPQueryField.saved,word,
        ZeroPadding.pad,DecompositionSource.natWord_length]
  have all := small.dock headerSlots (by decide) (heads 0 0 0 0)
    (data g (word g) (List.replicate C false) [] [] [] (List.replicate (word g).length false))
    (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl)
  refine all.congr ?_ ?_
  · funext i;fin_cases i <;> first
      | exact dockH_slot headerSlots (by decide) _ _ 0
      | exact dockH_slot headerSlots (by decide) _ _ 1
      | exact dockH_slot headerSlots (by decide) _ _ 2
      | exact dockH_other headerSlots _ _ _ (by decide)
  · apply HierarchyAllocation.install_eq headerSlots (by decide)
    · intro j;fin_cases j <;>rfl
    · intro i hi;fin_cases i <;>first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)

theorem records_run {q : Nat} (g : ExactThresholdGate q) (C : Nat) :
    Step records ((exactWord g).length+6*q+7)
      (heads (natWord q).length (natWord q).length 0 1)
      (data g (word g) (ZeroPadding.pad C (natWord q)) (PCPPQueryField.saved q []) [] []
        (List.replicate (word g).length false))
      (heads (word g).length (natWord q).length (exactWord g).length 1) (output g C) := by
  obtain ⟨r,hr,hf,_⟩ := DecompositionSource.Records.child_run g (natWord q) [] [] []
  simp only [List.append_nil,List.nil_append] at hr hf
  have h := (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).dock
    recordSlots (by decide) (heads (natWord q).length (natWord q).length 0 1)
    (data g (word g) (ZeroPadding.pad C (natWord q)) (PCPPQueryField.saved q []) [] []
      (List.replicate (word g).length false))
    (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl)
  have hlen : (natWord q).length+(exactWord g).length=(word g).length := by simp [word]
  refine h.congr ?_ ?_
  · funext i;fin_cases i <;> first
      | exact (dockH_slot recordSlots (by decide) _ _ 0).trans hlen
      | exact dockH_slot recordSlots (by decide) _ _ 1
      | exact dockH_slot recordSlots (by decide) _ _ 2
      | exact dockH_slot recordSlots (by decide) _ _ 3
      | exact dockH_other recordSlots _ _ _ (by decide)
  · apply HierarchyAllocation.install_eq recordSlots (by decide)
    · intro j;fin_cases j <;>rfl
    · intro i hi;fin_cases i <;>first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)

theorem raw_run {q : Nat} (g : ExactThresholdGate q) (C : Nat) :
    Step raw (rawBudget g) (heads 0 0 0 0) (input g C)
      (heads (word g).length (natWord q).length (exactWord g).length 0) (output g C) := by
  have all := ((((unwrap_run g C).seq (header_run g C)).seq
    (move_run true (natWord q).length (natWord q).length 0 _)).seq (records_run g C)).seq
    (move_run false (word g).length (natWord q).length (exactWord g).length _)
  have time : 4*(word g).length+2+1+(2*natBitLength q+3)+1+1+1+
      ((exactWord g).length+6*q+7)+1+1=rawBudget g := by unfold rawBudget;omega
  simpa only [raw,time,Bool.false_eq_true,ite_false] using all

def selected (i : Fin 8) := decide (i=2 ∨ i=5)
noncomputable def machine := MaskedReset.machine raw selected
def budget {q : Nat} (g : ExactThresholdGate q) := 2*rawBudget g+2
theorem load_run {q : Nat} (g : ExactThresholdGate q) (C L : Nat) (hL : rawBudget g≤L) :
    Step machine (budget g)
      (fun _ : Fin 9=>0) (Fin.addCases (input g C) (fun _ : Fin 1=>List.replicate L false))
      (![0,(word g).length,0,0,0,0,0,0,0] : Fin 9→Nat)
      (Fin.addCases (output g C) (fun _ : Fin 1=>List.replicate L false)) := by
  have h := (raw_run g C).mask selected (by intro i hi;fin_cases i <;>rfl) hL
  refine (h.congr_in ?_ rfl).congr ?_ rfl
  all_goals funext i;fin_cases i <;>rfl

end NearCubicWires.P1Closure.PoolEntryLoad

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntry
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation RepairSource VerifierDecoding
open SupplierPipeline ProjectionNormalization CompilerSemantics
open scoped BigOperators

def sourceFields {q : Nat} (g : SupportedNormalizedGate q) : ExactThresholdGate q :=
  ⟨g.gate.weight,g.gate.threshold-1⟩

noncomputable def ready {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat) :=
  AppendOutputFrame.input (ConstantGateFrame.input (CloseoutRowsPoolMinimum.items g.gate live)
    (g.gate.threshold-1) [] [] w (ConstantGateReusable.C w) 0 (ConstantGateReusable.E B q))

theorem ready_source {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat) :
    ready live g B w 0=exactWord (sourceFields g) := by
  change CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g.gate live)++intWord (g.gate.threshold-1)++[]=exactWord (sourceFields g)
  simp only [List.append_nil,CloseoutRowsPoolMinimum.items_word];rfl

theorem ready_arity {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat) :
    ready live g B w 48=ZeroPadding.pad (ConstantGateReusable.C w) (natWord q) := by
  change ZeroPadding.pad _ (natWord (CloseoutRowsPoolMinimum.items g.gate live).length)=_
  rw [CloseoutRowsPoolMinimum.items_length]

theorem ready_count {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat) :
    ready live g B w 42=CompareMachine.word q := by
  change CompareMachine.word (CloseoutRowsPoolMinimum.items g.gate live).length=_
  rw [CloseoutRowsPoolMinimum.items_length]

theorem arity_bits (q : Nat) : natBitLength q≤q+1 := by
  unfold natBitLength
  have h := Nat.log_le_self 2 q
  omega

theorem fields_bytes {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B : Nat)
    (hb : (CloseoutRowsCircuitBottom.nativeWord g).length≤B) :
    (CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g.gate live)++intWord (g.gate.threshold-1)++[]).length≤B := by
  have hfields : (exactWord (sourceFields g)).length≤B := by
    rw [CloseoutRowsPoolWriter.original_native,List.append_assoc] at hb
    change (natWord q++exactWord (sourceFields g)).length≤B at hb
    simp only [List.length_append] at hb
    omega
  simpa only [List.append_nil,CloseoutRowsPoolMinimum.items_word,exactWord,sourceFields] using hfields

end NearCubicWires.P1Closure.PoolEntry

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntry
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch

def xSlots : Fin 3 → Fin 64 := ![55,61,62]
def cSlots : Fin 3 → Fin 64 := ![53,61,63]
theorem x_inj : Function.Injective xSlots := by decide
theorem c_inj : Function.Injective cSlots := by decide
noncomputable def appendX := RecoveryFocus.machine xSlots CompetitorFrameAppend.machine
noncomputable def appendC := RecoveryFocus.machine cSlots CompetitorFrameAppend.machine
def heads (pos : Nat) (out : List Bool) : Fin 64 → Nat :=
  fun i=>if i=56 then pos else if i=61 then out.length else 0

theorem append_run (which : Bool) (pos : Nat) (bits out : List Bool) (A : Fin 64→List Bool)
    (hA : ∀ j,A ((if which then cSlots else xSlots) j)=(![frame bits,out,[]] : Fin 3→List Bool) j) :
    Step (if which then appendC else appendX) (4*bits.length+3) (heads pos out) A
      (heads pos (out++frame bits))
      (install (if which then cSlots else xSlots) A
        ![frame bits,out++frame bits,List.replicate (2*bits.length+1) false]) := by
  obtain ⟨r,hr,hf,_⟩ := CompetitorFrameAppend.append_run bits [] out
  simp only [List.append_nil] at hr hf
  have small : Step CompetitorFrameAppend.machine (4*bits.length+3)
      (![0,out.length,0] : Fin 3→Nat) ![frame bits,out,[]]
      ![0,(out++frame bits).length,0] ![frame bits,out++frame bits,List.replicate (2*bits.length+1) false] := by
    exact Step.of_run hr (by rw [hf];rfl) (by rw [hf];rfl)
  have h := small.dock (if which then cSlots else xSlots) (by cases which <;>decide)
    (heads pos out) A (by intro j;cases which <;>fin_cases j <;>rfl) hA
  have hh : dockH (if which then cSlots else xSlots) (heads pos out) ![0,(out++frame bits).length,0]=
      heads pos (out++frame bits) := by
    cases which <;>funext i <;>fin_cases i <;>first
      | exact dockH_slot _ (by decide) _ _ 0
      | exact dockH_slot _ (by decide) _ _ 1
      | exact dockH_slot _ (by decide) _ _ 2
      | exact dockH_other _ _ _ _ (by decide)
  cases which <;>exact h.congr hh rfl

end NearCubicWires.P1Closure.PoolEntry

end

section

/-! One physical X/C pool entry, built from an original gate RepairOrdinary.frame.
The original arity and signed fields are loaded by the machine; the C
RepairOrdinary.frame is computed from those fields and runtime membership. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntry
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource VerifierDecoding
open SupplierPipeline ProjectionNormalization CompilerSemantics
open scoped BigOperators

abbrev workerSlots : Fin 55 → Fin 64 := fun i=>i.castAdd 9
def loadSlots : Fin 9 → Fin 64 := ![55,56,48,57,58,0,42,59,60]
theorem load_inj : Function.Injective loadSlots := by decide
theorem worker_inj : Function.Injective workerSlots := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 64=>x.val) h
theorem worker_ne (j : Fin 55) (k : Fin 64) (hk : 55≤k.val) : workerSlots j≠k := by
  intro he
  have hv := congrArg (fun i : Fin 64=>i.val) he
  change j.val=k.val at hv
  have hj := j.isLt
  omega
theorem worker_heads (pos : Nat) (out : List Bool) (j : Fin 55) : heads pos out (workerSlots j)=0 := by
  simp only [heads,if_neg (worker_ne j 56 (by decide)),if_neg (worker_ne j 61 (by decide))]
noncomputable def loader := RecoveryFocus.machine loadSlots PoolEntryLoad.machine
noncomputable def frozen := RecoveryFocus.machine workerSlots ConstantGateFrame.machine
noncomputable def machine := Composition.machine (Composition.machine (Composition.machine loader frozen) appendX) appendC

def base {q : Nat} (g : ExactThresholdGate q) (A : Fin 55→List Bool) (L : Nat) (out : List Bool) : Fin 64→List Bool :=
  Fin.addCases (m:=55) (n:=9) (motive:=fun _=>List Bool) A ![RepairOrdinary.frame (PoolEntryLoad.word g),[],[],[],[],List.replicate L false,out,[],[]]
noncomputable def initial {q : Nat} (g : ExactThresholdGate q) (A : Fin 55→List Bool) (C L : Nat) (out : List Bool) :=
  install loadSlots (base g A L out) (Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool) (PoolEntryLoad.input g C) (fun _ : Fin 1=>List.replicate L false))
noncomputable def loaded {q : Nat} (g : ExactThresholdGate q) (A : Fin 55→List Bool) (C L : Nat) (out : List Bool) :=
  install loadSlots (base g A L out) (Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool) (PoolEntryLoad.output g C) (fun _ : Fin 1=>List.replicate L false))

theorem load_run {q : Nat} (g : ExactThresholdGate q) (A : Fin 55→List Bool) (C L : Nat)
    (out : List Bool) (hL : PoolEntryLoad.rawBudget g≤L) :
    Step loader (PoolEntryLoad.budget g) (heads 0 out) (initial g A C L out)
      (heads (PoolEntryLoad.word g).length out) (loaded g A C L out) := by
  have h := (PoolEntryLoad.load_run g C L hL).dock loadSlots load_inj
    (heads 0 out) (initial g A C L out)
    (by intro j;fin_cases j <;>rfl)
    (by intro j;exact install_slot loadSlots load_inj _ _ j)
  refine h.congr ?_ ?_
  · funext i;fin_cases i <;> first
      | exact dockH_slot loadSlots load_inj _ _ 0
      | exact dockH_slot loadSlots load_inj _ _ 1
      | exact dockH_slot loadSlots load_inj _ _ 2
      | exact dockH_slot loadSlots load_inj _ _ 3
      | exact dockH_slot loadSlots load_inj _ _ 4
      | exact dockH_slot loadSlots load_inj _ _ 5
      | exact dockH_slot loadSlots load_inj _ _ 6
      | exact dockH_slot loadSlots load_inj _ _ 7
      | exact dockH_slot loadSlots load_inj _ _ 8
      | exact dockH_other loadSlots _ _ _ (by decide)
  · funext i
    change install loadSlots (install loadSlots (base g A L out) _) _ i=install loadSlots (base g A L out) _ i
    unfold install
    cases RecoveryFocus.pick loadSlots i <;>rfl

theorem loaded_worker {q : Nat} (g : ExactThresholdGate q) (A : Fin 55→List Bool) (C L : Nat)
    (out : List Bool) (h0 : A 0=exactWord g) (h48 : A 48=ZeroPadding.pad C (natWord q))
    (h42 : A 42=CompareMachine.word q) : ∀ j,loaded g A C L out (workerSlots j)=A j := by
  intro j
  fin_cases j <;> first
    | exact (install_slot loadSlots load_inj _ _ 5).trans h0.symm
    | exact (install_slot loadSlots load_inj _ _ 2).trans h48.symm
    | exact (install_slot loadSlots load_inj _ _ 6).trans h42.symm
    | exact install_other loadSlots _ _ _ (by decide)

def logCapacity (B q : Nat) := 32*(B+q+1)
noncomputable def input {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (B w : Nat) (out : List Bool) :=
  initial (sourceFields g) (ready live g B w) (ConstantGateReusable.C w) (logCapacity B q) out

def budget {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat) :=
  PoolEntryLoad.budget (sourceFields g)+
  ConstantGateFrame.budget (CloseoutRowsPoolMinimum.items g.gate live) (g.gate.threshold-1) w (ConstantGateReusable.C w)+
  4*(CloseoutRowsCircuitBottom.nativeWord g).length+
  4*(CloseoutRowsCircuitBottom.nativeWord (CloseoutRowsUniversal.constantSupportedGate live g)).length+9+0*B

private theorem native_word {q : Nat} (g : SupportedNormalizedGate q) :
    PoolEntryLoad.word (sourceFields g)=CloseoutRowsCircuitBottom.nativeWord g := by
  simp only [PoolEntryLoad.word,sourceFields,exactWord,CloseoutRowsPoolWriter.original_native,List.append_assoc]

theorem run {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat)
    (out : List Bool) (hw : 0<w) (hq : q≤w)
    (hb : (CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : (g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w) :
    ∃ result : Fin 64→List Bool,
      Step machine (budget live g B w) (heads 0 out) (input live g B w out)
        (heads (CloseoutRowsCircuitBottom.nativeWord g).length (out++CloseoutRowsPoolWriter.entry live g)) result ∧
      result 61=out++CloseoutRowsPoolWriter.entry live g ∧
      result 55=RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g) := by
  obtain ⟨hweights,hneg,hthreshold,hpos,hnpart⟩ := ConstantGateReusable.bounds live g.gate w hw hm
  have hbits : natBitLength q≤q+1 := by
    unfold natBitLength
    have h := Nat.log_le_self 2 q
    omega
  have hc : 2*natBitLength q+3≤ConstantGateReusable.C w := by unfold ConstantGateReusable.C;omega
  have hfields : (exactWord (sourceFields g)).length≤B := by
    rw [←native_word] at hb
    simp only [PoolEntryLoad.word,List.length_append] at hb
    omega
  have hbytes : (CloseoutRowsPoolWeight.word (CloseoutRowsPoolMinimum.items g.gate live)++
      intWord (g.gate.threshold-1)++[]).length≤B := by
    simpa only [List.append_nil,CloseoutRowsPoolMinimum.items_word,exactWord,sourceFields] using hfields
  have hlog : PoolEntryLoad.rawBudget (sourceFields g)≤logCapacity B q := by
    unfold PoolEntryLoad.rawBudget logCapacity
    rw [native_word]
    omega
  have he := ConstantGateReusable.weight_fit live g.gate [] B hbytes
  let A := ready live g B w
  let loaded := PoolEntry.loaded (sourceFields g) A (ConstantGateReusable.C w) (logCapacity B q) out
  have hl := load_run (sourceFields g) A (ConstantGateReusable.C w) (logCapacity B q) out hlog
  have ha : ∀ j,loaded (workerSlots j)=A j :=
    loaded_worker (sourceFields g) A (ConstantGateReusable.C w) (logCapacity B q) out
      (ready_source live g B w) (ready_arity live g B w) (ready_count live g B w)
  obtain ⟨W,hW,hC⟩ := ConstantGateFrame.constant_run live g [] [] w (ConstantGateReusable.C w) 0
    (ConstantGateReusable.E B q) hweights (by rfl) hneg hthreshold hpos hnpart he hc
  have hf := hW.dock workerSlots worker_inj
    (heads (PoolEntryLoad.word (sourceFields g)).length out) loaded
    (worker_heads _ _) ha
  have hf' := hf.congr (dockH_existing _ _ _ (worker_heads _ _)) rfl
  let F := install workerSlots loaded W
  have f55 : F 55=RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g) := by
    dsimp only [F]
    rw [install_other workerSlots _ _ 55 (by intro j;exact worker_ne j _ (by decide))]
    exact (install_slot loadSlots load_inj _ _ 0).trans (congrArg RepairOrdinary.frame (native_word g))
  have f61 : F 61=out := by
    dsimp only [F]
    rw [install_other workerSlots _ _ 61 (by intro j;exact worker_ne j _ (by decide))]
    exact install_other loadSlots _ _ _ (by decide)
  have f62 : F 62=[] := by
    dsimp only [F]
    rw [install_other workerSlots _ _ 62 (by intro j;exact worker_ne j _ (by decide))]
    exact install_other loadSlots _ _ _ (by decide)
  have hx := append_run false (PoolEntryLoad.word (sourceFields g)).length
    (CloseoutRowsCircuitBottom.nativeWord g) out F (by intro j;fin_cases j;exact f55;exact f61;exact f62)
  let X := install xSlots F ![RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g),out++RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g),
    List.replicate (2*(CloseoutRowsCircuitBottom.nativeWord g).length+1) false]
  have x53 : X 53=RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord (CloseoutRowsUniversal.constantSupportedGate live g)) := by
    dsimp only [X]
    rw [install_other xSlots _ _ 53 (by decide)]
    exact (install_slot workerSlots worker_inj _ _ 53).trans hC
  have x61 : X 61=out++RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g) := install_slot xSlots x_inj _ _ 1
  have x63 : X 63=[] := by
    dsimp only [X,F]
    rw [install_other xSlots _ _ 63 (by decide),install_other workerSlots _ _ 63
      (by intro j;exact worker_ne j _ (by decide))]
    exact install_other loadSlots _ _ _ (by decide)
  have hcstep := append_run true (PoolEntryLoad.word (sourceFields g)).length
    (CloseoutRowsCircuitBottom.nativeWord (CloseoutRowsUniversal.constantSupportedGate live g))
    (out++RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)) X
    (by intro j;fin_cases j;exact x53;exact x61;exact x63)
  have total := ((hl.seq hf').seq hx).seq hcstep
  have ht : PoolEntryLoad.budget (sourceFields g)+1+
      ConstantGateFrame.budget (CloseoutRowsPoolMinimum.items g.gate live) (g.gate.threshold-1) w (ConstantGateReusable.C w)+1+
      (4*(CloseoutRowsCircuitBottom.nativeWord g).length+3)+1+
      (4*(CloseoutRowsCircuitBottom.nativeWord (CloseoutRowsUniversal.constantSupportedGate live g)).length+3)=budget live g B w := by
    unfold budget;omega
  let result : Fin 64→List Bool := install cSlots X
    ![RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord (CloseoutRowsUniversal.constantSupportedGate live g)),
      (out++RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g))++
        RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord (CloseoutRowsUniversal.constantSupportedGate live g)),
      List.replicate (2*(CloseoutRowsCircuitBottom.nativeWord (CloseoutRowsUniversal.constantSupportedGate live g)).length+1) false]
  refine ⟨result,?_,?_,?_⟩
  · simpa only [machine,frozen,ht,native_word,CloseoutRowsPoolWriter.entry,RepairSource.frame,List.append_assoc,Bool.false_eq_true,ite_false,ite_true,result,input,A] using total
  · dsimp only [result]
    exact (install_slot cSlots c_inj _ _ 1).trans (List.append_assoc _ _ _)
  · dsimp only [result]
    rw [install_other cSlots _ _ 55 (by decide)]
    exact (install_slot xSlots x_inj _ _ 0).trans rfl

end NearCubicWires.P1Closure.PoolEntry

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntry
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch
open RepairRepresentation RepairSource SupplierPipeline
open scoped BigOperators

def uniformBudget (B q w : Nat) := 8192*(B+q+w+1)^2
def reserve (B q w : Nat) := 65536*(B+q+w+1)^2

theorem budget_le {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat)
    (hw : 0<w) (hq : q≤w) (hb : (CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : (g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w) :
    budget live g B w≤uniformBudget B q w := by
  obtain ⟨hweights,hneg,hthreshold,hpos,hnpart⟩ := ConstantGateReusable.bounds live g.gate w hw hm
  have hbits := arity_bits q
  have hc : 2*natBitLength q+3≤ConstantGateReusable.C w := by unfold ConstantGateReusable.C;omega
  have hbytes := fields_bytes live g B hb
  have he := ConstantGateReusable.weight_fit live g.gate [] B hbytes
  obtain ⟨W,⟨r,hr,hh,_,hs⟩,_⟩ := ConstantGateFrame.raw_run
    (CloseoutRowsPoolMinimum.items g.gate live) (g.gate.threshold-1) [] [] w (ConstantGateReusable.C w) 0
    (ConstantGateReusable.E B q) hweights (by rfl) hneg hthreshold hpos hnpart he
    (by simpa only [CloseoutRowsPoolMinimum.items_length] using hc)
  have len := SelectiveReset.prefix_head (prefix_of_run ConstantGateFrame.raw _ _ r hr).1 (34 : Fin 51)
  rw [hh] at len
  change (ConstantGateFrame.native (CloseoutRowsPoolMinimum.items g.gate live) (g.gate.threshold-1)).length≤0+r.steps at len
  rw [ConstantGateFrame.constant_native] at len
  have hworker := ConstantGateReusable.worker_bound live g.gate [] B w hbytes hthreshold
  have hraw : ConstantGateFrame.rawBudget (CloseoutRowsPoolMinimum.items g.gate live)
      (g.gate.threshold-1) w (ConstantGateReusable.C w)≤512*(B+q+w+1)^2+4*q+15 := by
    unfold ConstantGateFrame.rawBudget CloseoutCaseTwo.NativeCopy.budget
    rw [CloseoutRowsPoolMinimum.items_length]
    omega
  have hfield : (exactWord (sourceFields g)).length≤B := by
    simpa only [List.append_nil,CloseoutRowsPoolMinimum.items_word,exactWord,sourceFields] using hbytes
  have hword : (PoolEntryLoad.word (sourceFields g)).length≤B := by
    simpa only [PoolEntryLoad.word,exactWord,sourceFields,CloseoutRowsPoolWriter.original_native,List.append_assoc] using hb
  have hload : PoolEntryLoad.rawBudget (sourceFields g)≤32*(B+q+1) := by
    unfold PoolEntryLoad.rawBudget
    omega
  have square : B+q+w+1≤(B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  unfold budget PoolEntryLoad.budget ConstantGateFrame.budget uniformBudget
  nlinarith

theorem bounded_run {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat)
    (out : List Bool) (hw : 0<w) (hq : q≤w)
    (hb : (CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : (g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w) :
    ∃ result : Fin 64→List Bool,
      Step machine (uniformBudget B q w) (heads 0 out) (input live g B w out)
        (heads (CloseoutRowsCircuitBottom.nativeWord g).length (out++CloseoutRowsPoolWriter.entry live g)) result ∧
      result 61=out++CloseoutRowsPoolWriter.entry live g ∧
      result 55=RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g) := by
  obtain ⟨result,hr,ho,hkeep⟩ := run live g B w out hw hq hb hm
  exact ⟨result,hr.enlarge (budget_le live g B w hw hq hb hm),ho,hkeep⟩

end NearCubicWires.P1Closure.PoolEntry

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryCursor
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch

def selected (i : Fin 2) := decide (i=1)
noncomputable def copy := MaskedReset.machine (CloseoutRowsTupleSeek.frameMachine true) selected
def heads (pos : Nat) (i : Fin 3) := if i=0 then pos else 0
def bank (source target : List Bool) (S : Nat) (i : Fin 3) :=
  if i=0 then source else if i=1 then target else List.replicate S false

theorem copy_run (pre bits tail : List Bool) (S : Nat) (hS : (frame bits).length≤S) :
    Step copy (4*bits.length+4) (heads pre.length)
      (bank (pre++frame bits++tail) (List.replicate S false) S)
      (heads (pre.length+(frame bits).length))
      (bank (pre++frame bits++tail) (ZeroPadding.pad S (frame bits)) S) := by
  have h := (CloseoutRowsTupleSeek.frame_run true pre bits tail []).pad (![0,S] : Fin 2→Nat)
  have hmask := h.mask selected (by intro i hi;fin_cases i <;>first | rfl | simp [selected] at hi)
    (by simpa only [frame_length'] using hS)
  have hc : 2*(2*bits.length+1)+2=4*bits.length+4 := by omega
  refine (hmask.congr_in ?_ ?_).congr ?_ ?_ |>.enlarge (by rw [hc])
  all_goals funext i;fin_cases i <;>
    simp [heads,bank,selected,CloseoutRowsTupleSeek.fieldHeads,CloseoutRowsTupleSeek.fieldData,
      CloseoutRowsTupleSeek.selected,ZeroPadding.pad,Fin.addCases]

theorem erase_run (bits : List Bool) (S : Nat) (hS : bits.length≤S) :
    Step (RecoveryScratchErase.resetMachine 1) (2*S+4)
      (fun _ : Fin 3=>0) ![bits,List.replicate S true,List.replicate (S+1) false]
      (fun _ : Fin 3=>0) ![List.replicate S false,List.replicate S true,List.replicate (S+1) false] := by
  have h := Step.of_ready (RecoveryScratchErase.erase_ready S (S+1) (fun _ : Fin 1=>bits) (by intro i;exact hS))
  refine (h.congr_in rfl ?_).congr rfl ?_
  all_goals funext i;fin_cases i <;>simp [Fin.addCases]

end NearCubicWires.P1Closure.PoolEntryCursor

end

section

/-! Complete paid restoration of the original-gate callback. The protected
ports are growing output61 and retained original frame55. Every other working tape is restored from its retained
baseline master. Padding handles allocated blank tails without truncation. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryRestore
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch ExtIncidence

def work : Fin 62 → Fin 64 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,56,57,58,59,60,62,63]
def caps (S : Nat) (i : Fin 64) := if i=61 ∨ i=55 then 0 else S
def selected (i : Fin 64) : Bool := decide (i≠61)
def localHeads (out : List Bool) (i : Fin 64) : Nat := if i=61 then out.length else 0
def heads (out : List Bool) (i : Fin 129) : Nat := if i=61 then out.length else 0
def masters (A : List Bool → Fin 64 → List Bool) (j : Fin 62) := A [] (work j)
def padded (A : List Bool → Fin 64 → List Bool) (out : List Bool) (S : Nat) :=
  fun i=>ZeroPadding.pad (caps S i) (A out i)
def state (child : Fin 64 → List Bool) (master : Fin 62 → List Bool) (S : Nat) : Fin 129 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool) child
    (Fin.addCases (motive:=fun _=>List Bool) master
      (![List.replicate S false,List.replicate S true,List.replicate (S+1) false] : Fin 3 → List Bool))
def input (A : List Bool → Fin 64 → List Bool) (out : List Bool) (S : Nat) :=
  state (padded A out S) (masters A) S

def maskSlots : Fin 65 → Fin 129 :=
  Fin.addCases (m:=64) (n:=1) (motive:=fun _=>Fin 129) (fun j : Fin 64=>j.castAdd 65) (fun _ : Fin 1=>126)
def restoreSlots : Fin 126 → Fin 129 :=
  Fin.addCases (m:=125) (n:=1) (motive:=fun _=>Fin 129)
    (Fin.addCases (m:=62) (n:=63) (motive:=fun _=>Fin 129) (fun j : Fin 62=>(j.castAdd 3).natAdd 64)
      (Fin.addCases (m:=62) (n:=1) (motive:=fun _=>Fin 129)
        (fun j : Fin 62=>(work j).castAdd 65) (fun _ : Fin 1=>127)))
    (fun _ : Fin 1=>128)
theorem mask_injective : Function.Injective maskSlots := by decide
theorem restore_injective : Function.Injective restoreSlots := by decide
noncomputable def first {s : Nat} (p : Machine 64 s) := RecoveryFocus.machine maskSlots (MaskedReset.machine p selected)
noncomputable def restore := RecoveryFocus.machine restoreSlots (TemplateRestore.machine 62)
noncomputable def machine {s : Nat} (p : Machine 64 s) := Composition.machine (first p) restore

theorem pad_work (A : List Bool → Fin 64 → List Bool)
    (hA : ∀ a i,i≠61 → A a i=A [] i) (out : List Bool) (S : Nat) (j : Fin 62) :
    padded A out S (work j)=ZeroPadding.pad S (masters A j) := by
  have hc : caps S (work j)=S := by fin_cases j <;>rfl
  have hn : work j≠61 := by fin_cases j <;>decide
  simp only [padded,hc,hA out _ hn,masters]

theorem restore_run (before after : Fin 64 → List Bool) (master : Fin 62 → List Bool)
    (out : List Bool) (S : Nat) (hm : ∀ j,(master j).length≤S)
    (hd : ∀ j,(before (work j)).length≤S)
    (ha : ∀ j,after (work j)=ZeroPadding.pad S (master j))
    (hk : ∀ i,i=61 ∨ i=55 → after i=before i) :
    Step restore (4*S+9) (heads out) (state before master S)
      (heads out) (state after master S) := by
  have hh : ∀ j,heads out (restoreSlots j)=0 := by intro j;fin_cases j <;>rfl
  have hi : ∀ j,state before master S (restoreSlots j)=TemplateRestore.input master (fun j=>before (work j)) S j := by
    intro j
    refine Fin.addCases (m:=125) (n:=1) (fun j=>?_) (fun j=>?_) j
    · refine Fin.addCases (m:=62) (n:=63) (fun j=>?_) (fun j=>?_) j
      · simp only [restoreSlots,state,TemplateRestore.input,TemplateRestore.pack,TemplateRestore.localInput,
          Fin.addCases_left,Fin.addCases_right]
      · refine Fin.addCases (m:=62) (n:=1) (fun j=>?_) (fun j=>?_) j
        · simp only [restoreSlots,state,TemplateRestore.input,TemplateRestore.pack,TemplateRestore.localInput,
            Fin.addCases_left,Fin.addCases_right]
        · fin_cases j;rfl
    · fin_cases j;rfl
  have he : install restoreSlots (state before master S)
      (NativeFanout.output (fun j=>some j) master S)=state after master S := by
    apply HierarchyAllocation.install_eq restoreSlots restore_injective
    · intro j
      refine Fin.addCases (m:=125) (n:=1) (fun j=>?_) (fun j=>?_) j
      · refine Fin.addCases (m:=62) (n:=63) (fun j=>?_) (fun j=>?_) j
        · simp only [restoreSlots,state,NativeFanout.output,Fin.addCases_left,Fin.addCases_right]
        · refine Fin.addCases (m:=62) (n:=1) (fun j=>?_) (fun j=>?_) j
          · simpa only [restoreSlots,state,NativeFanout.output,NativeFanout.word,Option.elim_some,
              Fin.addCases_left,Fin.addCases_right] using ha j
          · fin_cases j;rfl
      · fin_cases j;rfl
    · intro i hi
      have outside : ∀ i,(∀ j,restoreSlots j≠i) → i=61 ∨ i=55 ∨ i=126 := by decide
      rcases outside i hi with rfl|rfl|rfl
      · exact hk 61 (by simp)
      · exact hk 55 (by simp)
      · rfl
  have call := (TemplateRestore.run master (fun j=>before (work j)) S hm hd).focus
    restoreSlots restore_injective (heads out) (state before master S)
  exact (call.congr_in (dockH_existing _ _ _ hh) (install_existing _ _ _ hi)).congr
    (dockH_existing _ _ _ hh) he

theorem run {s : Nat} (p : Machine 64 s) (A : List Bool → Fin 64 → List Bool)
    (out next : List Bool) (n S : Nat) (J : Fin 64 → Nat) (result : Fin 64 → List Bool)
    (hA : ∀ a i,i≠61 → A a i=A [] i) (houtput : ∀ a,A a 61=a)
    (hr : Step p n (localHeads out) (A out) J result)
    (hj : J 61=next.length) (hout : result 61=next)
    (hkeep : ∀ i,i=55 → result i=A out i)
    (hm : ∀ j,(masters A j).length≤S) (hS : n+1≤S) :
    Step (machine p) (2*n+4*S+12) (heads out) (input A out S)
      (heads next) (input A next S) := by
  let resultP : Fin 64 → List Bool := fun i=>ZeroPadding.pad (caps S i) (result i)
  have hp := hr.pad (caps S)
  have fit : ∀ j,(resultP (work j)).length≤S := by
    intro j
    apply LocalSupport.step_fits hp (work j) S
    · change (padded A out S (work j)).length≤S
      rw [pad_work A hA out S j,ZeroPadding.pad_length,Nat.max_eq_left (hm j)]
    · have hn : work j≠61 := by fin_cases j <;>decide
      simp only [localHeads,if_neg hn]
      omega
  have reset := hp.mask selected (by
    intro i hi
    have hn : i≠61 := of_decide_eq_true hi
    exact if_neg hn) (by omega : n≤S)
  have mh : (fun i=>if selected i then 0 else J i)=localHeads next := by
    funext i
    by_cases he : i=61
    · subst i;simpa [selected,localHeads] using hj
    · simp [selected,localHeads,he]
  rw [mh] at reset
  have hmask : ∀ j,heads out (maskSlots j)=
      Fin.addCases (m:=64) (n:=1) (motive:=fun _=>Nat) (localHeads out) (fun _=>0) j := by
    intro j;fin_cases j <;>rfl
  have tmask : ∀ j,input A out S (maskSlots j)=
      Fin.addCases (m:=64) (n:=1) (motive:=fun _=>List Bool) (padded A out S)
        (fun _=>List.replicate S false) j := by
    intro j
    refine Fin.addCases (m:=64) (n:=1) (fun j=>?_) (fun j=>?_) j
    · simp only [maskSlots,input,state,Fin.addCases_left]
    · fin_cases j;rfl
  have rhead : dockH maskSlots (heads out)
      (Fin.addCases (m:=64) (n:=1) (motive:=fun _=>Nat) (localHeads next) (fun _=>0))=heads next := by
    funext i
    unfold dockH
    cases hi : RecoveryFocus.pick maskSlots i with
    | none =>
      have hn : i≠61 := by
        intro he;subst i
        have hk : RecoveryFocus.pick maskSlots 61=some 61 := RecoveryFocus.pick_slot maskSlots mask_injective 61
        rw [hi] at hk
        contradiction
      simp only [heads,if_neg hn]
    | some j =>
      have he := RecoveryFocus.slot_of_pick maskSlots hi
      rw [←he]
      fin_cases j <;>rfl
  have rtapes : install maskSlots (input A out S)
      (Fin.addCases (m:=64) (n:=1) (motive:=fun _=>List Bool) resultP (fun _=>List.replicate S false))=
      state resultP (masters A) S := by
    apply HierarchyAllocation.install_eq maskSlots mask_injective
    · intro j
      refine Fin.addCases (m:=64) (n:=1) (fun j=>?_) (fun j=>?_) j
      · simp only [maskSlots,state,Fin.addCases_left]
      · fin_cases j;rfl
    · intro i hi
      exact Fin.addCases (m:=64) (n:=65)
        (fun j hj=>False.elim (hj (j.castAdd 1) (by simp only [maskSlots,Fin.addCases_left])))
        (fun _ _=>by simp only [input,state,Fin.addCases_right]) i hi
  have call := ((reset.focus maskSlots mask_injective (heads out) (input A out S)).congr_in
    (dockH_existing _ _ _ hmask) (install_existing _ _ _ tmask)).congr rhead rtapes
  have retained : ∀ i,i=61 ∨ i=55 → padded A next S i=resultP i := by
    intro i hi
    rcases hi with rfl|rfl
    · change ZeroPadding.pad 0 (A next 61)=ZeroPadding.pad 0 (result 61)
      rw [houtput,hout]
    all_goals
      change ZeroPadding.pad 0 _=ZeroPadding.pad 0 _
      congr 1
      rw [hkeep _ (by simp),hA out _ (by decide),hA next _ (by decide)]
  have last := restore_run resultP (padded A next S) (masters A) next S hm fit
    (pad_work A hA next S) retained
  have all := call.seq last
  convert all using 1 <;>first | rfl | omega

end NearCubicWires.P1Closure.PoolEntryRestore

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryBaseline
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch RepairRepresentation RepairSource
open SupplierPipeline VerifierDecoding CloseoutFinal SignedSortKey
open scoped BigOperators

def seed (q : Nat) : SupportedNormalizedGate q :=
  ⟨⟨fun _=>0,1⟩,∅,by intro i hi;rfl⟩

theorem joined {m n : Nat} (A B : Fin m→List Bool) (C : Fin n→List Bool)
    (h : ∀ i,i.val≠0 → A i=B i) :
    ∀ i : Fin (m+n),i.val≠0 →
      Fin.addCases (motive:=fun _=>List Bool) A C i=Fin.addCases (motive:=fun _=>List Bool) B C i := by
  intro i
  refine Fin.addCases (m:=m) (n:=n) (fun j hj=>?_) (fun j _=>?_) i
  · simpa only [Fin.addCases_left] using h j hj
  · simp only [Fin.addCases_right]

theorem ready_other {q : Nat} (live : Finset (Fin q)) (g h : SupportedNormalizedGate q)
    (B w : Nat) (i : Fin 55) (hi : i≠0) :
    PoolEntry.ready live g B w i=PoolEntry.ready live h B w i := by
  have hh : ∀ i : Fin 55,i.val≠0 → PoolEntry.ready live g B w i=PoolEntry.ready live h B w i := by
    unfold PoolEntry.ready AppendOutputFrame.input AppendOutputLength.input
      ConstantGateFrame.input ConstantGate.data C10NaturalHardwireScoreInputs.data
      C10NaturalHardwireTarget.input C10NaturalHardwireTarget.pairInput
    simp only [CloseoutRowsPoolMinimum.items_length,CloseoutRowsPoolMinimum.items_mask]
    apply joined (m:=53) (n:=2)
    apply joined (m:=52) (n:=1)
    apply joined (m:=51) (n:=1)
    apply joined (m:=48) (n:=3)
    apply joined (m:=44) (n:=4)
    apply joined (m:=39) (n:=5)
    apply joined (m:=21) (n:=18)
    apply joined (m:=13) (n:=8)
    intro j hj
    have hn : j≠0 := by intro he;subst j;exact hj rfl
    simp only [CloseoutRowsPoolMagnitude.input,if_neg hn]
  exact hh i (by intro he;apply hi;exact Fin.ext he)

attribute [local irreducible] PoolEntry.ready PoolEntryLoad.word RepairOrdinary.frame

theorem input_source {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (B w : Nat) (out : List Bool) :
    PoolEntry.input live g B w out 55=RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g) := by
  unfold PoolEntry.input PoolEntry.initial
  rw [show (55 : Fin 64)=PoolEntry.loadSlots 0 from rfl,install_slot _ PoolEntry.load_inj]
  change RepairOrdinary.frame (PoolEntryLoad.word (PoolEntry.sourceFields g))=_
  congr 1
  simp only [PoolEntryLoad.word,PoolEntry.sourceFields,exactWord,
    CloseoutRowsPoolWriter.original_native,List.append_assoc]

theorem input_output {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (B w : Nat) (out : List Bool) : PoolEntry.input live g B w out 61=out := by
  unfold PoolEntry.input PoolEntry.initial
  rw [install_other PoolEntry.loadSlots _ _ 61 (by decide)]
  rfl

theorem extra_out (source out : List Bool) (L : Nat) (i : Fin 9) (hi : i≠6) :
    (![source,[],[],[],[],List.replicate L false,out,[],[]] : Fin 9→List Bool) i=
    (![source,[],[],[],[],List.replicate L false,[],[],[]] : Fin 9→List Bool) i := by
  fin_cases i <;>simp_all

theorem output_only {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (B w : Nat) (out : List Bool) (i : Fin 64) (hi : i≠61) :
    PoolEntry.input live g B w out i=PoolEntry.input live g B w [] i := by
  unfold PoolEntry.input PoolEntry.initial install
  cases h : RecoveryFocus.pick PoolEntry.loadSlots i with
  | some j => rfl
  | none =>
    revert hi
    refine Fin.addCases (m:=55) (n:=9) (fun j hj=>?_) (fun j hj=>?_) i
    · simp only [PoolEntry.base,Fin.addCases_left]
    · simp only [PoolEntry.base,Fin.addCases_right]
      apply extra_out
      intro he;subst j;exact hj rfl

theorem gate_only {q : Nat} (live : Finset (Fin q)) (g h : SupportedNormalizedGate q)
    (B w : Nat) (out : List Bool) (i : Fin 64) (hi : i≠55) :
    PoolEntry.input live g B w out i=PoolEntry.input live h B w out i := by
  unfold PoolEntry.input PoolEntry.initial install
  cases hp : RecoveryFocus.pick PoolEntry.loadSlots i with
  | some j =>
    have he := RecoveryFocus.slot_of_pick PoolEntry.loadSlots hp
    fin_cases j <;> first | exact False.elim (hi he.symm) | rfl
  | none =>
    have hn : ∀ j,PoolEntry.loadSlots j≠i := by
      intro j he
      rw [←he,RecoveryFocus.pick_slot PoolEntry.loadSlots PoolEntry.load_inj j] at hp
      contradiction
    revert hn hi
    refine Fin.addCases (m:=55) (n:=9) (fun j hj hn=>?_) (fun j hj hn=>?_) i
    · simp only [PoolEntry.base,Fin.addCases_left]
      apply ready_other
      intro he
      subst j
      exact hn 5 rfl
    · simp only [PoolEntry.base,Fin.addCases_right]
      fin_cases j <;>first | exact False.elim (hj rfl) | rfl

noncomputable def bank {q : Nat} (live : Finset (Fin q)) (B w : Nat)
    (framed out : List Bool) : Fin 64→List Bool :=
  Function.update (PoolEntry.input live (seed q) B w out) 55 framed

theorem bank_source {q : Nat} (live : Finset (Fin q)) (B w : Nat) (framed out : List Bool) :
    bank live B w framed out 55=framed := by simp [bank]
theorem bank_output {q : Nat} (live : Finset (Fin q)) (B w : Nat) (framed out : List Bool) :
    bank live B w framed out 61=out := by
  rw [bank,Function.update_of_ne (by decide : (61 : Fin 64)≠55),input_output]
theorem bank_outside {q : Nat} (live : Finset (Fin q)) (B w : Nat) (framed out : List Bool)
    (i : Fin 64) (hi : i≠61) : bank live B w framed out i=bank live B w framed [] i := by
  by_cases hs : i=55
  · subst i;rw [bank_source,bank_source]
  · simp only [bank,Function.update_of_ne hs,output_only live (seed q) B w out i hi]

theorem joined_fit {m n : Nat} (A : Fin m→List Bool) (C : Fin n→List Bool) (S : Nat)
    (hA : ∀ i,i.val≠0 → (A i).length≤S) (hC : ∀ i,(C i).length≤S) :
    ∀ i : Fin (m+n),i.val≠0 → (Fin.addCases (motive:=fun _=>List Bool) A C i).length≤S := by
  intro i
  refine Fin.addCases (m:=m) (n:=n) (fun j hj=>?_) (fun j _=>?_) i
  · simpa only [Fin.addCases_left] using hA j hj
  · simpa only [Fin.addCases_right] using hC j

theorem ready_fit {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (B w : Nat) (i : Fin 55) (hi : i≠0) :
    (PoolEntry.ready live g B w i).length≤PoolEntry.reserve B q w := by
  have square : B+q+w+1≤(B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  have hC : ConstantGateReusable.C w+1≤PoolEntry.reserve B q w := by
    unfold ConstantGateReusable.C PoolEntry.reserve;omega
  have hE : ConstantGateReusable.E B q≤PoolEntry.reserve B q w := by
    unfold ConstantGateReusable.E PoolEntry.reserve;omega
  have hq : q+1≤PoolEntry.reserve B q w := by unfold PoolEntry.reserve;omega
  have hw : 2*w+1≤PoolEntry.reserve B q w := by unfold PoolEntry.reserve;omega
  have hbits := PoolEntry.arity_bits q
  have harity : 2*natBitLength q+3≤PoolEntry.reserve B q w := by unfold PoolEntry.reserve;omega
  have hh : ∀ i : Fin 55,i.val≠0 → (PoolEntry.ready live g B w i).length≤PoolEntry.reserve B q w := by
    unfold PoolEntry.ready AppendOutputFrame.input AppendOutputLength.input
      ConstantGateFrame.input ConstantGate.data C10NaturalHardwireScoreInputs.data
      C10NaturalHardwireTarget.input C10NaturalHardwireTarget.pairInput
    simp only [CloseoutRowsPoolMinimum.items_length,CloseoutRowsPoolMinimum.items_mask]
    apply joined_fit (m:=53) (n:=2)
    swap
    · intro j;simp
    apply joined_fit (m:=52) (n:=1)
    swap
    · intro j;simp
    apply joined_fit (m:=51) (n:=1)
    swap
    · intro j;simp
    apply joined_fit (m:=48) (n:=3)
    swap
    · intro j;fin_cases j <;>simp [ConstantGateFrame.extra,ZeroPadding.pad_length,
        DecompositionSource.natWord_length] <;>omega
    apply joined_fit (m:=44) (n:=4)
    swap
    · intro j;fin_cases j <;>simp [HardwireChild.extra,CompareMachine.word] <;>omega
    apply joined_fit (m:=39) (n:=5)
    swap
    · intro j;fin_cases j <;>simp [C10NaturalHardwireScoreInputs.extra,CompareMachine.word] <;>omega
    apply joined_fit (m:=21) (n:=18)
    swap
    · intro j;fin_cases j <;>simp [C10NaturalHardwireTarget.extra] <;>omega
    apply joined_fit (m:=13) (n:=8)
    swap
    · intro j;fin_cases j <;>simp [C10NaturalHardwireTarget.pairExtra,MatrixScoreWeight.scalar,
        ZeroPadding.pad_length,RepairOrdinary.frame_length,binary_length] <;>omega
    intro j hj
    have hn : j≠0 := by intro he;subst j;exact hj rfl
    simp only [CloseoutRowsPoolMagnitude.input,if_neg hn]
    split <;>simp only [List.length_replicate] <;>omega
  exact hh i (by intro he;apply hi;exact Fin.ext he)

theorem input_fit {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (B w : Nat) (out : List Bool) (i : Fin 64) (hi : i≠55) (ho : i≠61) :
    (PoolEntry.input live g B w out i).length≤PoolEntry.reserve B q w := by
  have square : B+q+w+1≤(B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  have hc : ConstantGateReusable.C w≤PoolEntry.reserve B q w := by
    unfold ConstantGateReusable.C PoolEntry.reserve;omega
  have hq : q+1≤PoolEntry.reserve B q w := by unfold PoolEntry.reserve;omega
  have hl : PoolEntry.logCapacity B q≤PoolEntry.reserve B q w := by
    unfold PoolEntry.logCapacity PoolEntry.reserve;omega
  unfold PoolEntry.input PoolEntry.initial install
  cases hp : RecoveryFocus.pick PoolEntry.loadSlots i with
  | some j =>
    have he := RecoveryFocus.slot_of_pick PoolEntry.loadSlots hp
    fin_cases j <;> first
      | exact False.elim (hi he.symm)
      | (simp [Fin.addCases,PoolEntryLoad.input,PoolEntryLoad.data,CompareMachine.word] <;>omega)
  | none =>
    have hn : ∀ j,PoolEntry.loadSlots j≠i := by
      intro j he
      rw [←he,RecoveryFocus.pick_slot PoolEntry.loadSlots PoolEntry.load_inj j] at hp
      contradiction
    revert hn hi ho
    refine Fin.addCases (m:=55) (n:=9) (fun j hj hout hn=>?_) (fun j hj hout hn=>?_) i
    · simp only [PoolEntry.base,Fin.addCases_left]
      apply ready_fit
      intro he;subst j;exact hn 5 rfl
    · simp only [PoolEntry.base,Fin.addCases_right]
      fin_cases j <;>first
        | exact False.elim (hj rfl)
        | exact False.elim (hout rfl)
        | exact Nat.zero_le _
        | simpa using hl

def caps (S : Nat) (i : Fin 64) := if i=55 then S else 0

theorem padded_input {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q)
    (B w S : Nat) (out : List Bool) :
    (fun i=>ZeroPadding.pad (caps S i) (PoolEntry.input live g B w out i))=
      bank live B w (ZeroPadding.pad S (RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g))) out := by
  funext i
  by_cases hi : i=55
  · subst i;simp [caps,input_source,bank_source]
  · simp only [caps,if_neg hi,ZeroPadding.pad_zero,bank,Function.update_of_ne hi]
    exact gate_only live g (seed q) B w out i hi

noncomputable def state {q : Nat} (live : Finset (Fin q)) (B w : Nat)
    (framed out : List Bool) := PoolEntryRestore.input (bank live B w framed) out (PoolEntry.reserve B q w)
noncomputable def machine := PoolEntryRestore.machine PoolEntry.machine

def budget (B q w : Nat) := 2*PoolEntry.uniformBudget B q w+4*PoolEntry.reserve B q w+12

theorem run {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat)
    (out : List Bool) (hw : 0<w) (hq : q≤w)
    (hb : (CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : (g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w) :
    Step machine (budget B q w) (PoolEntryRestore.heads out)
      (state live B w (ZeroPadding.pad (PoolEntry.reserve B q w)
        (RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g))) out)
      (PoolEntryRestore.heads (out++CloseoutRowsPoolWriter.entry live g))
      (state live B w (ZeroPadding.pad (PoolEntry.reserve B q w)
        (RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g))) (out++CloseoutRowsPoolWriter.entry live g)) := by
  obtain ⟨result,hr,hout,hkeep⟩ := PoolEntry.bounded_run live g B w out hw hq hb hm
  let S := PoolEntry.reserve B q w
  let framed := ZeroPadding.pad S (RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g))
  have hheads : PoolEntry.heads 0 out=PoolEntryRestore.localHeads out := by
    funext i
    by_cases hi : i=56
    · subst i;rfl
    · simp only [PoolEntry.heads,PoolEntryRestore.localHeads,if_neg hi]
  have padded := (hr.pad (caps S)).congr_in hheads
    (padded_input live g B w S out)
  have hmaster : ∀ j,(PoolEntryRestore.masters (bank live B w framed) j).length≤S := by
    intro j
    have h55 : PoolEntryRestore.work j≠55 := by fin_cases j <;>decide
    have h61 : PoolEntryRestore.work j≠61 := by fin_cases j <;>decide
    simp only [PoolEntryRestore.masters,bank,Function.update_of_ne h55]
    exact input_fit live (seed q) B w [] _ h55 h61
  have hS : PoolEntry.uniformBudget B q w+1≤S := by
    have one : 1≤(B+q+w+1)^2 := Nat.one_le_pow _ _ (by omega)
    dsimp [S,PoolEntry.uniformBudget,PoolEntry.reserve];omega
  exact PoolEntryRestore.run PoolEntry.machine (bank live B w framed) out
    (out++CloseoutRowsPoolWriter.entry live g) _ S _ _
    (bank_outside live B w framed) (bank_output live B w framed) padded (by rfl)
    (by simpa only [caps,show (61 : Fin 64)≠55 by decide,if_false,ZeroPadding.pad_zero] using hout)
    (by intro i hi;subst i;simp only [caps,hkeep,bank_source];rfl)
    hmaster hS

end NearCubicWires.P1Closure.PoolEntryBaseline

end

section

namespace NearCubicWires.RepairSource.CloseoutRowsPoolWriter
open LocalBitMultitape SupplierPipeline RepairRepresentation ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.CloseoutRowsCircuitBottom
open RepairSource.CloseoutRowsUniversal RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {q : ℕ}

/-! ### Indexing the emission by the driver's counter -/

/-- What the driver emits at counter value `j`. -/
def emitAt (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (j : ℕ) : List Bool:=
  (occ[j]?).elim [] (entry live)

theorem range_flatMap {α β : Type} (l : List α) (f : α→List β) :
    (List.range l.length).flatMap (fun j=>(l[j]?).elim [] f)=l.flatMap f:=by
  have h:(List.range l.length).map (fun j=>(l[j]?).elim [] f)=l.map f:=by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range]
      rw [List.getElem?_eq_getElem (by simpa using hj)]
      rfl
  simp only [List.flatMap_def,h]

/-- The driver's accumulated stream is the batch's gate stream over the pool. -/
theorem emit_stream (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) :
    (List.range occ.length).flatMap (emitAt live occ)=occ.flatMap (entry live):=
  range_flatMap occ (entry live)

/-! ### The loop -/

/-- THE WRITER LOOP: one paid body call per retained occurrence accumulates
exactly the pool's gate stream. -/
theorem writer_loop {t s : ℕ} (body : Machine t s)
    (source : ℕ → List Bool → Configuration t s) (cost : ℕ)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (out : List Bool)
    (hstart : ∀ j<occ.length,∀ pre,(source j pre).control=body.start)
    (supplier : ∀ j<occ.length,∀ pre,∃ r,runFrom body cost (source j pre)=some r ∧
      r.final.heads=(source (j+1) (pre++emitAt live occ j)).heads ∧
      r.final.tapes=(source (j+1) (pre++emitAt live occ j)).tapes ∧ r.steps≤cost) :
    ∃ r,runFrom (CloseoutRowsDegreeLoop.machine body) (occ.length*(cost+3)+3)
        (RepeatMachine.cfg 0 (source 0 out) occ.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (source occ.length (out++occ.flatMap (entry live)))
        occ.length 1 ∧
      r.steps≤occ.length*(cost+3)+3:=by
  have h:=CloseoutRowsDegreeLoop.loop_run body source (emitAt live occ) cost occ.length
    hstart supplier out
  rw [emit_stream] at h
  exact h

/-- ACCEPTANCE: started at the batch's count header and framed top, the
writer's exit output is byte-equal to the batch's segment of the pool. -/
theorem writer_cursor (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (top : List Bool) :
    (natWord (2*occ.length)++frame top)++occ.flatMap (entry live)=
      ExtDecompositionBatch.segment (pool live occ) top:=
  (pool_segment live occ top).symm

/-- The writer loop at the batch's own cursor. -/
theorem pool_writer_run {t s : ℕ} (body : Machine t s)
    (source : ℕ → List Bool → Configuration t s) (cost : ℕ)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (top : List Bool)
    (hstart : ∀ j<occ.length,∀ pre,(source j pre).control=body.start)
    (supplier : ∀ j<occ.length,∀ pre,∃ r,runFrom body cost (source j pre)=some r ∧
      r.final.heads=(source (j+1) (pre++emitAt live occ j)).heads ∧
      r.final.tapes=(source (j+1) (pre++emitAt live occ j)).tapes ∧ r.steps≤cost) :
    ∃ r,runFrom (CloseoutRowsDegreeLoop.machine body) (occ.length*(cost+3)+3)
        (RepeatMachine.cfg 0 (source 0 (natWord (2*occ.length)++frame top)) occ.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3
        (source occ.length (ExtDecompositionBatch.segment (pool live occ) top)) occ.length 1 ∧
      r.steps≤occ.length*(cost+3)+3:=by
  have h:=writer_loop body source cost live occ (natWord (2*occ.length)++frame top)
    hstart supplier
  rw [writer_cursor] at h
  exact h

/-! ### The B2 segment bound -/

theorem entry_length (live : Finset (Fin q)) (g : SupportedNormalizedGate q) :
    (entry live g).length=
      (frame (nativeWord g)).length+
        (frame (nativeWord (constantSupportedGate live g))).length:=
  List.length_append

theorem flat_length (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (m : ℕ)
    (h : ∀ g ∈ occ, (entry live g).length ≤ m) :
    (occ.flatMap (entry live)).length ≤ occ.length*m := by
  induction occ with
  | nil=>simp
  | cons g rest ih=>
    have h1:=h g (List.mem_cons_self)
    have h2:=ih (fun x hx=>h x (List.mem_cons_of_mem g hx))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem segment_length (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (top : List Bool) :
    (ExtDecompositionBatch.segment (pool live occ) top).length=
      (natWord (2*occ.length)).length+(frame top).length+
        (occ.flatMap (entry live)).length:=by
  rw [pool_segment]
  simp only [List.length_append]

/-- The transformed pool segment fits the batch's own interface bound as soon
as each per-occurrence emission does: the doubling is a factor `|occ|`, never
a factor on the hot column scan. -/
theorem segment_fits (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (top : List Bool) (P m : ℕ) (h : ∀ g ∈ occ, (entry live g).length ≤ m)
    (hfit : (natWord (2*occ.length)).length+(frame top).length+occ.length*m ≤ 1000*(P+2)^2) :
    (ExtDecompositionBatch.segment (pool live occ) top).length ≤ 1000*(P+2)^2 := by
  rw [segment_length]
  have hb:=flat_length live occ m h
  omega

end
end NearCubicWires.RepairSource.CloseoutRowsPoolWriter

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryOccurrence
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairSource SupplierPipeline
open scoped BigOperators

def copySlots : Fin 3→Fin 131 := ![129,55,130]
def eraseSlots : Fin 3→Fin 131 := ![55,127,128]
theorem copy_inj : Function.Injective copySlots := by decide
theorem erase_inj : Function.Injective eraseSlots := by decide
noncomputable def copy := RecoveryFocus.machine copySlots PoolEntryCursor.copy
noncomputable def entry := TapeEmbedding.machine 2 PoolEntryBaseline.machine
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine (Composition.machine copy entry) erase

def heads (pos : Nat) (out : List Bool) : Fin 131→Nat :=
  Fin.addCases (motive:=fun _=>Nat) (PoolEntryRestore.heads out) ![pos,0]
noncomputable def bank {q : Nat} (live : Finset (Fin q)) (B w : Nat)
    (source framed out : List Bool) : Fin 131→List Bool :=
  Fin.addCases (motive:=fun _=>List Bool) (PoolEntryBaseline.state live B w framed out)
    ![source,List.replicate (PoolEntry.reserve B q w) false]

theorem state_source {q : Nat} (live : Finset (Fin q)) (B w : Nat) (framed out : List Bool) :
    PoolEntryBaseline.state live B w framed out 55=framed := by
  simp [PoolEntryBaseline.state,PoolEntryRestore.input,PoolEntryRestore.state,
    PoolEntryRestore.padded,PoolEntryRestore.caps,Fin.addCases,PoolEntryBaseline.bank_source]

theorem state_other {q : Nat} (live : Finset (Fin q)) (B w : Nat) (a b out : List Bool)
    (i : Fin 129) (hi : i≠55) :
    PoolEntryBaseline.state live B w a out i=PoolEntryBaseline.state live B w b out i := by
  unfold PoolEntryBaseline.state PoolEntryRestore.input PoolEntryRestore.state
  revert hi
  refine Fin.addCases (m:=64) (n:=65) (fun j hj=>?_) (fun j _=>?_) i
  · simp only [Fin.addCases_left,PoolEntryRestore.padded]
    have hn : j≠55 := by intro he;subst j;exact hj rfl
    simp only [PoolEntryBaseline.bank,Function.update_of_ne hn]
  · simp only [Fin.addCases_right]
    refine Fin.addCases (m:=62) (n:=3) (fun k=>?_) (fun k=>?_) j
    · simp only [Fin.addCases_left,PoolEntryRestore.masters]
      have hn : PoolEntryRestore.work k≠55 := by fin_cases k <;>decide
      simp only [PoolEntryBaseline.bank,Function.update_of_ne hn]
    · simp only [Fin.addCases_right]

theorem bank_other {q : Nat} (live : Finset (Fin q)) (B w : Nat) (source a b out : List Bool)
    (i : Fin 131) (hi : i≠55) : bank live B w source a out i=bank live B w source b out i := by
  unfold bank
  revert hi
  refine Fin.addCases (m:=129) (n:=2) (fun j hj=>?_) (fun j _=>?_) i
  · simp only [Fin.addCases_left]
    apply state_other
    intro he;subst j;exact hj rfl
  · simp only [Fin.addCases_right]

theorem head_other (pos next : Nat) (out : List Bool) (i : Fin 131) (hi : i≠129) :
    heads pos out i=heads next out i := by
  unfold heads
  revert hi
  refine Fin.addCases (m:=129) (n:=2) (fun j _=>?_) (fun j hj=>?_) i
  · simp only [Fin.addCases_left]
  · simp only [Fin.addCases_right]
    fin_cases j
    · exact False.elim (hj rfl)
    · rfl

theorem copy_bank {q : Nat} (live : Finset (Fin q)) (B w : Nat) (source framed out : List Bool) :
    ∀ j,bank live B w source framed out (copySlots j)=
      PoolEntryCursor.bank source framed (PoolEntry.reserve B q w) j := by
  intro j;fin_cases j
  · rfl
  · exact state_source live B w framed out
  · rfl

theorem copy_run {q : Nat} (live : Finset (Fin q)) (B w : Nat)
    (pre bits tail out : List Bool) (hS : (RepairOrdinary.frame bits).length≤PoolEntry.reserve B q w) :
    Step copy (4*bits.length+4) (heads pre.length out)
      (bank live B w (pre++RepairOrdinary.frame bits++tail) (List.replicate (PoolEntry.reserve B q w) false) out)
      (heads (pre.length+(RepairOrdinary.frame bits).length) out)
      (bank live B w (pre++RepairOrdinary.frame bits++tail)
        (ZeroPadding.pad (PoolEntry.reserve B q w) (RepairOrdinary.frame bits)) out) := by
  have h := (PoolEntryCursor.copy_run pre bits tail (PoolEntry.reserve B q w) hS).dock
    copySlots copy_inj (heads pre.length out)
    (bank live B w (pre++RepairOrdinary.frame bits++tail) (List.replicate (PoolEntry.reserve B q w) false) out)
    (by intro j;fin_cases j <;>rfl) (copy_bank live B w _ _ out)
  refine h.congr ?_ ?_
  · funext i
    cases hp : RecoveryFocus.pick copySlots i with
    | some j =>
      have he := RecoveryFocus.slot_of_pick copySlots hp
      rw [←he,dockH_slot _ copy_inj]
      fin_cases j <;>rfl
    | none =>
      have hn : ∀ j,copySlots j≠i := by
        intro j he
        rw [←he,RecoveryFocus.pick_slot copySlots copy_inj j] at hp
        contradiction
      rw [dockH_other _ _ _ i hn]
      exact head_other _ _ out i (Ne.symm (hn 0))
  · apply HierarchyAllocation.install_eq copySlots copy_inj
    · exact copy_bank live B w _ _ out
    · intro i hi
      exact bank_other live B w _ _ _ out i (Ne.symm (hi 1))

theorem erase_bank {q : Nat} (live : Finset (Fin q)) (B w : Nat) (source framed out : List Bool) :
    ∀ j,bank live B w source framed out (eraseSlots j)=
      (![framed,List.replicate (PoolEntry.reserve B q w) true,
        List.replicate (PoolEntry.reserve B q w+1) false] : Fin 3→List Bool) j := by
  intro j;fin_cases j
  · exact state_source live B w framed out
  · rfl
  · rfl

theorem erase_run {q : Nat} (live : Finset (Fin q)) (B w : Nat) (source framed out : List Bool)
    (pos : Nat) (hS : framed.length≤PoolEntry.reserve B q w) :
    Step erase (2*PoolEntry.reserve B q w+4) (heads pos out)
      (bank live B w source framed out) (heads pos out)
      (bank live B w source (List.replicate (PoolEntry.reserve B q w) false) out) := by
  have hh : ∀ j,heads pos out (eraseSlots j)=0 := by intro j;fin_cases j <;>rfl
  have h := (PoolEntryCursor.erase_run framed (PoolEntry.reserve B q w) hS).dock
    eraseSlots erase_inj (heads pos out) (bank live B w source framed out) hh
    (erase_bank live B w source framed out)
  refine h.congr (dockH_existing _ _ _ hh) ?_
  apply HierarchyAllocation.install_eq eraseSlots erase_inj
  · exact erase_bank live B w source _ out
  · intro i hi
    exact bank_other live B w source _ _ out i (Ne.symm (hi 0))

def budget (B q w : Nat) := PoolEntryBaseline.budget B q w+2*PoolEntry.reserve B q w+4*B+10

theorem run {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat)
    (pre tail out : List Bool) (hw : 0<w) (hq : q≤w)
    (hb : (CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : (g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w) :
    Step machine (budget B q w) (heads pre.length out)
      (bank live B w (pre++RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)++tail)
        (List.replicate (PoolEntry.reserve B q w) false) out)
      (heads (pre.length+(RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)).length)
        (out++CloseoutRowsPoolWriter.entry live g))
      (bank live B w (pre++RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)++tail)
        (List.replicate (PoolEntry.reserve B q w) false) (out++CloseoutRowsPoolWriter.entry live g)) := by
  have square : B+q+w+1≤(B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  have hS : (RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)).length≤PoolEntry.reserve B q w := by
    rw [RepairOrdinary.frame_length]
    unfold PoolEntry.reserve
    omega
  have first := copy_run live B w pre (CloseoutRowsCircuitBottom.nativeWord g) tail out hS
  have middle := (PoolEntryBaseline.run live g B w out hw hq hb hm).embed
    (![pre.length+(RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)).length,0] : Fin 2→Nat)
    (![pre++RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)++tail,
      List.replicate (PoolEntry.reserve B q w) false] : Fin 2→List Bool)
  have last := erase_run live B w
    (pre++RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)++tail)
    (ZeroPadding.pad (PoolEntry.reserve B q w) (RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)))
    (out++CloseoutRowsPoolWriter.entry live g)
    (pre.length+(RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)).length)
    (by rw [ZeroPadding.pad_length,Nat.max_eq_left hS])
  have all := (first.seq middle).seq last
  exact all.enlarge (by unfold budget;omega)

end NearCubicWires.P1Closure.PoolEntryOccurrence

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryLoop
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairSource SupplierPipeline VerifierDecoding
open scoped BigOperators

def original {q : Nat} (g : SupportedNormalizedGate q) :=
  RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g)
def stream {q : Nat} (occ : List (SupportedNormalizedGate q)) := occ.flatMap original
def cursorPrefix {q : Nat} (occ : List (SupportedNormalizedGate q)) (j : Nat) := stream (occ.take j)
noncomputable def cfg {q : Nat} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (B w j : Nat) (out : List Bool) :=
  ({ control:=PoolEntryOccurrence.machine.start
     heads:=PoolEntryOccurrence.heads (cursorPrefix occ j).length out
     tapes:=PoolEntryOccurrence.bank live B w (stream occ) (List.replicate (PoolEntry.reserve B q w) false) out } :
    Configuration 131 _)
noncomputable def machine := CloseoutRowsDegreeLoop.machine PoolEntryOccurrence.machine
def budget (N B q w : Nat) := N*(PoolEntryOccurrence.budget B q w+3)+3

theorem split_stream {q : Nat} (occ : List (SupportedNormalizedGate q)) (j : Nat) (hj : j<occ.length) :
    cursorPrefix occ j++original occ[j]++stream (occ.drop (j+1))=stream occ := by
  have h : occ.take j++occ[j]::occ.drop (j+1)=occ := by
    rw [←List.drop_eq_getElem_cons hj,List.take_append_drop]
  have h := congrArg (fun xs=>xs.flatMap original) h
  simpa only [cursorPrefix,stream,List.flatMap_append,List.flatMap_cons,List.append_assoc] using h

theorem next_cursor {q : Nat} (occ : List (SupportedNormalizedGate q)) (j : Nat) (hj : j<occ.length) :
    (cursorPrefix occ (j+1)).length=(cursorPrefix occ j).length+(original occ[j]).length := by
  simp only [cursorPrefix,stream,List.take_succ_eq_append_getElem hj,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]

theorem body_run {q : Nat} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (B w j : Nat) (out : List Bool) (hj : j<occ.length) (hw : 0<w) (hq : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w) :
    Step PoolEntryOccurrence.machine (PoolEntryOccurrence.budget B q w)
      (cfg live occ B w j out).heads (cfg live occ B w j out).tapes
      (cfg live occ B w (j+1) (out++CloseoutRowsPoolWriter.emitAt live occ j)).heads
      (cfg live occ B w (j+1) (out++CloseoutRowsPoolWriter.emitAt live occ j)).tapes := by
  have hmem : occ[j]∈occ := List.getElem_mem hj
  have h := PoolEntryOccurrence.run live occ[j] B w (cursorPrefix occ j) (stream (occ.drop (j+1))) out
    hw hq (hb _ hmem) (hm _ hmem)
  have he : CloseoutRowsPoolWriter.emitAt live occ j=CloseoutRowsPoolWriter.entry live occ[j] := by
    simp only [CloseoutRowsPoolWriter.emitAt,List.getElem?_eq_getElem hj,Option.elim_some]
  rw [←original,split_stream occ j hj,←next_cursor occ j hj,←he] at h
  exact h

theorem run {q : Nat} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (B w : Nat) (out : List Bool) (hw : 0<w) (hq : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w) :
    ∃ r,runFrom machine (budget occ.length B q w)
      (RepeatMachine.cfg 0 (cfg live occ B w 0 out) occ.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3
        (cfg live occ B w occ.length (out++occ.flatMap (CloseoutRowsPoolWriter.entry live))) occ.length 1 ∧
      r.steps≤budget occ.length B q w := by
  apply CloseoutRowsPoolWriter.writer_loop PoolEntryOccurrence.machine (cfg live occ B w)
    (PoolEntryOccurrence.budget B q w) live occ out
  · intro j hj pre;rfl
  · intro j hj pre
    obtain ⟨r,hr,hh,ht,hs⟩ := body_run live occ B w j pre hj hw hq hb hm
    exact ⟨r,hr,hh,ht,hs⟩

theorem segment_run {q : Nat} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (B w : Nat) (top : List Bool) (hw : 0<w) (hq : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w) :
    ∃ r,runFrom machine (budget occ.length B q w)
      (RepeatMachine.cfg 0
        (cfg live occ B w 0 (RepairRepresentation.natWord (2*occ.length)++RepairOrdinary.frame top)) occ.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3
        (cfg live occ B w occ.length (ExtDecompositionBatch.segment (CloseoutRowsUniversal.pool live occ) top))
        occ.length 1 ∧
      r.steps≤budget occ.length B q w := by
  have h := run live occ B w (RepairRepresentation.natWord (2*occ.length)++RepairOrdinary.frame top) hw hq hb hm
  rw [CloseoutRowsPoolWriter.writer_cursor] at h
  exact h

end NearCubicWires.P1Closure.PoolEntryLoop

end
