import Proof.PCP.PCPPNativeOracleSkipLoop

/-! The original native oracle is scanned from its real beginning through
the two header fields and every three-field node. Its original footer is
therefore reached by execution, using the actual retained size driver. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeOracleFooterPosition
open LocalBitMultitape SourceInterfaces RepairRepresentation PCPPQueryField
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 (pair false)
noncomputable def machine := Composition.machine first PCPPNativeOracleSkip.machine
def backing {R : ℕ} (oracle : BooleanCircuit R) :=
  PCPPNativeOracleSkip.savedNodes oracle.nodes (saved oracle.size (saved R []))
def bodyPrefix {R : ℕ} (oracle : BooleanCircuit R) := PCPPNativeQuery.originalHead oracle++PCPPNativeQuery.originalBody oracle
def budget {R : ℕ} (oracle : BooleanCircuit R) :=
  pairCost R oracle.size+1+(PCPPNativeOracleSkip.stream oracle.nodes).length+11*oracle.size+3
noncomputable def entry {R : ℕ} (oracle : BooleanCircuit R) :=
  (⟨machine.start,![0,0,0,1],![PCPPNative.descriptor oracle,[],[],CompareMachine.word oracle.size]⟩ : Configuration 4 _)

theorem position_run {R : ℕ} (oracle : BooleanCircuit R) : ∃ result,
    runFrom machine (budget oracle) (entry oracle)=some result ∧ result.steps=budget oracle ∧
    result.final.heads=![(bodyPrefix oracle).length,0,0,1] ∧
    result.final.tapes=![PCPPNative.descriptor oracle,backing oracle,[],CompareMachine.word oracle.size] := by
  obtain ⟨a,ha,af,as⟩ := pair_run false []
    (PCPPNativeOracleSkip.stream oracle.nodes++natWord oracle.output.val) [] [] R oracle.size
  have he : []++pairBits R oracle.size++(PCPPNativeOracleSkip.stream oracle.nodes++natWord oracle.output.val)=
      PCPPNative.descriptor oracle := by
    rw [PCPPNativeQuery.original_parts oracle]
    simp only [List.nil_append,pairBits,fieldBits,PCPPNativeQuery.originalHead,PCPPNativeQuery.originalBody,
      PCPPNativeOracleSkip.stream,PCPPNativeNodeLoop.nativeWords,List.append_assoc]
  rw [he] at ha af
  simp only [List.length_nil,Nat.zero_add,selected,Bool.false_eq_true,ite_false,List.append_nil] at af
  let lifted := TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word oracle.size) a
  have firstRun := TapeEmbedding.run_embed (pair false) (fun _ : Fin 1 => 1)
    (fun _ => CompareMachine.word oracle.size) _ _ a ha
  obtain ⟨b,hb,bf,bs⟩ := PCPPNativeOracleSkip.nodes_run (pairBits R oracle.size) oracle.nodes
    (natWord oracle.output.val) (saved oracle.size (saved R [])) []
  have hbsource : pairBits R oracle.size++PCPPNativeOracleSkip.stream oracle.nodes++natWord oracle.output.val=
      PCPPNative.descriptor oracle := by simpa only [List.nil_append,List.append_assoc] using he
  rw [hbsource] at hb bf
  have hmid : Composition.restart lifted.final PCPPNativeOracleSkip.machine.start=
      PCPPNativeOracleSkip.cfg 0 (PCPPNative.descriptor oracle) (pairBits R oracle.size).length
        (saved oracle.size (saved R [])) [] oracle.nodes.length 1 := by
    dsimp only [lifted,TapeEmbedding.receipt]
    rw [af]
    apply configuration_ext <;> rfl
  rw [←hmid] at hb
  have joined := Composition.run_join first PCPPNativeOracleSkip.machine _ _ _ lifted b firstRun hb
  have ht : pairCost R oracle.size+1+
      ((PCPPNativeOracleSkip.stream oracle.nodes).length+11*oracle.nodes.length+3)=budget oracle := by
    unfold budget BooleanCircuit.size
    omega
  rw [ht] at joined
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 1 => 1)
      (fun _ => CompareMachine.word oracle.size)
      (store (s := 8) 0 (PCPPNative.descriptor oracle) 0 [] []))=entry oracle := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  simp only [List.length_nil] at joined
  rw [hi] at joined
  refine ⟨Composition.joinedReceipt lifted b,joined,?_,?_,?_⟩
  · change a.steps+1+b.steps=_
    rw [as,bs]
    exact ht
  · change b.final.heads=_
    rw [bf]
    have hp : (pairBits R oracle.size).length+(PCPPNativeOracleSkip.stream oracle.nodes).length=(bodyPrefix oracle).length := by
      simp only [bodyPrefix,pairBits,fieldBits,PCPPNativeQuery.originalHead,PCPPNativeQuery.originalBody,
        PCPPNativeOracleSkip.stream,PCPPNativeNodeLoop.nativeWords,List.length_append]
    simp only [PCPPNativeOracleSkip.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,store]
    funext i; fin_cases i <;> simp [hp,Fin.addCases]
  · change b.final.tapes=_
    rw [bf]
    funext i
    fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.PCPPNativeOracleFooterPosition
