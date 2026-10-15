import Proof.CaseAnalysis.WitnessTraversalCounted
import Proof.PCP.PCPTraversalProducer
import Proof.MachineModel.OrdinaryMatrixWilliamsProduct

/-! The accepted canonical serializer consumes the actual all-raw DFS
stream. Its raw-input exponent is 24, fixed before the hierarchy clock. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Reencode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree CanonicalBinaryProgram
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem atom_le (code a : ℕ) (ha:a∈(tree code).atoms) : a≤code := by
  induction code using Nat.strong_induction_on generalizing a with
  | h code ih=>
    rw [tree] at ha
    split_ifs at ha with hb hl
    · have hp:(Nat.unpair code).2<code:=by
        have h:=Nat.unpair_add_le code
        rw [hb] at h
        omega
      simp only [BalancedTraversalTree.atoms,List.mem_append] at ha
      rcases ha with h|h
      · exact (ih _ ((Nat.unpair_left_le _).trans_lt hp) a h).trans
          ((Nat.unpair_left_le _).trans (Nat.unpair_right_le code))
      · exact (ih _ ((Nat.unpair_right_le _).trans_lt hp) a h).trans
          ((Nat.unpair_right_le _).trans (Nat.unpair_right_le code))
    · simp only [BalancedTraversalTree.atoms,List.mem_singleton] at ha
      exact ha.trans_le (Nat.unpair_right_le code)
    · simp only [BalancedTraversalTree.atoms,List.not_mem_nil] at ha

theorem atoms_length (t : BalancedTraversalTree) : t.atoms.length≤t.nodeCount := by
  induction t with
  | empty=>simp [BalancedTraversalTree.atoms,BalancedTraversalTree.nodeCount]
  | leaf a=>rfl
  | branch l r hl hr=>
    simp only [BalancedTraversalTree.atoms,List.length_append,BalancedTraversalTree.nodeCount]
    omega

def fields (bits : List Bool) := (tree (value bits)).atoms.map (SignedSortKey.binary bits.length)

theorem fields_values (bits : List Bool) : PCPSerializerMass.values (fields bits)=(tree (value bits)).atoms := by
  unfold PCPSerializerMass.values fields
  rw [List.map_map]
  calc
    _ = List.map id (tree (value bits)).atoms := by
      apply List.map_congr_left
      intro a ha
      exact SignedSortKey.binary_value bits.length a ((atom_le _ _ ha).trans_lt (value_lt bits))
    _ = _ := List.map_id _

theorem fields_stream (bits : List Bool) :
    FieldList.stream (fields bits)=atomStream bits.length (tree (value bits)).atoms := by
  unfold fields
  generalize (tree (value bits)).atoms=values
  induction values with
  | nil=>rfl
  | cons a values ih=>
    simpa only [List.map_cons,FieldList.stream_cons,atomStream,List.flatMap_cons] using
      (congrArg (fun xs=>frame (SignedSortKey.binary bits.length a)++xs) ih)

theorem fields_mass (bits : List Bool) :
    PCPSerializerMass.mass (fields bits)=(tree (value bits)).atoms.length*(2*bits.length+1) := by
  simp [PCPSerializerMass.mass,fields,List.map_map,Function.comp_def]

theorem count_bound (bits : List Bool) : TraversalCounted.count bits≤bits.length+1 :=
  (atoms_length _).trans (word_nodes bits)

def budget (bits : List Bool) := TraversalCounted.budget bits+1+PCPTraversal.budget (PCPSerializerMass.mass (fields bits))
def polynomialBudget (bits : List Bool) := 1000000000000000000*(bits.length+1)^24

theorem budget_bound (bits : List Bool) : budget bits≤polynomialBudget bits := by
  have hc:=count_bound bits
  have hm:PCPSerializerMass.mass (fields bits)+1≤3*(bits.length+1)^2:=by
    rw [fields_mass]
    have hn:=Nat.mul_le_mul_right (2*bits.length+1) hc
    change (tree (value bits)).atoms.length*(2*bits.length+1)≤_ at hn
    nlinarith
  have hp:=Nat.pow_le_pow_left hm 12
  rw [mul_pow,←pow_mul] at hp
  norm_num at hp
  have h3:(bits.length+1)^3≤(bits.length+1)^24:=pow_le_pow_right₀ (by omega) (by omega)
  have h1:bits.length+1≤(bits.length+1)^24:=Nat.le_self_pow (by decide) _
  have hpos:1≤(bits.length+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold budget polynomialBudget TraversalCounted.budget TraversalCold.budget
    RepairSource.ProjectionNormalization.Counter.budget PCPTraversal.budget
  omega

noncomputable def machine:=PCPTraversalBank.producerMachine
  (27 : Fin (36+1+3)) (38 : Fin (36+1+3)) TraversalCounted.machine
def input (bits : List Bool) : Fin (36+1+3+128)→List Bool:=
  Fin.addCases (m:=36+1+3) (n:=128) (motive:=fun _=>List Bool) (TraversalCounted.input bits) (fun _=>[])

theorem reencode_run (bits : List Bool) :
    ∃ r,run machine (polynomialBudget bits) (input bits)=some r ∧ r.steps≤polynomialBudget bits ∧
      r.final.tapes 118=(CanonicalBinary.encodeBalancedList (tree (value bits)).atoms).bits ∧
      r.final.heads 118=0 ∧
      r.final.tapes 27=atomStream bits.length (tree (value bits)).atoms := by
  obtain ⟨raw,hr,_,hout,hcount,hsourceHead,hcountHead⟩:=TraversalCounted.counted_run bits
  obtain ⟨r,h,_,hraw,_,hhead,htapes,_,hsteps⟩:=PCPTraversalBank.producer_run
    (27 : Fin (36+1+3)) (38 : Fin (36+1+3)) (by decide) TraversalCounted.machine (TraversalCounted.budget bits)
    _ raw hr [] (fields bits) [] hsourceHead hcountHead
    (by simpa only [List.nil_append,List.append_nil,fields_stream] using hout)
    (by simpa only [fields,List.length_map,TraversalCounted.count] using hcount)
  rw [MatrixWilliamsProduct.initial_join] at h
  change run machine (budget bits) (input bits)=some r at h
  have more:=run_moreFuel machine (budget bits) (polynomialBudget bits-budget bits) (input bits) r h
  rw [Nat.add_sub_of_le (budget_bound bits)] at more
  have hi : (78 : Fin 128).natAdd (36+1+3) = (118 : Fin (36+1+3+128)) := by decide
  rw [hi] at hraw hhead
  refine ⟨r,more,hsteps.trans (budget_bound bits),?_,hhead,?_⟩
  · simpa only [PCPTraversal.code,fields_values] using hraw
  · exact (htapes 27).trans hout

end NearCubicWires.RepairOrdinary.CloseoutWitness.Reencode
