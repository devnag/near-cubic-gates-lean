import Proof.MachineModel.OrdinaryMatrixVariableReset
import Proof.Amplification.RecoveryTapeSupport

/-! Finite workspace for the actual indexed source call and paid reset.
The enclosing scheduler must physically supply this capacity; after a call,
every local tape has exactly that bounded support and can be erased together. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableWorkspace
open LocalBitMultitape MatrixScoreBatch RepairRepresentation MatrixWilliamsProduct
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapeCount (a : WilliamsAlgorithm) := MatrixVariableProduct.tapes a+1
noncomputable def caps (a : WilliamsAlgorithm) (capacity : ℕ) (i : Fin (tapeCount a)) :=
  if i.val=424 then 0 else capacity
noncomputable def footprint (a : WilliamsAlgorithm) (r : Request) :=
  (physicalInput r).length+2*r.p+MatrixVariableReset.budget a r+4

theorem add_bound {m n : ℕ} {f : Fin m → ℕ} {g : Fin n → ℕ} {bound : ℕ}
    (hf : ∀ i,f i≤bound) (hg : ∀ i,g i≤bound) (i : Fin (m+n)) :
    Fin.addCases f g i≤bound := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left] using hf j
  · simpa only [Fin.addCases_right] using hg j

theorem add_length_bound {m n : ℕ} {f : Fin m → List Bool} {g : Fin n → List Bool} {bound : ℕ}
    (hf : ∀ i,(f i).length≤bound) (hg : ∀ i,(g i).length≤bound) (i : Fin (m+n)) :
    (Fin.addCases (motive := fun _ => List Bool) f g i).length≤bound := by
  refine Fin.addCases (motive := fun i => (Fin.addCases (motive := fun _ => List Bool) f g i).length≤bound) (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left] using hf j
  · simpa only [Fin.addCases_right] using hg j

theorem entry_bounds (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) :
    (∀ i,(MatrixVariableReset.input a r bit).heads i≤1) ∧
    (∀ i,((MatrixVariableReset.input a r bit).tapes i).length≤(physicalInput r).length+2*bit+2) := by
  have hp (i : Fin 425) : (MatrixVariableInput.input r bit).heads i≤1 := by
    change (MatrixVariablePlane.input r bit).heads i≤1
    rw [MatrixVariablePlane.input_heads]
    split <;> omega
  have ht (i : Fin 425) : ((MatrixVariableInput.input r bit).tapes i).length≤(physicalInput r).length+2*bit+2 := by
    change ((MatrixVariablePlane.input r bit).tapes i).length≤_
    rw [MatrixVariablePlane.input_tapes]
    split
    · omega
    · split
      · rw [UnaryTemplate.tape_length]; omega
      · simp
  constructor
  · intro i
    change Fin.addCases (MatrixVariableProduct.input a r bit).heads (fun _ : Fin 1 => 0) i≤1
    apply add_bound (hg := by intro j; omega)
    intro j
    change Fin.addCases (MatrixVariableInput.input r bit).heads
      (fun _ : Fin (source a).program.tapeCount => 0) j≤1
    exact add_bound hp (by intro k; omega) j
  · intro i
    change (Fin.addCases (motive := fun _ => List Bool) (MatrixVariableProduct.input a r bit).tapes (fun _ : Fin 1 => [] ) i).length≤_
    apply add_length_bound (hg := by intro j; simp)
    intro j
    change (Fin.addCases (motive := fun _ => List Bool) (MatrixVariableInput.input r bit).tapes
      (fun _ : Fin (source a).program.tapeCount => []) j).length≤_
    exact add_length_bound ht (by intro k; simp) j

theorem workspace_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit capacity : ℕ)
    (ht : bit<r.p) (hc : footprint a r≤capacity) : ∃ actual,
    runFrom (MatrixVariableReset.machine a negative) (MatrixVariableReset.budget a r)
      (ZeroPadding.config (caps a capacity) (MatrixVariableReset.input a r bit))=some actual ∧
    actual.final.tapes ((MatrixVariableProduct.outputTape a).castAdd 1)=
      ZeroPadding.pad (caps a capacity ((MatrixVariableProduct.outputTape a).castAdd 1)) (planeCounts r negative bit) ∧
    (∀ j,actual.final.tapes (((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 1)=
      ZeroPadding.pad (caps a capacity (((MatrixVariableDimensions.selected j).castAdd (source a).program.tapeCount).castAdd 1))
        (MatrixVariableDimensions.values r negative bit j)) ∧
    (∀ i : Fin (MatrixVariableProduct.tapes a),actual.final.heads (i.castAdd 1)=if i.val=424 then 1 else 0) ∧
    actual.final.heads ((0 : Fin 1).natAdd (MatrixVariableProduct.tapes a))=0 ∧
    (∀ i,i.val≠424 → (actual.final.tapes i).length=capacity) ∧
    actual.steps≤MatrixVariableReset.budget a r := by
  obtain ⟨base,hb,bt,fields,heads,logH,_,bs⟩ := MatrixVariableReset.reset_run a r negative bit ht
  obtain ⟨hh,htape⟩ := entry_bounds a r bit
  have supp := RecoveryTapeSupport.run_support (MatrixVariableReset.machine a negative) _ _ base hb
    ((physicalInput r).length+2*bit+2) 1 hh
    (fun i => (htape i).trans (Nat.le_max_left _ _))
  have support (i : Fin (tapeCount a)) : (base.final.tapes i).length≤capacity := by
    have h := supp i
    have hm : max ((physicalInput r).length+2*bit+2) (1+base.steps+1)≤footprint a r := by
      unfold footprint
      omega
    exact h.trans (hm.trans hc)
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config (MatrixVariableReset.machine a negative)
    (caps a capacity) _ _ base hb
  refine ⟨actual,ha,?_,?_,?_,?_,?_,hs.trans_le bs⟩
  · simp only [hf,ZeroPadding.config,bt]
  · intro j; simp only [hf,ZeroPadding.config,fields j]
  · intro i; exact (congrArg (fun c => c.heads (i.castAdd 1)) hf).trans (heads i)
  · exact (congrArg (fun c => c.heads ((0 : Fin 1).natAdd (MatrixVariableProduct.tapes a))) hf).trans logH
  · intro i hi
    simp only [hf,ZeroPadding.config,ZeroPadding.pad_length,caps,hi,if_false]
    exact max_eq_left (support i)

end NearCubicWires.RepairOrdinary.MatrixVariableWorkspace
