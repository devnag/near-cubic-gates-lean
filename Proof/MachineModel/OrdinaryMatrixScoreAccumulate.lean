import Proof.MachineModel.OrdinaryMatrixScoreWeightLoad

/-! The selected score update uses only the accepted add and copy/reset
programs. This five-tape parent is reused for either signed accumulator. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreAccumulate
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def add : Machine 5 7 := TapeEmbedding.machine 1 BoundaryAdvance.machine
def copySlots : Fin 4 → Fin 5 := ![2,1,4,3]
noncomputable def copy : Machine 5 6 := RecoveryFocus.machine copySlots copyMachine
noncomputable def machine : Machine 5 13 := Composition.machine add copy
def input (w x a : ℕ) (backing : List Bool) : Fin 5 → List Bool :=
  ![frame (binary w x),frame (binary w a),backing,List.replicate (4*w+3) false,
    List.replicate (2*w+1) false]
def output (w x a : ℕ) : Fin 5 → List Bool :=
  ![frame (binary w x),frame (binary w (x+a)),frame (binary w (x+a)),
    List.replicate (4*w+3) false,List.replicate (2*w+1) false]

theorem accumulate_ready (w x a : ℕ) (backing : List Bool)
    (hfit : x+a<2^w) (hb : backing.length≤2*w+1) :
    ReadyRun machine (12*w+13) (input w x a backing) (output w x a) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := HierarchyBinary.add_ready w x a (4*w+3) backing hfit hb
  simp only [max_eq_left (by omega : 2*w+1≤4*w+3)] at ht
  have he := TapeEmbedding.run_embed BoundaryAdvance.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => List.replicate (2*w+1) false) _ _ base hr
  let first := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate (2*w+1) false) base
  obtain ⟨last,hl,hlt,hlh,hls⟩ := copy_ready (binary w (x+a)) (frame (binary w a))
    (2*w+1) (4*w+3) (by simp)
  simp only [binary_length,max_self] at hl hlt hls
  let entry := initialConfiguration copyMachine
    ![frame (binary w (x+a)),frame (binary w a),List.replicate (2*w+1) false,List.replicate (4*w+3) false]
  have hi : RecoveryFocus.config copySlots first.final.heads first.final.tapes entry=
      Composition.restart first.final copy.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i <;> simp [copySlots,first,TapeEmbedding.receipt,TapeEmbedding.config,
        Fin.addCases,hh,entry,initialConfiguration]
    · intro i
      fin_cases i <;> simp [copySlots,first,TapeEmbedding.receipt,TapeEmbedding.config,
        Fin.addCases,ht,entry,initialConfiguration]
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config copySlots (by decide) copyMachine
    first.final.heads first.final.tapes _ entry last hl
  rw [hi] at hf
  have hj := Composition.run_join add copy (4*w+4) (8*w+8) _ first focused he hf
  have hin : Composition.leftConfig 6 (TapeEmbedding.config (fun _ : Fin 1 => 0)
      (fun _ : Fin 1 => List.replicate (2*w+1) false) (initialConfiguration BoundaryAdvance.machine
        ![frame (binary w x),frame (binary w a),backing,List.replicate (4*w+3) false]))=
      initialConfiguration machine (input w x a backing) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,initialConfiguration]
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,initialConfiguration,input]
  rw [hin] at hj
  have htime : 4*w+4+1+(8*w+8)=12*w+13 := by omega
  rw [htime] at hj
  have pick (i : Fin 5) : RecoveryFocus.pick copySlots i=
      (![none,some 1,some 0,some 3,some 2] : Fin 5 → Option (Fin 4)) i := by
    fin_cases i
    · decide
    · exact RecoveryFocus.pick_slot copySlots (by decide) 1
    · exact RecoveryFocus.pick_slot copySlots (by decide) 0
    · exact RecoveryFocus.pick_slot copySlots (by decide) 3
    · exact RecoveryFocus.pick_slot copySlots (by decide) 2
  refine ⟨Composition.joinedReceipt first focused,hj,?_,?_,?_⟩
  · change focused.final.tapes=_
    rw [hff]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,pick,output,first,TapeEmbedding.receipt,
      TapeEmbedding.config,Fin.addCases,ht,hlt]
  · intro i
    change focused.final.heads i=0
    rw [hff]
    fin_cases i <;> simp [RecoveryFocus.config,pick,hlh,first,TapeEmbedding.receipt,TapeEmbedding.config,
      Fin.addCases,hh]
  · change base.steps+1+focused.steps=_
    rw [hs,hfs,hls]
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreAccumulate
