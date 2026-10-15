import Proof.Hierarchy.HierarchyBinaryMultiplyEntry

/-! Complete short binary multiplication: actual blank-workspace setup,
factor-bit loop, and global rewind. Inputs and the paid width are retained.
Runtime is polynomial in operand width, never in the multiplied value. -/
namespace NearCubicWires.RepairOrdinary.HierarchyMultiplyEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loopPhase := TapeEmbedding.machine 5 HierarchyMultiply.machine
noncomputable def raw := Composition.machine bootstrap loopPhase
noncomputable def machine := Rewind.machine raw
def rawBudget (w : ℕ) (bits : List Bool) := 20*w+25+(bits.length*(32*w+40)+2)
def budget (w : ℕ) (bits : List Bool) := 128*(w+1)*(bits.length+1)
def input14 (w a : ℕ) (bits : List Bool) : Fin 14 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (13+1) => List Bool) (input w a bits) (fun _ : Fin 1 => [])

theorem raw_run (w a : ℕ) (bits : List Bool) (hfit : a*2^bits.length<2^w) :
    ∃ r : ExecutionReceipt 13 (20+Fintype.card (RecoveryCalls.Control HierarchyMultiply.sizes)),
      run raw (rawBudget w bits) (input w a bits)=some r ∧
      r.final.tapes 3=frame (binary w (a*value bits)) ∧ r.final.tapes 0=frame bits ∧
      r.final.tapes 8=frame (binary w a) ∧ r.final.tapes 9=List.replicate w true ∧
      r.final.tapes 12=List.replicate (2*w+1) false ∧
      r.steps≤rawBudget w bits := by
  obtain ⟨boot,hboot,hbt,hbh,hbs⟩ := bootstrap_ready w a bits
  obtain ⟨mul,hmul,hout,hfactor,_,hms⟩ := HierarchyMultiply.multiply_run w a bits [] []
    (by simp) (by simp) hfit
  let extra : Fin 5 → List Bool := ![frame (binary w a),List.replicate w true,[false],[true],
    List.replicate (2*w+1) false]
  have hembed := TapeEmbedding.run_embed HierarchyMultiply.machine (fun _ : Fin 5 => 0) extra
    (bits.length*(32*w+40)+2) _ mul hmul
  have hi : TapeEmbedding.config (fun _ : Fin 5 => 0) extra
      (initialConfiguration HierarchyMultiply.machine
        (({left:=a,duplicate:=a,accumulator:=0,sum:=[],doubled:=[]} : HierarchyMultiply.Store).tapes w (frame bits)))=
      initialConfiguration loopPhase (prepared w a bits) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hembed
  have hrestart : Composition.restart boot.final loopPhase.start=
      initialConfiguration loopPhase (prepared w a bits) := by
    apply configuration_ext
    · rfl
    · exact funext hbh
    · exact hbt
  have hsecond : runFrom loopPhase (bits.length*(32*w+40)+2)
      (Composition.restart boot.final loopPhase.start)=
      some (TapeEmbedding.receipt (fun _ : Fin 5 => 0) extra mul) := by
    rw [hrestart]
    exact hembed
  have h := Composition.run_join bootstrap loopPhase (20*w+24) (bits.length*(32*w+40)+2)
    _ boot (TapeEmbedding.receipt (fun _ : Fin 5 => 0) extra mul) hboot hsecond
  let r := Composition.joinedReceipt boot (TapeEmbedding.receipt (fun _ : Fin 5 => 0) extra mul)
  refine ⟨r,?_,?_,?_,?_,?_,?_,?_⟩
  · exact h
  · exact hout
  · exact hfactor
  · rfl
  · rfl
  · rfl
  · change boot.steps+1+mul.steps≤rawBudget w bits
    dsimp only [rawBudget]
    omega

theorem budget_dominates (w : ℕ) (bits : List Bool) : 2*rawBudget w bits+2≤budget w bits := by
  dsimp only [rawBudget,budget]
  nlinarith

theorem multiply_run (w a : ℕ) (bits : List Bool) (hfit : a*2^bits.length<2^w) :
    ∃ r : ExecutionReceipt 14 (20+Fintype.card (RecoveryCalls.Control HierarchyMultiply.sizes)+2),
      run machine (budget w bits) (input14 w a bits)=some r ∧
      r.final.tapes 3=frame (binary w (a*value bits)) ∧ r.final.tapes 0=frame bits ∧
      r.final.tapes 8=frame (binary w a) ∧ r.final.tapes 9=List.replicate w true ∧
      r.final.tapes 12=List.replicate (2*w+1) false ∧
      (∀ i,r.final.heads i=0) ∧ r.steps≤budget w bits := by
  obtain ⟨base,hbase,hout,hfactor,hleft,hwidth,hreset,hs⟩ := raw_run w a bits hfit
  obtain ⟨r,hr,ht,_,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase 0
  have hb : 2*base.steps+2≤budget w bits := (by omega : 2*base.steps+2≤2*rawBudget w bits+2).trans
    (budget_dominates w bits)
  have hm := run_moreFuel machine (2*base.steps+2) (budget w bits-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨r,hm,?_,?_,?_,?_,?_,hh,hsteps.le.trans hb⟩
  · exact (ht 3).trans hout
  · exact (ht 0).trans hfactor
  · exact (ht 8).trans hleft
  · exact (ht 9).trans hwidth
  · exact (ht 12).trans hreset

end NearCubicWires.RepairOrdinary.HierarchyMultiplyEntry
