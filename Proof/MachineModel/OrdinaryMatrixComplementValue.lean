import Proof.MachineModel.OrdinaryMatrixComplement

/-! Exact arithmetic of the physically emitted complement and its use as
the second operand of the existing right-cell interval scan. -/
namespace NearCubicWires.RepairOrdinary.MatrixComplement
open LocalBitMultitape SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem value_injective (xs ys : List Bool) (hl : xs.length=ys.length) (hv : value xs=value ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hlen : xs.length=ys.length := by simpa using hl
      cases x <;> cases y <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv
      · have ht : value xs=value ys := by omega
        simp [ih ys hlen ht]
      · omega
      · omega
      · have ht : value xs=value ys := by omega
        simp [ih ys hlen ht]

theorem complement_value (bits : List Bool) : value (bits.map Bool.not)+value bits+1=2^bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [value,pow_succ] at * <;> omega

def difference (w a : ℕ) := 2^w-1-a

theorem complement_binary (w a : ℕ) (ha : a<2^w) :
    (binary w a).map Bool.not=binary w (difference w a) := by
  have hp : 0<2^w := pow_pos (by decide) _
  have hb : difference w a<2^w := by unfold difference; omega
  apply value_injective
  · simp
  · have h := complement_value (binary w a)
    rw [binary_value w a ha,binary_length] at h
    rw [binary_value w (difference w a) hb]
    unfold difference
    omega

theorem sum_difference (w a : ℕ) (ha : a<2^w) : a+difference w a=2^w-1 := by
  unfold difference
  omega

theorem selected_right (w a rank : ℕ) (ha : a<2^w) (hr : rank<2^w-1) :
    LeftCell.selected a (difference w a) rank true=decide (a≤rank) := by
  have hn : ¬2^w-1≤rank := by omega
  simp [LeftCell.selected,sum_difference w a ha,hn]

theorem numeric_run (w a : ℕ) (backing : List Bool) (ha : a<2^w) (hb : backing.length ≤ 2*w+1) :
    ∃ r : ExecutionReceipt 3 5,run resetMachine (4*w+4) (resetInput (binary w a) backing)=some r ∧
      r.final.tapes 0=frame (binary w a) ∧ r.final.tapes 1=frame (binary w (difference w a)) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=4*w+4 := by
  obtain ⟨r,hr,h0,h1,hh,hs⟩ := reset_run (binary w a) backing (by simpa using hb)
  rw [complement_binary w a ha] at h1
  simp only [binary_length] at hr hs
  exact ⟨r,hr,h0,h1,hh,hs⟩

def workspaceInput (w a : ℕ) (backing : List Bool) : Fin 3 → List Bool :=
  ![frame (binary w a),backing,List.replicate (2*w+1) false]

theorem workspace_run (w a : ℕ) (backing : List Bool) (ha : a<2^w) (hb : backing.length ≤ 2*w+1) :
    ∃ r : ExecutionReceipt 3 5,run resetMachine (4*w+4) (workspaceInput w a backing)=some r ∧
      r.final.tapes 0=frame (binary w a) ∧ r.final.tapes 1=frame (binary w (difference w a)) ∧
      r.final.tapes 2=List.replicate (2*w+1) false ∧ (∀ i,r.final.heads i=0) ∧ r.steps=4*w+4 := by
  obtain ⟨base,hbase,h0,h1,hs⟩ := copy_run (binary w a) backing (by simpa using hb)
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace machine _
    (input (binary w a) backing) base hbase (2*w+1)
  have hin : Fin.addCases (motive := fun _ : Fin (2+1) => List Bool) (input (binary w a) backing)
      (fun _ : Fin 1 => List.replicate (2*w+1) false)=workspaceInput w a backing := by
    funext i; fin_cases i <;> rfl
  simp only [binary_length] at hs
  rw [hin,hs] at hr
  have htime : 2*(2*w+1)+2=4*w+4 := by omega
  rw [htime] at hr
  rw [complement_binary w a ha] at h1
  refine ⟨r,hr,(ht 0).trans h0,(ht 1).trans h1,?_,hh,by omega⟩
  have hi : (0 : Fin 1).natAdd 2=(2 : Fin 3) := by decide
  rw [hi] at hcounter
  simpa only [hs,max_self] using hcounter

end NearCubicWires.RepairOrdinary.MatrixComplement
