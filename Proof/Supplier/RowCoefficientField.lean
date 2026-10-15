import Proof.Supplier.RowCoefficientEmit

/-! The whole once-per-coefficient normalizer emits the exact sign/magnitude
field consumed by the existing equation-row printer. Its two P/N source
frames and all reset cursors are retained by this seven-tape execution. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientField
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 5) : Fin 7 := i.castAdd 2
theorem old_injective : Function.Injective old := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 7=>a.val) h)
def emitSlots : Fin 4 → Fin 7 := ![2,3,5,6]
theorem emit_injective : Function.Injective emitSlots := by decide
noncomputable def first := RecoveryFocus.machine old RowCoefficientNormalize.machine
noncomputable def last := RecoveryFocus.machine emitSlots RowCoefficientEmit.machine
noncomputable def machine := Composition.machine first last
def extra (cap : ℕ) : Fin 2 → List Bool := ![[],List.replicate cap false]
def input (w p n cap emitCap : ℕ) :=
  Fin.addCases (m:=5) (n:=2) (motive:=fun _=>List Bool)
    (RowCoefficientNormalize.input w p n cap) (extra emitCap)
def middle (w p n cap emitCap : ℕ) :=
  Fin.addCases (m:=5) (n:=2) (motive:=fun _=>List Bool)
    (RowCoefficientNormalize.output w p n cap) (extra emitCap)
noncomputable def output (w p n cap emitCap : ℕ) := install emitSlots (middle w p n cap emitCap)
  (RowCoefficientEmit.output (decide (n≤p)) (binary w (RowCoefficientNormalize.magnitude p n)) emitCap)

theorem first_ready (w p n cap emitCap : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ReadyRun first (8*w+10) (input w p n cap emitCap) (middle w p n cap emitCap) := by
  have h := (RowCoefficientNormalize.normalize_run w p n cap hp hn).focus old old_injective
    (input w p n cap emitCap) (by intro i; simp [input,old])
  have he : install old (input w p n cap emitCap) (RowCoefficientNormalize.output w p n cap)=
      middle w p n cap emitCap := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot old old_injective _ _ 0
      | exact install_slot old old_injective _ _ 1
      | exact install_slot old old_injective _ _ 2
      | exact install_slot old old_injective _ _ 3
      | exact install_slot old old_injective _ _ 4
      | exact install_other old _ _ _ (by intro j; have hj:=j.isLt; simp only [old,Fin.ne_iff_vne,Fin.val_castAdd]; omega)
  exact he ▸ h

theorem last_ready (w p n cap emitCap : ℕ) :
    ReadyRun last (4*w+10) (middle w p n cap emitCap) (output w p n cap emitCap) := by
  have h := RowCoefficientEmit.emit_ready (decide (n≤p)) (binary w (RowCoefficientNormalize.magnitude p n)) emitCap
  simp only [binary_length] at h
  exact h.focus emitSlots emit_injective (middle w p n cap emitCap)
    (by intro i; fin_cases i <;> simp [emitSlots,middle,RowCoefficientNormalize.output,
      RowCoefficientNormalize.data,extra,RowCoefficientEmit.input,Fin.addCases])

theorem field_ready (w p n cap emitCap : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ReadyRun machine (12*w+21) (input w p n cap emitCap) (output w p n cap emitCap) := by
  obtain ⟨a,ha,atapes,ah,asteps⟩ := first_ready w p n cap emitCap hp hn
  obtain ⟨b,hb,bt,bh,bs⟩ := last_ready w p n cap emitCap
  have he : initialConfiguration last (middle w p n cap emitCap)=Composition.restart a.final last.start := by
    apply configuration_ext
    · rfl
    · exact (funext ah).symm
    · exact atapes.symm
  unfold run at hb
  rw [he] at hb
  have whole := Composition.run_join first last _ _ _ a b ha hb
  have time : (8*w+10)+1+(4*w+10)=12*w+21 := by omega
  rw [time] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bt,bh,?_⟩
  change a.steps+1+b.steps=_
  rw [asteps,bs,time]

theorem field_output (w p n cap emitCap : ℕ) :
    output w p n cap emitCap 5=frame (signMagnitude w ((p : ℤ)-n)) := by
  have h := install_slot emitSlots emit_injective (middle w p n cap emitCap)
    (RowCoefficientEmit.output (decide (n≤p)) (binary w (RowCoefficientNormalize.magnitude p n)) emitCap) 2
  change output w p n cap emitCap 5=frame ((!decide (n≤p))::binary w (RowCoefficientNormalize.magnitude p n)) at h
  rw [RowCoefficientNormalize.sign_eq,RowCoefficientNormalize.magnitude_eq] at h
  exact h

end NearCubicWires.RepairOrdinary.RowCoefficientField
