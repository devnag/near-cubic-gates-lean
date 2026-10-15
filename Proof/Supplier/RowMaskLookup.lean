import Proof.Supplier.RowMaskPositionLoop
import Proof.Supplier.RowMaskConsume
import Proof.Supplier.RowMaskIndexClear

/-! The complete selected-mask lookup physically positions the retained
cache and appends the chosen native occurrences in its existing output bank. -/
namespace NearCubicWires.RepairOrdinary.RowMaskLookup
open LocalBitMultitape RecoveryExecution RowMaskPositionParts RowMaskConsume
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine RowMaskPositionLoop.machine RowMaskConsume.machine

theorem flatten_length (N : ℕ) (rows : List (List Bool)) (hl : ∀ row∈rows,row.length=N) :
    rows.flatten.length=N*rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    simp only [List.flatten_cons,List.length_append,List.length_cons]
    rw [hl row (by simp),ih (by intro r hr; exact hl r (by simp [hr]))]
    simp [Nat.mul_add,Nat.add_comm]

def result (N : ℕ) (rows : List (List Bool)) (bits : List Bool) (x : Data) : Data :=
  consumed N bits (RowMaskPositionLoop.endpoint N x rows.length)
def budget (N w d : ℕ) := d*(2*N+8*w+15)+8*w+14+N*(4*N+21)

theorem lookup_run (N w : ℕ) (rows : List (List Bool)) (bits tail : List Bool) (x : Data)
    (hx : x.source=rows.flatten++bits++tail) (hp : x.pos=0) (hi : x.index=0)
    (hl : ∀ row∈rows,row.length=N) (hn : bits.length=N)
    (hc : x.counter=0) (hd : x.bound=rows.length) (hb : rows.length+1<2^w) :
    ∃ r,runFrom machine (budget N w rows.length) (bank machine.start N w x)=some r ∧
      r.final.heads=(bank machine.start N w (result N rows bits x)).heads ∧
      r.final.tapes=(bank machine.start N w (result N rows bits x)).tapes ∧
      r.steps≤budget N w rows.length := by
  obtain ⟨base,hbase,bh,bt,_⟩ := RowMaskPositionLoop.scan_run N w rows (bits++tail) x
    (by simpa [List.append_assoc] using hx) hp hl hc hd hb
  obtain ⟨a,ha,af,_,_⟩ := ZeroPadding.run_config RowMaskPositionLoop.machine (capacities N) _ _ base hbase
  let y := RowMaskPositionLoop.endpoint N x rows.length
  have ah : a.final.heads=(bank RowMaskConsume.machine.start N w y).heads := by
    rw [af]; exact bh
  have atapes : a.final.tapes=(bank RowMaskConsume.machine.start N w y).tapes := by
    rw [af]
    change (fun i=>ZeroPadding.pad (capacities N i) (base.final.tapes i))=_
    rw [bt]; rfl
  obtain ⟨b,hb,bh',bt',_⟩ := consume_run N w rows.flatten bits tail y hx
    (by simp [y,RowMaskPositionLoop.endpoint,hp,flatten_length N rows hl]) hi hn
  have he : bank RowMaskConsume.machine.start N w y=Composition.restart a.final RowMaskConsume.machine.start := by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact atapes.symm
  rw [he] at hb
  have whole := Composition.run_join RowMaskPositionLoop.machine RowMaskConsume.machine _ _ _ a b ha hb
  have ht : rows.length*(2*N+8*w+15)+8*w+10+1+(N*(4*N+21)+3)=budget N w rows.length := by
    simp only [budget]; omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh',bt',?_⟩
  exact runFrom_steps_le machine _ _ _ whole

end NearCubicWires.RepairOrdinary.RowMaskLookup
