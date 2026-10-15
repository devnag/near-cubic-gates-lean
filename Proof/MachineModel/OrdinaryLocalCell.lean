import Proof.MachineModel.OrdinaryLeftCell

/-! A reusable scalar cell workspace. The result occupies one local bit;
only bounded scalar heads are reset. A surrounding output cursor is not
part of this machine and can remain on an inactive extra tape. -/
namespace NearCubicWires.RepairOrdinary.LocalCell
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw (width a b rank : ℕ) (backing : List Bool) (mask : Bool) : Fin 7 → List Bool :=
  ![frame (binary width a), frame (binary width b), backing,
    List.replicate (2 * width + 1) false, frame (binary width rank), [false], [mask]]
def capacity : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 1, 0]
def input (width a b rank : ℕ) (backing : List Bool) (mask : Bool) : Fin 8 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (7 + 1) => List Bool)
    (raw width a b rank backing mask) (fun _ => List.replicate (6 * width + 6) false)
def output (width a b rank : ℕ) (mask : Bool) : Fin 8 → List Bool :=
  ![frame (binary width a), frame (binary width b), frame (binary width (a + b)),
    List.replicate (2 * width + 1) false, frame (binary width rank),
    [LeftCell.selected a b rank mask], [mask], List.replicate (6 * width + 6) false]
def machine : Machine 8 18 := Rewind.machine LeftCell.machine

theorem local_run (width a b rank : ℕ) (backing : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ width) (hrank : rank < 2 ^ width) (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 8 18,
      run machine (12 * width + 14) (input width a b rank backing mask) = some r ∧
      r.final.tapes = output width a b rank mask ∧ (∀ i, r.final.heads i = 0) ∧
      r.steps = 12 * width + 14 ∧ r.peakTapeCells ≤ 26 * width + 21 := by
  obtain ⟨base, hbase, hbf, hbs, hbp⟩ := LeftCell.cell_run width a b rank backing [] mask hfit hrank hb
  obtain ⟨source, hsrun, hsf, hss, hsp⟩ := ZeroPadding.run_config LeftCell.machine capacity _ _ base hbase
  have hi : ZeroPadding.config capacity
      (Composition.leftConfig 9 (LeftCell.input width a b rank backing [] mask)) =
      initialConfiguration LeftCell.machine (raw width a b rank backing mask) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, ZeroPadding.pad, capacity, Composition.leftConfig,
        LeftCell.input, initialConfiguration, raw]
  have hf : ZeroPadding.config capacity (LeftCell.finished width a b rank [] mask) =
      LeftCell.finished width a b rank [] mask := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, capacity, LeftCell.finished, ZeroPadding.pad]
  have hfinal : source.final = LeftCell.finished width a b rank [] mask := by rw [hsf, hbf, hf]
  have hsteps : source.steps = 6 * width + 6 := hss.trans hbs
  have hpeak : source.peakTapeCells ≤ 14 * width + 9 := by
    simp [ZeroPadding.cells, capacity, Fin.sum_univ_succ] at hsp
    simp only [List.length_nil] at hbp
    omega
  have hsrun' : run LeftCell.machine (6 * width + 6) (raw width a b rank backing mask) = some source := by
    rw [run, ← hi]
    exact hsrun
  obtain ⟨r, hr, ht, hc, hh, hs, hp⟩ := Rewind.Workspace.reset_workspace LeftCell.machine
    (6 * width + 6) (raw width a b rank backing mask) source hsrun' (6 * width + 6)
  have htime : 2 * source.steps + 2 = 12 * width + 14 := by rw [hsteps]; omega
  refine ⟨r, by rw [htime] at hr; exact hr, ?_, hh, hs.trans htime, by omega⟩
  have hcore (i : Fin 7) : r.final.tapes (i.castAdd 1) = (LeftCell.finished width a b rank [] mask).tapes i := by
    rw [ht i, hfinal]
  have hlast : r.final.tapes 7 = List.replicate (6 * width + 6) false := by
    have hindex : (0 : Fin 1).natAdd 7 = (7 : Fin 8) := by decide
    simpa only [hsteps, max_self, hindex] using hc
  funext i
  fin_cases i
  · exact hcore 0
  · exact hcore 1
  · exact hcore 2
  · exact hcore 3
  · exact hcore 4
  · exact hcore 5
  · exact hcore 6
  · exact hlast

end NearCubicWires.RepairOrdinary.LocalCell
