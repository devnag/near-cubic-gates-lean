import Proof.PCP.VerifierDecodingUnary
import Proof.Foundations.OrdinaryComposition
import Proof.Foundations.OrdinaryTapeRenaming

/-! The actual two-count producer at the verifier header. Both count tapes
begin blank. The original framed code is retained, and its cursor stops
exactly at the first fixed-width field. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.HeaderMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def swap : Fin 3 ≃ Fin 3 where
  toFun := ![0,2,1]
  invFun := ![0,2,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def first : Machine 3 4 := TapeEmbedding.machine 1 UnaryMachine.machine
def second : Machine 3 4 := TapeRenaming.machine swap first
def machine : Machine 3 8 := Composition.machine first second

def word (t s : ℕ) (fields : List Bool) : List Bool :=
  List.replicate t true ++ false :: (List.replicate s true ++ false :: fields)

def finished (t s : ℕ) (fields : List Bool) : Configuration 3 8 :=
  ⟨6, ![2*t+2*s+4,t,s], ![frame (word t s fields), List.replicate t true, List.replicate s true]⟩

theorem header_run (t s : ℕ) (fields : List Bool) :
    ∃ receipt : ExecutionReceipt 3 8,
      run machine (2*t+2*s+5) ![frame (word t s fields), [], []] = some receipt ∧
      receipt.final = finished t s fields ∧
      receipt.steps = 2*t+2*s+5 ∧
      receipt.peakTapeCells ≤ 3*(word t s fields).length+1 := by
  obtain ⟨r, hr, hrf, hrs, hrp⟩ := UnaryMachine.parse_run t [] (List.replicate s true ++ false::fields)
  have hfirst := TapeEmbedding.run_embed UnaryMachine.machine (fun _ : Fin 1 => 0) (fun _ => []) _ _ r hr
  let r' := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ => []) r
  let pre := Streaming.marks (List.replicate t true ++ [false])
  have hpre : pre.length = 2*t+2 := by simp [pre, Streaming.marks_length]
  have hword : pre ++ frame (List.replicate s true ++ false::fields) = frame (word t s fields) := by
    simp [pre, word, ← Streaming.frame_append, List.append_assoc]
  obtain ⟨r2, hr2, hf2, hs2, hp2⟩ := UnaryMachine.parse_run s pre fields
  rw [hword] at hr2 hf2 hp2
  have hsecond := TapeEmbedding.run_embed UnaryMachine.machine (fun _ : Fin 1 => t)
    (fun _ => List.replicate t true) _ _ r2 hr2
  have hrenamed := TapeRenaming.run_rename swap first _ _ _ hsecond
  let r2' := TapeRenaming.receipt swap
    (TapeEmbedding.receipt (fun _ : Fin 1 => t) (fun _ => List.replicate t true) r2)
  have hmid : Composition.restart r'.final second.start =
      TapeRenaming.config swap (TapeEmbedding.config (fun _ : Fin 1 => t)
        (fun _ => List.replicate t true)
        (UnaryMachine.cfg 0 (frame (word t s fields)) pre.length 0)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, r', TapeEmbedding.receipt, TapeEmbedding.config,
        hrf, UnaryMachine.cfg, TapeRenaming.config, swap, hpre, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.restart, r', TapeEmbedding.receipt, TapeEmbedding.config,
        hrf, UnaryMachine.cfg, TapeRenaming.config, swap, word, Fin.addCases]
  have hsecond' : runFrom second (2*s+2) (Composition.restart r'.final second.start) = some r2' := by
    rw [hmid]
    exact hrenamed
  have hj := Composition.run_join first second (2*t+2) (2*s+2) _ r' r2' hfirst hsecond'
  have hi : Composition.leftConfig 4 (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => [])
      (UnaryMachine.cfg 0 ([] ++ frame (List.replicate t true ++ false::(List.replicate s true ++ false::fields))) 0 0)) =
      initialConfiguration machine ![frame (word t s fields), [], []] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  simp only [List.length_nil] at hj
  rw [hi] at hj
  have htime : (2*t+2)+1+(2*s+2) = 2*t+2*s+5 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt r' r2', hj, ?_, ?_, ?_⟩
  · apply configuration_ext
    · change r2.final.control.natAdd 4 = (6 : Fin 8)
      rw [hf2]
      rfl
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, r2',
        TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config,
        hf2, UnaryMachine.cfg, finished, swap, hpre, Fin.addCases]
      omega
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, r2',
        TapeRenaming.receipt, TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config,
        hf2, UnaryMachine.cfg, finished, swap, Fin.addCases]
  · change r.steps+1+r2.steps = _
    omega
  · change max (r.peakTapeCells+TapeEmbedding.extraCells (fun _ : Fin 1 => ([] : List Bool)))
      (r2.peakTapeCells+TapeEmbedding.extraCells (fun _ : Fin 1 => List.replicate t true)) ≤ _
    simp only [TapeEmbedding.extraCells, Fin.sum_univ_one, List.length_nil, List.length_replicate, Nat.add_zero]
    have hrp' : r.peakTapeCells ≤ (frame (word t s fields)).length+t := by
      simpa only [List.nil_append, word] using hrp
    simp only [RepairSource.frame, RepairOrdinary.frame_length, word, List.length_append,
      List.length_replicate, List.length_cons] at hrp' hp2 ⊢
    omega

/-- The exact consumer for the frozen encoder, including blank count tapes
and the first fixed-width-field cursor. -/
theorem code_header_run (v : OrdinaryVerifier) :
    ∃ receipt : ExecutionReceipt 3 8,
      run machine (2*v.tapeCount+2*v.stateCount+5) ![frame (VerifierEncoding.code v), [], []] = some receipt ∧
      receipt.final.tapes 1 = List.replicate v.tapeCount true ∧
      receipt.final.tapes 2 = List.replicate v.stateCount true ∧
      receipt.final.heads 0 = 2*v.tapeCount+2*v.stateCount+4 ∧
      receipt.peakTapeCells ≤ 3*(VerifierEncoding.code v).length+1 := by
  let fields := VerifierEncoding.fixedBits (natBitLength v.stateCount) v.machine.start.val ++ flags v ++ table v
  have he : word v.tapeCount v.stateCount fields = VerifierEncoding.code v := (code_split v).symm
  obtain ⟨r, hr, hf, _ht, hp⟩ := header_run v.tapeCount v.stateCount fields
  rw [he] at hr hp
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by rw [hf]; rfl, hp⟩

end NearCubicWires.RepairSource.VerifierDecoding.HeaderMachine
