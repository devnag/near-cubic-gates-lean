import SourceAdapters.Amplification.EncTable

/-!
# The width prefix for the amplifier request (A05, `app:sources`, "Full-range amplification interface")

`prep1P` (a word program, as `EncPrep.prepP` with one inner frame): `amplifierInput r ↦
frame (1^(size n) ++ false :: amplifierInput r)` (the input to the cell program `unaryP` of `DispUnary.lean`, which
widens the prefix to `n + 4` ones for the dispatcher).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource (amplifierInput AmplifierOutput)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms NearCubicWires.ExecutableInterfaces
open NearCubicGates.Adapters.Code.CappedInput (State Script emitWord appended emit_word)

def prep1P : Script :=
  .seq adv <| .seq frameLoop <| .seq (emitWord [true, false]) <|
  .seq (.wm (WM.rewind 0 0)) <| .seq copyLoop (emitWord [false])

/-- The word read by the widening program. -/
def middle1 (r : AmplifierRequest) : List Bool :=
  List.replicate r.inputArity.size true ++ false :: amplifierInput r

theorem amplifierInput_length' (r : AmplifierRequest) :
    (amplifierInput r).length = 2 * r.inputArity.size + 1 + 2 ^ r.inputArity := by
  simp [amplifierInput, frame_length, boolFunctionTable, Nat.size_eq_bits_len]

theorem prep1_runs (r : AmplifierRequest) :
    ∃ τ, WXExec (4 * (amplifierInput r).length + 10) prep1P
      (NearCubicGates.Close.Expand.PolyTab.idealStart 1 6 (amplifierInput r) (fun _ => 0)) τ
      (prepCost (amplifierInput r).length) ∧ τ.st 1 = frame (middle1 r) := by
  set w := amplifierInput r with hw
  set cap := 4 * w.length + 10 with hcap
  set sn := r.inputArity.size
  have hnb : r.inputArity.bits.length = sn := Nat.size_eq_bits_len _
  have hwdec : w = frame r.inputArity.bits ++ boolFunctionTable r.function := rfl
  have hwlen : w.length = 2 * sn + 1 + 2 ^ r.inputArity := amplifierInput_length' r
  have hpos : 0 < 2 ^ r.inputArity := Nat.two_pow_pos _
  have hs0 : PS (frame w) (NearCubicGates.Close.Expand.PolyTab.idealStart 1 6 w (fun _ => 0)) 0 0 [] := by
    refine ⟨by simp [NearCubicGates.Close.Expand.PolyTab.idealStart], rfl, rfl, ?_, ?_⟩ <;>
      simp [NearCubicGates.Close.Expand.PolyTab.idealStart]
  have rd_odd : ∀ i, i < w.length → readTapeBit (frame w) (2 * i + 1) = w.getD i false := fun i hi =>
    frame_getD_odd w i hi
  obtain ⟨σ1, e1, hs1⟩ := adv_spec cap (frame w) _ 0 0 [] hs0 (by omega)
  obtain ⟨σ2, e2, hs2⟩ := frameLoop_spec cap (frame w) sn σ1 _ _ _ hs1 (by omega) (by
    intro i hi
    rw [show 0 + 1 + 4 * i = 2 * (2 * i) + 1 by ring, rd_odd _ (by omega), hwdec,
      List.getD_append _ _ _ _ (by simp [frame_length, hnb]; omega), frame_getD_even, hnb])
  obtain ⟨σ3, e3, hs3⟩ := emit_spec cap (frame w) σ2 _ _ _ [true, false] hs2
  have e4 := wrewind_spec (cap := cap) (0 : Fin 2) (0 : Fin 6) (0 + 1 + 4 * sn) σ3 hs3.2.2.1
    (by rw [hs3.2.2.1]; omega)
  have hs4 : PS (frame w) ((σ3.setv 0 0).seth 0 (σ3.sh 0 - (0 + 1 + 4 * sn))) 0 0
      ([] ++ (List.replicate sn [true, true]).flatten ++ [true, false]) := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := hs3
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [a1, a2, a3, a4, a5]
  obtain ⟨σ5, e5, hs5⟩ := copyLoop_spec cap (frame w) w _ 0 0 _ hs4
    (fun i _ => by rw [Nat.zero_add]; exact frame_getD_even w i) (fun i hi => by rw [Nat.zero_add]; exact rd_odd i hi)
  obtain ⟨σ6, e6, hs6⟩ := emit_spec cap (frame w) σ5 _ _ _ [false] hs5
  refine ⟨σ6, ?_, ?_⟩
  · refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4) (WXExec.seq e5 e6))))).mono ?_
    unfold prepCost; simp; rw [hwlen] at *; nlinarith
  · rw [hs6.2.2.2.1, middle1, frame_replicate]
    simp [frame, frame_eq_flatMap, List.append_assoc]
    rfl

/-- The first preparation machine. -/
noncomputable def prep1WF :
    WordFunction AmplifierRequest amplifierInput (fun r => frame (middle1 r))
      (fun r => 2 * prepCost (amplifierInput r).length + 2) :=
  NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal prep1P 1 (by decide)
    (fun r => 4 * (amplifierInput r).length + 10) (fun _ _ => 0) (fun r => prepCost (amplifierInput r).length)
    (fun _ => le_rfl) (fun r => ⟨rfl, prep1_runs r⟩)

end NearCubicGates.Adapters.Amplification.Enc
