import SourceAdapters.Amplification.EncSetup
import SourceAdapters.Code.CappedInput

/-!
# The width prefix for the encoder's cell program (X9, `app:sources`, "Full-range amplification interface")

The released cell-language compiler (`Cells.wordFunction_of_lang`) takes its number width from the leading ones
of its input word. `prepP` (a word program, `WMX 1 6`) turns the request word
`w = frame (binary k) ++ frame (binary n) ++ table` into `frame (1^(|k.bits| + |n.bits|) ++ false :: w)`:
one `1` per bit of `k` and of `n` (`frameLoop`, scanning the inner frames), a `0`, then a copy of `w`
(`copyLoop`, after rewinding the input). `prepWordFunction`: the ordinary machine, linear time.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms NearCubicWires.ExecutableInterfaces
open NearCubicGates.Adapters.Code.CappedInput (State Script emitWord appended emit_word)

variable (cap : ℕ)

/-- The tracked part of a prep state: the input frame, its head `h`, the counter `R`, the output so far. -/
def PS (inp : List Bool) (σ : State) (h R : ℕ) (out : List Bool) : Prop :=
  σ.st 0 = inp ∧ σ.sh 0 = h ∧ σ.val 0 = R ∧ σ.st 1 = out ∧ σ.sh 1 = out.length

/-- Advance the input head and count it. -/
def adv : Script := .seq (WMX.fwd 0) (WMX.inc 0)

theorem adv_spec (inp : List Bool) (σ : State) (h R : ℕ) (out : List Bool) (hs : PS inp σ h R out) (hR : R < cap) :
    ∃ τ, WXExec cap adv σ τ 5 ∧ PS inp τ (h + 1) (R + 1) out := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  refine ⟨_, WXExec.seq (WXExec.fwd cap 0 σ) (WXExec.inc cap 0 _ (by simp [h3]; omega)), ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [h1, h2, h3, h4, h5]

theorem emit_spec (inp : List Bool) (σ : State) (h R : ℕ) (out word : List Bool) (hs : PS inp σ h R out) :
    ∃ τ, WXExec cap (emitWord word) σ τ (4 * word.length) ∧ PS inp τ h R (out ++ word) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  refine ⟨_, emit_word cap word σ (by rw [h4, h5]), ?_, ?_, ?_, ?_, ?_⟩ <;> simp [appended, h1, h2, h3, h4, h5]

/-- One `1` per marker of an inner frame. -/
def frameLoop : Script := .whs 0 (.seq (emitWord [true, true]) (.seq adv (.seq adv (.seq adv adv))))

theorem frameLoop_spec (inp : List Bool) :
    ∀ (d : ℕ) (σ : State) (h R : ℕ) (out : List Bool), PS inp σ h R out → R + 4 * d < cap →
      (∀ i ≤ d, readTapeBit inp (h + 4 * i) = decide (i < d)) →
      ∃ τ, WXExec cap frameLoop σ τ (40 * d + 1) ∧
        PS inp τ (h + 4 * d) (R + 4 * d) (out ++ (List.replicate d [true, true]).flatten) := by
  intro d
  induction d with
  | zero =>
    intro σ h R out hs _ hread
    refine ⟨σ, WXExec.whsF ?_, by simpa using hs⟩
    have := hread 0 le_rfl
    simp only [wbit, hs.1, hs.2.1]; simpa using this
  | succ d ih =>
    intro σ h R out hs hcap hread
    have hb : wbit σ 0 = true := by
      have := hread 0 (by omega); simp only [wbit, hs.1, hs.2.1]; simpa using this
    obtain ⟨σ1, e1, hs1⟩ := emit_spec cap inp σ h R out [true, true] hs
    obtain ⟨σ2, e2, hs2⟩ := adv_spec cap inp σ1 h R _ hs1 (by omega)
    obtain ⟨σ3, e3, hs3⟩ := adv_spec cap inp σ2 _ _ _ hs2 (by omega)
    obtain ⟨σ4, e4, hs4⟩ := adv_spec cap inp σ3 _ _ _ hs3 (by omega)
    obtain ⟨σ5, e5, hs5⟩ := adv_spec cap inp σ4 _ _ _ hs4 (by omega)
    obtain ⟨τ, e6, hs6⟩ := ih σ5 (h + 1 + 1 + 1 + 1) (R + 1 + 1 + 1 + 1) _ hs5 (by omega) (by
      intro i hi
      have := hread (i + 1) (by omega)
      rw [show h + 1 + 1 + 1 + 1 + 4 * i = h + 4 * (i + 1) by ring, this]; simp)
    refine ⟨τ, (WXExec.whsT hb (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))) e6).mono
      (by simp; omega), ?_⟩
    rw [show h + 4 * (d + 1) = h + 1 + 1 + 1 + 1 + 4 * d by ring,
      show R + 4 * (d + 1) = R + 1 + 1 + 1 + 1 + 4 * d by ring, List.replicate_succ, List.flatten_cons,
      ← List.append_assoc]
    exact hs6

/-- Copy the framed input: `[true, w_j]` per cell pair. -/
def copyLoop : Script :=
  .whs 0 (.seq (emitWord [true]) (.seq (WMX.fwd 0) (.seq (.ifs 0 (emitWord [true]) (emitWord [false])) (WMX.fwd 0))))

theorem copyLoop_spec (inp : List Bool) :
    ∀ (ws : List Bool) (σ : State) (h R : ℕ) (out : List Bool), PS inp σ h R out →
      (∀ i ≤ ws.length, readTapeBit inp (h + 2 * i) = decide (i < ws.length)) →
      (∀ i < ws.length, readTapeBit inp (h + 2 * i + 1) = ws.getD i false) →
      ∃ τ, WXExec cap copyLoop σ τ (20 * ws.length + 1) ∧
        PS inp τ (h + 2 * ws.length) R (out ++ ws.flatMap (fun b => [true, b])) := by
  intro ws
  induction ws with
  | nil =>
    intro σ h R out hs hm _
    refine ⟨σ, WXExec.whsF ?_, by simpa using hs⟩
    have := hm 0 le_rfl
    simp only [wbit, hs.1, hs.2.1]; simpa using this
  | cons b ws ih =>
    intro σ h R out hs hm hd
    have hb : wbit σ 0 = true := by
      have := hm 0 (by simp); simp only [wbit, hs.1, hs.2.1]; simpa using this
    obtain ⟨σ1, e1, hs1⟩ := emit_spec cap inp σ h R out [true] hs
    have e2 := WXExec.fwd cap (0 : Fin 2) σ1
    set σ2 := σ1.seth 0 (σ1.sh 0 + 1)
    have hs2 : PS inp σ2 (h + 1) R (out ++ [true]) := by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hs1; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [σ2, a1, a2, a3, a4, a5]
    have hbit : wbit σ2 0 = b := by
      have := hd 0 (by simp); simp only [wbit, hs2.1, hs2.2.1]; simpa using this
    obtain ⟨σ3, e3, hs3⟩ := emit_spec cap inp σ2 (h + 1) R (out ++ [true]) [b] hs2
    have e3' : WXExec cap (.ifs 0 (emitWord [true]) (emitWord [false])) σ2 σ3 5 := by
      cases b
      · exact WXExec.ifsF hbit e3
      · exact WXExec.ifsT hbit e3
    have e4 := WXExec.fwd cap (0 : Fin 2) σ3
    set σ4 := σ3.seth 0 (σ3.sh 0 + 1)
    have hs4 : PS inp σ4 (h + 2) R (out ++ [true, b]) := by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hs3; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [σ4, a1, a2, a3, a4, a5]
    obtain ⟨τ, e5, hs5⟩ := ih σ4 (h + 2) R _ hs4 (by
      intro i hi
      have := hm (i + 1) (by simp; omega)
      rw [show h + 2 + 2 * i = h + 2 * (i + 1) by ring, this]; simp)
      (by
      intro i hi
      have := hd (i + 1) (by simp; omega)
      rw [show h + 2 + 2 * i + 1 = h + 2 * (i + 1) + 1 by ring, this]; simp)
    refine ⟨τ, (WXExec.whsT hb (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3' e4))) e5).mono
      (by simp; omega), ?_⟩
    rw [show h + 2 * (b :: ws).length = h + 2 + 2 * ws.length by simp; ring, List.flatMap_cons,
      ← List.append_assoc]
    exact hs5

/-! ## The whole preparation -/

def prepP : Script :=
  .seq adv <| .seq frameLoop <| .seq adv <| .seq adv <| .seq frameLoop <| .seq (emitWord [true, false]) <|
  .seq (.wm (WM.rewind 0 0)) <| .seq copyLoop (emitWord [false])

/-- The prefix length: the binary lengths of `k` and `n`. -/
def prefixLen (r : Joins.EncoderRequest) : ℕ := r.k.size + r.n.size

/-- The word the encoder's cell program reads. -/
def middleWord (r : Joins.EncoderRequest) : List Bool :=
  List.replicate (prefixLen r) true ++ false :: Joins.encoderInput r

def prepCost (len : ℕ) : ℕ := 200 * (len + 1)

theorem frame_replicate (d : ℕ) (l : List Bool) :
    frame (List.replicate d true ++ l) = (List.replicate d [true, true]).flatten ++ frame l := by
  induction d with
  | zero => rfl
  | succ d ih => simp [List.replicate_succ, frame, ih]

theorem prep_runs (r : Joins.EncoderRequest) :
    ∃ τ, WXExec (4 * (Joins.encoderInput r).length + 10) prepP
      (NearCubicGates.Close.Expand.PolyTab.idealStart 1 6 (Joins.encoderInput r) (fun _ => 0)) τ
      (prepCost (Joins.encoderInput r).length) ∧ τ.st 1 = frame (middleWord r) := by
  set w := Joins.encoderInput r with hw
  set cap := 4 * w.length + 10 with hcap
  set sk := r.k.size
  set sn := r.n.size
  have hkb : r.k.bits.length = sk := Nat.size_eq_bits_len r.k
  have hnb : r.n.bits.length = sn := Nat.size_eq_bits_len r.n
  have hwdec : w = frame r.k.bits ++ (frame r.n.bits ++ boolFunctionTable r.msg) := by
    simp [w, Joins.encoderInput, RepairSource.amplifierInput]
  have hwlen : w.length = 2 * sk + 1 + (2 * sn + 1) + 2 ^ r.n := by
    rw [hwdec]; simp [frame_length, hkb, hnb, boolFunctionTable]; omega
  have hpos : 0 < 2 ^ r.n := Nat.two_pow_pos _
  have hs0 : PS (frame w) (NearCubicGates.Close.Expand.PolyTab.idealStart 1 6 w (fun _ => 0)) 0 0 [] := by
    refine ⟨by simp [NearCubicGates.Close.Expand.PolyTab.idealStart], rfl, rfl, ?_, ?_⟩ <;>
      simp [NearCubicGates.Close.Expand.PolyTab.idealStart]
  have rd_odd : ∀ i, i < w.length → readTapeBit (frame w) (2 * i + 1) = w.getD i false := fun i hi =>
    frame_getD_odd w i hi
  obtain ⟨σ1, e1, hs1⟩ := adv_spec cap (frame w) _ 0 0 [] hs0 (by omega)
  obtain ⟨σ2, e2, hs2⟩ := frameLoop_spec cap (frame w) sk σ1 _ _ _ hs1 (by omega) (by
    intro i hi
    rw [show 0 + 1 + 4 * i = 2 * (2 * i) + 1 by ring, rd_odd _ (by omega), hwdec,
      List.getD_append _ _ _ _ (by simp [frame_length, hkb]; omega), frame_getD_even, hkb])
  obtain ⟨σ3, e3, hs3⟩ := adv_spec cap (frame w) σ2 _ _ _ hs2 (by omega)
  obtain ⟨σ4, e4, hs4⟩ := adv_spec cap (frame w) σ3 _ _ _ hs3 (by omega)
  obtain ⟨σ5, e5, hs5⟩ := frameLoop_spec cap (frame w) sn σ4 _ _ _ hs4 (by omega) (by
    intro i hi
    rw [show 0 + 1 + 4 * sk + 1 + 1 + 4 * i = 2 * ((2 * sk + 1) + 2 * i) + 1 by ring, rd_odd _ (by omega), hwdec,
      List.getD_append_right _ _ _ _ (by simp [frame_length, hkb]),
      show 2 * sk + 1 + 2 * i - (frame r.k.bits).length = 2 * i by simp [frame_length, hkb],
      List.getD_append _ _ _ _ (by simp [frame_length, hnb]; omega), frame_getD_even, hnb])
  obtain ⟨σ6, e6, hs6⟩ := emit_spec cap (frame w) σ5 _ _ _ [true, false] hs5
  have e7 := wrewind_spec (cap := cap) (0 : Fin 2) (0 : Fin 6) (0 + 1 + 4 * sk + 1 + 1 + 4 * sn) σ6 hs6.2.2.1
    (by rw [hs6.2.2.1]; omega)
  have hs7 : PS (frame w) ((σ6.setv 0 0).seth 0 (σ6.sh 0 - (0 + 1 + 4 * sk + 1 + 1 + 4 * sn))) 0 0
      ([] ++ (List.replicate sk [true, true]).flatten ++ (List.replicate sn [true, true]).flatten ++ [true, false]) := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := hs6
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [a1, a2, a3, a4, a5]
  obtain ⟨σ8, e8, hs8⟩ := copyLoop_spec cap (frame w) w _ 0 0 _ hs7
    (fun i _ => by rw [Nat.zero_add]; exact frame_getD_even w i) (fun i hi => by rw [Nat.zero_add]; exact rd_odd i hi)
  obtain ⟨σ9, e9, hs9⟩ := emit_spec cap (frame w) σ8 _ _ _ [false] hs8
  refine ⟨σ9, ?_, ?_⟩
  · refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
      (WXExec.seq (WXExec.wm e7) (WXExec.seq e8 e9)))))))).mono ?_
    unfold prepCost; simp; rw [hwlen] at *; nlinarith
  · rw [hs9.2.2.2.1, middleWord, prefixLen, frame_replicate, List.replicate_add, List.flatten_append]
    simp [frame, frame_eq_flatMap, List.append_assoc]
    rfl

end NearCubicGates.Adapters.Amplification.Enc
