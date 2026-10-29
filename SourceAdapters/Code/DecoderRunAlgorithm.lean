import SourceAdapters.Code.DecoderInvoke
import SourceAdapters.Code.CountedCopy
import SourceAdapters.Code.DecoderTypes
import SourceAdapters.Code.SourcePrograms

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the complete second decoder stage executes three capped
source calls and normalizes their outputs, or performs the finite identity copy. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderRunAlgorithm

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Code DecoderTypes CountedParsing BlockArithmetic

abbrev State := DS 12 0
abbrev Script := St 12 0

def requests (F : BinaryFamily) : Work F → List (TotalSourceRequest F)
  | .inl _ => []
  | .inr p => [p.first, p.second, p.third]

def callee (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius) (K e : ℕ)
    (W : WordFunction (TotalSourceRequest F) (fun p => decoderInput F p.1 p.2)
      (fun p => frame (cappedOutput D.program (decoderCappedRequest F D p)))
      (fun p => K * ((decoderInput F p.1 p.2).length + 1) ^ e)) : Callee :=
  ⟨TotalSourceRequest F, (fun p => decoderInput F p.1 p.2),
    (fun p => frame (cappedOutput D.program (decoderCappedRequest F D p))),
    (fun p => K * ((decoderInput F p.1 p.2).length + 1) ^ e), W⟩

def large : Script := .seq DecoderInvoke.script (.seq DecoderInvoke.script DecoderInvoke.script)

def script : Script := .seq (addConstant 0 10 1) (.seq (skipUnary 0 1)
  (.seq (.op (.rdI 1)) (.ite (.lt 0 1) large CountedCopy.script)))

def cost (L len Lk Bk : ℕ) : ℕ := 1000 * (L + len + Lk + Bk + 1)

theorem packet_length (F : BinaryFamily) (p : TotalSourceRequest F) :
    (sourcePacket F p).length = 2 * p.1 + 2 * (decoderInput F p.1 p.2).length + 2 := by
  rw [source_packet]
  simp only [List.length_append, frame_length, List.length_replicate]
  omega

theorem runs (F : BinaryFamily) {onset : ℕ} {radius : ℝ} (D : PromisedDecoder F onset radius) (K e : ℕ)
    (W : WordFunction (TotalSourceRequest F) (fun p => decoderInput F p.1 p.2)
      (fun p => frame (cappedOutput D.program (decoderCappedRequest F D p)))
      (fun p => K * ((decoderInput F p.1 p.2).length + 1) ^ e))
    (Wd Lk Bk L : ℕ) (w : Work F)
    (hcap : 2 * (payload F w).length + 2 < 2 ^ Wd)
    (hfit : ∀ p ∈ requests F w, (decoderInput F p.1 p.2).length ≤ Lk ∧
      K * ((decoderInput F p.1 p.2).length + 1) ^ e ≤ Bk) :
    ∃ b, Ex (⟨Wd, input F L w, callee F D K e W, Lk, Bk⟩ : Ctx) script a0 b
      (cost L (payload F w).length Lk Bk) ∧ b.out = output F D w := by
  let C : Ctx := ⟨Wd, input F L w, callee F D K e W, Lk, Bk⟩
  have e1 := add_constant C (0 : Fin 12) 10 (by decide) 1 (a0 : State) rfl (by change 0 + 1 < 2 ^ Wd; omega)
  let a1 := (a0 : State).set 10 ((a0 : State).env 10 + 1)
  have e2 := skip_unary C (0 : Fin 12) 1 (by decide) a1
    (by simp [a1, DS.set, a0]) L [] (payload F w) (by simp [C, input]) (by simp [a1, a0])
  let a2 := flagged (1 : Fin 12) a1 (0 + L + 1) 0
  let pre := List.replicate L true ++ [false]
  cases w with
  | inl bits =>
    have e3 := read_at_prefix C (1 : Fin 12) a2 pre false (frame bits)
      (by simp [C, input, payload, pre, List.append_assoc]) (by simp [a2, flagged, pre])
    let a3 := readState (1 : Fin 12) a2 false
    let pre1 := pre ++ [false]
    obtain ⟨b, hb, hout⟩ := CountedCopy.runs C a3 pre1 bits
      (by simp [a3, readState, a2, flagged, a1, DS.set, a0])
      (by simp [a3, readState, a2, flagged, a1, DS.set, a0])
      (by simp [C, input, payload, pre1, pre, List.append_assoc])
      (by simp [a3, readState, a2, flagged, pre1, pre])
      (by simp only [payload, List.length_cons, frame_length] at hcap; dsimp [C]; omega)
    have e4 := Ex.iteF (c := Cnd.lt (0 : Fin 12) 1) (s := large) (by decide : (0 : Fin 12) ≠ 1)
      (show (Cnd.lt (0 : Fin 12) 1).eval a3 = false by simp [Cnd.eval, a3, readState, a2, flagged, a1, DS.set, a0]) hb
    refine ⟨b, (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))).mono ?_, ?_⟩
    · simp [cost, payload, frame_length]
      omega
    · simpa [output, a3, readState, a2, flagged, a1, a0] using hout
  | inr p =>
    let q0 := p.first
    let q1 := p.second
    let q2 := p.third
    let word0 := decoderInput F q0.1 q0.2
    let word1 := decoderInput F q1.1 q1.2
    let word2 := decoderInput F q2.1 q2.2
    let out0 := cappedOutput D.program (decoderCappedRequest F D q0)
    let out1 := cappedOutput D.program (decoderCappedRequest F D q1)
    let out2 := cappedOutput D.program (decoderCappedRequest F D q2)
    have fit0 := hfit q0 (by simp [requests, q0])
    have fit1 := hfit q1 (by simp [requests, q1])
    have fit2 := hfit q2 (by simp [requests, q2])
    have hp : (payload F (.inr p)).length = 1 +
        (2 * q0.1 + 2 * word0.length + 2) + (2 * q1.1 + 2 * word1.length + 2) +
          (2 * q2.1 + 2 * word2.length + 2) := by
      simp only [payload, List.length_cons, List.length_append, packet_length]
      dsimp [q0, q1, q2, word0, word1, word2]
      omega
    have e3 := read_at_prefix C (1 : Fin 12) a2 pre true
      (sourcePacket F q0 ++ sourcePacket F q1 ++ sourcePacket F q2)
      (by simp [C, input, payload, pre, q0, q1, q2, List.append_assoc]) (by simp [a2, flagged, pre])
    let a3 := readState (1 : Fin 12) a2 true
    let pre0 := pre ++ [true]
    have hz : a3.env 0 = 0 := by simp [a3, readState, a2, flagged, a1, DS.set, a0]
    have ho : a3.env 10 = 1 := by simp [a3, readState, a2, flagged, a1, DS.set, a0]
    have hi0 : C.inp = pre0 ++ frame (List.replicate q0.1 true) ++ frame word0 ++
        (sourcePacket F q1 ++ sourcePacket F q2) := by
      simp [C, input, payload, pre0, pre, q0, q1, q2, word0, source_packet, List.append_assoc]
    obtain ⟨b0, eb0, hz0, ho0, hk0, hi0', hout0⟩ := DecoderInvoke.runs C q0 q0.1 word0 out0 pre0
      (sourcePacket F q1 ++ sourcePacket F q2) a3 hz ho
      (by simp [a3, readState, a2, flagged, a1, a0]) hi0
      (by simp [a3, readState, a2, flagged, pre0, pre]) rfl rfl fit0.1 fit0.2
      (by rw [hp] at hcap; dsimp [C]; omega)
    let pre1 := pre0 ++ sourcePacket F q0
    have hi1 : C.inp = pre1 ++ frame (List.replicate q1.1 true) ++ frame word1 ++ sourcePacket F q2 := by
      simp [C, input, payload, pre1, pre0, pre, q0, q1, q2, word1, source_packet, List.append_assoc]
    obtain ⟨b1, eb1, hz1, ho1, hk1, hi1', hout1⟩ := DecoderInvoke.runs C q1 q1.1 word1 out1 pre1
      (sourcePacket F q2) b0 hz0 ho0 hk0 hi1
      (by simpa [pre1, source_packet, List.length_append, word0, Nat.add_assoc] using hi0') rfl rfl fit1.1 fit1.2
      (by rw [hp] at hcap; dsimp [C]; omega)
    let pre2 := pre1 ++ sourcePacket F q1
    have hi2 : C.inp = pre2 ++ frame (List.replicate q2.1 true) ++ frame word2 ++ [] := by
      simp [C, input, payload, pre2, pre1, pre0, pre, q0, q1, q2, word2, source_packet, List.append_assoc]
    obtain ⟨b2, eb2, _, _, _, _, hout2⟩ := DecoderInvoke.runs C q2 q2.1 word2 out2 pre2 [] b1 hz1 ho1 hk1 hi2
      (by simpa [pre2, source_packet, List.length_append, word1, Nat.add_assoc] using hi1') rfl rfl fit2.1 fit2.2
      (by rw [hp] at hcap; dsimp [C]; omega)
    have el := Ex.seq eb0 (Ex.seq eb1 eb2)
    have e4 := Ex.iteT (c := Cnd.lt (0 : Fin 12) 1) (t := CountedCopy.script) (by decide : (0 : Fin 12) ≠ 1)
      (show (Cnd.lt (0 : Fin 12) 1).eval a3 = true by simp [Cnd.eval, a3, readState, a2, flagged, a1, DS.set, a0]) el
    refine ⟨b2, (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))).mono ?_, ?_⟩
    · simp only [cost, hp, C]
      omega
    · rw [hout2, hout1, hout0]
      simp [output, out0, out1, out2, source_resize, a3, readState, a2, flagged, a1, a0, q0, q1, q2]

end NearCubicGates.Adapters.Code.DecoderRunAlgorithm
