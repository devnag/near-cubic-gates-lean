import SourceAdapters.Code.EncoderBody
import SourceAdapters.Code.SourcePrograms

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the complete finite-patched encoder in the
ordinary cell language, using the actual framed source encoder as its callee. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.EncoderAlgorithm

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Code
open CountedParsing CellSending BlockArithmetic

abbrev State := DS 12 0
abbrev Script := St 12 0

def callee (F : BinaryFamily) (onset K e : ℕ)
    (W : WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => frame (List.ofFn (F.encode p.1 p.2.val))) (fun p => K * (p.1 + 1) ^ e)) : Callee :=
  ⟨SourceMessage onset, sourceMessageWord, (fun p => frame (List.ofFn (F.encode p.1 p.2.val))),
    (fun p => K * (p.1 + 1) ^ e), W⟩

def script (onset : ℕ) : Script := .seq EncoderFront.script
  (.seq (.op (.zero 11)) (.seq (addConstant 0 11 (cutoff onset))
    (.ite (.lt 2 11) EncoderBody.small EncoderBody.large)))

def languageCost (onset L n Lk Bk : ℕ) : ℕ := 1000 * (L + n + cutoff onset + Lk + Bk + 1)

theorem runs (F : BinaryFamily) {onset : ℕ} {radius : ℝ}
    (D : PromisedDecoder F onset radius) (hlinear : IsLinear F) (K e : ℕ)
    (W : WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => frame (List.ofFn (F.encode p.1 p.2.val))) (fun p => K * (p.1 + 1) ^ e))
    (Wd Lk Bk L n : ℕ) (x : BitInput n)
    (hcap : 2 * n + 6 + cutoff onset < 2 ^ Wd) (hroom : n ≤ Lk)
    (hclock : ∀ i : Fin 3, K * (blockSize n i + 1) ^ e ≤ Bk) :
    ∃ b, Ex (⟨Wd, List.replicate L true ++ false :: frame (List.ofFn x), callee F onset K e W, Lk, Bk⟩ : Ctx)
      (script onset) a0 b (languageCost onset L n Lk Bk) ∧
      b.out = List.ofFn ((patchedFamily F D).enc n x) := by
  let C : Ctx := ⟨Wd, List.replicate L true ++ false :: frame (List.ofFn x), callee F onset K e W, Lk, Bk⟩
  obtain ⟨a, he, ha⟩ := EncoderFront.runs C L (List.ofFn x) rfl (by simpa [C] using (show 2 * n + 6 < 2 ^ Wd by omega))
  have e0 := Ex.op (OpEx.zero (C := C) (11 : Fin 12) a)
  let a1 := a.set 11 0
  have e1 := add_constant C (0 : Fin 12) 11 (by decide) (cutoff onset) a1
    (by simp [a1, DS.set, ha.zero]) (by simp [a1, C]; omega)
  let a2 := a1.set 11 (a1.env 11 + cutoff onset)
  let pre := List.replicate L true ++ [false]
  have hz : a2.env 0 = 0 := by simp [a2, a1, DS.set, ha.zero]
  have ho : a2.env 10 = 1 := by simp [a2, a1, DS.set, ha.one]
  have hf : a2.env 1 = 0 := by simp [a2, a1, DS.set, ha.flag]
  have hn : a2.env 2 = n := by simpa [a2, a1, DS.set] using ha.length
  have ht : a2.env 11 = cutoff onset := by simp [a2, a1]
  have hp : a2.ip = pre.length := by simp [a2, a1, pre, ha.position]
  have hout : a2.out = [] := by simp [a2, a1, ha.output]
  by_cases hs : n < cutoff onset
  · obtain ⟨b, hb, hbo⟩ := EncoderBody.small_runs C a2 pre (List.ofFn x) hz ho hf
      (by simpa using hn) (by simp [C, pre, List.append_assoc]) hp
    have hif := Ex.iteT (s := EncoderBody.small) (t := EncoderBody.large)
      (show (Cnd.lt (2 : Fin 12) 11).wf from (by decide : (2 : Fin 12) ≠ 11)) (by simp [Cnd.eval, hn, ht, hs]) hb
    refine ⟨b, (Ex.seq he (Ex.seq e0 (Ex.seq e1 hif))).mono ?_, ?_⟩
    · simp only [List.length_ofFn, languageCost]
      omega
    · rw [patched_encoder_word_small F D n hs x]
      simpa [hout] using hbo
  · have hl : cutoff onset ≤ n := by omega
    let w0 := List.ofFn (x ∘ firstIndex n)
    let w1 := List.ofFn (x ∘ secondIndex n)
    let w2 := List.ofFn (x ∘ thirdIndex n)
    let o0 := List.ofFn (F.encode (blockSize n 0) (x ∘ firstIndex n))
    let o1 := List.ofFn (F.encode (blockSize n 1) (x ∘ secondIndex n))
    let o2 := List.ofFn (F.encode (blockSize n 2) (x ∘ thirdIndex n))
    let r0 : SourceMessage onset := ⟨blockSize n 0, ⟨x ∘ firstIndex n, (blockSize_large onset n hl 0).1⟩⟩
    let r1 : SourceMessage onset := ⟨blockSize n 1, ⟨x ∘ secondIndex n, (blockSize_large onset n hl 1).1⟩⟩
    let r2 : SourceMessage onset := ⟨blockSize n 2, ⟨x ∘ thirdIndex n, (blockSize_large onset n hl 2).1⟩⟩
    have hword : List.ofFn x = w0 ++ w1 ++ w2 := by
      rw [← ofFn_joinMessage, joinMessage_reconstruct]
    have hinput : C.inp = pre ++ frame (w0 ++ w1 ++ w2) := by
      simp [C, pre, hword, List.append_assoc]
    have hlen0 : a2.env 6 = w0.length := by simpa [a2, a1, DS.set, w0] using ha.first
    have hlen1 : a2.env 7 = w1.length := by simpa [a2, a1, DS.set, w1] using ha.second
    have hlen2 : a2.env 8 = w2.length := by simpa [a2, a1, DS.set, w2] using ha.third
    have room0 : w0.length ≤ C.Lk := by
      have hh := (blockSize_bounds n 0).2
      simp only [w0, List.length_ofFn, C]
      omega
    have room1 : w1.length ≤ C.Lk := by
      have hh := (blockSize_bounds n 1).2
      simp only [w1, List.length_ofFn, C]
      omega
    have room2 : w2.length ≤ C.Lk := by
      have hh := (blockSize_bounds n 2).2
      simp only [w2, List.length_ofFn, C]
      omega
    obtain ⟨b, hb, hbo⟩ := EncoderBody.large_runs C a2 pre w0 w1 w2 o0 o1 o2 r0 r1 r2
      hz ho hf hlen0 hlen1 hlen2 hinput hp (by simp [a2, a1, ha.callInput])
      rfl rfl rfl rfl rfl rfl room0 room1 room2 (hclock 0) (hclock 1) (hclock 2)
    have len0 : o0.length ≤ Bk + 3 := by
      have hh := wf_out_len W r0
      simp only [frame_length, List.length_ofFn] at hh
      have hh' := hclock 0
      dsimp [r0] at hh
      simp only [o0, List.length_ofFn]
      omega
    have len1 : o1.length ≤ Bk + 3 := by
      have hh := wf_out_len W r1
      simp only [frame_length, List.length_ofFn] at hh
      have hh' := hclock 1
      dsimp [r1] at hh
      simp only [o1, List.length_ofFn]
      omega
    have len2 : o2.length ≤ Bk + 3 := by
      have hh := wf_out_len W r2
      simp only [frame_length, List.length_ofFn] at hh
      have hh' := hclock 2
      dsimp [r2] at hh
      simp only [o2, List.length_ofFn]
      omega
    have hsum : w0.length + w1.length + w2.length = n := by
      simp only [w0, w1, w2, List.length_ofFn]
      exact blockSize_sum n
    have hif := Ex.iteF (s := EncoderBody.small) (t := EncoderBody.large)
      (show (Cnd.lt (2 : Fin 12) 11).wf from (by decide : (2 : Fin 12) ≠ 11)) (by simp [Cnd.eval, hn, ht, hs]) hb
    refine ⟨b, (Ex.seq he (Ex.seq e0 (Ex.seq e1 hif))).mono ?_, ?_⟩
    · simp only [List.length_ofFn, languageCost, hsum, C]
      omega
    · rw [patched_encoder_word_large F D hlinear n hl x]
      simpa [hout, o0, o1, o2] using hbo

end NearCubicGates.Adapters.Code.EncoderAlgorithm
