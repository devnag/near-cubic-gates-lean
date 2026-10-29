import SourceAdapters.Code.DecoderFront
import SourceAdapters.Code.DecoderPrepareBody
import SourceAdapters.Code.DecoderTypes
import SourceAdapters.Code.EncoderAlgorithm

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the entire decoder request-preparation stage, with
actual source encoder length queries and explicit finite-patch selection. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DecoderPrepareAlgorithm

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Code DecoderTypes BlockArithmetic

abbrev State := DS 12 0
abbrev Script := St 12 0

def script (onset : ℕ) : Script := .seq DecoderFront.script
  (.seq (.op (.zero 11)) (.seq (addConstant 0 11 (cutoff onset))
    (.ite (.lt 2 11) (.seq (.op (.emit false)) DecoderPrepareBody.small)
      (.seq (.op (.emit true)) DecoderPrepareBody.large))))

def cost (onset L n len Lk Bk : ℕ) : ℕ := 1000 * (L + n.bits.length + n + len + cutoff onset + Lk + Bk + 1)

theorem runs (F : BinaryFamily) (onset K e : ℕ)
    (W : WordFunction (SourceMessage onset) sourceMessageWord
      (fun p => frame (List.ofFn (F.encode p.1 p.2.val))) (fun p => K * (p.1 + 1) ^ e))
    (Wd Lk Bk L : ℕ) (j : Job F onset)
    (hcap : (jobBits F j).length + 2 * jobLength F j + 6 + cutoff onset + 2 ^ (jobLength F j).bits.length < 2 ^ Wd)
    (hroom : jobLength F j ≤ Lk)
    (hclock : ∀ i : Fin 3, K * (blockSize (jobLength F j) i + 1) ^ e ≤ Bk) :
    ∃ b, Ex (⟨Wd, List.replicate L true ++ false :: jobWord F j, EncoderAlgorithm.callee F onset K e W, Lk, Bk⟩ : Ctx)
      (script onset) a0 b (cost onset L (jobLength F j) (jobBits F j).length Lk Bk) ∧
      b.out = input F L (workOf F j) := by
  let C : Ctx := ⟨Wd, List.replicate L true ++ false :: jobWord F j, EncoderAlgorithm.callee F onset K e W, Lk, Bk⟩
  have hp : 1 ≤ 2 ^ (jobLength F j).bits.length := Nat.one_le_pow _ _ (by omega)
  obtain ⟨a, he, ha⟩ := DecoderFront.runs C L (jobLength F j) (frame (jobBits F j)) rfl (by dsimp [C]; omega)
  have e0 := Ex.op (OpEx.zero (C := C) (11 : Fin 12) a)
  let a1 := a.set 11 0
  have e1 := add_constant C (0 : Fin 12) 11 (by decide) (cutoff onset) a1
    (by simp [a1, DS.set, ha.zero]) (by simp [a1, C]; omega)
  let a2 := a1.set 11 (a1.env 11 + cutoff onset)
  let pre := List.replicate L true ++ [false] ++ frame (jobLength F j).bits
  have hz : a2.env 0 = 0 := by simp [a2, a1, DS.set, ha.zero]
  have ho : a2.env 10 = 1 := by simp [a2, a1, DS.set, ha.one]
  have hf : a2.env 1 = 0 := by simp [a2, a1, DS.set, ha.flag]
  have hn : a2.env 2 = jobLength F j := by simpa [a2, a1, DS.set] using ha.length
  have ht : a2.env 11 = cutoff onset := by simp [a2, a1]
  have hpos : a2.ip = pre.length := by simp [a2, a1, pre, ha.position]; omega
  have hout : a2.out = List.replicate L true ++ [false] := by simp [a2, a1, ha.output]
  cases j with
  | inl p =>
    have hs : jobLength F (.inl p : Job F onset) < cutoff onset := p.2.property
    have ef := Ex.op (OpEx.emit (C := C) false a2)
    let a3 : State := {a2 with out := a2.out ++ [false]}
    obtain ⟨b, hb, hbo⟩ := DecoderPrepareBody.small_runs C a3 pre (List.ofFn p.2.val) hz ho hf
      (by simpa [a3, jobLength] using hn) (by simp [C, jobWord, jobLength, jobBits, pre, List.append_assoc]) hpos
    have hif := Ex.iteT (c := Cnd.lt (2 : Fin 12) 11)
      (t := .seq (.op (.emit true)) DecoderPrepareBody.large) (by decide : (2 : Fin 12) ≠ 11)
      (by simp [Cnd.eval, hn, ht, hs]) (Ex.seq ef hb)
    refine ⟨b, (Ex.seq he (Ex.seq e0 (Ex.seq e1 hif))).mono ?_, ?_⟩
    · simp only [cost, jobLength, jobBits, List.length_ofFn]
      omega
    · simpa [input, workOf, payload, a3, hout, List.append_assoc] using hbo
  | inr p =>
    have hl : cutoff onset ≤ p.1 := p.2.property
    have hs : ¬jobLength F (.inr p : Job F onset) < cutoff onset := by exact not_lt_of_ge hl
    have ef := Ex.op (OpEx.emit (C := C) true a2)
    let a3 : State := {a2 with out := a2.out ++ [true]}
    let w0 := List.ofFn (p.2.val ∘ firstOutputIndex F p.1)
    let w1 := List.ofFn (p.2.val ∘ secondOutputIndex F p.1)
    let w2 := List.ofFn (p.2.val ∘ thirdOutputIndex F p.1)
    let o0 := List.ofFn (F.encode (blockSize p.1 0) (fun _ => false))
    let o1 := List.ofFn (F.encode (blockSize p.1 1) (fun _ => false))
    let o2 := List.ofFn (F.encode (blockSize p.1 2) (fun _ => false))
    let r0 : SourceMessage onset := ⟨blockSize p.1 0, ⟨fun _ => false, (blockSize_large onset p.1 hl 0).1⟩⟩
    let r1 : SourceMessage onset := ⟨blockSize p.1 1, ⟨fun _ => false, (blockSize_large onset p.1 hl 1).1⟩⟩
    let r2 : SourceMessage onset := ⟨blockSize p.1 2, ⟨fun _ => false, (blockSize_large onset p.1 hl 2).1⟩⟩
    have hw : List.ofFn p.2.val = w0 ++ w1 ++ w2 := received_split F p.1 p.2.val
    have hi : C.inp = pre ++ frame (w0 ++ w1 ++ w2) := by
      simp [C, pre, jobWord, jobLength, jobBits, hw, List.append_assoc]
    have hlen0 : a3.env 6 = blockSize p.1 0 := by simpa [a3, a2, a1, DS.set, jobLength] using ha.first
    have hlen1 : a3.env 7 = blockSize p.1 1 := by simpa [a3, a2, a1, DS.set, jobLength] using ha.second
    have hlen2 : a3.env 8 = blockSize p.1 2 := by simpa [a3, a2, a1, DS.set, jobLength] using ha.third
    have hbound : ∀ i : Fin 3, blockSize p.1 i ≤ p.1 := by
      intro i
      have hh := (blockSize_bounds p.1 i).2
      omega
    have hroom' : p.1 ≤ Lk := hroom
    simp only [jobBits, jobLength, List.length_ofFn, threeBlock] at hcap
    simp only [jobLength] at hp
    have h0 : F.length (blockSize p.1 0) + 2 * blockSize p.1 0 < 2 ^ Wd := by
      have hb := hbound 0
      change F.length (blockSize p.1 0) + F.length (blockSize p.1 1) + F.length (blockSize p.1 2) +
        2 * p.1 + 6 + cutoff onset + 2 ^ p.1.bits.length < 2 ^ Wd at hcap
      omega
    have h1 : F.length (blockSize p.1 1) + 2 * blockSize p.1 1 < 2 ^ Wd := by
      have hb := hbound 1
      change F.length (blockSize p.1 0) + F.length (blockSize p.1 1) + F.length (blockSize p.1 2) +
        2 * p.1 + 6 + cutoff onset + 2 ^ p.1.bits.length < 2 ^ Wd at hcap
      omega
    have h2 : F.length (blockSize p.1 2) + 2 * blockSize p.1 2 < 2 ^ Wd := by
      have hb := hbound 2
      change F.length (blockSize p.1 0) + F.length (blockSize p.1 1) + F.length (blockSize p.1 2) +
        2 * p.1 + 6 + cutoff onset + 2 ^ p.1.bits.length < 2 ^ Wd at hcap
      omega
    obtain ⟨b, hb, hbo⟩ := DecoderPrepareBody.large_runs C a3
      (blockSize p.1 0) (blockSize p.1 1) (blockSize p.1 2) pre w0 w1 w2 o0 o1 o2 r0 r1 r2
      hz ho hlen0 hlen1 hlen2 hi hpos (by simp [a3, a2, a1, ha.callInput])
      (by simp [C, EncoderAlgorithm.callee, r0, sourceMessageWord])
      (by simp [C, EncoderAlgorithm.callee, r1, sourceMessageWord])
      (by simp [C, EncoderAlgorithm.callee, r2, sourceMessageWord]) rfl rfl rfl
      (by simp [o0, w0]) (by simp [o1, w1]) (by simp [o2, w2])
      ((hbound 0).trans hroom') ((hbound 1).trans hroom') ((hbound 2).trans hroom')
      (hclock 0) (hclock 1) (hclock 2) (by simpa [o0, C] using h0) (by simpa [o1, C] using h1) (by simpa [o2, C] using h2)
    have hsum := blockSize_sum p.1
    have hwords : w0.length + w1.length + w2.length = (jobBits F (.inr p : Job F onset)).length := by
      simpa only [jobBits, List.length_append] using congrArg List.length hw.symm
    have hif := Ex.iteF (c := Cnd.lt (2 : Fin 12) 11)
      (s := .seq (.op (.emit false)) DecoderPrepareBody.small) (by decide : (2 : Fin 12) ≠ 11)
      (by simp [Cnd.eval, hn, ht, hs]) (Ex.seq ef hb)
    refine ⟨b, (Ex.seq he (Ex.seq e0 (Ex.seq e1 hif))).mono ?_, ?_⟩
    · simp only [cost, hsum, hwords, C]
      omega
    · simpa [input, workOf, payload, sourcePacket, a3, hout, w0, w1, w2, List.append_assoc] using hbo

end NearCubicGates.Adapters.Code.DecoderPrepareAlgorithm
