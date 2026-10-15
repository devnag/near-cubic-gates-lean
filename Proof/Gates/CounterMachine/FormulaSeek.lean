import Proof.Gates.CounterMachine.FormulaLin
import Proof.Gates.CounterMachine.CellNats
import Proof.Gates.Codec.Lists

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec

variable {ns nr : ℕ} (cap : ℕ)

/-- The framed words of a list of naturals. -/
def encN (L : List ℕ) : List Bool := (L.map fun x => enc true (natWord x)).flatten

theorem encN_append (L M : List ℕ) : encN (L ++ M) = encN L ++ encN M := by simp [encN]

theorem encN_flatMap (L : List ℕ) : encN L = (L.map fun x => enc true (natWord x)).flatten := rfl

theorem encN_take_drop (L : List ℕ) (i : ℕ) : encN L = encN (L.take i) ++ encN (L.drop i) := by
  rw [← encN_append, List.take_append_drop]

section Seek
variable (I : Fin (ns + 1)) (B Idx Cr C f c t : Fin nr)

/-- Rewind `I`, then step over `Idx` fields. -/
def seekP : WM ns nr :=
  .seq (copyR B Cr t) (.seq (WM.rewind I Cr) (.seq (copyR Idx C t) (listLoop C (skipNat true I f c))))

def seekCost (b i : ℕ) (L : List ℕ) : ℕ :=
  18 * b + 3 + 1 + (5 * b + 1 + 1 + (18 * i + 3 + 1 + (((L.take i).map fun x => 20 * natBitLength x + 20 + 4).sum + 1)))

theorem seekP_spec (hd : [B, Idx, Cr, C, f, c, t].Nodup) (L : List ℕ) (rest : List Bool) (σ : WState ns nr)
    (hst : σ.st I = encN L ++ rest) (hsh : σ.sh I ≤ σ.val B) (hidx : σ.val Idx ≤ L.length)
    (hCr : σ.val Cr = 0) (hC : σ.val C = 0) (hf : σ.val f = 0) (hc : σ.val c = 0) (ht : σ.val t = 0)
    (hfit : ∀ x ∈ L, natBitLength x + 1 ≤ cap) (hcap : σ.val B + σ.val Idx + 1 ≤ cap) :
    WExec cap (seekP I B Idx Cr C f c t) σ (σ.seth I (encN (L.take (σ.val Idx))).length)
      (seekCost (σ.val B) (σ.val Idx) L) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hBI, hBCr, hBC, hBf, hBc, hBt⟩, ⟨hICr, hIC, hIf, hIc, hIt⟩, ⟨hCrC, hCrf, hCrc, hCrt⟩, ⟨hCf, hCc, hCt⟩,
    ⟨hfc, hft⟩, hct⟩ := hd
  set b := σ.val B
  set i := σ.val Idx
  have e1 := copyR_spec cap hBCr hBt hCrt σ ht (by rw [hCr]; omega)
  rw [hCr, Nat.zero_add] at e1
  set σ1 := σ.setv Cr b with hσ1
  have e2 := wrewind_spec (cap := cap) I Cr b σ1 (by simp [hσ1]) (by simp [hσ1]; omega)
  have hsh0 : σ1.sh I - b = 0 := by simp [hσ1]; omega
  rw [hsh0] at e2
  set σ2 := (σ1.setv Cr 0).seth I 0 with hσ2
  have v2 : ∀ r, r ≠ Cr → σ2.val r = σ.val r := fun r hr => by simp [hσ2, hσ1, Function.update_of_ne hr]
  have e3 := copyR_spec cap hIC hIt hCt σ2 (by rw [v2 t (Ne.symm hCrt)]; exact ht)
    (by rw [v2 C (Ne.symm hCrC), v2 Idx hICr, hC]; omega)
  rw [v2 C (Ne.symm hCrC), v2 Idx hICr, hC, Nat.zero_add] at e3
  set σ3 := σ2.setv C i with hσ3
  have hsplit : encN L = encN (L.take i) ++ encN (L.drop i) := encN_take_drop L i
  have hlen : (L.take i).length = i := by simp; omega
  have e4 := listLoop_spec cap I C (skipNat true I f c) (fun x => enc true (natWord x))
    (fun x => 20 * natBitLength x + 20) (fun τ => τ.val f = 0 ∧ τ.val c = 0)
    (fun τ x h => ⟨by simpa using h.1, by simpa using h.2⟩)
    (fun τ x h => ⟨by simp [Function.update_of_ne (Ne.symm hCf), h.1], by simp [Function.update_of_ne (Ne.symm hCc), h.2]⟩)
    (L.take i)
    (fun x hx pre rest' τ h hst' hsh' => by
      have := skipNat_spec cap true I f c hfc x pre rest' τ hst' hsh' h.1 h.2 (hfit x (List.mem_of_mem_take hx))
      simpa [enc_length, stp] using this)
    [] (encN (L.drop i) ++ rest) σ3
    ⟨by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hCf), Function.update_of_ne (Ne.symm hCrf), hf],
     by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hCc), Function.update_of_ne (Ne.symm hCrc), hc]⟩
    (by simp only [hσ3, hσ2, hσ1, WState.setv_st, WState.seth_st]; rw [hst, hsplit]
        simp only [encN, List.flatMap, List.nil_append, List.append_assoc])
    (by simp [hσ3, hσ2]) (by simp [hσ3, hlen]) (by rw [hlen]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by
    unfold seekCost; exact le_refl _)
  apply WState.eq
  · funext j; by_cases hj : j = I
    · subst hj; simp [hσ3, hσ2, encN, List.flatMap]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne hj]
  · simp [hσ3, hσ2, hσ1]
  · funext r; by_cases r1 : r = C
    · subst r1; simp [hσ3, hσ2, hσ1, hC]
    · by_cases r2 : r = Cr
      · subst r2; simp [hσ3, hσ2, hσ1, Function.update_of_ne r1, hCr]
      · simp [hσ3, hσ2, hσ1, Function.update_of_ne r1, Function.update_of_ne r2]
  · simp [hσ3, hσ2, hσ1]

end Seek

end NearCubicGates.Close.CounterMachine
