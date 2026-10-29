import Proof.Gates.CounterMachine.FormulaDig

/-! # RG machine, part 12: one Fermat factor

**`facP_spec`**: around any printer `P` of a form's tokens `D`, the factor printer emits `facToks D ρ q`, the tokens
of `1 − (f − ρ)^{q−1}` (lem:residue-count), the residue `ρ` copied from the residue stream `KV` (whose head
moves past it) and `q − 1` held in a register. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ} (cap : ℕ)

section Fac
variable (S : Fin (ns + 1)) (F : Fin 24 ↪ Fin nr)

theorem TRest.seth {σ : WState ns nr} (h : TRest S F σ) (X : Fin (ns + 1)) (hX : X ≠ S) (x : ℕ) :
    TRest S F (σ.seth X x) :=
  ⟨⟨by simp [Function.update_of_ne hX.symm, h.pr.out], h.pr.zero⟩, h.z9, h.z10, h.z17, h.z18, h.z19⟩

/-- The factor printer around `P`. -/
def facP (KV : Fin (ns + 1)) (Q1 : Fin nr) (P : WM ns nr) : WM ns nr :=
  .seq (litC S F (.const 1)) (.seq P (.seq (constInC S F KV) (.seq (litC S F .sub)
    (.seq (powC S F Q1) (litC S F .sub)))))

theorem tokWord_const1_length : (tokWord (.const 1)).length = 9 := by decide

theorem facToks_eq (D : List Tok) (ρ : ℤ) (q : ℕ) :
    facToks D ρ q = (([Tok.const 1] ++ D) ++ [Tok.const ρ]) ++ ([Tok.sub] ++ ([Tok.pow (q - 1)] ++ [Tok.sub])) := by
  simp [facToks]

theorem facP_spec (KV : Fin (ns + 1)) (hKS : KV ≠ S) (Q1 : Fin nr) (hQ : ∀ i : Fin 24, F i ≠ Q1) (P : WM ns nr)
    (D : List Tok) (ρ q Λ cP : ℕ) (pre rest : List Bool) (σ : WState ns nr) (h : TRest S F σ)
    (hst : σ.st KV = pre ++ enc true (natWord ρ) ++ rest) (hsh : σ.sh KV = pre.length) (hQv : σ.val Q1 = q - 1)
    (hqΛ : q - 1 ≤ Λ) (hρΛ : natBitLength ρ ≤ Λ) (hcap : TCap cap F σ (facToks D (ρ : ℤ) q) Λ)
    (hP : WExec cap P (emitT S F σ [Tok.const 1]) (emitT S F (emitT S F σ [Tok.const 1]) D) cP) :
    WExec cap (facP S F KV Q1 P) σ ((emitT S F σ (facToks D (ρ : ℤ) q)).seth KV (pre.length + 2 * (natWord ρ).length))
      (cP + 4000 * (Λ + 1) ^ 2) := by
  rw [facToks_eq] at hcap ⊢
  have cA := TCap.left cap F hcap
  have cB := TCap.right cap S F hcap
  have c1 := TCap.left cap F (TCap.left cap F cA)
  have e1 := litC_spec cap S F (.const 1) σ h (by unfold TCap at c1; simp at c1; omega)
    (by unfold TCap at c1; simp at c1; omega)
  set σ2 := emitT S F (emitT S F σ [Tok.const 1]) D with hσ2
  have h2 : TRest S F σ2 := (h.emitT S F _).emitT S F _
  have hσ2' : σ2 = emitT S F σ ([Tok.const 1] ++ D) := by rw [hσ2, emitT_append]
  have cρ := TCap.right cap S F cA
  rw [← hσ2'] at cρ
  have e3 := constInC_spec cap S F KV hKS ρ pre rest σ2 h2
    (by rw [hσ2, emitT_st_ne S F KV hKS, emitT_st_ne S F KV hKS, hst])
    (by rw [hσ2, emitT_sh_ne S F KV hKS, emitT_sh_ne S F KV hKS, hsh])
    (by unfold TCap at cρ; simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at cρ
        rw [tokWord_const_nat] at cρ; simp only [List.length_append] at cρ ⊢; omega)
    (by unfold TCap at cρ; simp at cρ; omega)
  set pos := pre.length + 2 * (natWord ρ).length
  set σ3 := (emitT S F σ2 [Tok.const (ρ : ℤ)]).seth KV pos with hσ3
  have h3 : TRest S F σ3 := (h2.emitT S F _).seth S F KV hKS pos
  have hσ3' : σ3 = (emitT S F σ ((([Tok.const 1] ++ D) ++ [Tok.const (ρ : ℤ)]))).seth KV pos := by
    rw [hσ3, hσ2', emitT_append]
  rw [hσ3'] at h3
  have c4 : TCap cap F σ3 ([Tok.sub] ++ ([Tok.pow (q - 1)] ++ [Tok.sub])) Λ := by rw [hσ3']; exact cB.seth cap F KV pos
  have e4 := litC_spec cap S F .sub σ3 (by rw [hσ3']; exact h3) (by unfold TCap at c4; simp at c4; omega)
    (by unfold TCap at c4; simp at c4; omega)
  have c5 := TCap.right cap S F c4
  have hQ5 : (emitT S F σ3 [Tok.sub]).val Q1 = q - 1 := by
    rw [emitT_val_ne S F Q1 (hQ 7).symm (hQ 16).symm, hσ3', WState.seth_val,
      emitT_val_ne S F Q1 (hQ 7).symm (hQ 16).symm, hQv]
  have e5 := powC_spec cap S F Q1 hQ (emitT S F σ3 [Tok.sub]) ((by rw [hσ3']; exact h3 : TRest S F σ3).emitT S F _)
    (by have e6l : (natWord 6).length = 7 := by decide
        rw [hQ5, e6l]; unfold TCap at c5; simp [tokWord] at c5; omega)
    (by unfold TCap at c5; simp at c5; omega)
  rw [hQ5] at e5
  have c6 := TCap.right cap S F c5
  have e6 := litC_spec cap S F .sub (emitT S F (emitT S F σ3 [Tok.sub]) [Tok.pow (q - 1)])
    (((by rw [hσ3']; exact h3 : TRest S F σ3).emitT S F _).emitT S F _)
    (by unfold TCap at c6; simp at c6; omega) (by unfold TCap at c6; simp at c6; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq hP (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ ?_
  · rw [emitT_append, emitT_append, hσ3', emitT_seth S F KV hKS, emitT_append]
  · have h1 : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hp := printCost_le (q - 1) Λ hqΛ
    have e6l : (natWord 6).length = 7 := by decide
    have e00 : (natWord 0 ++ natWord 0).length = 6 := by decide
    rw [tokWord_const1_length, tokWord_sub_length, e6l, e00, natWord_length']
    nlinarith

end Fac

end NearCubicGates.Close.CounterMachine
