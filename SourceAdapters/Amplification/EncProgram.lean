import SourceAdapters.Amplification.EncSetup
import Proof.Gates.Cells.Run

/-!
# The encoder program of X9 and its run (`app:sources`, "Full-range amplification interface")

`encP R` on the input `1^L ++ false :: encoderInput r` (the unary prefix only sets the width of the cell
language): read `k` and `n`; compute `h, m, t, ℓ` and the powers (`paramsP`); find the X3 modulus
`firstPrimitive t` (`searchP`); write `frame (binary ℓ)` (`emitFrameP`) and the `2^ℓ` code bits (`mainLoop`).
`encP_run`: the output is exactly `encoderOutput R r` (the join's output word).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.ExecutableInterfaces

def constP : Sc := .seq (.op (.inc vONE)) (.seq (.op (.inc vTWO)) (.op (.inc vTWO)))

def restP (R : ℕ) : Sc := .seq (paramsP R) (.seq searchP (.seq emitFrameP mainLoop))

def encP (R : ℕ) : Sc :=
  .seq constP <| .seq skipP <| .seq parseP <| .seq (.op (.copy vK vPV)) <| .seq parseP <|
  .seq (.op (.copy vN vPV)) (restP R)

@[simp] theorem prm0_t (R n k : ℕ) : (prm0 R n k).t = tParam R n k := rfl
@[simp] theorem prm0_h (R n k : ℕ) : (prm0 R n k).h = hParam n k := rfl
@[simp] theorem prm0_m (R n k : ℕ) : (prm0 R n k).m = mParam n k := rfl
@[simp] theorem prm0_n (R n k : ℕ) : (prm0 R n k).n = n := rfl
@[simp] theorem prm0_L (R n k : ℕ) : (prm0 R n k).L = arityParam R n k := rfl
@[simp] theorem Prm.withP_h (g : Prm) (p : ℕ) : (g.withP p).h = g.h := rfl
@[simp] theorem Prm.withP_m (g : Prm) (p : ℕ) : (g.withP p).m = g.m := rfl
@[simp] theorem Prm.withP_n (g : Prm) (p : ℕ) : (g.withP p).n = g.n := rfl
@[simp] theorem Prm.withP_L (g : Prm) (p : ℕ) : (g.withP p).L = g.L := rfl

def allS : List Var := paramsS ++ searchS ++ emitS ++ mainS

/-- The cost of the part after reading the request. -/
def restCost (R n k : ℕ) : ℕ :=
  paramsCost R n (arityParam R n k) + searchCost (tParam R n k) + ((arityParam R n k).size * 12 + 10) +
    mainCost (tParam R n k) (hParam n k) (mParam n k) n (arityParam R n k) + 10

theorem restP_spec (C : Ctx) (R : ℕ) (a : Ds) (hc : Consts a) (n k : ℕ) (hn : a.env vN = n) (hk : a.env vK = k)
    (hp : a.env vP = 0) (hW : arityParam R n k + 5 ≤ C.Wd) (T : ℕ → Bool) (base : ℕ) (hT : TableAt C base n T)
    (hip : a.ip = base) :
    Runs C (restP R) a (restCost R n k) allS
      (frame (arityParam R n k).bits ++ tableBits ((prm0 R n k).withP (GF.firstPrimitive (tParam R n k))) T)
      (fun _ => True) := by
  obtain ⟨hnk, htL, hht, hmL, ht1⟩ := prm0_le R n k
  have hw0 : WOk (prm0 R n k) C := ⟨by show arityParam R n k + 4 ≤ C.Wd; omega, htL, hht,
    show n ≤ arityParam R n k by omega, hmL, ht1⟩
  refine Runs.callS (paramsP_spec C R a hc n k hn hk hp hW) (by decide) ?_ (by unfold restCost; omega)
  intro b hb hgb
  have hbip : b.ip = base := hb.ip.trans hip
  refine Runs.callS (searchP_spec C (prm0 R n k) hw0 b hgb) (by decide) ?_
    (by simp only [prm0_t]; unfold restCost; omega)
  rintro d hd ⟨-, hgd⟩
  have hdip : d.ip = base := hd.ip.trans hbip
  have hw : WOk ((prm0 R n k).withP (GF.firstPrimitive (tParam R n k))) C := hw0
  have hpok : GF.ModulusOk (GF.firstPrimitive (tParam R n k)) (tParam R n k) :=
    (Field.binaryFieldArithmetic.2.1 (tParam R n k) ht1).1.2.1
  have hW4 : 2 * 2 ≤ 2 ^ C.Wd := by
    have : 2 ^ 2 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have e1 := emitFrameP_spec C d hgd.c (arityParam R n k) hgd.L hW4
  refine (Runs.seq (n' := mainCost (tParam R n k) (hParam n k) (mParam n k) n (arityParam R n k))
    (e1.mono le_rfl (show emitS ⊆ allS by decide) (fun e he _ => he)) ?_).costLe ?_
  · intro e _ he
    have hge := hgd.of_fr he (by decide)
    have heip : e.ip = base := he.ip.trans hdip
    exact (mainLoop_spec C _ hw hpok e hge T base hT heip).mono le_rfl (show mainS ⊆ allS by decide)
      (fun _ _ h => h)
  · simp only [prm0_t]; unfold restCost; omega

/-- The cost of the whole encoder run. -/
def encCost (R n k L0 : ℕ) : ℕ :=
  5 + (L0 * 3 + 4) + (k.size * 10 + 10) + 1 + (n.size * 10 + 10) + 1 + restCost R n k + 10

theorem size_le_self (x : ℕ) : x.size ≤ x := by
  rcases Nat.eq_zero_or_pos x with rfl | h0
  · simp
  · exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem table_getD {n : ℕ} (msg : BoolFunction n) (i : ℕ) (hi : i < 2 ^ n) :
    (boolFunctionTable msg).getD i false = msgT msg i := by
  unfold boolFunctionTable msgT
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- **The run of the encoder program.** -/
theorem encP_run (C : Ctx) (R L0 : ℕ) (r : Joins.EncoderRequest)
    (hin : C.inp = List.replicate L0 true ++ false :: Joins.encoderInput r)
    (hW : arityParam R r.n r.k + 5 ≤ C.Wd) :
    ∃ b, Ex C (encP R) (a0 : Ds) b (encCost R r.n r.k L0) ∧ b.out = Joins.encoderOutput R r := by
  obtain ⟨hnk, -, -, -, -⟩ := prm0_le R r.n r.k
  have hsk : r.k.size + 2 ≤ C.Wd := by have := size_le_self r.k; omega
  have hsn : r.n.size + 2 ≤ C.Wd := by have := size_le_self r.n; omega
  have h2W : 2 < 2 ^ C.Wd := by
    have : 2 ^ 2 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp at this; omega
  -- constants
  set a1 : Ds := ((((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).set vTWO
    (((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).env vTWO + 1))).set vTWO
    ((((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).set vTWO
    (((a0 : Ds).set vONE ((a0 : Ds).env vONE + 1)).env vTWO + 1)).env vTWO + 1) with ha1
  have e0 : Ex C constP (a0 : Ds) a1 5 :=
    Ex.seq (Ex.op (OpEx.inc vONE _ (by simp [a0]; omega))) (Ex.seq (Ex.op (OpEx.inc vTWO _
      (by simp (config := { decide := true }) [a0, env_set]; omega)))
      (Ex.op (OpEx.inc vTWO _ (by simp (config := { decide := true }) [a0, env_set]; omega))))
  have hc1 : Consts a1 := ⟨by simp (config := { decide := true }) [a1, a0, env_set],
    by simp (config := { decide := true }) [a1, a0, env_set], by simp (config := { decide := true }) [a1, a0, env_set]⟩
  have hFr1 : ∀ x : Var, x ∉ [vONE, vTWO] → a1.env x = 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [a1, a0, env_set, hx.1, hx.2]
  -- skip the prefix
  obtain ⟨b1, e1, hf1, hip1⟩ := skipP_spec C L0 (Joins.encoderInput r) hin a1 hc1 (by simp [a1, a0, DS.set])
  have hc_b1 : Consts b1 := ⟨(hf1.env _ (by decide)).trans hc1.1, (hf1.env _ (by decide)).trans hc1.2.1,
    (hf1.env _ (by decide)).trans hc1.2.2⟩
  -- read k
  have hin2 : C.inp = (List.replicate L0 true ++ [false]) ++ frame r.k.bits ++ RepairSource.amplifierInput ⟨r.n, r.msg⟩ := by
    rw [hin]; simp [Joins.encoderInput, List.append_assoc]
  obtain ⟨b2, e2, hf2, hip2, hk2⟩ := parseP_spec C r.k (L0 + 1) _ _ hin2 (by simp) hsk b1 hc_b1 hip1
  have hc_b2 : Consts b2 := ⟨(hf2.env _ (by decide)).trans hc_b1.1, (hf2.env _ (by decide)).trans hc_b1.2.1,
    (hf2.env _ (by decide)).trans hc_b1.2.2⟩
  set b3 := b2.set vK (b2.env vPV) with hb3
  have e3 : Ex C (.op (.copy vK vPV)) b2 b3 1 := Ex.op (OpEx.copy vK vPV b2 (by decide))
  have hc_b3 : Consts b3 := ⟨by simp (config := { decide := true }) [b3, env_set, hc_b2.1], by simp (config := { decide := true }) [b3, env_set, hc_b2.2.1],
    by simp (config := { decide := true }) [b3, env_set, hc_b2.2.2]⟩
  -- read n
  have hin3 : C.inp = (List.replicate L0 true ++ [false] ++ frame r.k.bits) ++ frame r.n.bits ++
      boolFunctionTable r.msg := by
    rw [hin]; simp [Joins.encoderInput, RepairSource.amplifierInput, List.append_assoc]
  obtain ⟨b4, e4, hf4, hip4, hn4⟩ := parseP_spec C r.n (L0 + 1 + (2 * r.k.size + 1)) _ _ hin3
    (by simp [frame_length, Nat.size_eq_bits_len]; omega) hsn b3 hc_b3 (by simp [b3, DS.set, hip2]; omega)
  have hc_b4 : Consts b4 := ⟨(hf4.env _ (by decide)).trans hc_b3.1, (hf4.env _ (by decide)).trans hc_b3.2.1,
    (hf4.env _ (by decide)).trans hc_b3.2.2⟩
  set b5 := b4.set vN (b4.env vPV) with hb5
  have e5 : Ex C (.op (.copy vN vPV)) b4 b5 1 := Ex.op (OpEx.copy vN vPV b4 (by decide))
  have hc_b5 : Consts b5 := ⟨by simp (config := { decide := true }) [b5, env_set, hc_b4.1], by simp (config := { decide := true }) [b5, env_set, hc_b4.2.1],
    by simp (config := { decide := true }) [b5, env_set, hc_b4.2.2]⟩
  have hk5 : b5.env vK = r.k := by
    simp only [b5, env_set]; norm_num
    rw [hf4.env vK (by decide)]; simp (config := { decide := true }) [b3, env_set, hk2]
  have hn5 : b5.env vN = r.n := by simp (config := { decide := true }) [b5, env_set, hn4]
  have hp5 : b5.env vP = 0 := by
    simp only [b5, env_set]; norm_num
    rw [hf4.env vP (by decide)]; simp only [b3, env_set]; norm_num
    rw [hf2.env vP (by decide), hf1.env vP (by decide)]; exact hFr1 vP (by decide)
  set base := L0 + 1 + (2 * r.k.size + 1) + 2 * r.n.size + 1 with hbase
  have hT : TableAt C base r.n (msgT r.msg) := by
    have hlen : (List.replicate L0 true ++ [false] ++ frame r.k.bits ++ frame r.n.bits).length = base := by
      simp [frame_length, Nat.size_eq_bits_len]; omega
    constructor
    · rw [hin3, List.length_append, hlen]; simp [boolFunctionTable]
    · intro i hi
      rw [hin3, ← hlen, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      exact table_getD r.msg i hi
  obtain ⟨b6, e6, hf6, -⟩ := restP_spec C R b5 hc_b5 r.n r.k hn5 hk5 hp5 hW (msgT r.msg) base hT
    (by simp [b5, DS.set, hip4]; try omega)
  have hout5 : b5.out = [] := by
    have e5o : b5.out = b4.out := rfl
    have e3o : b3.out = b2.out := rfl
    rw [e5o, hf4.out, e3o, hf2.out, hf1.out]
    simp [a1, a0, DS.set]
  refine ⟨b6, ?_, ?_⟩
  · exact (Ex.seq e0 (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 e6)))))).mono (by unfold encCost; omega)
  · rw [hf6.out, hout5, List.nil_append, encoderOutput_eq]
    rfl

end NearCubicGates.Adapters.Amplification.Enc
