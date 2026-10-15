import Proof.Wire_3_5.PrimAsmDataRun
import Proof.Wire_3_5.PrimAsmStarNums
import Proof.Wire_3_5.PrimAsmEmit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.NumsX
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## The layout -/

/-- Streams `0 … 3`: the framed request, the fill count, the fill's marker tape, the output. -/
abbrev NS : ℕ := 3
/-- Registers: the star block `0 … 19`, the reader's `20 … 23`, `m`, the output counter, the loop register. -/
abbrev NR : ℕ := 32

def xIN : Fin (NS + 1) := 0
def xCT : Fin (NS + 1) := 1
def xAUX : Fin (NS + 1) := 2
def xOUT : Fin (NS + 1) := 3

/-- The star block. -/
def SN : Fin 20 ↪ Fin NR := Fin.castLEEmb (by norm_num)

def rF : Fin NR := 20
def rC : Fin NR := 21
def rP : Fin NR := 22
def rT : Fin NR := 23
def rM : Fin NR := 24
def rOP : Fin NR := 25
def rK : Fin NR := 26

theorem SN_val (i : Fin 20) : (SN i).val = i.val := rfl

theorem SN_ne (i : Fin 20) (r : Fin NR) (h : 20 ≤ r.val) : SN i ≠ r := by
  intro e
  have := congrArg Fin.val e
  rw [SN_val] at this
  have := i.isLt
  omega

/-! ## The program -/

/-- The exponent `m = 2·kh + L` in `rM`. -/
def mW : WM NS NR := .seq (addTo (SN 8) rM rT) (.seq (addTo (SN 8) rM rT) (addTo (SN 1) rM rT))

/-- The source `1^(m+1) 0 0^m 1`. -/
def srcW : WM NS NR :=
  .seq (emitW xOUT rOP [true]) (.seq (repRegW xOUT rOP rM rK rT [true]) (.seq (emitW xOUT rOP [false])
    (.seq (repRegW xOUT rOP rM rK rT [false]) (emitW xOUT rOP [true]))))

/-- The whole program: `n`, the star numbers, `m`, the source. -/
def numsW (cr : ℕ) : WM NS NR :=
  .seq (readNatM true xIN rF rC (SN 0) rP rT) (.seq (StarNums.starNumsM cr 0 SN) (.seq mW srcW))

/-- The CapReader source of `2^m`. -/
def srcWord (m : ℕ) : List Bool := [true] ++ reps m [true] ++ [false] ++ reps m [false] ++ [true]

theorem reps_single (m : ℕ) (b : Bool) : reps m [b] = List.replicate m b := by
  induction m with
  | zero => rfl
  | succ m ih => rw [reps_succ, ih, List.replicate_succ']

/-- The source in `CapReader.run`'s shape: `1^(m+1)`, `0`, then the bits `0^m 1`. -/
theorem srcWord_eq (m : ℕ) :
    srcWord m = List.replicate (List.replicate m false ++ [true]).length true ++
      false :: ((List.replicate m false ++ [true]) ++ []) := by
  simp only [srcWord, reps_single, List.length_append, List.length_replicate, List.length_singleton,
    List.append_nil, List.replicate_succ, List.cons_append, List.singleton_append, List.append_assoc, List.nil_append]

/-- The value of the bits: `2^m`. -/
theorem src_value (m : ℕ) : RadixSemantics.value (List.replicate m false ++ [true]) = 2 ^ m := by
  rw [RadixSemantics.value_append]
  have h0 : ∀ k, RadixSemantics.value (List.replicate k false) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, RadixSemantics.value, ih]
  simp [h0, RadixSemantics.value]

/-! ## The program's run -/

section Spec
variable (cap : ℕ)

theorem mW_spec (σ : WState NS NR) (kh L : ℕ) (h8 : σ.val (SN 8) = kh) (h1 : σ.val (SN 1) = L)
    (hm : σ.val rM = 0) (ht : σ.val rT = 0) (hc : 2 * kh + L ≤ cap) :
    WExec cap mW σ (σ.setv rM (2 * kh + L)) (18 * kh + 3 + 1 + (18 * kh + 3 + 1 + (18 * L + 3))) := by
  have n8m : SN 8 ≠ rM := SN_ne 8 rM (by decide)
  have n8t : SN 8 ≠ rT := SN_ne 8 rT (by decide)
  have n1m : SN 1 ≠ rM := SN_ne 1 rM (by decide)
  have n1t : SN 1 ≠ rT := SN_ne 1 rT (by decide)
  have nmt : rM ≠ rT := by decide
  have a1 := addTo_spec cap (SN 8) rM rT n8m n8t nmt σ ht (by omega) (by rw [hm, h8]; omega)
  rw [hm, h8] at a1
  have a2 := addTo_spec cap (SN 8) rM rT n8m n8t nmt (σ.setv rM (0 + kh)) (by simp [Function.update_apply, nmt.symm, ht])
    (by simp [Function.update_apply, n8m, h8]; omega) (by simp [Function.update_apply, n8m, h8]; omega)
  have v8 : (σ.setv rM (0 + kh)).val (SN 8) = kh := by simp [Function.update_apply, n8m, h8]
  have vm : (σ.setv rM (0 + kh)).val rM = kh := by simp
  rw [v8, vm] at a2
  have a3 := addTo_spec cap (SN 1) rM rT n1m n1t nmt ((σ.setv rM (0 + kh)).setv rM (kh + kh))
    (by simp [Function.update_apply, nmt.symm, ht]) (by simp [Function.update_apply, n1m, h1]; omega)
    (by simp [Function.update_apply, n1m, h1]; omega)
  have v1 : ((σ.setv rM (0 + kh)).setv rM (kh + kh)).val (SN 1) = L := by simp [Function.update_apply, n1m, h1]
  have vm2 : ((σ.setv rM (0 + kh)).setv rM (kh + kh)).val rM = kh + kh := by simp
  rw [v1, vm2] at a3
  refine WExec.cast cap (WExec.seq a1 (WExec.seq a2 a3)) ?_ (by omega)
  rw [wsetv_setv, wsetv_setv, show kh + kh + L = 2 * kh + L by omega]

theorem srcW_spec (σ : WState NS NR) (m : ℕ) (hm : σ.val rM = m) (hK : σ.val rK = 0) (hT : σ.val rT = 0)
    (hO : σ.st xOUT = []) (hOh : σ.sh xOUT = 0) (hOP : σ.val rOP = 0) (hc : 2 * m + 3 ≤ cap) :
    WExec cap srcW σ (appendO σ xOUT rOP (srcWord m)) (8 + 1 + (18 * m + 3 + 1 + (m * 12 + 1) + 1 + (8 + 1 +
      (18 * m + 3 + 1 + (m * 12 + 1) + 1 + 8)))) := by
  have nMK : rM ≠ rK := by decide
  have nMT : rM ≠ rT := by decide
  have nKT : rK ≠ rT := by decide
  have nKO : rK ≠ rOP := by decide
  have nMO : rM ≠ rOP := by decide
  have nTO : rT ≠ rOP := by decide
  -- 1
  have e1 := emitW_spec cap xOUT rOP [true] σ (by rw [hO, hOh]; rfl) (by simp [hOP]; omega)
  set σa := appendO σ xOUT rOP [true] with hσa
  have ha_m : σa.val rM = m := by simp [hσa, Function.update_apply, nMO, hm]
  have ha_K : σa.val rK = 0 := by simp [hσa, Function.update_apply, nKO, hK]
  have ha_T : σa.val rT = 0 := by simp [hσa, Function.update_apply, nTO, hT]
  have ha_O : σa.sh xOUT = (σa.st xOUT).length := by simp [hσa, hO, hOh]
  have ha_P : σa.val rOP = 1 := by simp [hσa, hOP]
  -- 2
  have e2 := repRegW_spec cap xOUT rOP rM rK rT nMK nMT nKT nKO [true] σa ha_K ha_T ha_O (by rw [ha_m]; omega)
    (by rw [ha_P, ha_m]; simp; omega)
  rw [ha_m] at e2
  set σb := appendO σa xOUT rOP (reps m [true]) with hσb
  have hb_m : σb.val rM = m := by simp [hσb, Function.update_apply, nMO, ha_m]
  have hb_K : σb.val rK = 0 := by simp [hσb, Function.update_apply, nKO, ha_K]
  have hb_T : σb.val rT = 0 := by simp [hσb, Function.update_apply, nTO, ha_T]
  have hb_O : σb.sh xOUT = (σb.st xOUT).length := by simp [hσb, ha_O]
  have hb_P : σb.val rOP = 1 + m := by simp [hσb, ha_P, reps_single]
  -- 3
  have e3 := emitW_spec cap xOUT rOP [false] σb hb_O (by rw [hb_P]; simp; omega)
  set σc := appendO σb xOUT rOP [false] with hσc
  have hc_m : σc.val rM = m := by simp [hσc, Function.update_apply, nMO, hb_m]
  have hc_K : σc.val rK = 0 := by simp [hσc, Function.update_apply, nKO, hb_K]
  have hc_T : σc.val rT = 0 := by simp [hσc, Function.update_apply, nTO, hb_T]
  have hc_O : σc.sh xOUT = (σc.st xOUT).length := by simp [hσc, hb_O]
  have hc_P : σc.val rOP = 2 + m := by simp [hσc, hb_P]; omega
  -- 4
  have e4 := repRegW_spec cap xOUT rOP rM rK rT nMK nMT nKT nKO [false] σc hc_K hc_T hc_O (by rw [hc_m]; omega)
    (by rw [hc_P, hc_m]; simp; omega)
  rw [hc_m] at e4
  set σd := appendO σc xOUT rOP (reps m [false]) with hσd
  have hd_O : σd.sh xOUT = (σd.st xOUT).length := by simp [hσd, hc_O]
  have hd_P : σd.val rOP = 2 + m + m := by simp [hσd, hc_P, reps_single]
  -- 5
  have e5 := emitW_spec cap xOUT rOP [true] σd hd_O (by rw [hd_P]; simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by simp)
  rw [hσd, hσc, hσb, hσa, appendO_append, appendO_append, appendO_append, appendO_append]
  simp only [srcWord, List.append_assoc]

end Spec

/-! ## The whole program from the filled state -/

/-- The register-language state after the fill: registers `0` at capacity `2W + 2`, the request, the fill count and
the marker tape on their streams, every head at `0`. -/
def σN (w : List Bool) (W : ℕ) : WState NS NR :=
  ⟨fun _ => 0, fun s => if s = xIN then RepairOrdinary.frame w else if s = xCT then List.replicate W true
    else if s = xAUX then List.replicate (2 * W + 3) false else [], fun _ => 0, false⟩

/-- The program's cost bound. -/
def numsCost (n cr : ℕ) : ℕ :=
  (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + StarNums.starCost n cr 0 + 300 * n + 600

/-- The exponent of the dimension: `m = 2·kh + L`. -/
def mOf (P : Shared.StarParams) : ℕ := 2 * (P.s * (P.r / 2)) + Nat.clog 2 (P.n + 2)

theorem rs_le (P : Shared.StarParams) : P.r * P.s ≤ P.n := by
  have h2s : 2 ^ P.s ≤ P.n / P.r + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  have hslt : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  have hrq : P.r * (P.n / P.r) ≤ P.n := Nat.mul_div_le P.n P.r
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) hrq

theorem kh2_le (P : Shared.StarParams) : 2 * (P.s * (P.r / 2)) ≤ P.n := by
  obtain ⟨q, hq⟩ := P.r_even
  have h1 : P.r / 2 = q := by omega
  have h2 := rs_le P
  rw [h1]
  rw [hq] at h2
  nlinarith

theorem clog_le (n : ℕ) : Nat.clog 2 (n + 2) ≤ n + 2 := by
  rw [StarNums.clog_two_add_two]
  have := CopyNat.natBitLength_le_self_succ (n + 1)
  omega

theorem mOf_le (P : Shared.StarParams) : mOf P ≤ 2 * P.n + 2 := by
  have := kh2_le P
  have := clog_le P.n
  unfold mOf
  omega

theorem frame_split (x sfx : List Bool) :
    RepairOrdinary.frame (x ++ sfx) = [] ++ ParseNat.enc true x ++ (marks sfx ++ [false]) := by
  have h1 := RepairOrdinary.Streaming.frame_append x sfx
  have h2 := RepairOrdinary.Streaming.frame_append sfx []
  simp only [List.append_nil] at h2
  have h3 : RepairOrdinary.frame ([] : List Bool) = [false] := rfl
  rw [h3] at h2
  rw [h1, h2]
  simp [ParseNat.enc]

theorem starOut_hi (σ : WState NS NR) (P : Shared.StarParams) (fe : ℕ) (r : Fin NR) (hr : 20 ≤ r.val) :
    (StarNums.starOut σ SN P fe).val r = σ.val r := by
  have h : ∀ i, r ≠ SN i := fun i e => SN_ne i r hr e.symm
  simp [StarNums.starOut, Function.update_apply, h]

/-- **The program's run**: from the filled state, the output stream holds the source of `2^(mOf P)`; the request and
the fill count stay. -/
theorem numsW_spec (cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 16 ≤ W) :
    ∃ σF c, WExec (2 * W + 2) (numsW cr) (σN w W) σF c ∧ σF.st xOUT = srcWord (mOf P) ∧
      σF.st xIN = RepairOrdinary.frame w ∧ σF.st xCT = List.replicate W true ∧ c ≤ numsCost P.n cr := by
  set cap := 2 * W + 2 with hcap
  have hpow := CopyNat.two_pow_natBitLength_le P.n
  have hkh := kh2_le P
  have hL := clog_le P.n
  have hmo := mOf_le P
  -- 1: `n` into `SN 0`
  have r1 := readNatM_spec cap true xIN rF rC (SN 0) rP rT (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) P.n [] (marks sfx ++ [false]) (σN w W)
    (by simp only [σN, if_pos rfl]; rw [hw]; exact frame_split _ _) (by rfl) rfl rfl rfl rfl
    (by simp only [σN]; rw [pow_succ]; omega)
  set σ1 := ((σN w W).seth xIN (([] : List Bool).length + stp true * (RepairRepresentation.natWord P.n).length)).setv
    (SN 0) ((σN w W).val (SN 0) + P.n) with hσ1
  have v1 : ∀ r : Fin NR, r ≠ SN 0 → σ1.val r = 0 := by
    intro r hr
    simp [hσ1, Function.update_apply, hr, σN]
  have v10 : σ1.val (SN 0) = P.n := by simp [hσ1, σN]
  -- 2: the star numbers
  have r2 := StarNums.starNums_spec cap cr 0 SN P hrP σ1 v10
    (fun i hi => v1 _ (fun e => hi (SN.injective e))) (by omega)
  set σ2 := StarNums.starOut σ1 SN P 0 with hσ2
  obtain ⟨o1, -, -, -, -, -, o8, -, -⟩ := StarNums.starOut_val σ1 SN P 0
  -- 3: `m`
  have r3 := mW_spec cap σ2 (P.s * (P.r / 2)) (Nat.clog 2 (P.n + 2)) o8 o1
    (by rw [hσ2, starOut_hi _ _ _ _ (by decide)]; exact v1 _ (SN_ne 0 rM (by decide)).symm)
    (by rw [hσ2, starOut_hi _ _ _ _ (by decide)]; exact v1 _ (SN_ne 0 rT (by decide)).symm) (by omega)
  set σ3 := σ2.setv rM (2 * (P.s * (P.r / 2)) + Nat.clog 2 (P.n + 2)) with hσ3
  have v3 : ∀ r : Fin NR, 20 ≤ r.val → r ≠ rM → σ3.val r = 0 := by
    intro r hr hrm
    rw [hσ3]
    simp only [WState.setv_val, Function.update_apply, if_neg hrm]
    rw [hσ2, starOut_hi _ _ _ _ hr]
    exact v1 _ (fun e => by rw [e, SN_val] at hr; simp at hr)
  -- 4: the source
  have r4 := srcW_spec cap σ3 (mOf P) (by simp [hσ3, mOf]) (v3 rK (by decide) (by decide))
    (v3 rT (by decide) (by decide)) (by simp [hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN, xCT, xAUX])
    (by simp [hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN]) (v3 rOP (by decide) (by decide)) (by omega)
  refine ⟨_, _, WExec.seq r1 (WExec.seq r2 (WExec.seq r3 r4)), ?_, ?_, ?_, ?_⟩
  · simp [hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN, xCT, xAUX]
  · simp [hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN, Function.update_apply]
  · simp [hσ3, hσ2, StarNums.starOut, hσ1, σN, xOUT, xIN, xCT, Function.update_apply]
  · unfold numsCost
    have e1 : 18 * (P.s * (P.r / 2)) + 3 + 1 + (18 * (P.s * (P.r / 2)) + 3 + 1 + (18 * Nat.clog 2 (P.n + 2) + 3)) ≤
        18 * P.n + 18 * (P.n + 2) + 11 := by omega
    have e2 : 8 + 1 + (18 * mOf P + 3 + 1 + (mOf P * 12 + 1) + 1 + (8 + 1 + (18 * mOf P + 3 + 1 + (mOf P * 12 + 1) +
        1 + 8))) ≤ 60 * (2 * P.n + 2) + 38 := by omega
    omega

/-! ## The stage as one run -/

/-- The register tapes (the fill's targets). -/
def regSelX (j : Fin (NS + 2 + NR)) : Bool := decide (NS + 2 ≤ j.val)

/-- The stage's entry bank: the framed request and `1^W`, everything else blank. -/
def rawInX (w : List Bool) (W : ℕ) : Fin (NS + 2 + NR) → List Bool := fun j =>
  if j = sTape xIN then RepairOrdinary.frame w else if j = sTape xCT then List.replicate W true else []

/-- The fill and the cell. -/
def fillX : Prog (NS + 2 + NR) :=
  .seq (UnionMachine.FrontFill.fillP (sTape xCT) (sTape xAUX) regSelX) (.act (writeAt cTape false) (fun _ => .stay))

theorem sTape_valX (s : Fin (NS + 1)) : (sTape (nr := NR) s).val = if s.val = 0 then 0 else s.val + 1 := rfl

theorem sTape_eq_iffX (a b : Fin (NS + 1)) : sTape (nr := NR) a = sTape b ↔ a = b :=
  ⟨fun h => sTape_inj h, fun h => h ▸ rfl⟩

theorem regSelX_s (s : Fin (NS + 1)) : regSelX (sTape (nr := NR) s) = false := by
  have := s.isLt
  simp only [regSelX, sTape_valX, decide_eq_false_iff_not, not_le]
  split <;> omega

theorem regSelX_c : regSelX (cTape (ns := NS) (nr := NR)) = false := by
  unfold regSelX
  rw [show (cTape (ns := NS) (nr := NR)).val = 1 from rfl]
  decide

theorem regSelX_r (r : Fin NR) : regSelX (rTape (ns := NS) r) = true := by simp [regSelX, rTape]

theorem rawInX_c (w : List Bool) (W : ℕ) : rawInX w W cTape = [] := by
  simp [rawInX, fun s => (sTape_ne_c (nr := NR) (ns := NS) s).symm]

theorem rawInX_r (w : List Bool) (W : ℕ) (r : Fin NR) : rawInX w W (rTape r) = [] := by
  simp [rawInX, fun s => (sTape_ne_r (nr := NR) (ns := NS) s r).symm]

theorem rawInX_s (w : List Bool) (W : ℕ) (s : Fin (NS + 1)) : rawInX w W (sTape s) =
    if s = xIN then RepairOrdinary.frame w else if s = xCT then List.replicate W true else [] := by
  simp only [rawInX, sTape_eq_iffX]

/-- **The fill and the cell**: from the entry bank to the register-language state `σN` at capacity `2W + 2`. -/
theorem fillX_exec (w : List Bool) (W : ℕ) :
    Exec fillX ⟨fun _ => 0, rawInX w W⟩ (wenc (2 * W + 2) (σN w W)) (11 * W + 20 + 1 + 1) := by
  have hca : sTape (nr := NR) xCT ≠ sTape xAUX := fun h => absurd (sTape_inj h) (by decide)
  have hA : ∀ i, UnionMachine.FrontFill.side (sTape (nr := NR) xAUX) regSelX i → rawInX w W i = [] := by
    intro i hi
    rcases hi with hi | hi
    · rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [regSelX_s] at hi; exact absurd hi (by decide)
      · rw [regSelX_c] at hi; exact absurd hi (by decide)
      · exact rawInX_r w W r
    · subst hi
      rw [rawInX_s]
      simp [xIN, xCT, xAUX]
  have e1 := UnionMachine.FrontFill.fillP_exec (sTape xCT) (sTape xAUX) regSelX (fun _ => 0) (rawInX w W) hca
    (regSelX_s _) (regSelX_s _) W (by rw [rawInX_s]; simp [xIN, xCT]) (fun _ _ => rfl) hA
  have e2 := Exec.act (UnionMachine.FrontFill.stB (sTape xCT) (sTape xAUX) regSelX (fun _ => 0) (rawInX w W) W 0)
    (writeAt (cTape (ns := NS) (nr := NR)) false) (fun _ => .stay)
  have eB : (UnionMachine.FrontFill.stB (sTape xCT) (sTape xAUX) regSelX (fun _ => 0) (rawInX w W) W 0).act
      (writeAt (cTape (ns := NS) (nr := NR)) false) (fun _ => .stay) = wenc (2 * W + 2) (σN w W) := by
    apply Bank.ext'
    · intro j
      simp only [Bank.act, HeadMove.apply, UnionMachine.FrontFill.stB]
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_H_s]
        split_ifs <;> simp [σN] <;> omega
      · rw [wenc_H_c]
        split_ifs <;> omega
      · rw [wenc_H_r]
        split_ifs <;> simp [σN] <;> omega
    · intro j
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_A_s]
        simp only [Bank.act, writeAt, sTape_ne_c, if_false, UnionMachine.FrontFill.stB, regSelX_s, Bool.false_eq_true,
          sTape_eq_iffX, rawInX_s, σN]
        by_cases hx : s = xAUX
        · subst hx; simp [xIN, xCT, xAUX]
        · simp [hx]
      · rw [wenc_A_c]
        simp only [Bank.act, writeAt, if_true, UnionMachine.FrontFill.stB, regSelX_c, Bool.false_eq_true, if_false,
          fun s => (sTape_ne_c (nr := NR) (ns := NS) s).symm, rawInX_c]
        simp [σN, UnionMachine.FrontFill.side, regSelX_c, fun s => (sTape_ne_c (nr := NR) (ns := NS) s).symm]
        rfl
      · rw [wenc_A_r]
        simp only [Bank.act, writeAt, cTape_ne_r, (cTape_ne_r _).symm, if_false, UnionMachine.FrontFill.stB,
          regSelX_r, if_true, σN]
        rw [regTape_zero]
  rw [← eB]
  exact Exec.seq e1 e2

/-- The stage before its teardown: the fill, then the program. -/
noncomputable def numsP (cr : ℕ) := Composition.machine fillX.compile (numsW cr).toProg.compile

/-- **The dimension stage** (every head back at `0`). -/
noncomputable def numsM (cr : ℕ) := MaskedReset.machine (numsP cr) (fun _ => true)

/-- The stage's cost before the teardown. -/
def numsStageCost (n cr W : ℕ) : ℕ := 11 * W + 20 + 1 + 1 + 1 + numsCost n cr

/-- **The dimension stage's run**: from `frame w` (`w = natWord n ++ sfx`) and `1^W`, every head back at `0`, the
output stream holds the CapReader source `srcWord (mOf P)` of `2^(2·kh + L)`; the request and the fill count stay. -/
theorem nums_step (cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 16 ≤ W) :
    ∃ (tout : Fin (NS + 2 + NR) → List Bool) (m : ℕ),
      Step (numsM cr) (2 * numsStageCost P.n cr W + 2) (fun _ => 0)
        (Fin.addCases (rawInX w W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => 0)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape xOUT) = srcWord (mOf P) ∧ tout (sTape xIN) = RepairOrdinary.frame w ∧
      tout (sTape xCT) = List.replicate W true := by
  have s0 := Exec.step (fillX_exec w W)
  obtain ⟨σF, c, hx, o, i, ct, hc⟩ := numsW_spec cr W P hrP sfx w hw hW
  have s1 := Exec.step (WExec.exec (2 * W + 2) hx)
  have core : Step (numsP cr) (numsStageCost P.n cr W) (fun _ => 0) (rawInX w W) (wenc (2 * W + 2) σF).H
      (wenc (2 * W + 2) σF).A := (s0.seq s1).enlarge (by unfold numsStageCost; omega)
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (NS + 2 + NR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc (2 * W + 2) σF).H i)
      (fun _ : Fin 1 => 0) : Fin (NS + 2 + NR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  refine ⟨(wenc (2 * W + 2) σF).A, m, (hm.congr_in eh rfl).congr eh' rfl, ?_, ?_, ?_⟩
  · rw [wenc_A_s, o]
  · rw [wenc_A_s, i]
  · rw [wenc_A_s, ct]

end NearCubicWires.WireExponent3_5.PrimAsm.NumsX
