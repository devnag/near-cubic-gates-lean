import Proof.Gates.Expand.PolyTabStage9f

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc enc_length stp)
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

theorem encT_length (w : List Bool) : (enc true w).length = 2 * w.length := by simp [enc_length, stp]

/-- The registers of the phase at rest. -/
structure FZ (f : Fin 64 → ℕ) (K : ℕ) : Prop where
  z0 : f 0 = 0
  z1 : f 1 = 0
  z9 : f 9 = 0
  z29 : f 29 = 0
  z28 : f 28 = 0
  z30 : f 30 = 0
  z35 : f 35 = 0
  z3 : f 3 = 0
  z4 : f 4 = 0
  z6 : f 6 = 0
  z7 : f 7 = 0
  z31 : f 31 = 0
  z36 : f 36 = 0
  z5 : f 5 = 0
  k27 : f 27 = K

def mA : WX :=
  .seq (readBin U2 RB 1 2) <| .seq (appendRecX (U2 1) (sZ 46) (rX 29) (rX 37)) <|
  .seq (toReg (U2 1) (U2 8) (U2 9) (rX 31) (rX 3) (rX 4) (rX 6)) <| .seq (addR (rX 31) (rX 36) (rX 7)) varLoop

def mB : WX := .seq (closeOutX (sS 5) (rX 34)) revLoop

def mC : WX :=
  .seq (readBin U2 RB 1 2) <| .seq (toReg (U2 1) (U2 8) (U2 9) (rX 5) (rX 3) (rX 4) (rX 6)) <|
  .seq (readBin U3 RB 1 2) <| .seq enc3 (appendRecX (U3 1) (sZ 56) (rX 29) (rX 38))

def monoBody : WX := .seq mA (.seq mB mC)

def mACost (Wb ℓ M : ℕ) : ℕ :=
  readBinCost Wb ℓ + 1 + (40 * Wb + 11 + 1 + ((M * (83 * Wb + 30) + 41 * Wb + 14) + 1 + ((18 * M + 3) + 1 +
    (M * (vCost Wb ℓ + 4) + 1))))

def mBCost (Wb M X K Y : ℕ) : ℕ := (5 * (M * (2 * Wb + 1)) + 3) + 1 + (M * (revCost Wb M X K Y + 4) + 1)

def mCCost (Wb Wc ℓ : ℕ) : ℕ :=
  readBinCost Wb ℓ + 1 + ((1 * (83 * Wb + 30) + 41 * Wb + 14) + 1 + (readBinCost Wc ℓ + 1 +
    ((41 * Wc + 8 + 1 + (41 * Wc + 7 + 1 + 1 + (3 * 1 + 1))) + 1 + (40 * Wc + 11))))

def mnCost (Wb Wc ℓ M X K Y : ℕ) : ℕ := mACost Wb ℓ M + 1 + (mBCost Wb M X K Y + 1 + mCCost Wb Wc ℓ)

theorem revCost_mono (Wb X K Y : ℕ) {N N' : ℕ} (h : N ≤ N') : revCost Wb N X K Y ≤ revCost Wb N' X K Y := by
  have a1 := Nat.mul_le_mul_right (40 * Wb + 40) h
  have a2 := Nat.mul_le_mul_right (2 * Wb + 1) (Nat.mul_le_mul_left 10 h)
  unfold revCost; omega

section Mono
variable {Wb Wc : ℕ} {inp VT : List Bool} {σA : WState (NSx te qa) NRk} {o46 o56 L5 : List Bool}

theorem ms_addV (cap : ℕ) {hd : ℕ} {oV : List Bool} {q2 q3 : (Fin 10 → ℕ) → Prop} {f : Fin 64 → ℕ} {τ : WSt}
    (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (a b : Fin 64) (ha : XR a) (hb : XR b) (hab : a ≠ b)
    (ha7 : a ≠ 7) (hb7 : b ≠ 7) (x y : ℕ) (hx : f a = x) (hy : f b = y) (h7 : f 7 = 0) (hcap : y + x ≤ cap) :
    Runs cap (addR (rX a) (rX b) (rX 7)) τ (18 * x + 3)
      (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f b (y + x)) q2 q3) := by
  have := ms_add cap h a b ha hb hab ha7 hb7 h7 (by rw [hx, hy]; exact hcap)
  rw [hx, hy] at this; exact this

theorem monoA_spec (cap : ℕ) (hW : 1 ≤ Wb) (xs : List ℕ) (pre B : List Bool) (ℓ M K : ℕ)
    (hinp : inp = pre ++ enc true (natWord xs.length) ++ encN xs ++ B) (f : Fin 64 → ℕ) (hf : FZ f K)
    (q2 q3 : (Fin 10 → ℕ) → Prop) (τ : WSt) (h : MS Wb Wc inp VT σA pre.length o46 o56 [] L5 f q2 q3 τ)
    (hM : xs.length ≤ M) (hmW : xs.length < 2 ^ Wb) (hlt : ∀ x ∈ xs, x < 2 ^ Wb) (hℓm : natBitLength xs.length ≤ ℓ)
    (hℓ : ∀ x ∈ xs, natBitLength x ≤ ℓ) (hcap : ℓ + 2 * Wb + 2 * M + 2 ≤ cap)
    (hcapV : (M + 1) * (2 * Wb + 1) + 2 ≤ cap) (hcap46 : o46.length + 2 * Wb + 2 ≤ cap) :
    Runs cap mA τ (mACost Wb ℓ M)
      (MS Wb Wc inp VT σA (pre.length + 2 * (natWord xs.length).length + (encN xs).length)
        (o46 ++ frame (binary Wb xs.length)) o56 (vrecs Wb xs) L5 (Function.update f 31 xs.length) (fun _ => True)
        q3) := by
  have hinp1 : inp = pre ++ enc true (natWord xs.length) ++ (encN xs ++ B) := by rw [hinp]; simp [List.append_assoc]
  obtain ⟨τ1, e1, m1⟩ := ms_read2 cap hW pre.length q2 q3 τ h xs.length pre _ hinp1 rfl (by omega) (by omega)
  rw [Nat.mod_eq_of_lt hmW] at m1
  obtain ⟨τ2, e2, m2⟩ := ms_app46 cap _ q3 xs.length τ1 m1 hf.z29 hcap46
  obtain ⟨τ3, e3, m3⟩ := ms_toReg2 cap _ q3 xs.length 31 (by decide) (by decide) τ2 m2 hf.z3 hf.z4 hf.z6 hmW (by omega)
    (by rw [hf.z31]; omega)
  obtain ⟨τ4, e4, m4⟩ := ms_addV cap m3 31 36 (by decide) (by decide) (by decide) (by decide) (by decide) xs.length 0
    (by simp [hf.z31]) (by simp [hf.z36]) (by simp [hf.z7]) (by omega)
  have eA : (pre ++ enc true (natWord xs.length)).length = pre.length + 2 * (natWord xs.length).length := by
    rw [List.length_append, encT_length]
  rw [← eA] at m4
  obtain ⟨τ5, e5, m5⟩ := varLoop_spec cap hW xs (pre ++ enc true (natWord xs.length)) B ℓ hinp _ _ τ4 m4 (by simp)
    (by simp [hf.z29]) hlt hℓ (by omega) (by omega) (by nlinarith)
  refine ⟨τ5, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))) ?_, ?_⟩
  · have a1 := readBinCost_mono Wb hℓm
    have a2 := Nat.mul_le_mul_right (83 * Wb + 30) hM
    have a3 := Nat.mul_le_mul_right (vCost Wb ℓ + 4) hM
    rw [hf.z31, Nat.zero_add] at *
    unfold mACost; omega
  · rw [eA] at m5
    refine m5.congr fun j _ => ?_
    by_cases j36 : j = 36
    · subst j36; simp [hf.z36]
    · by_cases j31 : j = 31
      · subst j31; simp [hf.z31]
      · simp only [Function.update_of_ne j36, Function.update_of_ne j31]

theorem monoB_spec (cap : ℕ) (hW : 1 ≤ Wb) (hd : ℕ) (xs ys : List ℕ) (K X M : ℕ) (f : Fin 64 → ℕ) (hf : FZ f K)
    (q2 q3 : (Fin 10 → ℕ) → Prop) (τ : WSt)
    (h : MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd o46 o56 (vrecs Wb xs) L5
      (Function.update f 31 xs.length) q2 q3 τ)
    (hM : xs.length ≤ M) (hys : ∀ x ∈ xs, x * K + K ≤ ys.length) (hX : ∀ x ∈ xs, x ≤ X) (hlt : ∀ x ∈ xs, x < 2 ^ Wb)
    (hcap : (M + 1) * (2 * Wb + 1) + 2 * M + (ys.length + 1) * (2 * Wb + 1) + 2 * ys.length +
      2 * Wb + X * K + 2 * X + 2 * K + 2 ≤ cap)
    (hcapO : o46.length + M * (K * (2 * Wb + 1)) + 1 ≤ cap) :
    Runs cap mB τ (mBCost Wb M X K ys.length)
      (MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd (o46 ++ revOut Wb K ys xs xs.length) o56 []
        (overlay (vrecs Wb xs ++ [false]) L5) f q2 q3) := by
  have hl := vrecs_length Wb xs
  have hMc : xs.length * (2 * Wb + 1) ≤ M * (2 * Wb + 1) := Nat.mul_le_mul_right _ hM
  obtain ⟨τ1, e1, m1⟩ := ms_closeV cap hd q2 q3 τ h (by rw [hl]; nlinarith)
  have eL : overlay (vrecs Wb xs ++ [false]) L5 = recStream (xs.map (binary Wb)) ++
      L5.drop (vrecs Wb xs ++ [false]).length := by rw [← vrecs_rec]; rfl
  rw [eL] at m1
  have hMO : xs.length * (K * (2 * Wb + 1)) ≤ M * (K * (2 * Wb + 1)) := Nat.mul_le_mul_right _ hM
  obtain ⟨τ2, e2, m2⟩ := revLoop_spec cap hW xs ys _ K X _ q2 τ1 m1 (by simp) (by simp [hf.z0]) (by simp [hf.z1])
    (by simp [hf.z9]) (by simp [hf.z29]) (by simp [hf.z28]) (by simp [hf.z30]) (by simp [hf.z35]) (by simp [hf.z3])
    (by simp [hf.z4]) (by simp [hf.z6]) (by simp [hf.z7]) (by simp [hf.k27]) hys hX hlt
    (by have : (xs.length + 1) * (2 * Wb + 1) ≤ (M + 1) * (2 * Wb + 1) := Nat.mul_le_mul_right _ (by omega)
        omega) (by omega)
  refine ⟨τ2, WXExec.mono (WXExec.seq e1 e2) ?_, ?_⟩
  · have a1 := revCost_mono Wb X K ys.length hM
    have a2 := Nat.mul_le_mul_right (revCost Wb xs.length X K ys.length + 4) hM
    have a3 := Nat.mul_le_mul_right (revCost Wb M X K ys.length + 4) (le_refl M)
    have a4 : M * (revCost Wb xs.length X K ys.length + 4) ≤ M * (revCost Wb M X K ys.length + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [hl]; unfold mBCost; omega
  · rw [eL]
    refine m2.congr fun j _ => ?_
    by_cases j31 : j = 31
    · subst j31; simp [hf.z31]
    · simp only [Function.update_of_ne j31]

theorem monoC_spec (cap : ℕ) (hW : 1 ≤ Wb) (hWc : 1 ≤ Wc) (A B : List Bool) (sg mag ℓ : ℕ) (hsg : sg ≤ 1)
    (hmag : 2 * mag + 1 < 2 ^ Wc) (hinp : inp = A ++ enc true (natWord sg) ++ enc true (natWord mag) ++ B)
    (f : Fin 64 → ℕ) (hf5 : f 5 = 0) (hf3 : f 3 = 0) (hf4 : f 4 = 0) (hf6 : f 6 = 0) (hf29 : f 29 = 0)
    (q2 q3 : (Fin 10 → ℕ) → Prop) (τ : WSt) (oV : List Bool) (h : MS Wb Wc inp VT σA A.length o46 o56 oV L5 f q2 q3 τ)
    (hℓs : natBitLength sg ≤ ℓ) (hℓm : natBitLength mag ≤ ℓ) (hcap : ℓ + 2 * Wb + 2 * Wc + 4 ≤ cap)
    (hcap56 : o56.length + 2 * Wc + 2 ≤ cap) :
    Runs cap mC τ (mCCost Wb Wc ℓ)
      (MS Wb Wc inp VT σA (A.length + 2 * (natWord sg).length + 2 * (natWord mag).length) o46
        (o56 ++ frame (binary Wc (2 * mag + sg))) oV L5 f (fun _ => True) (fun _ => True)) := by
  have hsgW : sg < 2 ^ Wb := lt_of_le_of_lt hsg (Nat.one_lt_two_pow (by omega))
  have hmW : mag < 2 ^ Wc := by omega
  have hinp1 : inp = A ++ enc true (natWord sg) ++ (enc true (natWord mag) ++ B) := by
    rw [hinp]; simp [List.append_assoc]
  obtain ⟨τ1, e1, m1⟩ := ms_read2 cap hW A.length q2 q3 τ h sg A _ hinp1 rfl (by omega) (by omega)
  rw [Nat.mod_eq_of_lt hsgW] at m1
  obtain ⟨τ2, e2, m2⟩ := ms_toReg2 cap _ q3 sg 5 (by decide) (by decide) τ1 m1 hf3 hf4 hf6 hsgW (by omega)
    (by rw [hf5]; omega)
  have eA : (A ++ enc true (natWord sg)).length = A.length + 2 * (natWord sg).length := by
    rw [List.length_append, encT_length]
  rw [← eA] at m2
  obtain ⟨τ3, e3, m3⟩ := ms_read3 cap hWc _ _ q3 τ2 m2 mag (A ++ enc true (natWord sg)) B hinp rfl (by omega)
    (by omega)
  rw [Nat.mod_eq_of_lt hmW] at m3
  obtain ⟨τ4, e4, m4⟩ := ms_enc3 cap mag sg hsg hmag τ3 m3 (by simp [hf5]) (by omega)
  obtain ⟨τ5, e5, m5⟩ := ms_app56 cap _ _ (2 * mag + sg) τ4 m4 (by simp [hf29]) hcap56
  refine ⟨τ5, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))) ?_, ?_⟩
  · have a1 := readBinCost_mono Wb hℓs
    have a2 := readBinCost_mono Wc hℓm
    have a3 := Nat.mul_le_mul_right (83 * Wb + 30) hsg
    unfold mCCost; omega
  · rw [eA] at m5
    refine ((m5.withQ2 (fun _ _ => trivial)).withQ3 (fun _ _ => trivial)).congr fun j _ => ?_
    by_cases j5 : j = 5
    · subst j5; simp [hf5]
    · simp only [Function.update_of_ne j5]

end Mono

end NearCubicGates.Close.Expand.PolyTab
