import Proof.Gates.Cells.Setup
import Proof.Gates.Cells.OutLen

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq

variable {V M t : ℕ}

/-- The encoded initial state: entry word on `IN`, zero words on `Z`, `TP` and the variables, empty stores, the
log and the ruler; every head and register `0`. -/
def initSt (W Lk Bk : ℕ) (inp : List Bool) : WState (NS M t V) (NR M) :=
  ⟨fun _ => 0, fun i =>
    if i.val = 0 then frame inp
    else if i.val = 2 ∨ i.val = 7 ∨ 8 + 2 * M + t ≤ i.val then frame (binary W 0)
    else if 8 ≤ i.val ∧ i.val < 8 + M then [false]
    else if i.val = 5 then List.replicate Bk false
    else if i.val = 6 then List.replicate (2 * Lk + Bk + 3) true
    else [], fun _ => 0, false⟩

/-- The initial language state. -/
def a0 : DS V M := ⟨fun _ => 0, 0, [], fun _ => [], fun _ => 0, [], [], 0⟩

theorem rdEq_nil_false : RdEq [] [false] := by
  intro p; unfold readTapeBit; cases p <;> simp

theorem initSt_enc (C : Ctx) :
    Enc C (a0 : DS V M) (initSt (t := TS C) C.Wd C.Lk C.Bk C.inp) := by
  refine ⟨?_, rfl, rfl, ?_, rfl, rfl, ⟨?_, rfl⟩, fun x => ⟨?_, rfl⟩, fun m => ?_, fun m => ?_, fun m => ?_,
    fun m => ?_, fun m => rfl, ⟨0, ?_⟩, rfl, ?_, rfl, rfl, ?_, rfl, rfl, fun j => ?_, fun j => rfl, ?_, rfl, ?_, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [initSt, sIN]
  · simp [initSt, sOUT, a0]; intro h; omega
  · simp [initSt, sZ]
  · simp only [initSt, vs_val, a0]
    rw [if_neg (by omega), if_pos (by omega)]
  · have := m.isLt
    simp only [initSt, sM_val, a0]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    simp [encR, enc]
  · simp [initSt, a0]
  · simp [initSt, a0]
  · have := m.isLt
    simp only [initSt, sS_val, sM_val]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · simp [initSt, sTP]
  · simp only [initSt, sKI_val, a0]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact rdEq_nil_false
  · simp only [initSt, sKO_val, a0]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact RdEq.refl _
  · simp only [initSt, sT_val]
    have := j.isLt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact RdEq.refl _
  · simp [initSt, sLG]; intro h; omega
  · simp [initSt, sRU, Rk]; intro h; omega

theorem a0_valid (C : Ctx) : Valid C (a0 : DS V M) :=
  ⟨fun _ => Nat.two_pow_pos _, by simp [a0], fun _ v hv => by simp [a0] at hv, fun _ => by simp [a0],
    by simp [a0], by simp [a0], by simp [a0]⟩

/-! ## The set-up program -/

/-- The size constants: `Wd = 2^{c₁L}·a₁`, `Lk = 2^{c₂L}·a₂`, `Bk = 2^{c₃L}·a₃` (`L` = leading ones of the entry). -/
structure Sz where
  a1 : ℕ
  c1 : ℕ
  a2 : ℕ
  c2 : ℕ
  a3 : ℕ
  c3 : ℕ

def Sz.W (z : Sz) (L : ℕ) : ℕ := 2 ^ (z.c1 * L) * z.a1
def Sz.Lk (z : Sz) (L : ℕ) : ℕ := 2 ^ (z.c2 * L) * z.a2
def Sz.Bk (z : Sz) (L : ℕ) : ℕ := 2 ^ (z.c3 * L) * z.a3

/-- The zero-word streams: `Z`, `TP`, the variables. -/
def numStreams : List (Fin (NS M t V + 1)) := sZ :: sTP :: (List.finRange V).map vs

/-- The store streams. -/
def storeStreams : List (Fin (NS M t V + 1)) := (List.finRange M).map sM

theorem mem_numStreams (i : Fin (NS M t V + 1)) :
    i ∈ (numStreams : List (Fin (NS M t V + 1))) ↔ i.val = 2 ∨ i.val = 7 ∨ 8 + 2 * M + t ≤ i.val := by
  simp only [numStreams, List.mem_cons, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro (rfl | rfl | ⟨x, rfl⟩)
    · simp
    · simp
    · simp
  · intro h
    rcases h with h | h | h
    · left; ext; simp [h]
    · right; left; ext; simp [h]
    · right; right
      have := i.isLt; unfold NS at this
      exact ⟨⟨i.val - (8 + 2 * M + t), by omega⟩, by ext; simp; omega⟩

theorem mem_storeStreams (i : Fin (NS M t V + 1)) :
    i ∈ (storeStreams : List (Fin (NS M t V + 1))) ↔ 8 ≤ i.val ∧ i.val < 8 + M := by
  simp only [storeStreams, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨m, rfl⟩; simp
  · intro h; exact ⟨⟨i.val - 8, by omega⟩, by ext; simp; omega⟩

theorem numStreams_nodup : (numStreams : List (Fin (NS M t V + 1))).Nodup := by
  simp only [numStreams, List.nodup_cons, List.mem_cons, List.mem_map, List.mem_finRange, true_and, not_or]
  refine ⟨⟨by lay_ne, fun ⟨x, h⟩ => by revert h; lay_ne⟩, fun ⟨x, h⟩ => by revert h; lay_ne, ?_⟩
  exact List.Nodup.map (fun x y h => by ext; have := congrArg Fin.val h; simp at this; omega) (List.nodup_finRange V)

theorem storeStreams_nodup : (storeStreams : List (Fin (NS M t V + 1))).Nodup :=
  List.Nodup.map (fun x y h => by ext; have := congrArg Fin.val h; simp at this; omega) (List.nodup_finRange M)

variable (K : Callee)

/-- Set-up phase A: the sizes in registers (`L`, `Wd`, `Lk`, `Bk`, `Rk = 2Lk + Bk + 3`). -/
def setupA (z : Sz) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (countOnes sIN rG rC2)
  (.seq (incN rK z.a1) (.seq (pw2 rK rIP rOP rG rC2 z.c1)
  (.seq (incN rT z.a2) (.seq (pw2 rT rIP rOP rG rC2 z.c2)
  (.seq (incN rC1 z.a3) (.seq (pw2 rC1 rIP rOP rG rC2 z.c3)
  (.seq (addR rT rR rOP) (.seq (addR rT rR rOP) (.seq (addR rC1 rR rOP) (incN rR 3))))))))))

/-- Set-up phase B: the zero words, the empty stores, the log and the ruler. -/
def setupB : WMX (NS M (TSK K) V) (NR M) :=
  .seq (forStreams (initNum rK rC2) numStreams)
  (.seq (forStreams (fun X => WMX.wr X false) storeStreams)
  (.seq (fillB rC1 rC2 sLG false) (fillB rR rC2 sRU true)))

/-- Set-up phase C: the registers back to `0`. -/
def setupC : WMX (NS M (TSK K) V) (NR M) :=
  .seq (clearR rG) (.seq (clearR rK) (.seq (clearR rT) (.seq (clearR rC1) (clearR rR))))

/-- **The set-up.** -/
def setupP (z : Sz) : WMX (NS M (TSK K) V) (NR M) := .seq (setupA K z) (.seq (setupB K) (setupC K))

/-- The size registers after phase A. -/
def regsOf (L W Lk Bk : ℕ) (r : Fin (NR M)) : ℕ :=
  if r = rR then Lk + Lk + Bk + 3 else if r = rC1 then Bk else if r = rT then Lk else if r = rK then W else
    if r = rG then L else 0

/-- The state after phase A. -/
def stA (L W Lk Bk : ℕ) (inp : List Bool) : WState (NS M t V) (NR M) :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame inp else [], regsOf L W Lk Bk, false⟩

/-- The state after phase B. -/
def stB (L W Lk Bk : ℕ) (inp : List Bool) : WState (NS M t V) (NR M) :=
  ⟨fun _ => 0, (initSt (M := M) (t := t) (V := V) W Lk Bk inp).st, regsOf L W Lk Bk, false⟩

def costA (z : Sz) (L : ℕ) : ℕ :=
  (30 * L + 20) + 4 * z.a1 + (L * (60 * z.W L + 11 * z.c1 + 8) + 7 * L + 3) +
  4 * z.a2 + (L * (60 * z.Lk L + 11 * z.c2 + 8) + 7 * L + 3) +
  4 * z.a3 + (L * (60 * z.Bk L + 11 * z.c3 + 8) + 7 * L + 3) +
  (18 * z.Lk L + 3) + (18 * z.Lk L + 3) + (18 * z.Bk L + 3) + 4 * 3 + 10

theorem setupA_spec (z : Sz) (inp : List Bool) (cap : ℕ)
    (hcap : 2 * inp.length + 4 * (z.W (leadOnes inp) + z.Lk (leadOnes inp) + z.Bk (leadOnes inp)) + 4 * z.a1 +
      4 * z.a2 + 4 * z.a3 + 20 ≤ cap) :
    WXExec cap (setupA (V := V) (M := M) K z) (Interfaces.startState (NS M (TSK K) V) (NR M) inp)
      (stA (t := TSK K) (leadOnes inp) (z.W (leadOnes inp)) (z.Lk (leadOnes inp)) (z.Bk (leadOnes inp)) inp)
      (costA z (leadOnes inp)) := by
  set L := leadOnes inp with hL
  set W := z.W L with hW
  set Lk := z.Lk L with hLk
  set Bk := z.Bk L with hBk
  have hLi : L ≤ inp.length := leadOnes_le inp
  have hWa : z.a1 ≤ W := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hLa : z.a2 ≤ Lk := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hBa : z.a3 ≤ Bk := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  set σs := Interfaces.startState (NS M (TSK K) V) (NR M) inp with hσs
  have v0 : ∀ r, σs.val r = 0 := fun _ => rfl
  have st0 : ∀ i, σs.st i = if i.val = 0 then frame inp else [] := fun _ => rfl
  have sh0 : ∀ i, σs.sh i = 0 := fun _ => rfl
  -- registers
  have s1 := countOnes_spec cap (sIN : Fin (NS M (TSK K) V + 1)) (G := rG) (G2 := rC2) (by lay_ne) σs inp
    (by rw [st0]; rfl) (sh0 _) (v0 _) (v0 _) (by omega)
  rw [← hL] at s1
  set σ1 := σs.setv rG L
  have s2 := incN_spec cap rK z.a1 σ1 (by simp [σ1, v0, Fin.ext_iff]; omega)
  have e2 : σ1.val rK = 0 := by simp [σ1, v0, Fin.ext_iff]
  rw [e2, zero_add] at s2
  set σ2 := σ1.setv rK z.a1
  have s3 := pw2_spec cap (X := rK) (Y := rIP) (T := rOP) (G := rG) (G2 := rC2)
    (by simp [List.nodup_cons, Fin.ext_iff]) z.c1 σ2 (by simp [σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ2, σ1, v0, Fin.ext_iff]) (by simp [σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ2, σ1, Fin.ext_iff]; simp [Sz.W] at hW; omega) (by simp [σ2, σ1, Fin.ext_iff]; omega)
  have e3a : σ2.val rG = L := by simp [σ2, σ1, Fin.ext_iff]
  have e3b : σ2.val rK = z.a1 := by simp [σ2]
  rw [e3a, e3b, show 2 ^ (z.c1 * L) * z.a1 = W from rfl] at s3
  set σ3 := σ2.setv rK W
  have s4 := incN_spec cap rT z.a2 σ3 (by simp [σ3, σ2, σ1, v0, Fin.ext_iff]; omega)
  have e4 : σ3.val rT = 0 := by simp [σ3, σ2, σ1, v0, Fin.ext_iff]
  rw [e4, zero_add] at s4
  set σ4 := σ3.setv rT z.a2
  have s5 := pw2_spec cap (X := rT) (Y := rIP) (T := rOP) (G := rG) (G2 := rC2)
    (by simp [List.nodup_cons, Fin.ext_iff]) z.c2 σ4 (by simp [σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ4, σ3, σ2, σ1, Fin.ext_iff]; simp [Sz.Lk] at hLk; omega)
    (by simp [σ4, σ3, σ2, σ1, Fin.ext_iff]; omega)
  have e5a : σ4.val rG = L := by simp [σ4, σ3, σ2, σ1, Fin.ext_iff]
  have e5b : σ4.val rT = z.a2 := by simp [σ4]
  rw [e5a, e5b, show 2 ^ (z.c2 * L) * z.a2 = Lk from rfl] at s5
  set σ5 := σ4.setv rT Lk
  have s6 := incN_spec cap rC1 z.a3 σ5 (by simp [σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]; omega)
  have e6 : σ5.val rC1 = 0 := by simp [σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]
  rw [e6, zero_add] at s6
  set σ6 := σ5.setv rC1 z.a3
  have s7 := pw2_spec cap (X := rC1) (Y := rIP) (T := rOP) (G := rG) (G2 := rC2)
    (by simp [List.nodup_cons, Fin.ext_iff]) z.c3 σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Fin.ext_iff]; simp [Sz.Bk] at hBk; omega)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Fin.ext_iff]; omega)
  have e7a : σ6.val rG = L := by simp [σ6, σ5, σ4, σ3, σ2, σ1, Fin.ext_iff]
  have e7b : σ6.val rC1 = z.a3 := by simp [σ6]
  rw [e7a, e7b, show 2 ^ (z.c3 * L) * z.a3 = Bk from rfl] at s7
  set σ7 := σ6.setv rC1 Bk
  have s8 := addR_spec cap (ns := NS M (TSK K) V) (A := rT) (B := rR) (T := rOP) (by lay_ne) (by lay_ne) (by lay_ne) σ7
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]; omega)
  have e8a : σ7.val rR = 0 := by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]
  have e8b : σ7.val rT = Lk := by simp [σ7, σ6, σ5, Fin.ext_iff]
  rw [e8a, e8b, zero_add] at s8
  set σ8 := σ7.setv rR Lk
  have s9 := addR_spec cap (ns := NS M (TSK K) V) (A := rT) (B := rR) (T := rOP) (by lay_ne) (by lay_ne) (by lay_ne) σ8
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]) (by simp [σ8, σ7, σ6, σ5, Fin.ext_iff]; omega)
  have e9a : σ8.val rR = Lk := by simp [σ8]
  have e9b : σ8.val rT = Lk := by simp [σ8, σ7, σ6, σ5, Fin.ext_iff]
  rw [e9a, e9b] at s9
  set σ9 := σ8.setv rR (Lk + Lk)
  have s10 := addR_spec cap (ns := NS M (TSK K) V) (A := rC1) (B := rR) (T := rOP) (by lay_ne) (by lay_ne) (by lay_ne)
    σ9 (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]) (by simp [σ9, σ8, σ7, Fin.ext_iff]; omega)
  have e10a : σ9.val rR = Lk + Lk := by simp [σ9]
  have e10b : σ9.val rC1 = Bk := by simp [σ9, σ8, σ7, Fin.ext_iff]
  rw [e10a, e10b] at s10
  set σ10 := σ9.setv rR (Lk + Lk + Bk)
  have s11 := incN_spec cap rR 3 σ10 (by simp [σ10]; omega)
  have e11 : σ10.val rR = Lk + Lk + Bk := by simp [σ10]
  rw [e11] at s11
  set σ11 := σ10.setv rR (Lk + Lk + Bk + 3)
  refine WXExec.mono (WXExec.seq s1 (WXExec.seq s2 (WXExec.seq s3 (WXExec.seq s4 (WXExec.seq s5 (WXExec.seq s6
    (WXExec.seq s7 (WXExec.seq s8 (WXExec.seq s9 (WXExec.seq s10 s11))))))))) |>.cast cap ?_ le_rfl) ?_
  · refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, sh0, stA]
    · funext i; simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, st0, stA]
    · funext r
      simp only [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply, v0, stA,
        regsOf]
      split_ifs <;> simp_all
  · simp only [costA]; rw [← hW, ← hLk, ← hBk]; omega

def costB (V M W Lk Bk : ℕ) : ℕ :=
  (V + 2) * (50 * W + 10 + 1) + M * (1 + 1) + (40 * Bk + 10) + (40 * (Lk + Lk + Bk + 3) + 10) + 3

theorem regsOf_rK (L W Lk Bk : ℕ) : regsOf (M := M) L W Lk Bk rK = W := by simp [regsOf, Fin.ext_iff]
theorem regsOf_rC2 (L W Lk Bk : ℕ) : regsOf (M := M) L W Lk Bk rC2 = 0 := by simp [regsOf, Fin.ext_iff]
theorem regsOf_rC1 (L W Lk Bk : ℕ) : regsOf (M := M) L W Lk Bk rC1 = Bk := by simp [regsOf, Fin.ext_iff]
theorem regsOf_rR (L W Lk Bk : ℕ) : regsOf (M := M) L W Lk Bk rR = Lk + Lk + Bk + 3 := by simp [regsOf, Fin.ext_iff]

theorem setupB_spec (L W Lk Bk : ℕ) (inp : List Bool) (cap : ℕ) (hcap : 2 * (W + 3 * Lk + 2 * Bk + 3) + 10 ≤ cap) :
    WXExec cap (setupB (V := V) (M := M) K) (stA (t := TSK K) L W Lk Bk inp) (stB (t := TSK K) L W Lk Bk inp)
      (costB V M W Lk Bk) := by
  set σ := stA (V := V) (M := M) (t := TSK K) L W Lk Bk inp with hσ
  have hv : σ.val = regsOf L W Lk Bk := rfl
  have hst : ∀ i, σ.st i = if i.val = 0 then frame inp else [] := fun _ => rfl
  have hsh : ∀ i, σ.sh i = 0 := fun _ => rfl
  have s12 := forStreams_spec cap (initNum (ns := NS M (TSK K) V) rK rC2) (fun _ => frame (binary W 0)) (50 * W + 10)
    σ.val (fun X τ hX hh hvτ => by
      have := initNum_spec cap (G := rK) (G2 := rC2) (by lay_ne) X τ hX hh (by rw [hvτ, hv, regsOf_rC2])
        (by rw [hvτ, hv, regsOf_rK]; omega)
      rwa [hvτ, hv, regsOf_rK] at this)
    numStreams σ numStreams_nodup (fun X hX => by
      rw [mem_numStreams] at hX
      refine ⟨by rw [hst, if_neg (by omega)], hsh X⟩) rfl
  set σ12 := { σ with st := fun i => if i ∈ (numStreams : List _) then frame (binary W 0) else σ.st i }
  have s13 := forStreams_spec cap (fun X => (WMX.wr X false : WMX (NS M (TSK K) V) (NR M))) (fun _ => [false]) 1
    σ12.val (fun X τ hX hh _ => by
      have := WXExec.wr cap X false τ
      rwa [hX, hh] at this)
    storeStreams σ12 storeStreams_nodup (fun X hX => by
      rw [mem_storeStreams] at hX
      refine ⟨?_, by simp [σ12, hsh]⟩
      simp only [σ12]
      rw [if_neg (by rw [mem_numStreams]; have := X.isLt; omega), hst, if_neg (by omega)]) rfl
  set σ13 := { σ12 with st := fun i => if i ∈ (storeStreams : List _) then [false] else σ12.st i }
  have v13 : σ13.val = regsOf L W Lk Bk := rfl
  have s14 := fillB_spec cap (Nr := rC1) (S := rC2) (by lay_ne) (sLG : Fin (NS M (TSK K) V + 1)) false σ13
    (by simp only [σ13, σ12]
        rw [if_neg (by rw [mem_storeStreams]; simp), if_neg (by rw [mem_numStreams]; simp; omega), hst,
          if_neg (by simp)])
    (by simp [σ13, σ12, hsh]) (by rw [v13, regsOf_rC2]) (by rw [v13, regsOf_rC1]; omega)
  rw [v13, regsOf_rC1] at s14
  set σ14 := σ13.sets sLG (List.replicate Bk false)
  have s15 := fillB_spec cap (Nr := rR) (S := rC2) (by lay_ne) (sRU : Fin (NS M (TSK K) V + 1)) true σ14
    (by simp only [σ14, σ13, σ12, WState.sets_st]
        rw [Function.update_of_ne (by lay_ne), if_neg (by rw [mem_storeStreams]; simp),
          if_neg (by rw [mem_numStreams]; simp; omega), hst, if_neg (by simp)])
    (by simp [σ14, σ13, σ12, hsh]) (by simp [σ14, v13, regsOf_rC2]) (by simp [σ14, v13, regsOf_rR]; omega)
  have e15 : σ14.val rR = Lk + Lk + Bk + 3 := by simp [σ14, v13, regsOf_rR]
  rw [e15] at s15
  refine WXExec.mono (WXExec.seq s12 (WXExec.seq s13 (WXExec.seq s14 s15)) |>.cast cap ?_ le_rfl) ?_
  · refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp [σ14, σ13, σ12, hsh, stB]
    · funext i
      simp only [σ14, σ13, σ12, WState.sets_st, stB, initSt, Function.update_apply]
      have hi := i.isLt
      by_cases h6 : i.val = 6
      · rw [if_pos (Fin.ext h6)]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h6]; ring_nf
      · rw [if_neg (fun e => h6 (by rw [e]; rfl))]
        by_cases h5 : i.val = 5
        · rw [if_pos (Fin.ext h5)]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h5]
        · rw [if_neg (fun e => h5 (by rw [e]; rfl))]
          by_cases hs : 8 ≤ i.val ∧ i.val < 8 + M
          · rw [if_pos ((mem_storeStreams i).2 hs)]; rw [if_neg (by omega), if_neg (by omega), if_pos hs]
          · rw [if_neg (fun h => hs ((mem_storeStreams i).1 h))]
            by_cases hn : i.val = 2 ∨ i.val = 7 ∨ 8 + 2 * M + TSK K ≤ i.val
            · rw [if_pos ((mem_numStreams i).2 hn)]
              by_cases h0 : i.val = 0
              · omega
              · rw [if_neg h0, if_pos hn]
            · rw [if_neg (fun h => hn ((mem_numStreams i).1 h)), hst]
              by_cases h0 : i.val = 0
              · rw [if_pos h0, if_pos h0]
              · rw [if_neg h0, if_neg h0, if_neg hn, if_neg hs, if_neg h5, if_neg h6]
    · rfl
  · simp only [costB, numStreams, storeStreams, List.length_cons, List.length_map, List.length_finRange]
    ring_nf; omega

def costC (L W Lk Bk : ℕ) : ℕ :=
  (3 * L + 1) + (3 * W + 1) + (3 * Lk + 1) + (3 * Bk + 1) + (3 * (Lk + Lk + Bk + 3) + 1) + 4

theorem setupC_spec (L W Lk Bk : ℕ) (inp : List Bool) (cap : ℕ) (hcap : L + W + 3 * Lk + 2 * Bk + 3 ≤ cap) :
    WXExec cap (setupC (V := V) (M := M) K) (stB (t := TSK K) L W Lk Bk inp) (initSt (t := TSK K) W Lk Bk inp)
      (costC L W Lk Bk) := by
  set σ := stB (V := V) (M := M) (t := TSK K) L W Lk Bk inp
  have s1 := clearR_spec cap rG L σ (by simp [σ, stB, regsOf, Fin.ext_iff]) (by omega)
  have s2 := clearR_spec cap rK W (σ.setv rG 0) (by simp [σ, stB, regsOf, Fin.ext_iff]) (by omega)
  have s3 := clearR_spec cap rT Lk ((σ.setv rG 0).setv rK 0) (by simp [σ, stB, regsOf, Fin.ext_iff]) (by omega)
  have s4 := clearR_spec cap rC1 Bk (((σ.setv rG 0).setv rK 0).setv rT 0) (by simp [σ, stB, regsOf, Fin.ext_iff])
    (by omega)
  have s5 := clearR_spec cap rR (Lk + Lk + Bk + 3) ((((σ.setv rG 0).setv rK 0).setv rT 0).setv rC1 0)
    (by simp [σ, stB, regsOf, Fin.ext_iff]) (by omega)
  refine WXExec.mono (WXExec.seq s1 (WXExec.seq s2 (WXExec.seq s3 (WXExec.seq s4 s5))) |>.cast cap ?_ le_rfl)
    (by simp only [costC]; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext r
  simp only [σ, stB, initSt, WState.setv_val, Function.update_apply, regsOf]
  split_ifs <;> rfl

/-! ## The whole set-up, the teardown -/

theorem setup_spec (z : Sz) (inp : List Bool) (cap : ℕ)
    (hcap : 2 * inp.length + 8 * (z.W (leadOnes inp) + z.Lk (leadOnes inp) + z.Bk (leadOnes inp)) + 4 * z.a1 +
      4 * z.a2 + 4 * z.a3 + 20 ≤ cap) :
    WXExec cap (setupP (V := V) (M := M) K z) (Interfaces.startState (NS M (TSK K) V) (NR M) inp)
      (initSt (t := TSK K) (z.W (leadOnes inp)) (z.Lk (leadOnes inp)) (z.Bk (leadOnes inp)) inp)
      (costA z (leadOnes inp) + 1 + (costB V M (z.W (leadOnes inp)) (z.Lk (leadOnes inp)) (z.Bk (leadOnes inp)) + 1 +
        costC (leadOnes inp) (z.W (leadOnes inp)) (z.Lk (leadOnes inp)) (z.Bk (leadOnes inp)))) := by
  have hL := leadOnes_le inp
  exact WXExec.seq (setupA_spec K z inp cap (by omega)) (WXExec.seq (setupB_spec K _ _ _ _ inp cap (by omega))
    (setupC_spec K _ _ _ _ inp cap (by omega)))

/-- Rewind store heads by their mirror registers. -/
def rewStores : List (Fin M) → WMX (NS M t V) (NR M)
  | [] => WMX.skip
  | m :: l => .seq (rewindR (sM m) (rM m)) (rewStores l)

/-- **The teardown**: every head back to `0`, every register `0`. -/
def tearP : WMX (NS M t V) (NR M) :=
  .seq (rewindR sIN rIP) (.seq (rewindR sOUT rOP) (.seq (rewindR sKI rKI) (.seq (rewindR sKO rKO)
    (rewStores (List.finRange M)))))

/-- The state after rewinding the stores of `l`. -/
def rewSt (l : List (Fin M)) (σ : WState (NS M t V) (NR M)) : WState (NS M t V) (NR M) :=
  ⟨fun i => if (∃ m ∈ l, i = sM m) then 0 else σ.sh i, σ.st, fun q => if (∃ m ∈ l, q = rM m) then 0 else σ.val q,
    σ.cell⟩

theorem rewStores_spec (cap : ℕ) : ∀ (l : List (Fin M)) (σ : WState (NS M t V) (NR M)), l.Nodup →
    (∀ m ∈ l, σ.val (rM m) = σ.sh (sM m) ∧ σ.sh (sM m) ≤ cap) →
    WXExec cap (rewStores l) σ (rewSt l σ) ((l.map fun m => 5 * σ.sh (sM m) + 2).sum) := by
  intro l
  induction l with
  | nil =>
    intro σ _ _
    have : rewSt [] σ = σ := by
      refine WState.eq ?_ rfl ?_ rfl <;> funext <;> simp [rewSt]
    rw [this]; simpa [rewStores] using WXExec.skip cap σ
  | cons m l ih =>
    intro σ hnd h
    have hm := h m (by simp)
    have hnd' := List.nodup_cons.mp hnd
    have r1 := rewindR_spec cap (sM m) (rM m) (σ.sh (sM m)) σ hm.1 rfl hm.2
    have r2 := ih ((σ.setv (rM m) 0).seth (sM m) 0) hnd'.2 (fun m' hm' => by
      have hne : m' ≠ m := fun e => hnd'.1 (e ▸ hm')
      have := h m' (by simp [hm'])
      simp [Function.update_of_ne (sM_inj hne), Function.update_of_ne (rM_inj hne), this])
    refine WXExec.mono (WXExec.seq r1 r2 |>.cast cap ?_ le_rfl) ?_
    · refine WState.eq ?_ rfl ?_ rfl
      · funext i
        by_cases hi : i = sM m
        · subst hi; simp only [rewSt, WState.seth_sh, WState.setv_sh]; split_ifs <;> simp_all
        · simp only [rewSt, WState.seth_sh, WState.setv_sh, Function.update_of_ne hi, List.mem_cons, exists_eq_or_imp,
            hi, false_or]
      · funext q
        by_cases hq : q = rM m
        · subst hq; simp only [rewSt, WState.seth_val, WState.setv_val]; split_ifs <;> simp_all
        · simp only [rewSt, WState.seth_val, WState.setv_val, Function.update_of_ne hq, List.mem_cons,
            exists_eq_or_imp, hq, false_or]
    · simp only [List.map_cons, List.sum_cons]
      have : (l.map fun m' => 5 * ((σ.setv (rM m) 0).seth (sM m) 0).sh (sM m') + 2).sum =
          (l.map fun m' => 5 * σ.sh (sM m') + 2).sum := by
        congr 1; apply List.map_congr_left; intro m' hm'
        have hne : m' ≠ m := fun e => hnd'.1 (e ▸ hm')
        simp [Function.update_of_ne (sM_inj hne)]
      omega

/-- Every head of an encoded state is `0` except the cursors' (entry, output, call words, stores). -/
theorem enc_sh_other (C : Ctx) {a : DS V M} {τ : WState (NS M (TS C) V) (NR M)} (he : Enc C a τ)
    (i : Fin (NS M (TS C) V + 1)) (h0 : i.val ≠ 0) (h1 : i.val ≠ 1) (h3 : i.val ≠ 3) (h4 : i.val ≠ 4)
    (hm : ¬ (8 ≤ i.val ∧ i.val < 8 + M)) : τ.sh i = 0 := by
  have hi := i.isLt
  unfold NS at hi
  by_cases h2 : i.val = 2
  · rw [show i = sZ from Fin.ext h2]; exact he.zero.2
  by_cases h5 : i.val = 5
  · rw [show i = sLG from Fin.ext h5]; exact he.lgH
  by_cases h6 : i.val = 6
  · rw [show i = sRU from Fin.ext h6]; exact he.ruH
  by_cases h7 : i.val = 7
  · rw [show i = sTP from Fin.ext h7]; exact he.tpH
  by_cases hS : i.val < 8 + 2 * M
  · rw [show i = sS ⟨i.val - 8 - M, by omega⟩ from Fin.ext (by simp; omega)]; exact he.shH _
  by_cases hT : i.val < 8 + 2 * M + TS C
  · rw [show i = sT ⟨i.val - 8 - 2 * M, by omega⟩ from Fin.ext (by simp; omega)]; exact he.scH _
  · rw [show i = vs ⟨i.val - 8 - 2 * M - TS C, by omega⟩ from Fin.ext (by simp; omega)]; exact (he.var _).2

/-- Every register of an encoded state is `0` except the cursor mirrors. -/
theorem enc_val_other (C : Ctx) {a : DS V M} {τ : WState (NS M (TS C) V) (NR M)} (he : Enc C a τ) (q : Fin (NR M))
    (h5 : q.val ≠ 5) (h6 : q.val ≠ 6) (h7 : q.val ≠ 7) (h8 : q.val ≠ 8) (hm : q.val < 11) : τ.val q = 0 := by
  have : q.val = 0 ∨ q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 4 ∨ q.val = 9 ∨ q.val = 10 := by omega
  rcases this with h | h | h | h | h | h | h
  · rw [show q = rF from Fin.ext h]; exact he.zF
  · rw [show q = rR from Fin.ext h]; exact he.zR
  · rw [show q = rG from Fin.ext h]; exact he.zG
  · rw [show q = rK from Fin.ext h]; exact he.zK
  · rw [show q = rT from Fin.ext h]; exact he.zT
  · rw [show q = rC1 from Fin.ext h]; exact he.zC1
  · rw [show q = rC2 from Fin.ext h]; exact he.zC2

def tearCost (C : Ctx) (a : DS V M) : ℕ :=
  (5 * (2 * a.ip) + 1) + 1 + ((5 * a.out.length + 1) + 1 + ((5 * (2 * a.kin.length) + 1) + 1 + ((5 * a.kc + 1) + 1 +
    ((List.finRange M).map fun m => 5 * ((2 * C.Wd + 1) * a.rc m) + 2).sum)))

/-- **The teardown.** -/
theorem tear_spec (C : Ctx) (b : DS V M) (τ : WState (NS M (TS C) V) (NR M)) (he : Enc C b τ) (cap : ℕ)
    (hcap : 2 * b.ip + b.out.length + 2 * b.kin.length + b.kc + (2 * C.Wd + 1) * (∑ m : Fin M, b.rc m) ≤ cap) :
    ∃ ρ, WXExec cap (tearP (t := TS C)) τ ρ (tearCost C b) ∧ ρ.st sOUT = b.out ∧ (∀ i, ρ.sh i = 0) ∧
      ∀ q, ρ.val q = 0 := by
  have hrc : ∀ m, (2 * C.Wd + 1) * b.rc m ≤ cap := fun m => by
    have : b.rc m ≤ ∑ m : Fin M, b.rc m := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    have := Nat.mul_le_mul_left (2 * C.Wd + 1) this
    omega
  have r1 := rewindR_spec cap (sIN : Fin (NS M (TS C) V + 1)) rIP (2 * b.ip) τ he.inR he.inH (by omega)
  set τ1 := (τ.setv rIP 0).seth sIN 0
  have r2 := rewindR_spec cap (sOUT : Fin (NS M (TS C) V + 1)) rOP b.out.length τ1
    (by simp [τ1, Function.update_of_ne (show (rOP : Fin (NR M)) ≠ rIP by lay_ne), he.outR])
    (by simp [τ1, Function.update_of_ne (show (sOUT : Fin (NS M (TS C) V + 1)) ≠ sIN by lay_ne), he.outH]) (by omega)
  set τ2 := (τ1.setv rOP 0).seth sOUT 0
  have r3 := rewindR_spec cap (sKI : Fin (NS M (TS C) V + 1)) rKI (2 * b.kin.length) τ2
    (by simp [τ2, τ1, Function.update_of_ne (show (rKI : Fin (NR M)) ≠ rIP by lay_ne),
      Function.update_of_ne (show (rKI : Fin (NR M)) ≠ rOP by lay_ne), he.kiR])
    (by simp [τ2, τ1, Function.update_of_ne (show (sKI : Fin (NS M (TS C) V + 1)) ≠ sIN by lay_ne),
      Function.update_of_ne (show (sKI : Fin (NS M (TS C) V + 1)) ≠ sOUT by lay_ne), he.kiH]) (by omega)
  set τ3 := (τ2.setv rKI 0).seth sKI 0
  have r4 := rewindR_spec cap (sKO : Fin (NS M (TS C) V + 1)) rKO b.kc τ3
    (by simp [τ3, τ2, τ1, Function.update_of_ne (show (rKO : Fin (NR M)) ≠ rIP by lay_ne),
      Function.update_of_ne (show (rKO : Fin (NR M)) ≠ rOP by lay_ne),
      Function.update_of_ne (show (rKO : Fin (NR M)) ≠ rKI by lay_ne), he.koR])
    (by simp [τ3, τ2, τ1, Function.update_of_ne (show (sKO : Fin (NS M (TS C) V + 1)) ≠ sIN by lay_ne),
      Function.update_of_ne (show (sKO : Fin (NS M (TS C) V + 1)) ≠ sOUT by lay_ne),
      Function.update_of_ne (show (sKO : Fin (NS M (TS C) V + 1)) ≠ sKI by lay_ne), he.koH]) (by omega)
  set τ4 := (τ3.setv rKO 0).seth sKO 0
  have hsM : ∀ m, τ4.sh (sM m) = (2 * C.Wd + 1) * b.rc m := fun m => by
    simp [τ4, τ3, τ2, τ1, Function.update_of_ne (show (sM m : Fin (NS M (TS C) V + 1)) ≠ sKO by lay_ne),
      Function.update_of_ne (show (sM m : Fin (NS M (TS C) V + 1)) ≠ sKI by lay_ne),
      Function.update_of_ne (show (sM m : Fin (NS M (TS C) V + 1)) ≠ sOUT by lay_ne),
      Function.update_of_ne (show (sM m : Fin (NS M (TS C) V + 1)) ≠ sIN by lay_ne), he.ramH]
  have hrM : ∀ m, τ4.val (rM m) = (2 * C.Wd + 1) * b.rc m := fun m => by
    simp [τ4, τ3, τ2, τ1, Function.update_of_ne (show (rM m : Fin (NR M)) ≠ rKO by lay_ne),
      Function.update_of_ne (show (rM m : Fin (NR M)) ≠ rKI by lay_ne),
      Function.update_of_ne (show (rM m : Fin (NR M)) ≠ rOP by lay_ne),
      Function.update_of_ne (show (rM m : Fin (NR M)) ≠ rIP by lay_ne), he.ramR]
  have r5 := rewStores_spec cap (List.finRange M) τ4 (List.nodup_finRange M)
    (fun m _ => ⟨by rw [hrM, hsM], by rw [hsM]; exact hrc m⟩)
  refine ⟨_, WXExec.seq r1 (WXExec.seq r2 (WXExec.seq r3 (WXExec.seq r4 r5))) |>.mono (le_of_eq ?_), ?_, ?_, ?_⟩
  · simp only [tearCost, hsM]
  · simp [rewSt, τ4, τ3, τ2, τ1, he.outS]
  · intro i
    simp only [rewSt]
    split_ifs with hex
    · rfl
    · simp only [τ4, τ3, τ2, τ1, WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs with e1 e2 e3 e4 <;> try rfl
      refine enc_sh_other C he i ?_ ?_ ?_ ?_ ?_
      · intro h; exact e4 (Fin.ext h)
      · intro h; exact e3 (Fin.ext h)
      · intro h; exact e2 (Fin.ext h)
      · intro h; exact e1 (Fin.ext h)
      · intro h; exact hex ⟨⟨i.val - 8, by omega⟩, List.mem_finRange _, Fin.ext (by simp; omega)⟩
  · intro q
    simp only [rewSt]
    split_ifs with hex
    · rfl
    · simp only [τ4, τ3, τ2, τ1, WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs with e1 e2 e3 e4 <;> try rfl
      have hq := q.isLt; unfold NR at hq
      refine enc_val_other C he q (fun h => e4 (Fin.ext h)) (fun h => e3 (Fin.ext h)) (fun h => e2 (Fin.ext h))
        (fun h => e1 (Fin.ext h)) ?_
      by_contra hc
      exact hex ⟨⟨q.val - 11, by omega⟩, List.mem_finRange _, Fin.ext (by simp; omega)⟩

/-! ## The packaging -/

/-- The run context of an entry word: width and call bounds from its leading ones. -/
def ctxOf (K : Callee) (z : Sz) (inp : List Bool) : Ctx :=
  ⟨z.W (leadOnes inp), inp, K, z.Lk (leadOnes inp), z.Bk (leadOnes inp)⟩

/-- The whole program: set-up, the compiled language program, teardown. -/
noncomputable def progOf (K : Callee) (z : Sz) (main : St V M) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (setupP K z) (.seq (comp K main) tearP)

/-- The step budget for an entry word whose language run costs at most `N`. -/
def langBudget (K : Callee) (z : Sz) (V M : ℕ) (inp : List Bool) (N : ℕ) : ℕ :=
  let L := leadOnes inp
  (costA z L + 1 + (costB V M (z.W L) (z.Lk L) (z.Bk L) + 1 + costC L (z.W L) (z.Lk L) (z.Bk L))) + 1 +
    (N * (500 * (z.W L + 1) ^ 2 + 100 * (TSK K + 3)) + 1 +
      (10 * inp.length + 5 * N + 10 * z.Lk L + 5 * (z.Bk L + 3) + M * (5 * ((2 * z.W L + 1) * N) + 2) + 10))

/-- The space bound used for the run. -/
def langCap (z : Sz) (M : ℕ) (inp : List Bool) (N : ℕ) : ℕ :=
  let L := leadOnes inp
  2 * inp.length + 8 * (z.W L + z.Lk L + z.Bk L) + 4 * (z.a1 + z.a2 + z.a3) + 40 + (2 * z.W L + 1) * (N + 1) * (M + 1) +
    N

theorem callee_hB (C : Ctx) : ∀ s, C.K.bud s ≤ C.Bk → (C.K.outw s).length ≤ C.Bk + 3 :=
  fun s h => (wf_out_len C.K.wf s).trans (by omega)

theorem sum_rc_le {b : DS V M} (n : ℕ) (hb : ∀ m, b.rc m ≤ n) : ∑ m : Fin M, b.rc m ≤ M * n := by
  calc ∑ m : Fin M, b.rc m ≤ ∑ _m : Fin M, n := Finset.sum_le_sum (fun m _ => hb m)
    _ = M * n := by simp

/-- **A cell-language program as a `WordFunction`.** For every request, the language program `main` run
from the initial state `a0` in the context of the entry word (width and call bounds from its leading ones) prints
the output word within `N r` cost units. -/
noncomputable def wordFunction_of_lang {Req : Type} (input output : Req → List Bool) (K : Callee) (z : Sz)
    (main : St V M) (N : Req → ℕ)
    (hrun : ∀ r, ∃ b n, Ex (ctxOf K z (input r)) main a0 b n ∧ b.out = output r ∧ n ≤ N r)
    (hW : ∀ r, 1 ≤ z.W (leadOnes (input r))) :
    WordFunction Req input output (fun r => langBudget K z V M (input r) (N r)) :=
  Interfaces.wordFunction_of_wmx (progOf K z main) sOUT (by simp) (fun r => langCap z M (input r) (N r)) (by
    intro r
    obtain ⟨b, n, hex, hout, hn⟩ := hrun r
    set C := ctxOf K z (input r) with hC
    set cap := langCap z M (input r) (N r) with hcap
    have hcapv : cap = 2 * (input r).length + 8 * (z.W (leadOnes (input r)) + z.Lk (leadOnes (input r)) + z.Bk (leadOnes (input r))) + 4 * (z.a1 + z.a2 + z.a3) + 40 +
        (2 * z.W (leadOnes (input r)) + 1) * (N r + 1) * (M + 1) + N r := rfl
    have hLi : leadOnes (input r) ≤ (input r).length := leadOnes_le _
    have hc1 : C.inp.length = (input r).length := rfl
    have hc2 : C.Lk = z.Lk (leadOnes (input r)) := rfl
    have hc3 : C.Bk = z.Bk (leadOnes (input r)) := rfl
    have hc4 : C.Wd = z.W (leadOnes (input r)) := rfl
    have hcapv' : langCap z M (input r) (N r) = cap := rfl
    have hWN : 2 * z.W (leadOnes (input r)) + 1 ≤ (2 * z.W (leadOnes (input r)) + 1) * (N r + 1) * (M + 1) := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    have s1 := setup_spec (V := V) (M := M) K z (input r) cap (by rw [hcapv]; omega)
    have henc : Enc C (a0 : DS V M) (initSt (t := TS C) C.Wd C.Lk C.Bk C.inp) := initSt_enc C
    have hcapok : CapOK C cap (a0 : DS V M) n := by
      refine ⟨hW r, ?_, ?_, ?_, fun m => ?_, ?_⟩
      · show 2 * z.W (leadOnes (input r)) + 2 ≤ cap
        rw [hcapv]; omega
      · show 2 * (input r).length + 2 ≤ cap
        rw [hcapv]; omega
      · show ([] : List Bool).length + n ≤ cap
        rw [hcapv]; simp only [List.length_nil]; omega
      · show (2 * z.W (leadOnes (input r)) + 1) * (([] : List ℕ).length + n + 1) + 1 ≤ cap
        rw [hcapv]; simp only [List.length_nil, zero_add]
        have : (2 * z.W (leadOnes (input r)) + 1) * (n + 1) ≤ (2 * z.W (leadOnes (input r)) + 1) * (N r + 1) * (M + 1) := by
          calc (2 * z.W (leadOnes (input r)) + 1) * (n + 1) ≤ (2 * z.W (leadOnes (input r)) + 1) * (N r + 1) := Nat.mul_le_mul_left _ (by omega)
            _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
        omega
      · show 2 * z.Lk (leadOnes (input r)) + z.Bk (leadOnes (input r)) + 3 + 2 ≤ cap
        rw [hcapv]; omega
    obtain ⟨⟨τ, e1, r2⟩, _⟩ := comp_ok C cap (callee_hB C) hex (a0_valid C) _ henc hcapok
    have hval := hex.valid (hW r) (callee_hB C) (a0_valid C)
    have hol := hex.out_len
    have hrl := hex.ram_len
    have hrc : ∀ m, b.rc m ≤ n := fun m => by
      have := hval.rc_le m; have := hrl m; simp [a0] at this; omega
    obtain ⟨ρ, r3, hρo, hρs, hρv⟩ := tear_spec C b τ e1 cap (by
      have h1 := hval.ip_le
      have h2 := hval.kin_le
      have h3 := hval.kc_le
      have h4 := hval.kout_le
      have h5 := sum_rc_le n hrc
      have h6 : (2 * C.Wd + 1) * ∑ m : Fin M, b.rc m ≤ (2 * z.W (leadOnes (input r)) + 1) * (N r + 1) * (M + 1) := by
        calc (2 * C.Wd + 1) * ∑ m : Fin M, b.rc m ≤ (2 * z.W (leadOnes (input r)) + 1) * (M * n) := Nat.mul_le_mul_left _ h5
          _ ≤ (2 * z.W (leadOnes (input r)) + 1) * ((N r + 1) * (M + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
          _ = _ := by ring
      simp only [a0, List.length_nil, zero_add] at hol
      rw [hcapv]
      show 2 * b.ip + b.out.length + 2 * b.kin.length + b.kc + (2 * C.Wd + 1) * ∑ m : Fin M, b.rc m ≤ _
      have : C.inp = input r := rfl
      have : C.Lk = z.Lk (leadOnes (input r)) := rfl
      have : C.Bk = z.Bk (leadOnes (input r)) := rfl
      omega)
    refine ⟨ρ, WXExec.seq s1 (WXExec.seq r2 r3) |>.mono ?_, hρo.trans hout, hρs, hρv⟩
    -- the budget
    have hval' := hval
    have h1 := hval.ip_le
    have h2 := hval.kin_le
    have h3 := hval.kc_le
    have h4 := hval.kout_le
    simp only [a0, List.length_nil, zero_add] at hol
    have htear : tearCost C b ≤ 10 * (input r).length + 5 * N r + 10 * z.Lk (leadOnes (input r)) + 5 * (z.Bk (leadOnes (input r)) + 3) +
        M * (5 * ((2 * z.W (leadOnes (input r)) + 1) * N r) + 2) + 10 := by
      unfold tearCost
      have hs : ((List.finRange M).map fun m => 5 * ((2 * C.Wd + 1) * b.rc m) + 2).sum ≤
          M * (5 * ((2 * z.W (leadOnes (input r)) + 1) * N r) + 2) := by
        have := List.sum_le_card_nsmul ((List.finRange M).map fun m => 5 * ((2 * C.Wd + 1) * b.rc m) + 2)
          (5 * ((2 * z.W (leadOnes (input r)) + 1) * N r) + 2) (fun x hx => by
            obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
            have := Nat.mul_le_mul_left (2 * z.W (leadOnes (input r)) + 1) ((hrc m).trans hn)
            show 5 * ((2 * z.W (leadOnes (input r)) + 1) * b.rc m) + 2 ≤ _
            omega)
        simpa using this
      have : C.inp = input r := rfl
      have : C.Lk = z.Lk (leadOnes (input r)) := rfl
      have : C.Bk = z.Bk (leadOnes (input r)) := rfl
      omega
    have hKC : n * KC C ≤ N r * (500 * (z.W (leadOnes (input r)) + 1) ^ 2 + 100 * (TSK K + 3)) := Nat.mul_le_mul_right _ hn
    simp only [langBudget]
    omega)

end NearCubicGates.Close.Cells
