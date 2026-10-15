import Proof.Gates.Expand.PolyTabPS

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- Stage 1, part A: the header and `G(2n+3)`. -/
def st1A : WX :=
  .seq (rdF sI (rX 10)) <| .seq (rdF sI (rX 11)) <| .seq (rdF sI (rX 12)) <| .seq (rdF sI (rX 13)) <|
  .seq (rdF sI (rX 14)) <| .seq (addR (rX 10) (rX 16) (rX 7)) <| .seq (addR (rX 10) (rX 16) (rX 7)) <|
  .seq (WMX.inc (rX 16)) <| .seq (WMX.inc (rX 16)) <| .seq (WMX.inc (rX 16)) <|
  .seq (mulR (rX 14) (rX 17) (rX 16) (rX 15) (rX 7)) <| .wm (WM.clear (rX 16))
/-- Stage 1, part B: skip the gates and the two coordinate lists. -/
def st1B : WX :=
  .seq (skF sI (rX 15)) <| .seq (rdF sI (rX 16)) <| .seq (skF sI (rX 16)) <| .seq (rdF sI (rX 16)) <| skF sI (rX 16)
/-- Stage 1, part C: `2^k`, the bits, `V`, the roles. -/
def st1C : WX :=
  .seq (rdF sI (rX 19)) <| .seq (addR (rX 19) (rX 16) (rX 7)) <| .seq (skF sI (rX 16)) <|
  .seq (rdF sI (rX 18)) <| .seq (addR (rX 18) (rX 16) (rX 7)) <| .seq (addR (rX 18) (rX 16) (rX 7)) <|
  skF sI (rX 16)
/-- Stage 1. -/
def st1 : WX := .seq st1A (.seq st1B st1C)

/-- The magnitude bound of the header values. -/
def Mh (r : TabReq) : ℕ := r.n + r.k + r.s + r.B + r.G + r.V + 2 ^ r.k
/-- The input length. -/
def Lt (r : TabReq) : ℕ := (tabWord r).length
/-- One step's cost bound. -/
def Cst (r : TabReq) : ℕ := 400 * (Mh r + 1) ^ 2 + 50 * Lt r + 50

theorem nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength; have := Nat.log_lt_self 2 (show x + 1 ≠ 0 by omega)
  have := Nat.log_mono_right (b := 2) (show x ≤ x + 1 by omega); omega

theorem two_pow_nbl (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [pow_succ]; have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega); omega

theorem rdCost_le (x M : ℕ) (hx : x ≤ M) : rdCost x ≤ 400 * (M + 1) ^ 2 := by
  unfold rdCost
  have h1 := nbl_le x
  have h2 := two_pow_nbl x
  calc (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (M + 3) * (40 * (2 * M + 2) + 40) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ ≤ 400 * (M + 1) ^ 2 := by nlinarith

theorem skCost_le (L : List ℕ) (i m : ℕ) : skCost ((L.drop i).take m) ≤ 24 * (L.flatMap natWord).length + 1 := by
  unfold skCost
  have h1 : (((L.drop i).take m).map fun x => 20 * natBitLength x + 20 + 4).sum ≤
      ((L.map fun x => 20 * natBitLength x + 20 + 4)).sum := by
    have hs : ((L.drop i).take m).Sublist L := (List.take_sublist _ _).trans (List.drop_sublist _ _)
    exact (hs.map _).sum_le_sum (fun _ _ => Nat.zero_le _)
  have h2 : ((L.map fun x => 20 * natBitLength x + 20 + 4)).sum ≤ ((L.map fun x => 24 * (natWord x).length)).sum :=
    List.sum_le_sum fun x _ => by
      rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]; omega
  have h3 : ((L.map fun x => 24 * (natWord x).length)).sum = 24 * (L.flatMap natWord).length := by
    rw [List.length_flatMap, List.sum_map_mul_left]
  omega

/-- The registers after the header. -/
def fB (r : TabReq) : Fin 64 → ℕ := fun j =>
  if j = 10 then r.n else if j = 11 then r.k else if j = 12 then r.s else if j = 13 then r.B else
  if j = 14 then r.G else 0
/-- The registers after part A. -/
def fA (r : TabReq) : Fin 64 → ℕ := fun j => if j = 15 then r.G * (2 * r.n + 3) else fB r j
/-- The registers after stage 1. -/
def f1 (r : TabReq) : Fin 64 → ℕ := fun j => if j = 18 then r.V else if j = 19 then 2 ^ r.k else fB r j

/-- The facts every part uses. -/
structure Hdr (cap : ℕ) (r : TabReq) : Prop where
  fit : ∀ x ∈ preN r, natBitLength x + 1 ≤ cap
  pow : ∀ i (hi : i < (preN r).length), 2 ^ (natBitLength (preN r)[i] + 1) ≤ cap
  sk : ∀ i m, skCost (((preN r).drop i).take m) ≤ Cst r
  rd : ∀ x, x ≤ Mh r → rdCost x ≤ Cst r
  sq : Mh r + 1 ≤ (Mh r + 1) ^ 2
  cst : 400 * (Mh r + 1) ^ 2 ≤ Cst r
  capM : 8 * (Mh r + 1) ^ 2 ≤ cap
  len : (preN r).length = pV r + 1 + 2 * r.V
  bn : r.n ≤ Mh r
  bk : r.k ≤ Mh r
  bs : r.s ≤ Mh r
  bB : r.B ≤ Mh r
  bG : r.G ≤ Mh r
  bV : r.V ≤ Mh r
  b2 : 2 ^ r.k ≤ Mh r
  g2 : r.G * (2 * r.n + 3) ≤ 3 * (Mh r + 1) ^ 2

theorem hdr (cap : ℕ) (r : TabReq) (hcap : 2 ^ (Lt r + 1) + 8 * (Mh r + 1) ^ 2 ≤ cap) : Hdr cap r := by
  have hk2 := Nat.two_pow_pos r.k
  have hL2 := Nat.two_pow_pos (Lt r + 1)
  have hM1 : r.n ≤ Mh r := by unfold Mh; omega
  have hMG : r.G ≤ Mh r := by unfold Mh; omega
  refine ⟨fun x hx => ?_, fun i hi => ?_, fun i m => ?_, fun x hx => ?_, by nlinarith, by unfold Cst; omega,
    by omega, preN_length r, hM1, by unfold Mh; omega, by unfold Mh; omega, by unfold Mh; omega, hMG,
    by unfold Mh; omega, by unfold Mh; omega, by nlinarith⟩
  · have := preN_nbl r x hx
    have : Lt r + 1 < 2 ^ (Lt r + 1) := Nat.lt_two_pow_self
    unfold Lt at *; omega
  · have := preN_nbl r _ (List.getElem_mem hi)
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (show natBitLength _ + 1 ≤ Lt r + 1 by unfold Lt; omega))
      (by omega)
  · have := skCost_le (preN r) i m; have := preN_word_le r; unfold Cst Lt; omega
  · have := rdCost_le x (Mh r) hx; unfold Cst; omega

theorem st1A_spec (cap : ℕ) (r : TabReq) (σ0 σ : WSt) (rest : List Bool) (H : Hdr cap r)
    (h : PS σ0 sI [] (preN r) rest 0 (fun _ => 0) σ) :
    Runs cap st1A σ (12 * (Cst r + 1)) (PS σ0 sI [] (preN r) rest 5 (fA r)) := by
  obtain ⟨h0n, h0k, h0s, h0B, h0G⟩ := preN_hdr r
  have hl := H.len
  have epk : pk r = 5 + r.G * (2 * r.n + 3) := rfl
  have eps : ps r = pk r + r.k + 1 := rfl
  have epN : pN r = ps r + r.s + 1 := rfl
  have epV : pV r = pN r + 2 ^ r.k + 1 := rfl
  have hk2 := Nat.two_pow_pos r.k
  obtain ⟨τ1, e1, p1⟩ := (ps_rd cap 10 (by decide) h (by omega) rfl rfl rfl rfl rfl (H.pow 0 (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? h0n]; exact H.bn))
  rw [getElem_of_getElem? h0n] at p1
  obtain ⟨τ2, e2, p2⟩ := (ps_rd cap 11 (by decide) p1 (by omega) rfl rfl rfl rfl rfl (H.pow 1 (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? h0k]; exact H.bk))
  rw [getElem_of_getElem? h0k] at p2
  obtain ⟨τ3, e3, p3⟩ := (ps_rd cap 12 (by decide) p2 (by omega) rfl rfl rfl rfl rfl (H.pow 2 (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? h0s]; exact H.bs))
  rw [getElem_of_getElem? h0s] at p3
  obtain ⟨τ4, e4, p4⟩ := (ps_rd cap 13 (by decide) p3 (by omega) rfl rfl rfl rfl rfl (H.pow 3 (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? h0B]; exact H.bB))
  rw [getElem_of_getElem? h0B] at p4
  obtain ⟨τ5, e5, p5⟩ := (ps_rd cap 14 (by decide) p4 (by omega) rfl rfl rfl rfl rfl (H.pow 4 (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? h0G]; exact H.bG))
  rw [getElem_of_getElem? h0G] at p5
  have q5 := p5.congr (g := fB r) (fun j => by fin_cases j <;> simp [Function.update_apply, fB])
  have hM := H.bn; have hsq := H.sq; have hc := H.capM; have hcs := H.cst
  obtain ⟨τ6, e6, p6⟩ := (ps_add cap 16 10 (by decide) (by decide) (by decide) q5 0 r.n (by simp [fB])
    (by simp [fB]) (by simp [fB]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ7, e7, p7⟩ := (ps_add cap 16 10 (by decide) (by decide) (by decide) p6 (0 + r.n) r.n (by simp)
    (by simp [fB]) (by simp [fB]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ8, e8, p8⟩ := (ps_inc cap 16 p7 (0 + r.n + r.n) (by simp) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ9, e9, p9⟩ := (ps_inc cap 16 p8 (0 + r.n + r.n + 1) (by simp) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ10, e10, p10⟩ := (ps_inc cap 16 p9 (0 + r.n + r.n + 1 + 1) (by simp) (by omega)).cost (c' := Cst r) (by omega)
  have hg2 := H.g2; have hG := H.bG
  obtain ⟨τ11, e11, p11⟩ := (ps_mul cap 14 17 16 15 (by decide) p10 r.G (0 + r.n + r.n + 1 + 1 + 1) 0
    (by simp [fB]) (by simp) (by simp [fB]) (by simp [fB]) (by simp [fB]) (by nlinarith) (by omega)).cost
    (c' := Cst r) (by nlinarith)
  obtain ⟨τ12, e12, p12⟩ := (ps_clr cap 16 p11 (0 + r.n + r.n + 1 + 1 + 1) (by simp) (by omega)).cost (c' := Cst r) (by omega)
  refine ⟨τ12, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <|
    WXExec.seq e6 <| WXExec.seq e7 <| WXExec.seq e8 <| WXExec.seq e9 <| WXExec.seq e10 <| WXExec.seq e11 e12)
    (by omega), ?_⟩
  refine (p12.congr fun j => ?_).idx rfl
  fin_cases j <;> simp [Function.update_apply, fA, fB] <;> (try ring_nf) <;> (try simp)

theorem st1B_spec (cap : ℕ) (r : TabReq) (σ0 σ : WSt) (rest : List Bool) (H : Hdr cap r)
    (h : PS σ0 sI [] (preN r) rest 5 (fA r) σ) :
    Runs cap st1B σ (5 * (Cst r + 1)) (PS σ0 sI [] (preN r) rest (pN r) (fB r)) := by
  have hl := H.len
  have epk : pk r = 5 + r.G * (2 * r.n + 3) := rfl
  have eps : ps r = pk r + r.k + 1 := rfl
  have epN : pN r = ps r + r.s + 1 := rfl
  have epV : pV r = pN r + 2 ^ r.k + 1 := rfl
  have hk2 := Nat.two_pow_pos r.k
  have hpk := preN_pk r
  have hps := preN_ps r
  have hg2 := H.g2; have hsq := H.sq; have hc := H.capM; have hk := H.bk; have hs := H.bs
  obtain ⟨τ1, e1, p1⟩ := (ps_sk cap 15 (by decide) (m := r.G * (2 * r.n + 3)) h (by omega)
    (by simp [fA, fB]) (by simp [fA, fB]) (by simp [fA]) H.fit (by omega)).cost (H.sk _ _)
  have q1 := p1.idx (show 5 + r.G * (2 * r.n + 3) = pk r from rfl)
  obtain ⟨τ2, e2, p2⟩ := (ps_rd cap 16 (by decide) q1 (by omega) (by simp [fA, fB]) (by simp [fA, fB])
    (by simp [fA, fB]) (by simp [fA, fB]) (by simp [fA, fB]) (H.pow _ (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? hpk]; exact H.bk))
  rw [getElem_of_getElem? hpk] at p2
  obtain ⟨τ3, e3, p3⟩ := (ps_sk cap 16 (by decide) (m := r.k) p2 (by omega)
    (by simp [fA, fB]) (by simp [fA, fB]) (by simp) H.fit (by omega)).cost (H.sk _ _)
  have q3 := p3.idx (show pk r + 1 + r.k = ps r by omega)
  obtain ⟨τ4, e4, p4⟩ := (ps_rd cap 16 (by decide) q3 (by omega) (by simp [fA, fB]) (by simp [fA, fB])
    (by simp [fA, fB]) (by simp [fA, fB]) (by simp) (H.pow _ (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? hps]; exact H.bs))
  rw [getElem_of_getElem? hps] at p4
  obtain ⟨τ5, e5, p5⟩ := (ps_sk cap 16 (by decide) (m := r.s) p4 (by omega)
    (by simp [fA, fB]) (by simp [fA, fB]) (by simp) H.fit (by omega)).cost (H.sk _ _)
  refine ⟨τ5, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 e5) (by omega), ?_⟩
  refine (p5.congr fun j => ?_).idx (by omega)
  fin_cases j <;> simp [Function.update_apply, fA, fB]

theorem st1C_spec (cap : ℕ) (r : TabReq) (σ0 σ : WSt) (rest : List Bool) (H : Hdr cap r)
    (h : PS σ0 sI [] (preN r) rest (pN r) (fB r) σ) :
    Runs cap st1C σ (7 * (Cst r + 1)) (PS σ0 sI [] (preN r) rest (preN r).length (f1 r)) := by
  have hl := H.len
  have epk : pk r = 5 + r.G * (2 * r.n + 3) := rfl
  have eps : ps r = pk r + r.k + 1 := rfl
  have epN : pN r = ps r + r.s + 1 := rfl
  have epV : pV r = pN r + 2 ^ r.k + 1 := rfl
  have hk2 := Nat.two_pow_pos r.k
  have hpN := preN_pN r
  have hpV := preN_pV r
  have hsq := H.sq; have hc := H.capM; have h2 := H.b2; have hV := H.bV; have hcs := H.cst
  obtain ⟨τ1, e1, p1⟩ := (ps_rd cap 19 (by decide) h (by omega) (by simp [fB]) (by simp [fB])
    (by simp [fB]) (by simp [fB]) (by simp [fB]) (H.pow _ (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? hpN]; exact H.b2))
  rw [getElem_of_getElem? hpN] at p1
  obtain ⟨τ2, e2, p2⟩ := (ps_add cap 16 19 (by decide) (by decide) (by decide) p1 0 (2 ^ r.k) (by simp [fB])
    (by simp) (by simp [fB]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ3, e3, p3⟩ := (ps_sk cap 16 (by decide) (m := 2 ^ r.k) p2 (by omega)
    (by simp [fB]) (by simp [fB]) (by simp) H.fit (by omega)).cost (H.sk _ _)
  have q3 := p3.idx (show pN r + 1 + 2 ^ r.k = pV r by omega)
  obtain ⟨τ4, e4, p4⟩ := (ps_rd cap 18 (by decide) q3 (by omega) (by simp [fB]) (by simp [fB])
    (by simp [fB]) (by simp [fB]) (by simp [fB]) (H.pow _ (by omega))).cost
    (H.rd _ (by rw [getElem_of_getElem? hpV]; exact H.bV))
  rw [getElem_of_getElem? hpV] at p4
  obtain ⟨τ5, e5, p5⟩ := (ps_add cap 16 18 (by decide) (by decide) (by decide) p4 0 r.V (by simp [fB])
    (by simp) (by simp [fB]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ6, e6, p6⟩ := (ps_add cap 16 18 (by decide) (by decide) (by decide) p5 (0 + r.V) r.V (by simp)
    (by simp) (by simp [fB]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ7, e7, p7⟩ := (ps_sk cap 16 (by decide) (m := 2 * r.V) p6 (by omega)
    (by simp [fB]) (by simp [fB]) (by simp; ring) H.fit (by omega)).cost (H.sk _ _)
  refine ⟨τ7, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <|
    WXExec.seq e6 e7) (by omega), ?_⟩
  refine (p7.congr fun j => ?_).idx (by omega)
  fin_cases j <;> simp [Function.update_apply, f1, fB]

theorem st1_spec (cap : ℕ) (r : TabReq) (σ0 σ : WSt) (rest : List Bool)
    (h : PS σ0 sI [] (preN r) rest 0 (fun _ => 0) σ) (hcap : 2 ^ (Lt r + 1) + 8 * (Mh r + 1) ^ 2 ≤ cap) :
    Runs cap st1 σ (26 * (Cst r + 1)) (PS σ0 sI [] (preN r) rest (preN r).length (f1 r)) := by
  have H := hdr cap r hcap
  exact (Runs.seq (st1A_spec cap r σ0 σ rest H h) fun τ hτ => Runs.seq (st1B_spec cap r σ0 τ rest H hτ)
    fun ρ hρ => st1C_spec cap r σ0 ρ rest H hρ).cost (by omega)

end NearCubicGates.Close.Expand.PolyTab
