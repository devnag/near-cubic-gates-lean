import Proof.Gates.Expand.PolyTabStage6

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
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)
open StablePartition.Workspace (overlay)

section Gen
variable {ns nr : ℕ} {U : Fin 10 ↪ Fin (ns + 1)} {R : Fin 12 ↪ Fin nr}

/-- `EvV` only sees the block's streams and registers. -/
theorem evv_transfer {Wb hd e : ℕ} {inp : List Bool} {v : Fin 10 → ℕ} {σ τ : WState ns nr}
    (h : EvV U R Wb inp hd e v σ) (hs : ∀ i, τ.st (U i) = σ.st (U i) ∧ τ.sh (U i) = σ.sh (U i))
    (hr : ∀ j, τ.val (R j) = σ.val (R j)) : EvV U R Wb inp hd e v τ :=
  ⟨fun i hi => ⟨by rw [(hs i).1]; exact (h.num i hi).1, by rw [(hs i).2]; exact (h.num i hi).2⟩,
    by rw [(hs 0).1]; exact h.inp, by rw [(hs 0).2]; exact h.hd, by rw [hr]; exact h.r1,
    fun j h1 h11 => by rw [hr]; exact h.zero j h1 h11⟩

end Gen

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

theorem sS0_ne (i : Fin 9) : sS (te := te) (qa := qa) 0 ≠ ubv i := by
  intro e; have := congrArg Fin.val e; simp at this; omega

/-- The block on the input copy `sS 0`. -/
abbrev U0 : Fin 10 ↪ Fin (NSx te qa + 1) := UB (sS 0) sS0_ne

/-- One field: `U 1 := x mod 2^Wb`, appended as a record to `sS 3`. -/
def tcBody : WX := .seq (readBin U0 RB 1 2) (appendRecX (U0 1) (sS 3) (rX 29) (rX 39))

def tcLoop : WX := .whr (rX 9) (.seq (WMX.dec (rX 9)) tcBody)

/-- The table records of the first `k` fields. -/
def tbOut (Wb : ℕ) (L : List ℕ) (k : ℕ) : List Bool := (L.take k).flatMap fun x => frame (binary Wb (x % 2 ^ Wb))

theorem U0_one : (U0 (te := te) (qa := qa) 1) = ubv 0 := UB_succ _ _ 1 (by decide)

theorem U0_ne_tb (i : Fin 10) : U0 (te := te) (qa := qa) i ≠ sS 3 := by
  intro e
  by_cases hi : i.val = 0
  · have : i = 0 := Fin.ext hi
    subst this; rw [UB_zero] at e; have := congrArg Fin.val e; simp at this
  · rw [UB_succ _ _ i hi] at e; have := congrArg Fin.val e; simp at this; omega

theorem RB_ne (j : Fin 12) (k : Fin 64) (hk : k.val < 52) : RB j ≠ rX k := by
  intro e; have := congrArg Fin.val e; simp at this; omega

theorem tb_nmem : sS 3 ∉ evS (U0 (te := te) (qa := qa)) := fun hm => by
  simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e <;> exact U0_ne_tb _ e.symm

theorem rx_nmem (k : Fin 64) (hk : k.val < 52) : rX k ∉ evR RB := fun hm => by
  simp only [evR, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e | e | e | e <;> exact RB_ne _ k hk e.symm

/-- The loop invariant. -/
def TcInv (Wb : ℕ) (L : List ℕ) (inp : List Bool) (σA : WSt) (k : ℕ) (τ : WSt) : Prop :=
  (∃ v : Fin 10 → ℕ, EvV U0 RB Wb inp (encN (L.take k)).length 0 v τ ∧ v 8 = 1 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 9 = 0) ∧
  OutOn τ (sS 3) (rX 39) (tbOut Wb L k) [] ∧ τ.val (rX 29) = 0 ∧
  SameExcept σA τ (sS 3 :: sS 0 :: List.ofFn ubv) (rX 9 :: rX 39 :: List.ofFn RB)

theorem tcBody_spec (cap Wb : ℕ) (hW : 1 ≤ Wb) (L : List ℕ) (post : List Bool) (σA : WSt) (k : ℕ)
    (hk : k < L.length) (τ : WSt) (hI : TcInv Wb L (encN L ++ post) σA k τ)
    (hcap : natBitLength L[k] + 1 ≤ cap) (hcapW : 2 * Wb + 1 ≤ cap)
    (hcapO : (L.length + 1) * (2 * Wb + 1) + 2 ≤ cap) :
    Runs cap tcBody τ (readBinCost Wb (natBitLength L[k]) + 1 + (40 * Wb + 11))
      (fun ρ => TcInv Wb L (encN L ++ post) σA (k + 1) ρ ∧ ρ.val (rX 9) = τ.val (rX 9)) := by
  obtain ⟨⟨v, hv, hv8, hv3, hv4, hv9⟩, hO, h29, hfr⟩ := hI
  have hinp : encN L ++ post = encN (L.take k) ++ enc true (natWord L[k]) ++ (encN (L.drop (k + 1)) ++ post) := by
    rw [encN_split L k hk]; simp [List.append_assoc]
  refine Runs.seq (readBinV cap 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (Post.refl hv) hv8 hW
    L[k] _ _ hinp rfl hcap hcapW) fun τ1 hτ1 => ?_
  have hN := hτ1.1.num 1 (by decide)
  simp only [Function.update_of_ne (show (1 : Fin 10) ≠ 2 by decide), Function.update_self] at hN
  have hS : τ1.st (U0 1) = frameP (binary Wb (L[k] % 2 ^ Wb)) ++ false :: [] := by
    rw [hN.1, frame_eq_frameP]
  have hO1 : OutOn τ1 (sS 3) (rX 39) (tbOut Wb L k) [] := by
    have := hτ1.2
    exact ⟨by rw [this.st tb_nmem]; exact hO.1, by rw [this.sh tb_nmem]; exact hO.2.1,
      by rw [this.val (rx_nmem 39 (by decide))]; exact hO.2.2⟩
  have hc29 : τ1.val (rX 29) = 0 := by
    rw [hτ1.2.val (rx_nmem 29 (by decide))]; exact h29
  have htbl : (tbOut Wb L k).length ≤ L.length * (2 * Wb + 1) := by
    unfold tbOut
    rw [List.length_flatMap]
    have : ∀ x ∈ L.take k, (frame (binary Wb (x % 2 ^ Wb))).length = 2 * Wb + 1 := fun x _ => by
      rw [frame_length, binary_length]
    rw [List.map_congr_left this]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_take]
    exact Nat.mul_le_mul_right _ (min_le_right _ _)
  have e2 := appendRec_spec cap (Src := U0 1) (O := sS 3) (CS := rX 29) (CO := rX 39) (U0_ne_tb 1) (by polyTabNe) τ1
    (binary Wb (L[k] % 2 ^ Wb)) [] (tbOut Wb L k) [] hS hN.2 hc29 hO1 (by
      rw [binary_length]
      have : (L.length + 1) * (2 * Wb + 1) = L.length * (2 * Wb + 1) + (2 * Wb + 1) := by ring
      omega)
  have hd' : (encN (L.take (k + 1))).length = (encN (L.take k)).length + 2 * (natWord L[k]).length := by
    rw [encN_take_succ L k hk]
  have htb : tbOut Wb L (k + 1) = tbOut Wb L k ++ frame (binary Wb (L[k] % 2 ^ Wb)) := by
    unfold tbOut
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hU0mem : ∀ x ∈ evS (U0 (te := te) (qa := qa)), x ∈ sS 3 :: sS 0 :: List.ofFn ubv := by
    intro x hx
    simp only [evS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [UB_zero]
    all_goals (rw [UB_succ _ _ _ (by decide)]; simp only [List.mem_cons, List.mem_ofFn]; right; right; exact ⟨_, rfl⟩)
  have h9 : τ1.val (rX 9) = τ.val (rX 9) := hτ1.2.val (rx_nmem 9 (by decide))
  refine ⟨_, WXExec.mono (WXExec.wm e2) (by rw [binary_length]), ?_, ?_⟩
  swap
  · simp [Function.update_of_ne (show rX 9 ≠ rX 39 by polyTabNe), h9]
  refine ⟨⟨Function.update (Function.update v 1 (L[k] % 2 ^ Wb)) 2
    (2 ^ natBitLength L[k] % 2 ^ Wb), ?_, ?_, by simp [hv3], by simp [hv4], by simp [hv9]⟩, ?_, ?_, ?_⟩
  · rw [hd']
    exact evv_transfer hτ1.1 (fun i => by simp [Function.update_of_ne (U0_ne_tb i)])
      (fun j => by simp [Function.update_of_ne (RB_ne j 39 (by decide))])
  · simp [Function.update_of_ne (show (8 : Fin 10) ≠ 2 by decide), Function.update_of_ne (show (8 : Fin 10) ≠ 1 by decide), hv8]
  · rw [htb]
    refine ⟨by simp [overlay], by simp, by simp⟩
  · simp [Function.update_of_ne (show rX 29 ≠ rX 39 by polyTabNe), hc29]
  · refine se_ext (S' := [sS 3]) (R' := [rX 39]) (se_ext hfr hτ1.2 hU0mem fun q hq => ?_) ?_ (fun x hx => ?_)
      (fun q hq => ?_)
    · simp only [evR, List.mem_cons, List.not_mem_nil, or_false] at hq
      simp only [List.mem_cons, List.mem_ofFn]
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact ⟨fun x hx => by simp only [List.mem_singleton] at hx; simp [Function.update_of_ne hx],
        fun q hq => by simp only [List.mem_singleton] at hq; simp [Function.update_of_ne hq], rfl⟩
    · simp only [List.mem_singleton] at hx; subst hx; simp
    · simp only [List.mem_singleton] at hq; subst hq; simp

theorem TcInv.setv9 {Wb : ℕ} {L : List ℕ} {inp : List Bool} {σA : WSt} {k : ℕ} {τ : WSt}
    (h : TcInv Wb L inp σA k τ) (x : ℕ) : TcInv Wb L inp σA k (τ.setv (rX 9) x) := by
  obtain ⟨⟨v, hv, hv8, hv3, hv4, hv9⟩, hO, h29, hfr⟩ := h
  refine ⟨⟨v, evv_transfer hv (fun i => by simp) (fun j => by simp [Function.update_of_ne (RB_ne j 9 (by decide))]), hv8,
    hv3, hv4, hv9⟩,
    ⟨by simp [hO.1], by simp [hO.2.1], by simp [Function.update_of_ne (show rX 39 ≠ rX 9 by polyTabNe), hO.2.2]⟩,
    by simp [Function.update_of_ne (show rX 29 ≠ rX 9 by polyTabNe), h29], ?_⟩
  exact se_ext hfr (sameExcept_setv (S := []) τ (List.mem_singleton_self _) x) (fun x hx => by simp at hx)
    (fun q hq => by simp at hq; subst hq; simp)

def st6b : WX := .seq tcLoop (closeOutX (sS 3) (rX 39))

def tcCost (Wb : ℕ) (L : List ℕ) : ℕ :=
  L.length * (readBinCost Wb ((L.map natBitLength).foldr max 0) + 1 + (40 * Wb + 11) + 4) + 1 + 1 +
    (5 * (L.length * (2 * Wb + 1)) + 3)

theorem readBinCost_mono (Wb : ℕ) {a b : ℕ} (h : a ≤ b) : readBinCost Wb a ≤ readBinCost Wb b := by
  unfold readBinCost; have : a * (binStepCost Wb + 4) ≤ b * (binStepCost Wb + 4) := Nat.mul_le_mul_right _ h; omega

theorem st6b_spec (cap Wb : ℕ) (hW : 1 ≤ Wb) (L : List ℕ) (post : List Bool) (σA σ : WSt)
    (h : TcInv Wb L (encN L ++ post) σA 0 σ) (h9 : σ.val (rX 9) = L.length)
    (hcap : ∀ x ∈ L, natBitLength x + 1 ≤ cap) (hcapW : 2 * Wb + 1 ≤ cap)
    (hcapO : (L.length + 1) * (2 * Wb + 1) + 2 ≤ cap) :
    Runs cap st6b σ (tcCost Wb L) (fun τ => (∃ v : Fin 10 → ℕ, EvV U0 RB Wb (encN L ++ post) (encN L).length 0 v τ ∧
      v 8 = 1 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 9 = 0) ∧ τ.st (sS 3) = recStream (L.map fun x => binary Wb (x % 2 ^ Wb)) ∧ τ.sh (sS 3) = 0 ∧
      τ.val (rX 39) = 0 ∧ τ.val (rX 29) = 0 ∧ τ.val (rX 9) = 0 ∧
      SameExcept σA τ (sS 3 :: sS 0 :: List.ofFn ubv) (rX 9 :: rX 39 :: List.ofFn RB)) := by
  have hnb : ∀ k (hk : k < L.length), natBitLength L[k] ≤ (L.map natBitLength).foldr max 0 := fun k hk =>
    le_foldr_max _ _ (List.mem_map_of_mem (List.getElem_mem hk))
  have hloop := Runs.count (cap := cap) (K := rX 9) (body := tcBody)
    (readBinCost Wb ((L.map natBitLength).foldr max 0) + 1 + (40 * Wb + 11)) L.length (TcInv Wb L (encN L ++ post) σA)
    (by nlinarith) (fun k hk τ hτ _ => (tcBody_spec cap Wb hW L post σA k hk _ (hτ.setv9 _)
      (hcap _ (List.getElem_mem hk)) hcapW hcapO).mono (by have := readBinCost_mono Wb (hnb k hk); omega)
      fun ρ hρ => ⟨hρ.1, by rw [hρ.2]; simp⟩) σ h h9
  refine Runs.seq hloop fun τ ⟨hτ, hK⟩ => ?_
  obtain ⟨⟨v, hv, hv8, hv3, hv4, hv9⟩, hO, h29, hfr⟩ := hτ
  have htbl : (tbOut Wb L L.length).length = L.length * (2 * Wb + 1) := by
    unfold tbOut; rw [List.take_length, List.length_flatMap]
    simp [frame_length, binary_length]
  have e := closeOut_spec cap (σ := τ) (tbOut Wb L L.length) [] hO (by rw [htbl]; nlinarith)
  refine ⟨_, WXExec.mono (WXExec.wm e) (by rw [htbl]), ⟨v, ?_, hv8, hv3, hv4, hv9⟩, ?_, by simp, by simp, ?_, ?_, ?_⟩
  · rw [List.take_length] at hv
    exact evv_transfer hv (fun i => by simp [Function.update_of_ne (U0_ne_tb i)])
      (fun j => by simp [Function.update_of_ne (RB_ne j 39 (by decide))])
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, overlay, List.drop_nil,
      List.append_nil, recStream, tbOut, List.take_length, List.flatMap_map]
  · simp [Function.update_of_ne (show rX 29 ≠ rX 39 by polyTabNe), h29]
  · simp [Function.update_of_ne (show rX 9 ≠ rX 39 by polyTabNe), hK]
  · exact se_ext hfr (S' := [sS 3]) (R' := [rX 39])
      ⟨fun x hx => by simp only [List.mem_singleton] at hx; simp [Function.update_of_ne hx],
        fun q hq => by simp only [List.mem_singleton] at hq; simp [Function.update_of_ne hq], rfl⟩
      (by simp) (by simp)

end NearCubicGates.Close.Expand.PolyTab
