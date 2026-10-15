import Proof.Wire_3_5.OutMachineP4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.P5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WilliamsPublishedForm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires.WireExponent3_5.FinalPass.Out.Half NearCubicWires.WireExponent3_5.FinalPass.Out.P1
open NearCubicWires.WireExponent3_5.FinalPass.Out.P3 (fb)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

/-! ## The values -/

/-- **The length scan**: `(zeros since the last one, position after the last one)`. -/
def scanL : List Bool → ℕ × ℕ → ℕ × ℕ
  | [], p => p
  | b :: bs, p => if b then scanL bs (0, p.2 + p.1 + 1) else scanL bs (p.1 + 1, p.2)

theorem scanL_sum : ∀ (bs : List Bool) (z l : ℕ), (scanL bs (z, l)).1 + (scanL bs (z, l)).2 = z + l + bs.length
  | [], z, l => rfl
  | b :: bs, z, l => by
    cases b
    · simp only [scanL, Bool.false_eq_true, if_false]
      have := scanL_sum bs (z + 1) l
      simp only [List.length_cons]; omega
    · simp only [scanL, if_true]
      have := scanL_sum bs 0 (l + z + 1)
      simp only [List.length_cons]; omega

theorem size_succ (x : ℕ) (hx : 0 < x) : Nat.size x = Nat.size (x / 2) + 1 := by
  have h1 := Nat.lt_size_self x
  have h2 : 0 < Nat.size x := Nat.size_pos.2 hx
  obtain ⟨s, hs⟩ : ∃ s, Nat.size x = s + 1 := ⟨Nat.size x - 1, by omega⟩
  rw [hs] at h1 ⊢
  have h3 : 2 ^ s ≤ x := Nat.lt_size.1 (by omega)
  have h4 : Nat.size (x / 2) ≤ s := Nat.size_le.2 (by rw [pow_succ] at h1; omega)
  rcases s with _ | s
  · have : x / 2 = 0 := by simp at h1; omega
    rw [this]; rfl
  · have h5 : 2 ^ s ≤ x / 2 := by rw [pow_succ] at h3; omega
    have h6 : s < Nat.size (x / 2) := Nat.lt_size.2 h5
    omega

theorem scanL_binary : ∀ (W x z l : ℕ), x < 2 ^ W →
    (scanL (binary W x) (z, l)).2 = if x = 0 then l else l + z + Nat.size x
  | 0, x, z, l, hx => by
    have : x = 0 := by simpa using hx
    subst this; rfl
  | W + 1, x, z, l, hx => by
    have hd : x / 2 < 2 ^ W := by rw [pow_succ] at hx; omega
    show (scanL ((x % 2 == 1) :: binary W (x / 2)) (z, l)).2 = _
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have hb : (x % 2 == 1) = false := by simp [h]
      rw [hb]
      simp only [scanL, Bool.false_eq_true, if_false]
      rw [scanL_binary W (x / 2) (z + 1) l hd]
      by_cases h0 : x = 0
      · subst h0; simp
      · have hx2 : x / 2 ≠ 0 := by omega
        rw [if_neg hx2, if_neg h0, size_succ x (by omega)]
        omega
    · have hb : (x % 2 == 1) = true := by simp [h]
      rw [hb]
      simp only [scanL, if_true]
      rw [scanL_binary W (x / 2) 0 (l + z + 1) hd]
      have hx0 : x ≠ 0 := by omega
      rw [if_neg hx0, size_succ x (by omega)]
      by_cases h2 : x / 2 = 0
      · rw [if_pos h2, h2]; rfl
      · rw [if_neg h2]; omega

theorem natBitLength_eq (x : ℕ) (hx : 0 < x) : natBitLength x = Nat.size x := by
  unfold natBitLength
  have h1 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
  have h2 := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 hx)
  have a1 : Nat.size x ≤ Nat.log 2 x + 1 := Nat.size_le.2 h1
  have a2 : Nat.log 2 x < Nat.size x := Nat.lt_size.2 h2
  omega

theorem fixedWidth_binary : ∀ (L W x : ℕ), L ≤ W → fixedWidthNatBits L x = (binary W x).take L
  | 0, _, _, _ => rfl
  | L + 1, W + 1, x, h => by
    unfold fixedWidthNatBits
    rw [List.ofFn_succ]
    show _ = ((x % 2 == 1) :: binary W (x / 2)).take (L + 1)
    rw [List.take_succ_cons]
    congr 1
    · simp only [Fin.val_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one x with h2 | h2 <;> simp [h2]
    · have := fixedWidth_binary L W (x / 2) (by omega)
      unfold fixedWidthNatBits at this
      rw [← this]
      congr 1
      funext i
      simp only [Fin.val_succ, Nat.testBit_div_two]
  | L + 1, 0, _, h => absurd h (by omega)

/-- **The printed natural in terms of its binary word**. -/
theorem natWord_binary (W x : ℕ) (hW : 1 ≤ W) (hx : x < 2 ^ W) :
    natWord x = List.replicate (natBitLength x) true ++ false :: (binary W x).take (natBitLength x) := by
  have hL : natBitLength x ≤ W := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; unfold natBitLength; simp; omega
    · rw [natBitLength_eq x h]; exact Nat.size_le.2 hx
  unfold natWord framedNatBits
  rw [fixedWidth_binary _ W x hL]

/-- The scan's length is `natBitLength` (after `L := max 1 L`). -/
theorem scanL_nbl (W x : ℕ) (hx : x < 2 ^ W) :
    (if (scanL (binary W x) (0, 0)).2 = 0 then 1 else (scanL (binary W x) (0, 0)).2) = natBitLength x := by
  rw [scanL_binary W x 0 0 hx]
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; rfl
  · have hx0 : x ≠ 0 := by omega
    have : 0 < Nat.size x := Nat.size_pos.2 h
    simp only [hx0, if_false, Nat.zero_add]
    rw [if_neg (by omega), natBitLength_eq x h]

/-! ## Appending to the output -/

/-- Append bit `b` to `O` (head at its end). -/
def emit {ns nr : ℕ} (O : Fin (ns + 1)) (b : Bool) : WM ns nr := .seq (.wr O b) (.fwd O)

theorem emit_spec {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (b : Bool) (σ : WState ns nr)
    (h : σ.sh O = (σ.st O).length) :
    WExec cap (emit O b) σ ((σ.sets O (σ.st O ++ [b])).seth O ((σ.st O).length + 1)) 3 := by
  have w := WExec.wr (cap := cap) O b σ
  rw [h, writeTapeBit_end'] at w
  have f := WExec.fwd (cap := cap) O (σ.sets O (σ.st O ++ [b]))
  rw [WState.sets_sh, h] at f
  exact WExec.cast cap (WExec.seq w f) rfl (by omega)

/-! ## The registers of the print -/

/-- Zeros since the last one, the length, a copy counter, `dupR`'s scratch. -/
def rZ : Fin nrO := rg 0
def rL : Fin nrO := rg 1
def rC : Fin nrO := rg 2
def rT : Fin nrO := rg 3

/-! ## The ones -/

def onesBody : WM nsO nrO := .seq (.dec rC) (emit sO true)

theorem onesLoop_spec (W : ℕ) : ∀ (m : ℕ) (σ : St), σ.val rC = m → m ≤ capO W → σ.sh sO = (σ.st sO).length →
    WExec (capO W) (.whr rC onesBody) σ
      (((σ.sets sO (σ.st sO ++ List.replicate m true)).seth sO ((σ.st sO).length + m)).setv rC 0) (m * 7 + 1)
  | 0, σ, hC, _, hO => by
    refine WExec.cast (capO W) (WExec.whrF hC) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h
      · subst h; simp [hO]
      · rfl
    · funext i; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs with h
      · subst h; simp
      · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs with h
      · subst h; exact hC
      · rfl
  | m + 1, σ, hC, hm, hO => by
    have d := WExec.dec (cap := capO W) rC σ (by omega)
    rw [hC, Nat.add_sub_cancel] at d
    have e := emit_spec (capO W) sO true (σ.setv rC m) (by simpa using hO)
    simp only [WState.setv_st] at e
    have ih := onesLoop_spec W m (((σ.setv rC m).sets sO (σ.st sO ++ [true])).seth sO ((σ.st sO).length + 1))
      (by simp) (by omega) (by simp)
    refine WExec.cast (capO W) (WExec.whrT (by omega) (WExec.seq d e) ih) ?_ (by ring_nf; omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i
      simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh]
      by_cases h : i = sO
      · subst h
        simp only [Function.update_self, WState.seth_st, WState.sets_st, WState.setv_st, List.length_append,
          List.length_singleton]
        omega
      · simp only [Function.update_of_ne h]
    · funext i; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs with h
      · simp only [List.append_assoc, List.singleton_append, List.replicate_succ]
      · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> rfl

/-! ## The bits -/

def bitsBody (X : Fin (nsO + 1)) : WM nsO nrO :=
  .seq (.dec rL) (.seq (.ifs X (emit sO true) (emit sO false)) (.seq (.fwd X) (.fwd X)))

theorem rd_bit (pre bs : List Bool) (b : Bool) :
    readTapeBit (frameP pre ++ frameP (b :: bs) ++ [false]) (2 * pre.length + 1) = b := by
  have e : frameP pre ++ frameP (b :: bs) ++ [false] = (frameP pre ++ [true]) ++ b :: (frameP bs ++ [false]) := by
    simp
  have hl : 2 * pre.length + 1 = (frameP pre ++ [true]).length := by
    rw [List.length_append, frameP_length]; rfl
  rw [e, hl, readTapeBit_mid]

theorem bitsLoop_spec (X : Fin (nsO + 1)) (hX : X ≠ sO) (W : ℕ) :
    ∀ (m : ℕ) (bs pre : List Bool) (σ : St), σ.st X = frameP pre ++ frameP bs ++ [false] →
      σ.sh X = 2 * pre.length + 1 → σ.val rL = m → m ≤ bs.length → m ≤ capO W →
      σ.sh sO = (σ.st sO).length →
      WExec (capO W) (.whr rL (bitsBody X)) σ
        ((((σ.sets sO (σ.st sO ++ bs.take m)).seth sO ((σ.st sO).length + m)).seth X
          (2 * (pre.length + m) + 1)).setv rL 0) (m * 12 + 1)
  | 0, bs, pre, σ, _, hh, hL, _, _, hO => by
    refine WExec.cast (capO W) (WExec.whrF hL) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; simp [hh]
      · subst h2; simp [hO]
      · rfl
    · funext i; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs with h
      · subst h; simp
      · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs with h
      · subst h; exact hL
      · rfl
  | m + 1, [], _, _, _, _, _, hm, _, _ => absurd hm (by simp)
  | m + 1, b :: bs, pre, σ, hA, hh, hL, hm, hmc, hO => by
    have d := WExec.dec (cap := capO W) rL σ (by omega)
    rw [hL, Nat.add_sub_cancel] at d
    have hbit : wbit (σ.setv rL m) X = b := by
      unfold wbit; simp only [WState.setv_st, WState.setv_sh]; rw [hA, hh]; exact rd_bit pre bs b
    have e := emit_spec (capO W) sO b (σ.setv rL m) (by simpa using hO)
    simp only [WState.setv_st] at e
    have br : WExec (capO W) (.ifs X (emit sO true) (emit sO false)) (σ.setv rL m)
        (((σ.setv rL m).sets sO (σ.st sO ++ [b])).seth sO ((σ.st sO).length + 1)) 4 := by
      cases b
      · exact WExec.ifsF hbit e
      · exact WExec.ifsT hbit e
    set σ2 := ((σ.setv rL m).sets sO (σ.st sO ++ [b])).seth sO ((σ.st sO).length + 1) with hσ2
    have h2X : σ2.sh X = 2 * pre.length + 1 := by simp [hσ2, Function.update_of_ne hX, hh]
    have f1 := WExec.fwd (cap := capO W) X σ2
    rw [h2X] at f1
    have f2 := fwd_to (capO W) X σ2 (2 * pre.length + 1 + 1)
    have ih := bitsLoop_spec X hX W m bs (pre ++ [b]) (σ2.seth X (2 * pre.length + 1 + 1 + 1))
      (by simp [hσ2, Function.update_of_ne hX, hA, frameP_app]) (by simp; omega) (by simp [hσ2])
      (by simp at hm; omega) (by omega)
      (by simp [hσ2, Function.update_of_ne (Ne.symm hX)])
    refine WExec.cast (capO W) (WExec.whrT (by omega) (WExec.seq d (WExec.seq br (WExec.seq f1 f2))) ih) ?_
      (by ring_nf; omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp only [hσ2, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs with h1 h2 <;> simp_all <;> omega
    · funext i; simp only [hσ2, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs with h
      · simp
      · rfl
    · funext j; simp only [hσ2, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> rfl

/-! ## The length scan -/

theorem regs_ne : rZ ≠ rL ∧ rZ ≠ rR ∧ rZ ≠ rK ∧ rL ≠ rR ∧ rL ≠ rK ∧ rR ≠ rK ∧ rC ≠ rL ∧ rC ≠ rT ∧ rL ≠ rT ∧
    rC ≠ rK ∧ rC ≠ rR ∧ rC ≠ rZ ∧ rW ≠ rZ ∧ rW ≠ rL ∧ rW ≠ rR ∧ rW ≠ rK ∧ rW ≠ rC ∧ rW ≠ rT ∧ rT ≠ rK := by decide

/-- One position: if the bit is set, `L += Z + 1`, `Z := 0`, else `Z += 1`; two cells on; `R += 2`; `K −= 1`. -/
def scanBody (X : Fin (nsO + 1)) : WM nsO nrO :=
  .seq (.ifs X (.seq (WM.move rZ rL) (.inc rL)) (.inc rZ))
    (.seq (.fwd X) (.seq (.fwd X) (.seq (.inc rR) (.seq (.inc rR) (.dec rK)))))

/-- The scan's registers and head over `σ`. -/
def nfS (σ : St) (X : Fin (nsO + 1)) (h z l r : ℕ) : St :=
  ((((σ.seth X h).setv rZ z).setv rL l).setv rR r).setv rK 0

theorem nfS_congr (σ σ1 : St) (X : Fin (nsO + 1)) (h z l r : ℕ) (hst : σ1.st = σ.st)
    (hsh : ∀ i, i ≠ X → σ1.sh i = σ.sh i)
    (hval : ∀ j, j ≠ rZ → j ≠ rL → j ≠ rR → j ≠ rK → σ1.val j = σ.val j) (hc : σ1.cell = σ.cell) :
    nfS σ1 X h z l r = nfS σ X h z l r := by
  unfold nfS
  refine WState.eq ?_ (by simp [hst]) ?_ (by simp [hc])
  · funext i; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs with h1
    · rfl
    · exact hsh i h1
  · funext j; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs with h1 h2 h3 h4
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hval j h4 h3 h2 h1

theorem tail_spec (X : Fin (nsO + 1)) (W : ℕ) (τ : St) (h r k : ℕ) (hh : τ.sh X = h) (hr : τ.val rR = r)
    (hk : τ.val rK = k + 1) (hrc : r + 2 ≤ capO W) (hkc : k + 1 ≤ capO W) :
    WExec (capO W) (.seq (.fwd X) (.seq (.fwd X) (.seq (.inc rR) (.seq (.inc rR) (.dec rK))))) τ
      (((τ.seth X (h + 1 + 1)).setv rR (r + 1 + 1)).setv rK k) 13 := by
  have e0 : τ = τ.seth X h := by rw [← hh, wseth_same]
  have f1 := fwd_to (capO W) X τ h
  rw [← e0] at f1
  have f2 := fwd_to (capO W) X τ (h + 1)
  have i1 := WExec.inc (cap := capO W) rR (τ.seth X (h + 1 + 1)) (by simp [hr]; omega)
  have i2 := WExec.inc (cap := capO W) rR ((τ.seth X (h + 1 + 1)).setv rR ((τ.seth X (h + 1 + 1)).val rR + 1))
    (by simp [hr]; omega)
  have d := WExec.dec (cap := capO W) rK (((τ.seth X (h + 1 + 1)).setv rR ((τ.seth X (h + 1 + 1)).val rR + 1)).setv rR
    (((τ.seth X (h + 1 + 1)).setv rR ((τ.seth X (h + 1 + 1)).val rR + 1)).val rR + 1)) (by
      simp [Function.update_of_ne (show rK ≠ rR by decide), hk]; omega)
  refine WExec.cast (capO W) (WExec.seq f1 (WExec.seq f2 (WExec.seq i1 (WExec.seq i2 d)))) ?_ (by omega)
  simp only [WState.seth_val, wsetv_val_self, wsetv_setv, hr]
  simp only [WState.setv_val, Function.update_of_ne (show rK ≠ rR by decide), WState.seth_val, hk, Nat.add_sub_cancel]

theorem scanLoop_spec (X : Fin (nsO + 1)) (W : ℕ) :
    ∀ (bs pre : List Bool) (σ : St) (z l : ℕ), σ.st X = frameP pre ++ frameP bs ++ [false] →
      σ.sh X = 2 * pre.length + 1 → σ.val rZ = z → σ.val rL = l → σ.val rR = 2 * pre.length →
      σ.val rK = bs.length → z + l + bs.length ≤ W → pre.length + bs.length ≤ W →
      WExec (capO W) (.whr rK (scanBody X)) σ
        (nfS σ X (2 * (pre.length + bs.length) + 1) (scanL bs (z, l)).1 (scanL bs (z, l)).2
          (2 * (pre.length + bs.length))) (bs.length * (7 * W + 22) + 1)
  | [], pre, σ, z, l, _, hh, hz, hl, hr, hk, _, _ => by
    refine WExec.cast (capO W) (WExec.whrF hk) ?_ (by omega)
    unfold nfS
    obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := regs_ne
    refine WState.eq ?_ rfl ?_ rfl
    · funext i; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h1
      · subst h1; simp [hh]
      · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, Function.update_apply, scanL]
      split_ifs with h1 h2 h3 h4
      · subst h1; exact hk
      · subst h2; simp [hr]
      · subst h3; exact hl
      · subst h4; exact hz
      · rfl
  | b :: bs, pre, σ, z, l, hA, hh, hz, hl, hr, hk, hzl, hpb => by
    obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := regs_ne
    have hbit : wbit σ X = b := by unfold wbit; rw [hA, hh]; exact rd_bit pre bs b
    -- the branch
    obtain ⟨σb, cb, hb, hbZ, hbL, hbR, hbK, hbst, hbsh, hbv, hbc, hcb⟩ : ∃ (σb : St) (cb : ℕ),
        WExec (capO W) (.ifs X (.seq (WM.move rZ rL) (.inc rL)) (.inc rZ)) σ σb cb ∧
        σb.val rZ = (if b then 0 else z + 1) ∧ σb.val rL = (if b then l + z + 1 else l) ∧ σb.val rR = σ.val rR ∧
        σb.val rK = σ.val rK ∧ σb.st = σ.st ∧ σb.sh = σ.sh ∧
        (∀ j, j ≠ rZ → j ≠ rL → σb.val j = σ.val j) ∧ σb.cell = σ.cell ∧ cb ≤ 7 * W + 6 := by
      cases b
      · have i1 := WExec.inc (cap := capO W) rZ σ (by rw [hz]; unfold capO; simp at hzl; omega)
        refine ⟨_, _, WExec.ifsF hbit i1, by simp [hz], by simp [Function.update_of_ne (Ne.symm n1), hl],
          by simp [Function.update_of_ne (Ne.symm n2)], by simp [Function.update_of_ne (Ne.symm n3)], rfl, rfl,
          fun j h1 _ => by simp [Function.update_of_ne h1], rfl, by omega⟩
      · have m1 := wmove_spec (capO W) rZ rL n1 z σ hz (by rw [hz]; unfold capO; simp at hzl; omega)
          (by rw [hz, hl]; unfold capO; simp at hzl; omega)
        have i1 := WExec.inc (cap := capO W) rL ((σ.setv rZ 0).setv rL (σ.val rL + σ.val rZ))
          (by simp [hz, hl]; unfold capO; simp at hzl; omega)
        refine ⟨_, _, WExec.ifsT hbit (WExec.seq m1 i1), by simp [Function.update_of_ne n1],
          by simp [hz, hl], by simp [Function.update_of_ne (Ne.symm n2), Function.update_of_ne (Ne.symm n4)],
          by simp [Function.update_of_ne (Ne.symm n3), Function.update_of_ne (Ne.symm n5)], rfl, rfl,
          fun j h1 h2 => by simp [Function.update_of_ne h1, Function.update_of_ne h2], rfl, ?_⟩
        have : z ≤ W := by simp at hzl; omega
        omega
    have tl := tail_spec X W σb (2 * pre.length + 1) (2 * pre.length) bs.length (by rw [hbsh, hh]) (by rw [hbR, hr])
      (by rw [hbK, hk]; rfl) (by unfold capO; simp at hpb; omega) (by unfold capO; simp at hpb; omega)
    set σ1 := ((σb.seth X (2 * pre.length + 1 + 1 + 1)).setv rR (2 * pre.length + 1 + 1)).setv rK bs.length with hσ1
    have ih := scanLoop_spec X W bs (pre ++ [b]) σ1 (if b then 0 else z + 1) (if b then l + z + 1 else l)
      (by simp [hσ1, hbst, hA, frameP_app]) (by simp [hσ1]; omega)
      (by simp [hσ1, Function.update_of_ne n2, Function.update_of_ne n3, hbZ])
      (by simp [hσ1, Function.update_of_ne n4, Function.update_of_ne n5, hbL])
      (by simp [hσ1, Function.update_of_ne n6]; omega) (by simp [hσ1])
      (by simp at hzl; split_ifs <;> omega) (by simp at hpb ⊢; omega)
    have body := WExec.seq hb tl
    refine WExec.cast (capO W) (WExec.whrT (by rw [hk]; simp) body ih) ?_ ?_
    · have e : scanL (b :: bs) (z, l) = scanL bs ((if b then 0 else z + 1), (if b then l + z + 1 else l)) := by
        cases b <;> rfl
      rw [e]
      have e2 : 2 * ((pre ++ [b]).length + bs.length) = 2 * (pre.length + (b :: bs).length) := by simp; omega
      rw [e2]
      apply nfS_congr
      · simp [hσ1, hbst]
      · intro i hi; simp [hσ1, Function.update_of_ne hi, hbsh]
      · intro j h1 h2 h3 h4
        simp [hσ1, Function.update_of_ne h3, Function.update_of_ne h4, hbv j h1 h2]
      · simp [hσ1, hbc]
    · simp only [List.length_cons]
      have : cb + 1 + 13 + 2 + (bs.length * (7 * W + 22) + 1) ≤ (bs.length + 1) * (7 * W + 22) + 1 := by
        rw [Nat.add_mul]; omega
      omega

/-! ## One natural -/

/-- **Print `natWord x`** (appended to `O`) from the word `x` on `X`: `rK := W`; scan the length; back; `Z := 0`;
`L := max 1 L`; `1^L`; `0`; the `L` low bits. -/
def printNat (X : Fin (nsO + 1)) : WM nsO nrO :=
  .seq (UnionMachine.BinW.dupR rW rK rT) (.seq (.fwd X) (.seq (.whr rK (scanBody X)) (.seq (WM.rewind X rR)
    (.seq (WM.clear rZ) (.seq (.ifr rL .skip (.inc rL)) (.seq (UnionMachine.BinW.dupR rL rC rT)
    (.seq (.whr rC onesBody) (.seq (emit sO false) (.whr rL (bitsBody X))))))))))

def pnCost (W : ℕ) : ℕ := W * (7 * W + 22) + 100 * W + 60

theorem printNat_spec (X : Fin (nsO + 1)) (hX : X ≠ sO) (W x : ℕ) (σ : St) (hW : 1 ≤ W) (hx : x < 2 ^ W)
    (hXst : σ.st X = frame (binary W x)) (hXsh : σ.sh X = 0) (hO : σ.sh sO = (σ.st sO).length)
    (hw : σ.val rW = W) (hz : ∀ r, r ≠ rW → σ.val r = 0) :
    ∃ ρ : St, WExec (capO W) (printNat X) σ ρ (pnCost W) ∧ ρ.st sO = σ.st sO ++ natWord x ∧
      ρ.sh sO = (ρ.st sO).length ∧ (∀ i, i ≠ sO → ρ.st i = σ.st i) ∧ (∀ i, i ≠ sO → i ≠ X → ρ.sh i = σ.sh i) ∧
      ρ.val = σ.val ∧ ρ.cell = σ.cell := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19⟩ := regs_ne
  have hcap : 8 * W + 8 = capO W := rfl
  -- 1. `rK := W`
  have s1 := UnionMachine.BinW.dupR_spec (capO W) rW rK rT n16 n18 (Ne.symm n19) σ W hw (hz rK (Ne.symm n16))
    (hz rT (Ne.symm n18)) (by omega)
  set σ1 := σ.setv rK W with hσ1
  -- 2. to the first bit
  have s2 : WExec (capO W) (.fwd X) σ1 (σ1.seth X 1) 1 := by
    have e := WExec.fwd (cap := capO W) X σ1
    rwa [show σ1.sh X = 0 by simp [hσ1, hXsh]] at e
  set σ2 := σ1.seth X 1 with hσ2
  -- 3. the scan
  have s3 := scanLoop_spec X W (binary W x) [] σ2 0 0 (by simp [hσ2, hσ1, hXst, frame_eq_frameP]) (by simp [hσ2])
    (by simp [hσ2, hσ1, Function.update_of_ne n3, hz rZ (Ne.symm n13)])
    (by simp [hσ2, hσ1, Function.update_of_ne n5, hz rL (Ne.symm n14)])
    (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm (show rK ≠ rR from Ne.symm n6)), hz rR (Ne.symm n15)])
    (by simp [hσ2, hσ1]) (by simp) (by simp)
  simp only [List.length_nil, SignedSortKey.binary_length, Nat.zero_add] at s3
  set zs := (scanL (binary W x) (0, 0)).1 with hzs
  set ls := (scanL (binary W x) (0, 0)).2 with hls
  have hsum := scanL_sum (binary W x) 0 0
  simp only [SignedSortKey.binary_length, Nat.zero_add] at hsum
  set σ3 := nfS σ2 X (2 * W + 1) zs ls (2 * W) with hσ3
  -- 4. back to the first bit
  have h3R : σ3.val rR = 2 * W := by simp [hσ3, nfS, Function.update_of_ne n6]
  have s4 := wrewind_spec (capO W) X rR (2 * W) σ3 h3R (by rw [h3R]; omega)
  have h3X : σ3.sh X = 2 * W + 1 := by simp [hσ3, nfS]
  rw [h3X, show 2 * W + 1 - 2 * W = 1 by omega] at s4
  set σ4 := (σ3.setv rR 0).seth X 1 with hσ4
  -- 5. `Z := 0`
  have s5 := wclear_spec (capO W) rZ zs σ4
    (by simp [hσ4, hσ3, nfS, Function.update_of_ne n2, Function.update_of_ne n3, Function.update_of_ne n1])
    (by rw [show σ4.val rZ = zs by simp [hσ4, hσ3, nfS, Function.update_of_ne n2, Function.update_of_ne n3,
      Function.update_of_ne n1]]; omega)
  set σ5 := σ4.setv rZ 0 with hσ5
  have h5L : σ5.val rL = ls := by
    simp [hσ5, hσ4, hσ3, nfS, Function.update_of_ne (Ne.symm n1), Function.update_of_ne n4, Function.update_of_ne n5]
  -- 6. `L := max 1 L`
  set Lx := natBitLength x with hLx
  have hLx' : (if ls = 0 then 1 else ls) = Lx := scanL_nbl W x hx
  have hLW : Lx ≤ W := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [hLx, h0]; unfold natBitLength; simp; omega
    · rw [hLx, natBitLength_eq x h0]; exact Nat.size_le.2 hx
  have s6 : WExec (capO W) (.ifr rL .skip (.inc rL)) σ5 (σ5.setv rL Lx) 4 := by
    by_cases h0 : ls = 0
    · rw [if_pos h0] at hLx'
      have i1 := WExec.inc (cap := capO W) rL σ5 (by rw [h5L, h0]; omega)
      rw [h5L, h0] at i1
      rw [← hLx']
      exact WExec.ifrF (by rw [h5L, h0]) i1
    · rw [if_neg h0] at hLx'
      rw [← hLx', ← h5L, wsetv_same]
      exact WExec.mono (WExec.ifrT (by rw [h5L]; exact h0) (WExec.skip σ5)) (by omega)
  set σ6 := σ5.setv rL Lx with hσ6
  -- 7. `C := L`
  have s7 := UnionMachine.BinW.dupR_spec (capO W) rL rC rT (Ne.symm n7) n9 n8 σ6 Lx (by simp [hσ6])
    (by simp [hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne n7, Function.update_of_ne n12,
      Function.update_of_ne n10, Function.update_of_ne n11, hz rC (Ne.symm n17)])
    (by simp [hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne (Ne.symm n9),
      Function.update_of_ne n19, Function.update_of_ne (show rT ≠ rR by decide),
      Function.update_of_ne (show rT ≠ rZ by decide), hz rT (Ne.symm n18)]) (by omega)
  set σ7 := σ6.setv rC Lx with hσ7
  have h7O : σ7.sh sO = (σ7.st sO).length := by
    simp [hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne (Ne.symm hX), hO]
  -- 8. the ones
  have s8 := onesLoop_spec W Lx σ7 (by simp [hσ7]) (by omega) h7O
  set σ8 := ((σ7.sets sO (σ7.st sO ++ List.replicate Lx true)).seth sO ((σ7.st sO).length + Lx)).setv rC 0 with hσ8
  -- 9. the separator
  have s9 := emit_spec (capO W) sO false σ8 (by simp [hσ8])
  set σ9 := (σ8.sets sO (σ8.st sO ++ [false])).seth sO ((σ8.st sO).length + 1) with hσ9
  -- 10. the bits
  have s10 := bitsLoop_spec X hX W Lx (binary W x) [] σ9
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne hX, hXst, frame_eq_frameP])
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne hX])
    (by simp [hσ9, hσ8, hσ7, hσ6, Function.update_of_ne (Ne.symm n7)]) (by simp; exact hLW) (by omega)
    (by simp [hσ9])
  refine ⟨_, WExec.cast (capO W) (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 s10))))))))) rfl ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pnCost
    have : zs ≤ W := by omega
    omega
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    simp only [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, WState.setv_st, WState.seth_st, WState.sets_st,
      Function.update_self, List.nil_append]
    rw [natWord_binary W x hW hx, ← hLx]
    simp
  · simp only [WState.setv_sh, WState.setv_st, WState.seth_sh, WState.seth_st, WState.sets_st, WState.sets_sh,
      Function.update_of_ne (Ne.symm hX), Function.update_self]
    simp only [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, WState.setv_st, WState.seth_st, WState.sets_st,
      Function.update_self, List.length_append, List.length_replicate, List.length_take,
      SignedSortKey.binary_length, List.length_singleton]
    rw [Nat.min_eq_left hLW]
  · intro i hi
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne hi]
  · intro i hi hiX
    simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, Function.update_of_ne hi, Function.update_of_ne hiX]
  · funext j
    simp only [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, nfS, hσ2, hσ1, WState.setv_val, WState.seth_val, WState.sets_val,
      Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first
      | rfl
      | (symm; apply hz; decide)
  · rfl

/-! ## P5 -/

/-- **P5's program**: the sign `0`, then `natWord n'`, then `natWord d'`. -/
def p5P : WM nsO nrO := .seq (emit sO false) (.seq (printNat (sX 0)) (printNat (sX 1)))

def p5Cost (W : ℕ) : ℕ := 3 + 1 + (pnCost W + 1 + pnCost W)

theorem p5Cost_le (W : ℕ) : p5Cost W ≤ 200 * (W + 1) ^ 2 := by
  unfold p5Cost pnCost
  nlinarith [Nat.zero_le W]

theorem p5_run (W n d : ℕ) (σ : St) (h : Quot σ W n d) (hcop : Nat.Coprime n d) (hd : 0 < d) (hn : n < 2 ^ W)
    (hdW : d < 2 ^ W) : ∃ τ, WExec (capO W) p5P σ τ (p5Cost W) ∧ Printed τ W ((n : ℚ) / d) := by
  have hW : 1 ≤ W := by
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · subst h0; simp at hdW; omega
    · exact h0
  have hz : ∀ r, r ≠ rW → σ.val r = 0 := h.bd.regs
  have s0 := emit_spec (capO W) sO false σ (by rw [h.ho, h.bd.heads]; rfl)
  rw [h.ho] at s0
  set σ0 := (σ.sets sO ([] ++ [false])).seth sO (([] : List Bool).length + 1) with hσ0
  obtain ⟨ρ1, r1, o1, sh1, st1, shh1, v1, c1⟩ := printNat_spec (sX 0) (by decide) W n σ0 hW hn
    (by simp [hσ0, Function.update_of_ne (show sX 0 ≠ sO by decide), h.hq.1])
    (by simp [hσ0, Function.update_of_ne (show sX 0 ≠ sO by decide), h.hq.2]) (by simp [hσ0])
    (by simp [hσ0, h.bd.hw]) (fun r hr => by simp [hσ0, hz r hr])
  obtain ⟨ρ2, r2, o2, sh2, st2, shh2, v2, c2⟩ := printNat_spec (sX 1) (by decide) W d ρ1 hW hdW
    (by rw [st1 _ (by decide)]; simp [hσ0, Function.update_of_ne (show sX 1 ≠ sO by decide), h.hr.1])
    (by rw [shh1 _ (by decide) (by decide)]; simp [hσ0, Function.update_of_ne (show sX 1 ≠ sO by decide), h.hr.2])
    sh1 (by rw [v1]; simp [hσ0, h.bd.hw]) (fun r hr => by rw [v1]; simp [hσ0, hz r hr])
  refine ⟨ρ2, WExec.cast (capO W) (WExec.seq s0 (WExec.seq r1 r2)) rfl (by unfold p5Cost; omega), ?_⟩
  refine ⟨by rw [c2, c1]; simp [hσ0, h.bd.cell], by rw [v2, v1]; simp [hσ0, h.bd.hw],
    fun r hr => by rw [v2, v1]; simp [hσ0, hz r hr], ?_⟩
  rw [o2, o1, ratWord_coprime n d hd hcop]
  simp [hσ0]

/-- **P5**. -/
def ph5 : Ph5 := ⟨p5P, p5Cost, 200, p5Cost_le, p5_run⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.P5
