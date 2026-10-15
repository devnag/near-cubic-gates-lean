import Proof.Gates.Succinct.EvalSub
import Proof.Gates.Succinct.Arith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

theorem two_pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hx)
    rw [pow_succ]; omega

theorem nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  have := Nat.log_lt_self 2 (show x + 1 ≠ 0 by omega)
  have := Nat.log_mono_right (show x ≤ x + 1 by omega) (b := 2)
  simp only [natBitLength]; omega

/-! ## Peeking at a unary prefix -/

/-- Count the `true` cells from the head into `B` (`T` scratch), head back. -/
def peekW (i : Fin (ns + 1)) (B T : Fin nr) : WM ns nr :=
  .seq (.whs i (.seq (.fwd i) (.seq (.inc B) (.inc T)))) (WM.rewind i T)

theorem peekLoop (cap : ℕ) (i : Fin (ns + 1)) (B T : Fin nr) (hBT : B ≠ T) (σ : WState ns nr) (L : ℕ)
    (hL : ones (σ.st i) (σ.sh i) = L) (hcap : σ.val B + L + 1 ≤ cap) :
    ∀ m j, j + m = L →
      WExec cap (.whs i (.seq (.fwd i) (.seq (.inc B) (.inc T))))
        (((σ.seth i (σ.sh i + j)).setv B (σ.val B + j)).setv T j)
        (((σ.seth i (σ.sh i + L)).setv B (σ.val B + L)).setv T L) (m * 12 + 1) := by
  intro m
  induction m with
  | zero =>
    intro j hj; rw [Nat.add_zero] at hj; subst hj
    refine WExec.whsF ?_
    simp [wbit]; rw [← hL]; exact ones_false _ _
  | succ m ih =>
    intro j hj
    set τ := ((σ.seth i (σ.sh i + j)).setv B (σ.val B + j)).setv T j with hτ
    have hb : wbit τ i = true := by simp [wbit, τ]; exact ones_true _ _ j (by omega)
    have e1 := WExec.fwd (cap := cap) i τ
    have e2 := WExec.inc (cap := cap) B (τ.seth i (τ.sh i + 1)) (by simp [τ, Function.update_apply, hBT]; omega)
    have e3 := WExec.inc (cap := cap) T ((τ.seth i (τ.sh i + 1)).setv B ((τ.seth i (τ.sh i + 1)).val B + 1))
      (by simp [τ, Function.update_apply, Ne.symm hBT]; omega)
    have ih' := ih (j + 1) (by omega)
    refine WExec.mono (WExec.whsT hb (WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl) ih') (by omega)
    refine WState.eq ?_ rfl ?_ rfl
    · funext y; by_cases hy : y = i
      · subst hy; simp [τ]; ring
      · simp [τ, Function.update_apply, hy]
    · funext r; by_cases hrT : r = T
      · rw [hrT]; simp [τ, Function.update_apply, Ne.symm hBT]
      · by_cases hrB : r = B
        · rw [hrB]; simp [τ, Function.update_apply, hBT]; ring
        · simp [τ, Function.update_apply, hrT, hrB]

theorem peekW_spec (cap : ℕ) (i : Fin (ns + 1)) (B T : Fin nr) (hBT : B ≠ T) (σ : WState ns nr)
    (hT : σ.val T = 0) (hcap : σ.val B + ones (σ.st i) (σ.sh i) + 1 ≤ cap) :
    WExec cap (peekW i B T) σ (σ.setv B (σ.val B + ones (σ.st i) (σ.sh i))) (20 * ones (σ.st i) (σ.sh i) + 3) := by
  set L := ones (σ.st i) (σ.sh i) with hL
  have e1 := peekLoop cap i B T hBT σ L rfl hcap L 0 (by omega)
  have h0 : ((σ.seth i (σ.sh i + 0)).setv B (σ.val B + 0)).setv T 0 = σ := by
    refine WState.eq ?_ rfl ?_ rfl
    · funext y; by_cases hy : y = i
      · subst hy; simp
      · simp [Function.update_apply, hy]
    · funext r; by_cases hrT : r = T
      · subst hrT; simp [hT]
      · by_cases hrB : r = B
        · subst hrB; simp [hrT]
        · simp [Function.update_apply, hrT, hrB]
  rw [h0] at e1
  set τ := ((σ.seth i (σ.sh i + L)).setv B (σ.val B + L)).setv T L with hτ
  have e2 := wrewind_spec cap i T L τ (by simp [τ]) (by simp [τ]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl) (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext y; by_cases hy : y = i
    · subst hy; simp [τ]
    · simp [τ, Function.update_apply, hy]
  · funext r; by_cases hrT : r = T
    · subst hrT; simp [τ, Ne.symm hBT, hT]
    · by_cases hrB : r = B
      · subst hrB; simp [τ, hrT]
      · simp [τ, Function.update_apply, hrT, hrB]

/-! ## Exact reads and skips -/

/-- One field read exactly into `tgt` (`B`, `T` scratch). -/
def readEx (i : Fin (ns + 1)) (R : FReg → Fin nr) (B T tgt : Fin nr) : WM ns nr :=
  .seq (peekW i B T) (.seq (fieldTo i R B tgt) (WM.clear B))

/-- The cost class of one exact read. -/
def readCost (x : ℕ) : ℕ := 10000 * (x + 2) ^ 2

/-- Registers of an exact read: the field reader's family `R`, the peek registers `B`, `T`, the target. -/
structure ReadRegs (R : FReg → Fin nr) (B T tgt : Fin nr) : Prop where
  inj : Function.Injective R
  bt : B ≠ T
  btg : B ≠ tgt
  ttg : T ≠ tgt
  rb : ∀ k, R k ≠ B
  rt : ∀ k, R k ≠ T
  rtg : ∀ k, R k ≠ tgt

/-- **An exact read of one `natWord` field** (paper §11.4: the substitution machine reads `C`'s and `B_pf`'s
fields). -/
theorem readEx_spec (cap : ℕ) (i : Fin (ns + 1)) (R : FReg → Fin nr) (B T tgt : Fin nr) (hr : ReadRegs R B T tgt)
    (σ : WState ns nr) (pre rest : List Bool) (x : ℕ)
    (hst : σ.st i = pre ++ RepairRepresentation.natWord x ++ rest) (hsh : σ.sh i = pre.length)
    (h0 : ∀ k : FReg, k ≠ .cd → σ.val (R k) = 0) (hB : σ.val B = 0) (hT : σ.val T = 0) (htz : σ.val tgt = 0)
    (hcap : σ.val (R .cd) + 8 * x + 16 ≤ cap) :
    WExec cap (readEx i R B T tgt) σ
      (((σ.seth i (pre.length + (RepairRepresentation.natWord x).length)).setv (R .cd)
        (σ.val (R .cd) + (RepairRepresentation.natWord x).length)).setv tgt x) (readCost x) := by
  have hL : ones (σ.st i) (σ.sh i) = natBitLength x := by rw [hst, hsh]; exact ones_natWord pre rest x
  have hp2 := two_pow_nbl_le x
  have hnb := nbl_le x
  have hlen := natWord_length x
  have e1 := peekW_spec cap i B T hr.bt σ hT (by rw [hB, hL]; omega)
  rw [hB, hL, Nat.zero_add] at e1
  have rbB : ∀ k, B ≠ R k := fun k => Ne.symm (hr.rb k)
  have rtgB : ∀ k, tgt ≠ R k := fun k => Ne.symm (hr.rtg k)
  set σ1 := σ.setv B (natBitLength x) with hσ1
  have hs1 : σ1.st i = σ.st i := by simp [σ1]
  have hh1 : σ1.sh i = σ.sh i := by simp [σ1]
  have hb1 : σ1.val B = natBitLength x := by simp [σ1]
  have hcd1 : σ1.val (R .cd) = σ.val (R .cd) := by simp [σ1, Function.update_apply, hr.rb]
  have e2 := fieldTo_spec cap i R hr.inj B tgt hr.rb hr.rtg σ1
    (fun k hk => by simp [σ1, Function.update_apply, hr.rb k]; exact h0 k hk)
    (by simp [σ1, Function.update_apply, hr.btg.symm, htz])
    (by rw [hcd1, hs1, hh1, hL, hb1, pow_succ]; omega)
  rw [hs1, hh1, hb1, hcd1, hst, hsh, ones_natWord, fieldEnd_natWord, fieldVal_natWord pre rest x _ le_rfl] at e2
  set σ2 := ((σ1.seth i (pre.length + (RepairRepresentation.natWord x).length)).setv (R .cd)
    (σ.val (R .cd) + 2 * natBitLength x + 1)).setv tgt x with hσ2
  have e3 := wclear_spec cap B (natBitLength x) σ2
    (by simp [σ2, σ1, Function.update_apply, hr.rb, rbB, hr.btg]) (by
      simp [σ2, σ1, Function.update_apply, hr.rb, rbB, hr.btg]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl) ?_
  · refine WState.eq ?_ rfl ?_ rfl
    · simp [σ2, σ1]
    · funext r
      simp only [σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases hrB : r = B
      · rw [hrB]; simp [hr.rb, rbB, hr.btg, hB]
      · simp only [hrB, if_false]
        split_ifs <;> first | rfl | omega
  · have hf : fieldCost (natBitLength x) (natBitLength x) ≤ 400 * (2 * x + 4) * (2 * x + 3) := by
      unfold fieldCost
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    unfold readCost
    nlinarith

/-- The cost class of one skipped field. -/
def skipCost (x : ℕ) : ℕ := 1000 * (natBitLength x + 3)

/-- **Skipping one `natWord` field** (guard `0`: nothing is converted; the target stays `0`). -/
theorem skipF_spec (cap : ℕ) (i : Fin (ns + 1)) (R : FReg → Fin nr) (hR : Function.Injective R) (Z J : Fin nr)
    (hZ : ∀ k, R k ≠ Z) (hJ : ∀ k, R k ≠ J) (σ : WState ns nr) (pre rest : List Bool) (x : ℕ)
    (hst : σ.st i = pre ++ RepairRepresentation.natWord x ++ rest) (hsh : σ.sh i = pre.length)
    (h0 : ∀ k : FReg, k ≠ .cd → σ.val (R k) = 0) (hz : σ.val Z = 0) (hj : σ.val J = 0)
    (hcap : σ.val (R .cd) + 2 * natBitLength x + 12 ≤ cap) :
    WExec cap (fieldTo i R Z J) σ
      ((σ.seth i (pre.length + (RepairRepresentation.natWord x).length)).setv (R .cd)
        (σ.val (R .cd) + (RepairRepresentation.natWord x).length)) (skipCost x) := by
  have hL : ones (σ.st i) (σ.sh i) = natBitLength x := by rw [hst, hsh]; exact ones_natWord pre rest x
  have hnb := nbl_le x
  have hlen := natWord_length x
  have e := fieldTo_spec cap i R hR Z J hZ hJ σ h0 hj (by rw [hL, hz]; simp; omega)
  have hfv : fieldVal (σ.st i) (σ.sh i) (σ.val Z) = 0 := by
    rw [hz]; have := fieldVal_lt (σ.st i) (σ.sh i) 0; simpa using this
  rw [hfv, hL] at e
  refine WExec.mono (WExec.cast cap e ?_ le_rfl) ?_
  · refine WState.eq ?_ rfl ?_ rfl
    · rw [hst, hsh, fieldEnd_natWord]; simp
    · funext r; by_cases hrJ : r = J
      · rw [hrJ]; simp [Function.update_apply, Ne.symm (hJ _), hj]
      · simp [Function.update_apply, hrJ, hlen, Nat.add_assoc]
  · rw [hz]; unfold skipCost fieldCost; simp; omega

/-- Skip `K` fields. -/
def skipN (i : Fin (ns + 1)) (R : FReg → Fin nr) (Z J K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (fieldTo i R Z J))

theorem flatMap_take_succ {α : Type} (f : ℕ → List α) (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    (xs.take (k + 1)).flatMap f = (xs.take k).flatMap f ++ f xs[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]; simp

theorem flatMap_split {α : Type} (f : ℕ → List α) (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    xs.flatMap f = (xs.take k).flatMap f ++ f xs[k] ++ (xs.drop (k + 1)).flatMap f := by
  rw [← flatMap_take_succ f xs k hk, ← List.flatMap_append, List.take_append_drop]

/-- **Skipping `k` fields** (paper §11.4: `C`'s oracle-gate arguments, `B`'s nodes before its output index). -/
theorem skipN_spec (cap : ℕ) (i : Fin (ns + 1)) (R : FReg → Fin nr) (hR : Function.Injective R) (Z J K : Fin nr)
    (hZ : ∀ k, R k ≠ Z) (hJ : ∀ k, R k ≠ J) (hK : ∀ k, R k ≠ K) (hKZ : K ≠ Z) (hKJ : K ≠ J)
    (σ : WState ns nr) (pre rest : List Bool) (xs : List ℕ) (V : ℕ) (hV : ∀ x ∈ xs, natBitLength x ≤ V)
    (hst : σ.st i = pre ++ xs.flatMap RepairRepresentation.natWord ++ rest) (hsh : σ.sh i = pre.length)
    (h0 : ∀ k : FReg, k ≠ .cd → σ.val (R k) = 0) (hz : σ.val Z = 0) (hj : σ.val J = 0)
    (hKv : σ.val K = xs.length)
    (hcap : σ.val (R .cd) + (xs.flatMap RepairRepresentation.natWord).length + 2 * V + 12 ≤ cap)
    (hcapK : xs.length ≤ cap) :
    WExec cap (skipN i R Z J K) σ
      (((σ.seth i (pre.length + (xs.flatMap RepairRepresentation.natWord).length)).setv (R .cd)
        (σ.val (R .cd) + (xs.flatMap RepairRepresentation.natWord).length)).setv K 0)
      (xs.length * (1000 * (V + 3) + 4) + 1) := by
  set n := xs.length with hn
  set cd0 := σ.val (R .cd) with hcd0
  let len : ℕ → ℕ := fun k => ((xs.take k).flatMap RepairRepresentation.natWord).length
  let S : ℕ → WState ns nr := fun k =>
    ((σ.seth i (pre.length + len k)).setv (R .cd) (cd0 + len k)).setv K (n - k)
  have hS0 : S 0 = σ := by
    refine WState.eq ?_ rfl ?_ rfl
    · funext y; by_cases hy : y = i
      · rw [hy]; simp [S, len, hsh]
      · simp [S, Function.update_apply, hy]
    · funext r; by_cases hrK : r = K
      · rw [hrK]; simp [S, hKv]
      · by_cases hrc : r = R .cd
        · rw [hrc]; simp [S, len, hK, hcd0]
        · simp [S, Function.update_apply, hrK, hrc]
  have hSn : S n = ((σ.seth i (pre.length + (xs.flatMap RepairRepresentation.natWord).length)).setv (R .cd)
      (σ.val (R .cd) + (xs.flatMap RepairRepresentation.natWord).length)).setv K 0 := by
    simp only [S, len, hn, List.take_length, Nat.sub_self, hcd0]
  have hlenle : ∀ k ≤ n, len k ≤ (xs.flatMap RepairRepresentation.natWord).length := by
    intro k _
    simp only [len]
    conv_rhs => rw [← List.take_append_drop k xs]
    rw [List.flatMap_append, List.length_append]
    omega
  have e := UnionMachine.Round.wloop cap K (fieldTo i R Z J) (1000 * (V + 3)) n S
    (fun k _ => by simp [S]) hcapK
    (fun k hk => by
      have hk' : k < xs.length := hk
      have hxk := hV xs[k] (List.getElem_mem hk')
      have hstk : ((S k).setv K (n - k - 1)).st i = (pre ++ (xs.take k).flatMap RepairRepresentation.natWord) ++
          RepairRepresentation.natWord xs[k] ++ ((xs.drop (k + 1)).flatMap RepairRepresentation.natWord ++ rest) := by
        simp only [S, WState.setv_st, WState.seth_st, hst]
        rw [flatMap_split _ xs k hk']; simp only [List.append_assoc]
      have hl1 := hlenle (k + 1) (by omega)
      have hlk : len (k + 1) = len k + (RepairRepresentation.natWord xs[k]).length := by
        simp only [len]; rw [flatMap_take_succ _ xs k hk', List.length_append]
      have hlk0 : len k = ((xs.take k).flatMap RepairRepresentation.natWord).length := rfl
      have hKr : ∀ j, K ≠ R j := fun j => Ne.symm (hK j)
      have e1 := skipF_spec cap i R hR Z J hZ hJ ((S k).setv K (n - k - 1))
        (pre ++ (xs.take k).flatMap RepairRepresentation.natWord) _ xs[k] hstk
        (by simp [S, len])
        (fun j hj' => by simp [S, Function.update_apply, hK, hR.eq_iff, hj']; exact h0 j hj')
        (by simp [S, Function.update_apply, hKZ.symm, (hZ _).symm, hz])
        (by simp [S, Function.update_apply, hKJ.symm, (hJ _).symm, hj])
        (by simp [S, Function.update_apply, hK]; rw [hlk] at hl1; omega)
      refine WExec.mono (WExec.cast cap e1 ?_ le_rfl) (by unfold skipCost; omega)
      refine WState.eq ?_ rfl ?_ rfl
      · funext y; by_cases hy : y = i
        · rw [hy]; simp only [S, WState.setv_sh, WState.seth_sh, Function.update_self, List.length_append]
          rw [hlk]; omega
        · simp [S, Function.update_apply, hy]
      · funext r; by_cases hrK : r = K
        · rw [hrK]; simp [S, hK, hKr]; omega
        · by_cases hrc : r = R .cd
          · rw [hrc]; simp [S, hK, hKr]; rw [hlk, natWord_length]; omega
          · simp [S, Function.update_apply, hrK, hrc])
  rw [hS0, hSn] at e
  exact e

/-- Copy `K` cells from `i` (head on) to the end of `o`. -/
def copyCells (i o : Fin (ns + 1)) (K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (.ifs i (.wr o true) (.wr o false)) (.seq (.fwd i) (.fwd o))))

/-- **Copying cells** (paper §11.4: the machine keeps `ℓ`'s field for its oracle gates). -/
theorem copyCells_spec (cap : ℕ) (i o : Fin (ns + 1)) (hio : i ≠ o) (K : Fin nr) (σ : WState ns nr) (k : ℕ)
    (hK : σ.val K = k) (ho : σ.sh o = (σ.st o).length) (hcap : k ≤ cap) :
    WExec cap (copyCells i o K) σ
      ((((σ.seth i (σ.sh i + k)).sets o (σ.st o ++ List.ofFn (fun j : Fin k => readTapeBit (σ.st i) (σ.sh i + j)))).seth
        o (σ.sh o + k)).setv K 0) (k * 10 + 1) := by
  let cells : ℕ → List Bool := fun m => List.ofFn (fun j : Fin m => readTapeBit (σ.st i) (σ.sh i + j))
  let S : ℕ → WState ns nr := fun m =>
    (((σ.seth i (σ.sh i + m)).sets o (σ.st o ++ cells m)).seth o (σ.sh o + m)).setv K (k - m)
  have hS0 : S 0 = σ := by
    refine WState.eq ?_ ?_ ?_ rfl
    · funext y; by_cases hy : y = o
      · rw [hy]; simp [S]
      · by_cases hy2 : y = i
        · rw [hy2]; simp [S, hio]
        · simp [S, Function.update_apply, hy, hy2]
    · funext y; by_cases hy : y = o
      · rw [hy]; simp [S, cells]
      · simp [S, Function.update_apply, hy]
    · funext r; by_cases hr : r = K
      · rw [hr]; simp [S, hK]
      · simp [S, Function.update_apply, hr]
  have hcells : ∀ m, cells (m + 1) = cells m ++ [readTapeBit (σ.st i) (σ.sh i + m)] := by
    intro m; simp only [cells]; rw [List.ofFn_succ_last]; simp
  have e := UnionMachine.Round.wloop cap K (.seq (.ifs i (.wr o true) (.wr o false)) (.seq (.fwd i) (.fwd o))) 6 k S
    (fun m _ => by simp [S]) hcap
    (fun m hm => by
      set τ := (S m).setv K (k - m - 1) with hτ
      set b := readTapeBit (σ.st i) (σ.sh i + m) with hb
      have hbit : wbit τ i = b := by simp [wbit, τ, S, Function.update_apply, Ne.symm hio, hio]; exact hb.symm
      have hlen : (τ.st o).length = τ.sh o := by simp [τ, S, cells, ho]
      have e1 : WExec cap (.ifs i (.wr o true) (.wr o false)) τ (τ.sets o (τ.st o ++ [b])) 2 := by
        have hw : ∀ c, writeTapeBit (τ.st o) (τ.sh o) c = τ.st o ++ [c] := by
          intro c; rw [← hlen]; exact FinalPass.Tm.writeTapeBit_end' _ c
        cases hbv : b
        · have := WExec.wr (cap := cap) o false τ; rw [hw] at this
          exact WExec.ifsF (by rw [hbit, hbv]) this
        · have := WExec.wr (cap := cap) o true τ; rw [hw] at this
          exact WExec.ifsT (by rw [hbit, hbv]) this
      have e2 := WExec.fwd (cap := cap) i (τ.sets o (τ.st o ++ [b]))
      have e3 := WExec.fwd (cap := cap) o ((τ.sets o (τ.st o ++ [b])).seth i ((τ.sets o (τ.st o ++ [b])).sh i + 1))
      refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl) (by omega)
      refine WState.eq ?_ ?_ ?_ rfl
      · funext y; by_cases hy : y = o
        · rw [hy]; simp [τ, S, Function.update_apply, hio, Ne.symm hio]; ring
        · by_cases hy2 : y = i
          · rw [hy2]; simp [τ, S, hio, hy]; ring
          · simp [τ, S, Function.update_apply, hy, hy2]
      · funext y; by_cases hy : y = o
        · rw [hy]; simp [τ, S, hcells]; exact hb
        · simp [τ, S, Function.update_apply, hy]
      · funext r; by_cases hr : r = K
        · rw [hr]; simp [τ, S]; omega
        · simp [τ, S, Function.update_apply, hr])
  rw [hS0] at e
  refine WExec.cast cap e ?_ (by ring_nf; omega)
  simp [S, cells]

/-! ## Dispatch and comparison -/

/-- A dispatch on the value of `r` (`r` consumed): `Ps[v]` runs when `r = v`. -/
def caseL (r : Fin nr) : List (WM ns nr) → WM ns nr
  | [] => .skip
  | [P] => P
  | P :: Q :: Ps => .ifr r (.seq (.dec r) (caseL r (Q :: Ps))) P

theorem caseL_spec (cap : ℕ) (r : Fin nr) :
    ∀ (Ps : List (WM ns nr)) (v : ℕ) (hv : v < Ps.length) (σ τ : WState ns nr) (n : ℕ), σ.val r = v →
      σ.val r ≤ cap → WExec cap (Ps[v]) (σ.setv r 0) τ n → WExec cap (caseL r Ps) σ τ (n + 3 * v + 1)
  | [], v, hv, _, _, _, _, _, _ => by simp at hv
  | [P], 0, _, σ, τ, n, hr, _, h => by
    have e : σ.setv r 0 = σ := by rw [← hr, wsetv_same]
    rw [e] at h
    exact WExec.mono h (by omega)
  | [P], v + 1, hv, _, _, _, _, _, _ => by simp at hv
  | P :: Q :: Ps, 0, _, σ, τ, n, hr, _, h => by
    have e : σ.setv r 0 = σ := by rw [← hr, wsetv_same]
    rw [e] at h
    exact WExec.mono (WExec.ifrF hr h) (by omega)
  | P :: Q :: Ps, v + 1, hv, σ, τ, n, hr, hc, h => by
    have e1 := WExec.dec (cap := cap) r σ hc
    rw [hr, Nat.add_sub_cancel] at e1
    have ih := caseL_spec cap r (Q :: Ps) v (by simp at hv ⊢; omega) (σ.setv r v) τ n (by simp) (by simp; omega)
      (by rw [wsetv_setv]; simpa using h)
    exact WExec.mono (WExec.ifrT (by omega) (WExec.seq e1 ih)) (by omega)

/-- `F := [A < B]` from `F = 0` (`A`, `B` kept; `G`, `H`, `Z`, `T` scratch). -/
def ltWM (A B G H Z F T : Fin nr) : WM ns nr :=
  .seq (addTo A G T) (.seq (.inc G) (.seq (addTo B H T) (.seq (.whr G (.seq (.dec G) (.ifr H (.dec H) (WM.setF Z))))
    (.seq (WM.clear H) (.ifr Z (.dec Z) (.inc F))))))

/-- **Comparison** `F := [A < B]` (paper §11.4: `C`'s input `i` is `D`'s input when `i < q`; `B`'s input `j` reads an
argument wire when `j < ℓ`). -/
theorem ltWM_spec (cap : ℕ) (A B G H Z F T : Fin nr) (hR : [A, B, G, H, Z, F, T].Nodup) (σ : WState ns nr)
    (hG : σ.val G = 0) (hH : σ.val H = 0) (hZ : σ.val Z = 0) (hF : σ.val F = 0) (hT : σ.val T = 0)
    (hcap : σ.val A + σ.val B + 3 ≤ cap) :
    WExec cap (ltWM A B G H Z F T) σ (σ.setv F (if σ.val A < σ.val B then 1 else 0))
      (30 * (σ.val A + σ.val B) + 40) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5⟩, ⟨g1, g2, g3, g4⟩, ⟨h1, h2, h3⟩, ⟨z1, z2⟩, f1⟩ := hR
  have n1 := Ne.symm a1; have n2 := Ne.symm a2; have n3 := Ne.symm a3; have n4 := Ne.symm a4
  have n5 := Ne.symm a5; have n6 := Ne.symm a6; have n7 := Ne.symm b1; have n8 := Ne.symm b2
  have n9 := Ne.symm b3; have n10 := Ne.symm b4; have n11 := Ne.symm b5; have n12 := Ne.symm g1
  have n13 := Ne.symm g2; have n14 := Ne.symm g3; have n15 := Ne.symm g4; have n16 := Ne.symm h1
  have n17 := Ne.symm h2; have n18 := Ne.symm h3; have n19 := Ne.symm z1; have n20 := Ne.symm z2
  have n21 := Ne.symm f1
  generalize ha : σ.val A = a at hcap ⊢
  generalize hb : σ.val B = b at hcap ⊢
  have e1 := addTo_spec cap A G T a2 a6 g4 σ hT (by omega) (by omega)
  rw [ha, hG, Nat.zero_add] at e1
  have e1b := WExec.inc (cap := cap) G (σ.setv G a) (by simp; omega)
  rw [show (σ.setv G a).setv G ((σ.setv G a).val G + 1) = σ.setv G (a + 1) by simp [wsetv_setv]] at e1b
  have e2 := addTo_spec cap B H T b2 b5 h3 (σ.setv G (a + 1)) (by simp [Function.update_apply, n15, hT])
    (by simp [Function.update_apply, b1, hb]; omega) (by simp [Function.update_apply, b1, g1, n12, hH, hb]; omega)
  have hv : ((σ.setv G (a + 1)).setv H ((σ.setv G (a + 1)).val H + (σ.setv G (a + 1)).val B)) =
      (σ.setv G (a + 1)).setv H b := by simp [Function.update_apply, b1, n12, hH, hb]
  rw [hv, show (σ.setv G (a + 1)).val B = b by simp [Function.update_apply, b1, hb]] at e2
  have e3 := guard_step cap G H Z g1 g2 h1 ((σ.setv G (a + 1)).setv H b) (a + 1) b (by simp [Function.update_apply, g1])
    (by simp) (by simp [Function.update_apply, n16, n13, hZ]) (by omega)
  have e4 := wclear_spec cap H (b - (a + 1)) ((((σ.setv G (a + 1)).setv H b).setv G 0).setv H (b - (a + 1)) |>.setv Z
    (if b < a + 1 then 1 else 0)) (by simp [Function.update_apply, h1]) (by simp [Function.update_apply, h1]; omega)
  set σ4 := ((((((σ.setv G (a + 1)).setv H b).setv G 0).setv H (b - (a + 1))).setv Z
    (if b < a + 1 then 1 else 0)).setv H 0) with hσ4
  have hσ4Z : σ4.val Z = if b < a + 1 then 1 else 0 := by simp [σ4, Function.update_apply, n16]
  have hσ4F : σ4.val F = 0 := by simp [σ4, Function.update_apply, n17, n19, n14, hF]
  have e5 : WExec cap (.ifr Z (.dec Z) (.inc F)) σ4 (σ.setv F (if a < b then 1 else 0)) 4 := by
    by_cases hab : b < a + 1
    · have := WExec.dec (cap := cap) Z σ4 (by rw [hσ4Z, if_pos hab]; omega)
      refine WExec.mono (WExec.cast cap (WExec.ifrT (by rw [hσ4Z, if_pos hab]; omega) this) ?_ le_rfl) (by omega)
      rw [hσ4Z, if_pos hab, if_neg (by omega)]
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [σ4, WState.setv_val, Function.update_apply]
      by_cases hrZ : r = Z
      · rw [hrZ]; simp [z1, hZ, n16, n13, n19, n20]
      · by_cases hrH : r = H
        · rw [hrH]; simp [hrZ, hH, n17, h2, h1, g1, n16, n12]
        · by_cases hrG : r = G
          · rw [hrG]; simp [hrZ, hrH, hG, n14, g3, g2, g1]
          · by_cases hrF : r = F
            · rw [hrF]; simp [hrZ, hrH, hrG, hF, z1, h2, g3, n21, n17, n14, f1, n19]
            · simp [hrZ, hrH, hrG, hrF]
    · have := WExec.inc (cap := cap) F σ4 (by rw [hσ4F]; omega)
      refine WExec.mono (WExec.cast cap (WExec.ifrF (by rw [hσ4Z, if_neg hab]) this) ?_ le_rfl) (by omega)
      rw [hσ4F, if_pos (by omega)]
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [σ4, WState.setv_val, Function.update_apply]
      by_cases hrF : r = F
      · rw [hrF]; simp [z1, h2, g3, n21, n17, n14]
      · by_cases hrZ : r = Z
        · rw [hrZ]; simp [hrF, hZ, hab, z2, n16, n13]
        · by_cases hrH : r = H
          · rw [hrH]; simp [hrF, hrZ, hH, h3, h2, h1, n12]
          · by_cases hrG : r = G
            · rw [hrG]; simp [hrF, hrZ, hrH, hG, g3, g2, g1]
            · simp [hrF, hrZ, hrH, hrG]
  refine WExec.mono (WExec.seq e1 (WExec.seq e1b (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))))) ?_
  omega

end NearCubicGates.Close.Succinct
