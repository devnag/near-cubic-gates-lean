import Proof.Wire_3_5.UnionMachineRoundBits

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord intWord)
open NearCubicWires.WireExponent3_5 (ratWord)

/-! ## The counted loop -/

section Loop
variable {ns nr : ℕ} (cap : ℕ)

/-- **The counted loop** `while K ≠ 0 { K--; body }`, from a per-round body spec along a state sequence `S` with
`K = n − k` at round `k`. -/
theorem wloop (K : Fin nr) (body : WM ns nr) (c n : ℕ) (S : ℕ → WState ns nr)
    (hK : ∀ k ≤ n, (S k).val K = n - k) (hcap : n ≤ cap)
    (hbody : ∀ k < n, WExec cap body ((S k).setv K (n - k - 1)) (S (k + 1)) c) :
    WExec cap (.whr K (.seq (.dec K) body)) (S 0) (S n) (n * (c + 4) + 1) := by
  have key : ∀ m j, j + m = n → WExec cap (.whr K (.seq (.dec K) body)) (S j) (S n) (m * (c + 4) + 1) := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj; subst hj
      exact WExec.mono (WExec.whrF (by rw [hK j le_rfl]; omega)) (by omega)
    | succ m ih =>
      intro j hj
      have hKj : (S j).val K = n - j := hK j (by omega)
      have h1 := WExec.dec (cap := cap) K (S j) (by omega)
      rw [hKj] at h1
      have h2 := hbody j (by omega)
      have h3 := ih (j + 1) (by omega)
      exact WExec.mono (WExec.whrT (by omega) (WExec.seq h1 h2) h3) (by nlinarith)
  simpa using key n 0 (by omega)

end Loop

/-! ## The bank of the rounding program -/

/-- The rounding program's state: streams `0` (output), `1` (remainder), `2` (denominator); 14 registers. -/
abbrev RS := WState 2 14

local notation "sO" => (0 : Fin 3)
local notation "sR" => (1 : Fin 3)
local notation "sD" => (2 : Fin 3)
local notation "rF" => (0 : Fin 14)
local notation "rRC" => (1 : Fin 14)
local notation "rQ" => (2 : Fin 14)
local notation "rT" => (3 : Fin 14)
local notation "rSG" => (4 : Fin 14)
local notation "rAL" => (5 : Fin 14)
local notation "rBL" => (6 : Fin 14)
local notation "rOC" => (7 : Fin 14)
local notation "rK" => (8 : Fin 14)
local notation "rPC" => (9 : Fin 14)
local notation "rMP" => (10 : Fin 14)
local notation "rMN" => (11 : Fin 14)
local notation "rRMC" => (12 : Fin 14)
local notation "rDNC" => (13 : Fin 14)

/-- Close an equality of rounding-bank states. -/
syntax "req" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| req) => `(tactic| req [])
  | `(tactic| req [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | rfl
        | (funext x
           fin_cases x <;>
             simp (config := { decide := true }) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_sh,
               WState.seth_sh, WState.sets_sh, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply,
               $ts,*] <;> omega)
        | simp [$ts,*]))

variable (cap : ℕ)

/-! ## Moving registers -/

/-- `B += A; C += A; A := 0` (a two-target move). -/
def move2 (A B C : Fin 14) : WM 2 14 := .whr A (.seq (.dec A) (.seq (.inc B) (.inc C)))

theorem move2_spec (A B C : Fin 14) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (σ : RS)
    (hB : σ.val B + σ.val A ≤ cap) (hC : σ.val C + σ.val A ≤ cap) :
    WExec cap (move2 A B C) σ (((σ.setv A 0).setv B (σ.val B + σ.val A)).setv C (σ.val C + σ.val A))
      (σ.val A * (9 + 4) + 1) := by
  set n := σ.val A with hn
  let S : ℕ → RS := fun k => ((σ.setv A (n - k)).setv B (σ.val B + k)).setv C (σ.val C + k)
  have hS0 : S 0 = σ := by
    simp only [S]
    req [hn, Function.update_of_ne hAB, Function.update_of_ne hAC, Function.update_of_ne hBC,
      Function.update_of_ne hAB.symm, Function.update_of_ne hAC.symm, Function.update_of_ne hBC.symm]
  have hSn : S n = ((σ.setv A 0).setv B (σ.val B + n)).setv C (σ.val C + n) := by simp [S]
  have h := wloop cap A (.seq (.inc B) (.inc C)) 9 n S
    (fun k _ => by simp [S, Function.update_apply, hAB, hAC, hBC, hAB.symm, hAC.symm, hBC.symm]) (by omega)
    (fun k hk => by
      have h1 := WExec.inc (cap := cap) B ((S k).setv A (n - k - 1))
        (by simp [S, Function.update_apply, hAB, hAC, hBC, hAB.symm, hAC.symm, hBC.symm]; omega)
      have h2 := WExec.inc (cap := cap) C (((S k).setv A (n - k - 1)).setv B
          (((S k).setv A (n - k - 1)).val B + 1))
        (by simp [S, Function.update_apply, hAB, hAC, hBC, hAB.symm, hAC.symm, hBC.symm]; omega)
      refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
      simp only [S]
      refine WState.eq rfl rfl ?_ rfl
      funext x
      simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega)
  rw [hS0, hSn] at h
  exact h

/-! ## Tape reading -/

theorem readTapeBit_app (pre rest : List Bool) (k : ℕ) :
    readTapeBit (pre ++ rest) (pre.length + k) = readTapeBit rest k := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  congr 2; omega

theorem readTapeBit_cons (b : Bool) (rest : List Bool) (k : ℕ) :
    readTapeBit (b :: rest) (k + 1) = readTapeBit rest k := by
  unfold readTapeBit; simp

theorem readTapeBit_zero (b : Bool) (rest : List Bool) : readTapeBit (b :: rest) 0 = b := by
  unfold readTapeBit; simp

theorem readTapeBit_rep_true (n : ℕ) (rest : List Bool) (k : ℕ) (hk : k < n) :
    readTapeBit (List.replicate n true ++ rest) k = true := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hk)]
  simp [hk]

theorem readTapeBit_list (l rest : List Bool) (i : ℕ) (hi : i < l.length) :
    readTapeBit (l ++ rest) i = l[i] := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  simp [hi]

theorem frameP_append (l1 l2 : List Bool) : frameP (l1 ++ l2) = frameP l1 ++ frameP l2 := by
  simp [frameP, List.flatMap_append]

theorem frameP_take_succ (l : List Bool) (k : ℕ) (hk : k < l.length) :
    frameP (l.take (k + 1)) = frameP (l.take k) ++ [true, l[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, frameP_append]
  simp [frameP]

/-! ## Copying a raw word into a framed word -/

/-- One round of the copy: append the marker and the scanned bit of `src` to `dst`, advance `src`. -/
def copyBody (src dst : Fin 3) (dc oc : Fin 14) : WM 2 14 :=
  .seq (emitC dst dc true) (.seq (.ifs src (emitC dst dc true) (emitC dst dc false)) (WM.fwdC src oc))

theorem copyBody_spec (src dst : Fin 3) (dc oc : Fin 14) (hsd : src ≠ dst) (hdo : dc ≠ oc) (σ : RS)
    (hsh : σ.sh dst = (σ.st dst).length) (hdc : σ.val dc + 2 ≤ cap) (hoc : σ.val oc + 1 ≤ cap) :
    WExec cap (copyBody src dst dc oc) σ
      (((((σ.sets dst (σ.st dst ++ [true, readTapeBit (σ.st src) (σ.sh src)])).seth dst (σ.sh dst + 2)).setv dc
        (σ.val dc + 2)).seth src (σ.sh src + 1)).setv oc (σ.val oc + 1)) 22 := by
  have h1 := emitC_spec cap dst dc true σ hsh (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : RS, τ = ((σ.sets dst (σ.st dst ++ [true])).seth dst (σ.sh dst + 1)).setv dc
      (σ.val dc + 1) := ⟨_, rfl⟩
  rw [← hσ1] at h1
  have hs1 : σ1.sh dst = (σ1.st dst).length := by rw [hσ1]; simp [hsh]
  have hb : wbit σ1 src = readTapeBit (σ.st src) (σ.sh src) := by
    rw [hσ1]; simp [wbit, Function.update_apply, hsd]
  have hv1 : σ1.val dc = σ.val dc + 1 := by rw [hσ1]; simp
  have h2 : WExec cap (.ifs src (emitC dst dc true) (emitC dst dc false)) σ1
      (((σ1.sets dst (σ1.st dst ++ [readTapeBit (σ.st src) (σ.sh src)])).seth dst (σ1.sh dst + 1)).setv dc
        (σ1.val dc + 1)) 8 := by
    cases hr : readTapeBit (σ.st src) (σ.sh src)
    · exact WExec.ifsF (by rw [hb, hr]) (emitC_spec cap dst dc false σ1 hs1 (by omega))
    · exact WExec.ifsT (by rw [hb, hr]) (emitC_spec cap dst dc true σ1 hs1 (by omega))
  obtain ⟨σ2, hσ2⟩ : ∃ τ : RS, τ = ((σ1.sets dst (σ1.st dst ++ [readTapeBit (σ.st src) (σ.sh src)])).seth dst
      (σ1.sh dst + 1)).setv dc (σ1.val dc + 1) := ⟨_, rfl⟩
  rw [← hσ2] at h2
  have hv2 : σ2.val oc = σ.val oc := by
    rw [hσ2, hσ1]; simp [Function.update_apply, hdo.symm]
  have h3 := wfwdC_spec cap src oc σ2 (by omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  clear h1 h2 h3 hs1 hb hv1 hv2
  subst hσ2 hσ1
  refine WState.eq ?_ ?_ ?_ rfl
  · funext x
    simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega
  · funext x
    simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · funext x
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all <;> omega

/-- The copy loop's state after `k` rounds. -/
def copyState (src dst : Fin 3) (dc oc K : Fin 14) (bs : List Bool) (σ : RS) (k : ℕ) : RS :=
  (((((σ.sets dst (σ.st dst ++ frameP (bs.take k))).seth dst (σ.sh dst + 2 * k)).setv dc (σ.val dc + 2 * k)).seth src
    (σ.sh src + k)).setv oc (σ.val oc + k)).setv K (bs.length - k)

theorem copyLoop_spec (src dst : Fin 3) (dc oc K : Fin 14) (hsd : src ≠ dst) (hdo : dc ≠ oc) (hdK : dc ≠ K)
    (hoK : oc ≠ K) (bs : List Bool) (σ : RS) (hK : σ.val K = bs.length) (hsh : σ.sh dst = (σ.st dst).length)
    (hbits : ∀ i (hi : i < bs.length), readTapeBit (σ.st src) (σ.sh src + i) = bs[i])
    (hdc : σ.val dc + 2 * bs.length ≤ cap) (hoc : σ.val oc + bs.length ≤ cap) (hKc : bs.length ≤ cap) :
    WExec cap (.whr K (.seq (.dec K) (copyBody src dst dc oc))) σ (copyState src dst dc oc K bs σ bs.length)
      (bs.length * 26 + 1) := by
  have h0 : copyState src dst dc oc K bs σ 0 = σ := by
    unfold copyState
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  have h := wloop cap K (copyBody src dst dc oc) 22 bs.length (copyState src dst dc oc K bs σ)
    (fun k _ => by simp [copyState]) hKc (fun k hk => by
      set τ := (copyState src dst dc oc K bs σ k).setv K (bs.length - k - 1) with hτ
      have hτsh : τ.sh dst = (τ.st dst).length := by
        simp [τ, copyState, Function.update_apply, hsd, hsd.symm, hsh, hk.le]
      have hτb : readTapeBit (τ.st src) (τ.sh src) = bs[k] := by
        simp only [τ, copyState, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          WState.sets_sh, Function.update_apply, hsd, if_false, if_true]
        exact hbits k hk
      have hb := copyBody_spec cap src dst dc oc hsd hdo τ hτsh
        (by simp [τ, copyState, Function.update_apply, hdK, hdo]; omega)
        (by simp [τ, copyState, Function.update_apply, hoK, hdo.symm]; omega)
      rw [hτb] at hb
      refine WExec.cast cap hb ?_ le_rfl
      simp only [τ, copyState]
      refine WState.eq ?_ ?_ ?_ rfl
      · funext x
        simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all <;> omega
      · funext x
        simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [frameP_take_succ bs k hk]
      · funext x
        simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all <;> omega)
  rw [h0] at h
  exact WExec.mono h (by omega)

/-! ## Register copies and the padding loop -/

/-- `K += A` (`A` restored through `T = 0`). -/
def copyU (A K : Fin 14) : WM 2 14 := .seq (WM.move A rT) (move2 rT A K)

theorem copyU_spec (A K : Fin 14) (hAK : A ≠ K) (hAT : A ≠ rT) (hKT : K ≠ rT) (σ : RS) (hT : σ.val rT = 0)
    (hK : σ.val K + σ.val A ≤ cap) (hA : σ.val A ≤ cap) :
    WExec cap (copyU A K) σ (σ.setv K (σ.val K + σ.val A)) (20 * σ.val A + 3) := by
  have h1 := wmove_spec cap A rT hAT (σ.val A) σ rfl hA (by omega)
  have h2 := move2_spec cap rT A K hAT.symm hKT.symm hAK ((σ.setv A 0).setv rT (σ.val rT + σ.val A))
    (by simp [Function.update_apply, hAT]; omega) (by simp [Function.update_apply, hKT, hAK.symm]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp [Function.update_apply, hT]; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext x
  simp only [WState.setv_val, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- `K −= A` (`A` restored through `T = 0`), for `A ≤ K`. -/
def subU (K A : Fin 14) : WM 2 14 := .seq (WM.move A rT) (.whr rT (.seq (.dec rT) (.seq (.dec K) (.inc A))))

theorem subU_spec (K A : Fin 14) (hAK : A ≠ K) (hAT : A ≠ rT) (hKT : K ≠ rT) (σ : RS) (hT : σ.val rT = 0)
    (hAK' : σ.val A ≤ σ.val K) (hK : σ.val K ≤ cap) (hA : σ.val A ≤ cap) :
    WExec cap (subU K A) σ (σ.setv K (σ.val K - σ.val A)) (20 * σ.val A + 3) := by
  have h1 := wmove_spec cap A rT hAT (σ.val A) σ rfl hA (by omega)
  set n := σ.val A with hn
  let S : ℕ → RS := fun k => ((σ.setv A k).setv rT (n - k)).setv K (σ.val K - k)
  have hS0 : S 0 = (σ.setv A 0).setv rT (σ.val rT + σ.val A) := by
    simp only [S]
    refine WState.eq rfl rfl ?_ rfl
    funext x
    simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have h2 := wloop cap rT (.seq (.dec K) (.inc A)) 5 n S
    (fun k _ => by simp [S, Function.update_apply, hKT.symm]) (by omega)
    (fun k hk => by
      have e1 := WExec.dec (cap := cap) K ((S k).setv rT (n - k - 1))
        (by simp [S, Function.update_apply, hKT]; omega)
      have e2 := WExec.inc (cap := cap) A (((S k).setv rT (n - k - 1)).setv K
          (((S k).setv rT (n - k - 1)).val K - 1))
        (by simp [S, Function.update_apply, hAK, hAT]; omega)
      refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
      simp only [S]
      refine WState.eq rfl rfl ?_ rfl
      funext x
      simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega)
  rw [← hS0] at h1
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  simp only [S]
  refine WState.eq rfl rfl ?_ rfl
  funext x
  simp only [WState.setv_val, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- One round of the zero padding: append the framed bit `0`. -/
def padBody (dst : Fin 3) (dc : Fin 14) : WM 2 14 := .seq (emitC dst dc true) (emitC dst dc false)

theorem padBody_spec (dst : Fin 3) (dc : Fin 14) (σ : RS) (hsh : σ.sh dst = (σ.st dst).length)
    (hdc : σ.val dc + 2 ≤ cap) :
    WExec cap (padBody dst dc) σ (((σ.sets dst (σ.st dst ++ [true, false])).seth dst (σ.sh dst + 2)).setv dc
      (σ.val dc + 2)) 15 := by
  have h1 := emitC_spec cap dst dc true σ hsh (by omega)
  have h2 := emitC_spec cap dst dc false
    (((σ.sets dst (σ.st dst ++ [true])).seth dst (σ.sh dst + 1)).setv dc (σ.val dc + 1)) (by simp [hsh])
    (by simp; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  refine WState.eq ?_ ?_ ?_ rfl
  · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> simp_all <;> omega
  · funext x; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all
  · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp_all <;> omega

/-- The padding loop's state after `k` rounds. -/
def padState (dst : Fin 3) (dc K : Fin 14) (n : ℕ) (σ : RS) (k : ℕ) : RS :=
  (((σ.sets dst (σ.st dst ++ frameP (List.replicate k false))).seth dst (σ.sh dst + 2 * k)).setv dc
    (σ.val dc + 2 * k)).setv K (n - k)

theorem padLoop_spec (dst : Fin 3) (dc K : Fin 14) (hdK : dc ≠ K) (n : ℕ) (σ : RS) (hK : σ.val K = n)
    (hsh : σ.sh dst = (σ.st dst).length) (hdc : σ.val dc + 2 * n ≤ cap) (hKc : n ≤ cap) :
    WExec cap (.whr K (.seq (.dec K) (padBody dst dc))) σ (padState dst dc K n σ n) (n * 19 + 1) := by
  have h0 : padState dst dc K n σ 0 = σ := by
    unfold padState
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  have h := wloop cap K (padBody dst dc) 15 n (padState dst dc K n σ)
    (fun k _ => by simp [padState]) hKc (fun k hk => by
      have hb := padBody_spec cap dst dc ((padState dst dc K n σ k).setv K (n - k - 1))
        (by simp [padState, hsh]) (by simp [padState, Function.update_apply, hdK]; omega)
      refine WExec.cast cap hb ?_ le_rfl
      simp only [padState]
      refine WState.eq ?_ ?_ ?_ rfl
      · funext x
        simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all <;> omega
      · funext x
        simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [List.replicate_succ', frameP_append, frameP]
      · funext x
        simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all <;> omega)
  rw [h0] at h
  exact h

/-! ## The printed answer's word -/

section Word
variable (v : ℚ)

/-- The numerator's bit length `a`, the denominator's `b`, and their words. -/
abbrev la : ℕ := natBitLength v.num.natAbs
abbrev lb : ℕ := natBitLength v.den
abbrev nbits : List Bool := binary (la v) v.num.natAbs
abbrev dbits : List Bool := binary (lb v) v.den
abbrev sgn : Bool := decide (v.num < 0)

@[simp] theorem take_nbits : (nbits v).take (la v) = nbits v := List.take_of_length_le (by simp)
@[simp] theorem take_dbits : (dbits v).take (lb v) = dbits v := List.take_of_length_le (by simp)

theorem ratWord_split : ratWord v = ([sgn v] ++ List.replicate (la v) true ++ [false] ++ nbits v) ++
    (List.replicate (lb v) true ++ [false] ++ dbits v) := by
  simp only [ratWord, intWord, natWord_eq]
  simp

theorem rw_len1 : ([sgn v] ++ List.replicate (la v) true ++ [false] ++ nbits v).length = 2 * la v + 2 := by
  simp; omega

theorem readTapeBit_append (l1 l2 : List Bool) (k : ℕ) :
    readTapeBit (l1 ++ l2) k = if k < l1.length then readTapeBit l1 k else readTapeBit l2 (k - l1.length) := by
  unfold readTapeBit
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]

theorem readTapeBit_rep (n k : ℕ) (b : Bool) (hk : k < n) : readTapeBit (List.replicate n b) k = b := by
  unfold readTapeBit; simp [hk]

theorem readTapeBit_single (b : Bool) : readTapeBit [b] 0 = b := rfl

theorem readTapeBit_get (l : List Bool) (i : ℕ) (hi : i < l.length) : readTapeBit l i = l[i] := by
  unfold readTapeBit; simp [hi]

theorem rw_sign : readTapeBit (ratWord v) 0 = sgn v := by
  rw [ratWord_split]; simp [readTapeBit]

theorem rw_ones_a (k : ℕ) (hk : k < la v) : readTapeBit (ratWord v) (1 + k) = true := by
  rw [ratWord_split]
  simp only [readTapeBit_append, List.length_append, List.length_replicate, List.length_singleton]
  split_ifs <;> first | omega | (rw [readTapeBit_rep _ _ _ (by omega)])

theorem rw_end_a : readTapeBit (ratWord v) (1 + la v) = false := by
  rw [ratWord_split]
  simp only [readTapeBit_append, List.length_append, List.length_replicate, List.length_singleton]
  split_ifs <;> first | omega | (rw [show 1 + la v - (1 + la v) = 0 by omega]; rfl)

theorem rw_nbits (i : ℕ) (hi : i < (nbits v).length) :
    readTapeBit (ratWord v) (la v + 2 + i) = (nbits v)[i] := by
  rw [ratWord_split]
  simp only [readTapeBit_append, List.length_append, List.length_replicate, List.length_singleton]
  have hl : (nbits v).length = la v := by simp
  split_ifs <;> first | omega | (rw [readTapeBit_get _ _ (by omega)]; congr 1; omega)

theorem rw_ones_b (k : ℕ) (hk : k < lb v) : readTapeBit (ratWord v) (2 * la v + 2 + k) = true := by
  rw [ratWord_split]
  simp only [readTapeBit_append, List.length_append, List.length_replicate, List.length_singleton,
    binary_length]
  split_ifs <;> first | omega | (rw [readTapeBit_rep _ _ _ (by omega)])

theorem rw_end_b : readTapeBit (ratWord v) (2 * la v + 2 + lb v) = false := by
  rw [ratWord_split]
  simp only [readTapeBit_append, List.length_append, List.length_replicate, List.length_singleton,
    binary_length]
  split_ifs <;> first | omega | (rw [show 2 * la v + 2 + lb v - (1 + la v + 1 + la v) - lb v = 0 by omega]; rfl)

theorem rw_dbits (j : ℕ) (hj : j < (dbits v).length) :
    readTapeBit (ratWord v) (2 * la v + lb v + 3 + j) = (dbits v)[j] := by
  rw [ratWord_split]
  simp only [readTapeBit_append, List.length_append, List.length_replicate, List.length_singleton,
    binary_length]
  have hl : (dbits v).length = lb v := by simp
  split_ifs <;> first | omega | (rw [readTapeBit_get _ _ (by omega)]; congr 1; omega)

end Word

/-! ## The reading program -/

/-! ## The reading program -/

/-- Sign, numerator length, `K := a`. -/
def parse1 : WM 2 14 :=
  .seq (.ifs sO (.inc rSG) .skip) <| .seq (WM.fwdC sO rOC) <| .seq (WM.readU sO rOC rAL) (copyU rAL rK)

/-- Numerator bits, denominator length, `K := b`, denominator bits. -/
def parse2 : WM 2 14 :=
  .seq (.whr rK (.seq (.dec rK) (copyBody sO sR rRMC rOC))) <| .seq (WM.readU sO rOC rBL) <|
  .seq (copyU rBL rK) (.whr rK (.seq (.dec rK) (copyBody sO sD rDNC rOC)))

/-- The denominator's two padding zeros and end marker. -/
def parse3 : WM 2 14 := .seq (padBody sD rDNC) <| .seq (padBody sD rDNC) (.wr sD false)

/-- `K := b + 2 − a`, the numerator's padding zeros and end marker. -/
def parse4 : WM 2 14 :=
  .seq (copyU rBL rK) <| .seq (.inc rK) <| .seq (.inc rK) <| .seq (subU rK rAL) <|
  .seq (.whr rK (.seq (.dec rK) (padBody sR rRMC))) (.wr sR false)

/-- Both heads back. -/
def parse5 : WM 2 14 := .seq (WM.rewind sR rRMC) (WM.rewind sD rDNC)

/-- **The reading program**: sign, numerator length, numerator bits, denominator length, denominator bits, the
denominator's two padding zeros, the numerator's `b + 2 − a` padding zeros, both end markers, both heads back. -/
def parseP : WM 2 14 := .seq parse1 <| .seq parse2 <| .seq parse3 (.seq parse4 parse5)

/-- A rounding-bank state with the answer's word on stream `0`. -/
def st3 (v : ℚ) (h0 h1 h2 : ℕ) (t1 t2 : List Bool) (vals : Fin 14 → ℕ) (c : Bool) : RS :=
  ⟨![h0, h1, h2], ![ratWord v, t1, t2], vals, c⟩

/-- The reading program's entry: the answer's word, blank remainder and denominator, registers `0` but `PC = p`. -/
def parseIn (v : ℚ) (p : ℕ) (c : Bool) : RS := st3 v 0 0 0 [] [] ![0, 0, 0, 0, 0, 0, 0, 0, 0, p, 0, 0, 0, 0] c

/-- The reading program's exit. -/
def parseOut (v : ℚ) (p : ℕ) (c : Bool) : RS :=
  st3 v (2 * la v + 2 * lb v + 3) 0 0 (frameP (binary (lb v + 2) v.num.natAbs) ++ [false])
    (frameP (binary (lb v + 2) v.den) ++ [false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 0, 0] c

def pS4 (v : ℚ) (p : ℕ) (c : Bool) : RS :=
  st3 v (la v + 2) (0) (0) ([]) ([])
    ![0, 0, 0, 0, (sgn v).toNat, la v, 0, la v + 2, la v, p, 0, 0, 0, 0] c
def pS8 (v : ℚ) (p : ℕ) (c : Bool) : RS :=
  st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v) (frameP (nbits v)) (frameP (dbits v))
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v, 2 * lb v] c
def pS11 (v : ℚ) (p : ℕ) (c : Bool) : RS :=
  st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v, 2 * lb v + 4] c
def pS17 (v : ℚ) (p : ℕ) (c : Bool) : RS :=
  st3 v (2 * la v + 2 * lb v + 3) (2 * la v + 2 * (lb v + 2 - la v)) (2 * lb v + 4) (frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false) ++ [false]) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v + 2 * (lb v + 2 - la v), 2 * lb v + 4] c

/-- Close an equality of explicit rounding-bank states. -/
syntax "rlit" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rlit) => `(tactic| rlit [])
  | `(tactic| rlit [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ rfl <;> funext x <;> fin_cases x <;>
      simp [Function.update_apply, st3, parseIn, parseOut, pS4, pS8, pS11, pS17, copyState, padState, $ts,*] <;>
      omega))

variable (v : ℚ) (p : ℕ) (c : Bool)

theorem parse1_spec (hcap : 4 * lb v + 10 ≤ cap) (hab : la v ≤ lb v + 2) :
    WExec cap parse1 (parseIn v p c) (pS4 v p c) (31 * la v + 22) := by
  have e1 : WExec cap (.ifs sO (.inc rSG) .skip) (parseIn v p c)
      (st3 v 0 0 0 [] [] ![0, 0, 0, 0, (sgn v).toNat, 0, 0, 0, 0, p, 0, 0, 0, 0] c) 4 := by
    have hbit : wbit (parseIn v p c) sO = sgn v := by
      simp [wbit, parseIn, st3, rw_sign]
    cases hs : sgn v
    · have hk : WExec cap (.skip : WM 2 14) (parseIn v p c)
          (st3 v 0 0 0 [] [] ![0, 0, 0, 0, (false).toNat, 0, 0, 0, 0, p, 0, 0, 0, 0] c) 0 :=
        WExec.cast cap (WExec.skip _) (by rlit) le_rfl
      exact WExec.mono (WExec.ifsF (by rw [hbit, hs]) hk) (by omega)
    · exact WExec.ifsT (by rw [hbit, hs])
        (WExec.cast cap (WExec.inc (cap := cap) rSG _ (by simp [parseIn, st3]; omega)) (by rlit) le_rfl)
  have e2 := wfwdC_spec cap sO rOC (st3 v 0 0 0 [] [] ![0, 0, 0, 0, (sgn v).toNat, 0, 0, 0, 0, p, 0, 0, 0, 0] c)
    (by simp [st3]; omega)
  have e2' : WExec cap (WM.fwdC sO rOC) _ (st3 v 1 0 0 [] [] ![0, 0, 0, 0, (sgn v).toNat, 0, 0, 1, 0, p, 0, 0, 0, 0] c)
      5 := WExec.cast cap e2 (by rlit) le_rfl
  have e3 := wreadU_spec cap sO rOC rAL (by decide) (la v)
    (st3 v 1 0 0 [] [] ![0, 0, 0, 0, (sgn v).toNat, 0, 0, 1, 0, p, 0, 0, 0, 0] c)
    (fun k hk => by simp only [st3]; simpa [add_comm] using rw_ones_a v k hk)
    (by simp only [st3]; simpa [add_comm] using rw_end_a v) (by simp [st3]; omega) (by simp [st3]; omega)
  have e3' : WExec cap (WM.readU sO rOC rAL) _
      (st3 v (la v + 2) 0 0 [] [] ![0, 0, 0, 0, (sgn v).toNat, la v, 0, la v + 2, 0, p, 0, 0, 0, 0] c)
      (11 * la v + 7) := WExec.cast cap e3 (by rlit) le_rfl
  have e4 := copyU_spec cap rAL rK (by decide) (by decide) (by decide)
    (st3 v (la v + 2) 0 0 [] [] ![0, 0, 0, 0, (sgn v).toNat, la v, 0, la v + 2, 0, p, 0, 0, 0, 0] c) (by simp [st3])
    (by simp [st3]; omega) (by simp [st3]; omega)
  have e4' : WExec cap (copyU rAL rK) _ (pS4 v p c) (20 * la v + 3) :=
    WExec.cast cap e4 (by rlit) (by simp [st3])
  exact WExec.mono (e1.seq (e2'.seq (e3'.seq e4'))) (by omega)

theorem parse2_spec (hcap : 4 * lb v + 10 ≤ cap) (hab : la v ≤ lb v + 2) :
    WExec cap parse2 (pS4 v p c) (pS8 v p c) (26 * la v + 57 * lb v + 15) := by
  have e5 := copyLoop_spec cap sO sR rRMC rOC rK (by decide) (by decide) (by decide) (by decide) (nbits v)
    (pS4 v p c) (by simp [pS4, st3]) (by simp [pS4, st3])
    (fun i hi => by simp only [pS4, st3]; simpa [add_comm] using rw_nbits v i hi)
    (by simp [pS4, st3]; omega) (by simp [pS4, st3]; omega) (by simp; omega)
  have e5' : WExec cap (.whr rK (.seq (.dec rK) (copyBody sO sR rRMC rOC))) _
      (st3 v (2 * la v + 2) (2 * la v) 0 (frameP (nbits v)) []
        ![0, 0, 0, 0, (sgn v).toNat, la v, 0, 2 * la v + 2, 0, p, 0, 0, 2 * la v, 0] c) (la v * 26 + 1) :=
    WExec.cast cap e5 (by rlit) (by simp)
  have e6 := wreadU_spec cap sO rOC rBL (by decide) (lb v)
    (st3 v (2 * la v + 2) (2 * la v) 0 (frameP (nbits v)) []
        ![0, 0, 0, 0, (sgn v).toNat, la v, 0, 2 * la v + 2, 0, p, 0, 0, 2 * la v, 0] c)
    (fun k hk => by simp only [st3]; simpa using rw_ones_b v k hk)
    (by simp only [st3]; simpa using rw_end_b v) (by simp [st3]; omega) (by simp [st3]; omega)
  have e6' : WExec cap (WM.readU sO rOC rBL) _
      (st3 v (2 * la v + lb v + 3) (2 * la v) 0 (frameP (nbits v)) []
        ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + lb v + 3, 0, p, 0, 0, 2 * la v, 0] c) (11 * lb v + 7) :=
    WExec.cast cap e6 (by rlit) le_rfl
  have e7 := copyU_spec cap rBL rK (by decide) (by decide) (by decide)
    (st3 v (2 * la v + lb v + 3) (2 * la v) 0 (frameP (nbits v)) []
        ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + lb v + 3, 0, p, 0, 0, 2 * la v, 0] c) (by simp [st3])
    (by simp [st3]; omega) (by simp [st3]; omega)
  have e7' : WExec cap (copyU rBL rK) _
      (st3 v (2 * la v + lb v + 3) (2 * la v) 0 (frameP (nbits v)) []
        ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + lb v + 3, lb v, p, 0, 0, 2 * la v, 0] c) (20 * lb v + 3) :=
    WExec.cast cap e7 (by rlit) (by simp [st3])
  have e8 := copyLoop_spec cap sO sD rDNC rOC rK (by decide) (by decide) (by decide) (by decide) (dbits v)
    (st3 v (2 * la v + lb v + 3) (2 * la v) 0 (frameP (nbits v)) []
        ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + lb v + 3, lb v, p, 0, 0, 2 * la v, 0] c) (by simp [st3])
    (by simp [st3]) (fun j hj => by simp only [st3]; simpa using rw_dbits v j hj)
    (by simp [st3]; omega) (by simp [st3]; omega) (by simp; omega)
  have e8' : WExec cap (.whr rK (.seq (.dec rK) (copyBody sO sD rDNC rOC))) _ (pS8 v p c) (lb v * 26 + 1) :=
    WExec.cast cap e8 (by rlit) (by simp)
  exact WExec.mono (e5'.seq (e6'.seq (e7'.seq e8'))) (by omega)

theorem parse3_spec (hcap : 4 * lb v + 10 ≤ cap) :
    WExec cap parse3 (pS8 v p c) (pS11 v p c) 33 := by
  have e9 := padBody_spec cap sD rDNC (pS8 v p c) (by simp [pS8, st3]) (by simp [pS8, st3]; omega)
  have e9' : WExec cap (padBody sD rDNC) _
      (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 2) (frameP (nbits v)) (frameP (dbits v) ++ [true, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v, 2 * lb v + 2] c)
      15 := WExec.cast cap e9 (by rlit) le_rfl
  have e10 := padBody_spec cap sD rDNC
    (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 2) (frameP (nbits v)) (frameP (dbits v) ++ [true, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v, 2 * lb v + 2] c) (by simp [st3]) (by simp [st3]; omega)
  have e10' : WExec cap (padBody sD rDNC) _
      (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v, 2 * lb v + 4] c)
      15 := WExec.cast cap e10 (by rlit) le_rfl
  have e11 := WExec.wr (cap := cap) sD false
    (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v, 2 * lb v + 4] c)
  have hw11 : writeTapeBit (frameP (dbits v) ++ [true, false, true, false]) (2 * lb v + 4) false =
      frameP (dbits v) ++ [true, false, true, false, false] := by
    rw [show 2 * lb v + 4 = (frameP (dbits v) ++ [true, false, true, false]).length by simp, writeTapeBit_end']
    simp
  have e11' : WExec cap (.wr sD false) _ (pS11 v p c) 1 := WExec.cast cap e11 (by rlit [hw11]) le_rfl
  exact WExec.mono (e9'.seq (e10'.seq e11')) (by omega)

theorem parse4_spec (hcap : 4 * lb v + 10 ≤ cap) (hab : la v ≤ lb v + 2) :
    WExec cap parse4 (pS11 v p c) (pS17 v p c) (20 * la v + 20 * lb v + 19 * (lb v + 2 - la v) + 19) := by
  have e12 := copyU_spec cap rBL rK (by decide) (by decide) (by decide) (pS11 v p c) (by simp [pS11, st3])
    (by simp [pS11, st3]; omega) (by simp [pS11, st3]; omega)
  have e12' : WExec cap (copyU rBL rK) _
      (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, lb v, p, 0, 0, 2 * la v, 2 * lb v + 4] c) (20 * lb v + 3) :=
    WExec.cast cap e12 (by rlit) (by simp [pS11, st3])
  have e13 := WExec.inc (cap := cap) rK
    (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, lb v, p, 0, 0, 2 * la v, 2 * lb v + 4] c) (by simp [st3]; omega)
  have e13' : WExec cap (.inc rK) _
      (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, lb v + 1, p, 0, 0, 2 * la v, 2 * lb v + 4] c) 3 :=
    WExec.cast cap e13 (by rlit) le_rfl
  have e14 := WExec.inc (cap := cap) rK
    (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, lb v + 1, p, 0, 0, 2 * la v, 2 * lb v + 4] c) (by simp [st3]; omega)
  have e14' : WExec cap (.inc rK) _
      (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, lb v + 2, p, 0, 0, 2 * la v, 2 * lb v + 4] c) 3 :=
    WExec.cast cap e14 (by rlit) le_rfl
  have e15 := subU_spec cap rK rAL (by decide) (by decide) (by decide)
    (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, lb v + 2, p, 0, 0, 2 * la v, 2 * lb v + 4] c) (by simp [st3])
    (by simp [st3]; omega) (by simp [st3]; omega) (by simp [st3]; omega)
  have e15' : WExec cap (subU rK rAL) _
      (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, (lb v + 2 - la v), p, 0, 0, 2 * la v, 2 * lb v + 4] c) (20 * la v + 3) :=
    WExec.cast cap e15 (by rlit) (by simp [st3])
  have e16 := padLoop_spec cap sR rRMC rK (by decide) (lb v + 2 - la v)
    (st3 v (2 * la v + 2 * lb v + 3) (2 * la v) (2 * lb v + 4) (frameP (nbits v)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, (lb v + 2 - la v), p, 0, 0, 2 * la v, 2 * lb v + 4] c) (by simp [st3]) (by simp [st3])
    (by simp [st3]; omega) (by omega)
  have e16' : WExec cap (.whr rK (.seq (.dec rK) (padBody sR rRMC))) _
      (st3 v (2 * la v + 2 * lb v + 3) (2 * la v + 2 * (lb v + 2 - la v)) (2 * lb v + 4) (frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v + 2 * (lb v + 2 - la v), 2 * lb v + 4] c)
      ((lb v + 2 - la v) * 19 + 1) := WExec.cast cap e16 (by rlit) le_rfl
  have e17 := WExec.wr (cap := cap) sR false
    (st3 v (2 * la v + 2 * lb v + 3) (2 * la v + 2 * (lb v + 2 - la v)) (2 * lb v + 4) (frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false)) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 2 * la v + 2 * (lb v + 2 - la v), 2 * lb v + 4] c)
  have hw17 : writeTapeBit (frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false)) (2 * la v + 2 * (lb v + 2 - la v)) false = frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false) ++ [false] := by
    rw [show 2 * la v + 2 * (lb v + 2 - la v) = (frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false)).length by simp, writeTapeBit_end']
  have e17' : WExec cap (.wr sR false) _ (pS17 v p c) 1 := WExec.cast cap e17 (by rlit [hw17]) le_rfl
  exact WExec.mono (e12'.seq (e13'.seq (e14'.seq (e15'.seq (e16'.seq e17'))))) (by omega)

theorem parse5_spec (hcap : 4 * lb v + 10 ≤ cap) (hab : la v ≤ lb v + 2) :
    WExec cap parse5 (pS17 v p c) (parseOut v p c) (10 * la v + 10 * (lb v + 2 - la v) + 10 * lb v + 23) := by
  have e18 := wrewind_spec cap sR rRMC (2 * la v + 2 * (lb v + 2 - la v)) (pS17 v p c) (by simp [pS17, st3])
    (by simp [pS17, st3]; omega)
  have e18' : WExec cap (WM.rewind sR rRMC) _
      (st3 v (2 * la v + 2 * lb v + 3) (0) (2 * lb v + 4) (frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false) ++ [false]) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 0, 2 * lb v + 4] c) (5 * (2 * la v + 2 * (lb v + 2 - la v)) + 1) :=
    WExec.cast cap e18 (by rlit) le_rfl
  have e19 := wrewind_spec cap sD rDNC (2 * lb v + 4)
    (st3 v (2 * la v + 2 * lb v + 3) (0) (2 * lb v + 4) (frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false) ++ [false]) (frameP (dbits v) ++ [true, false, true, false, false])
    ![0, 0, 0, 0, (sgn v).toNat, la v, lb v, 2 * la v + 2 * lb v + 3, 0, p, 0, 0, 0, 2 * lb v + 4] c) (by simp [st3]) (by simp [st3]; omega)
  have hR : frameP (nbits v) ++ frameP (List.replicate (lb v + 2 - la v) false) ++ [false] = frameP (binary (lb v + 2) v.num.natAbs) ++ [false] := by
    rw [← frameP_append, bits_pad, show la v + (lb v + 2 - la v) = lb v + 2 by omega]
  have hD : frameP (dbits v) ++ [true, false, true, false, false] = frameP (binary (lb v + 2) v.den) ++ [false] := by
    rw [← bits_pad v.den 2]; simp [frameP_append, frameP]
  have e19' : WExec cap (WM.rewind sD rDNC) _ (parseOut v p c) (5 * (2 * lb v + 4) + 1) :=
    WExec.cast cap e19 (by rlit [hR, hD]) le_rfl
  exact WExec.mono (e18'.seq e19') (by omega)

/-- **The reading program reads the answer**: from the answer's word (with `|num| < 4·den`) to the framed
numerator and denominator words of width `b + 2`, the sign in `SG`, `PC` kept. -/
theorem parse_spec (hv : v.num.natAbs < 4 * v.den) (hcap : 4 * lb v + 10 ≤ cap) :
    WExec cap parseP (parseIn v p c) (parseOut v p c) (250 * (lb v + 2)) := by
  have hab : la v ≤ lb v + 2 := natBitLength_num_le _ _ hv
  exact WExec.mono ((parse1_spec cap v p c hcap hab).seq ((parse2_spec cap v p c hcap hab).seq
    ((parse3_spec cap v p c hcap).seq ((parse4_spec cap v p c hcap hab).seq (parse5_spec cap v p c hcap hab)))))
    (by omega)

end NearCubicWires.WireExponent3_5.UnionMachine.Round
