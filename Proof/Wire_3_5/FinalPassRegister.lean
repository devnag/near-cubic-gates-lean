import Proof.Wire_3_5.FinalPassProgram

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-- A unary register of capacity `cap` holding `v`: a `false` sentinel, `v` ones, then blanks up to cell `cap`. -/
def regTape (cap v : ℕ) : List Bool := false :: (List.replicate v true ++ List.replicate (cap - v) false)

theorem regTape_zero (cap : ℕ) : regTape cap 0 = List.replicate (cap + 1) false := by
  simp [regTape, List.replicate_succ]

theorem regTape_read (cap v : ℕ) : readTapeBit (regTape cap v) v = decide (v ≠ 0) := by
  unfold readTapeBit regTape
  cases v with
  | zero => simp
  | succ v =>
    simp only [List.getD_cons_succ, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, decide_true]
    rw [List.getD_append _ _ _ _ (by simp)]
    simp

theorem writeTapeBit_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem regTape_inc (cap v : ℕ) (hv : v < cap) : writeTapeBit (regTape cap v) (v + 1) true = regTape cap (v + 1) := by
  unfold regTape
  obtain ⟨m, hm⟩ : ∃ m, cap - v = m + 1 := ⟨cap - v - 1, by omega⟩
  have e1 : false :: (List.replicate v true ++ List.replicate (cap - v) false) =
      (false :: List.replicate v true) ++ false :: List.replicate m false := by
    rw [hm, List.replicate_succ]; simp
  have e2 : (false :: List.replicate v true).length = v + 1 := by simp
  rw [e1, ← e2, writeTapeBit_mid, e2]
  have e3 : cap - (v + 1) = m := by omega
  rw [e3]
  simp [List.replicate_succ']

theorem regTape_dec (cap v : ℕ) (hv : v ≤ cap) : writeTapeBit (regTape cap v) v false = regTape cap (v - 1) := by
  cases v with
  | zero => simp [regTape, writeTapeBit]
  | succ v =>
    unfold regTape
    have e1 : false :: (List.replicate (v + 1) true ++ List.replicate (cap - (v + 1)) false) =
        (false :: List.replicate v true) ++ true :: List.replicate (cap - (v + 1)) false := by
      simp [List.replicate_succ']
    have e2 : (false :: List.replicate v true).length = v + 1 := by simp
    rw [e1, ← e2, writeTapeBit_mid, e2]
    have e3 : cap - v = cap - (v + 1) + 1 := by omega
    simp only [Nat.add_sub_cancel]
    rw [e3]
    simp [List.replicate_succ]

/-! ## The abstract state and the layout -/

/-- Stream heads, register values and the result cell. -/
structure RState (ns nr : ℕ) where
  sh : Fin (ns + 1) → ℕ
  val : Fin nr → ℕ
  cell : Bool

variable {ns nr : ℕ}

def RState.setv (σ : RState ns nr) (r : Fin nr) (x : ℕ) : RState ns nr := ⟨σ.sh, Function.update σ.val r x, σ.cell⟩
def RState.seth (σ : RState ns nr) (i : Fin (ns + 1)) (x : ℕ) : RState ns nr := ⟨Function.update σ.sh i x, σ.val, σ.cell⟩
def RState.setc (σ : RState ns nr) (c : Bool) : RState ns nr := ⟨σ.sh, σ.val, c⟩

@[simp] theorem RState.setv_val (σ : RState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).val = Function.update σ.val r x :=
  rfl
@[simp] theorem RState.setv_sh (σ : RState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).sh = σ.sh := rfl
@[simp] theorem RState.setv_cell (σ : RState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).cell = σ.cell := rfl
@[simp] theorem RState.seth_val (σ : RState ns nr) (i : Fin (ns + 1)) (x : ℕ) : (σ.seth i x).val = σ.val := rfl
@[simp] theorem RState.seth_sh (σ : RState ns nr) (i : Fin (ns + 1)) (x : ℕ) :
    (σ.seth i x).sh = Function.update σ.sh i x := rfl
@[simp] theorem RState.seth_cell (σ : RState ns nr) (i : Fin (ns + 1)) (x : ℕ) : (σ.seth i x).cell = σ.cell := rfl
@[simp] theorem RState.setc_val (σ : RState ns nr) (c : Bool) : (σ.setc c).val = σ.val := rfl
@[simp] theorem RState.setc_sh (σ : RState ns nr) (c : Bool) : (σ.setc c).sh = σ.sh := rfl
@[simp] theorem RState.setc_cell (σ : RState ns nr) (c : Bool) : (σ.setc c).cell = c := rfl

/-- The tape of stream `i`. -/
def sTape (i : Fin (ns + 1)) : Fin (ns + 2 + nr) := ⟨if i.val = 0 then 0 else i.val + 1, by split <;> omega⟩

/-- The result cell. -/
def cTape : Fin (ns + 2 + nr) := ⟨1, by omega⟩

/-- The tape of register `r`. -/
def rTape (r : Fin nr) : Fin (ns + 2 + nr) := ⟨ns + 2 + r.val, by omega⟩

/-- The role of a tape. -/
inductive Role (ns nr : ℕ) where
  | stream (i : Fin (ns + 1))
  | cell
  | reg (r : Fin nr)

def role (j : Fin (ns + 2 + nr)) : Role ns nr :=
  if h0 : j.val = 0 then .stream 0
  else if h1 : j.val = 1 then .cell
  else if h2 : j.val ≤ ns + 1 then .stream ⟨j.val - 1, by omega⟩
  else .reg ⟨j.val - (ns + 2), by omega⟩

theorem role_sTape (i : Fin (ns + 1)) : role (sTape (nr := nr) i) = .stream i := by
  unfold role
  by_cases hi : i.val = 0
  · have e : i = 0 := Fin.ext hi
    subst e
    have : (sTape (nr := nr) (0 : Fin (ns + 1))).val = 0 := by simp [sTape]
    rw [dif_pos this]
  · have hv : (sTape (nr := nr) i).val = i.val + 1 := by simp [sTape, hi]
    have hi2 := i.isLt
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
    congr 1
    exact Fin.ext (by simp only [hv]; omega)

theorem role_cTape : role (cTape (ns := ns) (nr := nr)) = .cell := by
  have : (cTape (ns := ns) (nr := nr)).val = 1 := rfl
  unfold role
  rw [dif_neg (by omega), dif_pos this]

theorem role_rTape (r : Fin nr) : role (rTape (ns := ns) r) = .reg r := by
  have hv : (rTape (ns := ns) r).val = ns + 2 + r.val := rfl
  unfold role
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
  congr 1
  exact Fin.ext (by simp only [hv]; omega)

theorem role_stream {j : Fin (ns + 2 + nr)} {i : Fin (ns + 1)} (h : role j = .stream i) : j = sTape i := by
  unfold role at h
  by_cases h0 : j.val = 0
  · rw [dif_pos h0] at h
    injection h with h'
    subst h'
    exact Fin.ext (by simp [sTape, h0])
  · rw [dif_neg h0] at h
    by_cases h1 : j.val = 1
    · rw [dif_pos h1] at h; cases h
    · rw [dif_neg h1] at h
      by_cases h2 : j.val ≤ ns + 1
      · rw [dif_pos h2] at h
        injection h with h'
        subst h'
        apply Fin.ext
        show j.val = if j.val - 1 = 0 then 0 else j.val - 1 + 1
        split_ifs with h3 <;> omega
      · rw [dif_neg h2] at h; cases h

theorem role_cell {j : Fin (ns + 2 + nr)} (h : role j = .cell) : j = cTape := by
  unfold role at h
  by_cases h0 : j.val = 0
  · rw [dif_pos h0] at h; cases h
  · rw [dif_neg h0] at h
    by_cases h1 : j.val = 1
    · exact Fin.ext h1
    · rw [dif_neg h1] at h
      by_cases h2 : j.val ≤ ns + 1
      · rw [dif_pos h2] at h; cases h
      · rw [dif_neg h2] at h; cases h

theorem role_reg {j : Fin (ns + 2 + nr)} {r : Fin nr} (h : role j = .reg r) : j = rTape r := by
  unfold role at h
  by_cases h0 : j.val = 0
  · rw [dif_pos h0] at h; cases h
  · rw [dif_neg h0] at h
    by_cases h1 : j.val = 1
    · rw [dif_pos h1] at h; cases h
    · rw [dif_neg h1] at h
      by_cases h2 : j.val ≤ ns + 1
      · rw [dif_pos h2] at h; cases h
      · rw [dif_neg h2] at h
        injection h with h'
        subst h'
        apply Fin.ext
        show j.val = ns + 2 + (j.val - (ns + 2))
        omega

/-- The encoded bank of an abstract state, with stream contents `inp` and register capacity `cap`. -/
def enc (inp : Fin (ns + 1) → List Bool) (cap : ℕ) (σ : RState ns nr) : Bank (ns + 2 + nr) where
  H := fun j => match role j with
    | .stream i => σ.sh i
    | .cell => 0
    | .reg r => σ.val r
  A := fun j => match role j with
    | .stream i => inp i
    | .cell => [σ.cell]
    | .reg r => regTape cap (σ.val r)

variable (inp : Fin (ns + 1) → List Bool) (cap : ℕ)

@[simp] theorem enc_H_s (σ : RState ns nr) (i : Fin (ns + 1)) : (enc inp cap σ).H (sTape i) = σ.sh i := by
  simp [enc, role_sTape]
@[simp] theorem enc_A_s (σ : RState ns nr) (i : Fin (ns + 1)) : (enc inp cap σ).A (sTape i) = inp i := by
  simp [enc, role_sTape]
@[simp] theorem enc_H_c (σ : RState ns nr) : (enc inp cap σ).H cTape = 0 := by simp [enc, role_cTape]
@[simp] theorem enc_A_c (σ : RState ns nr) : (enc inp cap σ).A cTape = [σ.cell] := by simp [enc, role_cTape]
@[simp] theorem enc_H_r (σ : RState ns nr) (r : Fin nr) : (enc inp cap σ).H (rTape r) = σ.val r := by
  simp [enc, role_rTape]
@[simp] theorem enc_A_r (σ : RState ns nr) (r : Fin nr) : (enc inp cap σ).A (rTape r) = regTape cap (σ.val r) := by
  simp [enc, role_rTape]

/-- The scanned bit of a stream. -/
def sbit (σ : RState ns nr) (i : Fin (ns + 1)) : Bool := readTapeBit (inp i) (σ.sh i)

theorem bit_s (σ : RState ns nr) (i : Fin (ns + 1)) : (enc inp cap σ).bit (sTape i) = sbit inp σ i := by
  simp [Bank.bit, sbit]

theorem bit_r (σ : RState ns nr) (r : Fin nr) : (enc inp cap σ).bit (rTape r) = decide (σ.val r ≠ 0) := by
  simp [Bank.bit, regTape_read]

/-! ## Register programs -/

/-- Unary register programs over streams `0..ns` and `nr` registers. -/
inductive RM (ns nr : ℕ) where
  | skip : RM ns nr
  | inc (r : Fin nr) : RM ns nr
  | dec (r : Fin nr) : RM ns nr
  | fwd (i : Fin (ns + 1)) : RM ns nr
  | bwd (i : Fin (ns + 1)) : RM ns nr
  | setc (v : Bool) : RM ns nr
  | seq (P Q : RM ns nr) : RM ns nr
  | ifr (r : Fin nr) (P Q : RM ns nr) : RM ns nr
  | ifs (i : Fin (ns + 1)) (P Q : RM ns nr) : RM ns nr
  | whr (r : Fin nr) (P : RM ns nr) : RM ns nr
  | whs (i : Fin (ns + 1)) (P : RM ns nr) : RM ns nr

/-- Move one tape. -/
def moveAt {t : ℕ} (k : Fin t) (mv : HeadMove) : Fin t → HeadMove := fun j => if j = k then mv else .stay
/-- Write one tape. -/
def writeAt {t : ℕ} (k : Fin t) (v : Bool) : Fin t → Option Bool := fun j => if j = k then some v else none

/-- The compiled structured program. -/
def RM.toProg : RM ns nr → Prog (ns + 2 + nr)
  | .skip => .skip
  | .inc r => .seq (.act (fun _ => none) (moveAt (rTape r) .right)) (.act (writeAt (rTape r) true) (fun _ => .stay))
  | .dec r => .act (writeAt (rTape r) false) (moveAt (rTape r) .left)
  | .fwd i => .act (fun _ => none) (moveAt (sTape i) .right)
  | .bwd i => .act (fun _ => none) (moveAt (sTape i) .left)
  | .setc v => .act (writeAt cTape v) (fun _ => .stay)
  | .seq P Q => .seq P.toProg Q.toProg
  | .ifr r P Q => .ite (rTape r) P.toProg Q.toProg
  | .ifs i P Q => .ite (sTape i) P.toProg Q.toProg
  | .whr r P => .loop (rTape r) P.toProg
  | .whs i P => .loop (sTape i) P.toProg

/-- **Big-step semantics of register programs**, with the costs of the compiled machine. -/
inductive RExec : RM ns nr → RState ns nr → RState ns nr → ℕ → Prop where
  | skip (σ : RState ns nr) : RExec .skip σ σ 0
  | inc (r : Fin nr) (σ : RState ns nr) : σ.val r < cap → RExec (.inc r) σ (σ.setv r (σ.val r + 1)) 3
  | dec (r : Fin nr) (σ : RState ns nr) : σ.val r ≤ cap → RExec (.dec r) σ (σ.setv r (σ.val r - 1)) 1
  | fwd (i : Fin (ns + 1)) (σ : RState ns nr) : RExec (.fwd i) σ (σ.seth i (σ.sh i + 1)) 1
  | bwd (i : Fin (ns + 1)) (σ : RState ns nr) : RExec (.bwd i) σ (σ.seth i (σ.sh i - 1)) 1
  | setc (v : Bool) (σ : RState ns nr) : RExec (.setc v) σ (σ.setc v) 1
  | seq {P Q : RM ns nr} {σ τ ρ : RState ns nr} {n k : ℕ} : RExec P σ τ n → RExec Q τ ρ k →
      RExec (.seq P Q) σ ρ (n + 1 + k)
  | ifrT {r : Fin nr} {P Q : RM ns nr} {σ τ : RState ns nr} {n : ℕ} : σ.val r ≠ 0 → RExec P σ τ n →
      RExec (.ifr r P Q) σ τ (n + 1)
  | ifrF {r : Fin nr} {P Q : RM ns nr} {σ τ : RState ns nr} {n : ℕ} : σ.val r = 0 → RExec Q σ τ n →
      RExec (.ifr r P Q) σ τ (n + 1)
  | ifsT {i : Fin (ns + 1)} {P Q : RM ns nr} {σ τ : RState ns nr} {n : ℕ} : sbit inp σ i = true → RExec P σ τ n →
      RExec (.ifs i P Q) σ τ (n + 1)
  | ifsF {i : Fin (ns + 1)} {P Q : RM ns nr} {σ τ : RState ns nr} {n : ℕ} : sbit inp σ i = false → RExec Q σ τ n →
      RExec (.ifs i P Q) σ τ (n + 1)
  | whrF {r : Fin nr} {P : RM ns nr} {σ : RState ns nr} : σ.val r = 0 → RExec (.whr r P) σ σ 1
  | whrT {r : Fin nr} {P : RM ns nr} {σ τ ρ : RState ns nr} {n k : ℕ} : σ.val r ≠ 0 → RExec P σ τ n →
      RExec (.whr r P) τ ρ k → RExec (.whr r P) σ ρ (n + 2 + k)
  | whsF {i : Fin (ns + 1)} {P : RM ns nr} {σ : RState ns nr} : sbit inp σ i = false → RExec (.whs i P) σ σ 1
  | whsT {i : Fin (ns + 1)} {P : RM ns nr} {σ τ ρ : RState ns nr} {n k : ℕ} : sbit inp σ i = true →
      RExec P σ τ n → RExec (.whs i P) τ ρ k → RExec (.whs i P) σ ρ (n + 2 + k)
  | mono {P : RM ns nr} {σ τ : RState ns nr} {n m : ℕ} : RExec P σ τ n → n ≤ m → RExec P σ τ m

/-! ## Soundness -/

theorem Bank.ext' {t : ℕ} {b c : Bank t} (hH : ∀ j, b.H j = c.H j) (hA : ∀ j, b.A j = c.A j) : b = c := by
  cases b; cases c
  simp only [Bank.mk.injEq]
  exact ⟨funext hH, funext hA⟩

theorem act_move_s (σ : RState ns nr) (i : Fin (ns + 1)) (mv : HeadMove) :
    (enc inp cap σ).act (fun _ => none) (moveAt (sTape i) mv) = enc inp cap (σ.seth i (mv.apply (σ.sh i))) := by
  apply Bank.ext'
  · intro j
    simp only [Bank.act, moveAt]
    by_cases hj : j = sTape i
    · subst hj; simp
    · rw [if_neg hj]
      simp only [HeadMove.apply, enc, RState.seth_sh]
      cases hr : role j with
      | stream i' =>
        have hne : i' ≠ i := by
          rintro rfl; exact hj (role_stream hr)
        simp [Function.update_of_ne hne]
      | cell => rfl
      | reg r => rfl
  · intro j; rfl

theorem RExec.exec {P : RM ns nr} {σ τ : RState ns nr} {n : ℕ} (h : RExec inp cap P σ τ n) :
    Exec P.toProg (enc inp cap σ) (enc inp cap τ) n := by
  induction h with
  | skip σ => exact Exec.skip _
  | inc r σ hv =>
    have h1 := Exec.act (enc inp cap σ) (fun _ => none) (moveAt (rTape r) .right)
    have h2 := Exec.act ((enc inp cap σ).act (fun _ => none) (moveAt (rTape r) .right)) (writeAt (rTape r) true)
      (fun _ => .stay)
    have e : ((enc inp cap σ).act (fun _ => none) (moveAt (rTape r) .right)).act (writeAt (rTape r) true)
        (fun _ => .stay) = enc inp cap (σ.setv r (σ.val r + 1)) := by
      apply Bank.ext'
      · intro j
        simp only [Bank.act, moveAt, HeadMove.apply]
        by_cases hj : j = rTape r
        · subst hj; simp
        · rw [if_neg hj]
          simp only [enc, RState.setv_val, RState.setv_sh]
          cases hr : role j with
          | stream i => rfl
          | cell => rfl
          | reg r' =>
            have hne : r' ≠ r := by rintro rfl; exact hj (role_reg hr)
            simp [Function.update_of_ne hne]
      · intro j
        simp only [Bank.act, moveAt, writeAt, HeadMove.apply]
        by_cases hj : j = rTape r
        · subst hj; simp [regTape_inc cap _ hv]
        · rw [if_neg hj]
          simp only [enc, RState.setv_val, RState.setv_sh, RState.setv_cell]
          cases hr : role j with
          | stream i => rfl
          | cell => rfl
          | reg r' =>
            have hne : r' ≠ r := by rintro rfl; exact hj (role_reg hr)
            simp [Function.update_of_ne hne]
    rw [e] at h2
    exact Exec.seq h1 h2
  | dec r σ hv =>
    have h1 := Exec.act (enc inp cap σ) (writeAt (rTape r) false) (moveAt (rTape r) .left)
    have e : (enc inp cap σ).act (writeAt (rTape r) false) (moveAt (rTape r) .left) =
        enc inp cap (σ.setv r (σ.val r - 1)) := by
      apply Bank.ext'
      · intro j
        simp only [Bank.act, moveAt, HeadMove.apply]
        by_cases hj : j = rTape r
        · subst hj; simp
        · rw [if_neg hj]
          simp only [enc, RState.setv_val, RState.setv_sh]
          cases hr : role j with
          | stream i => rfl
          | cell => rfl
          | reg r' =>
            have hne : r' ≠ r := by rintro rfl; exact hj (role_reg hr)
            simp [Function.update_of_ne hne]
      · intro j
        simp only [Bank.act, writeAt]
        by_cases hj : j = rTape r
        · subst hj; simp [regTape_dec cap _ hv]
        · rw [if_neg hj]
          simp only [enc, RState.setv_val, RState.setv_sh, RState.setv_cell]
          cases hr : role j with
          | stream i => rfl
          | cell => rfl
          | reg r' =>
            have hne : r' ≠ r := by rintro rfl; exact hj (role_reg hr)
            simp [Function.update_of_ne hne]
    rw [e] at h1
    exact h1
  | fwd i σ =>
    have h1 := Exec.act (enc inp cap σ) (fun _ => none) (moveAt (sTape i) .right)
    rw [act_move_s] at h1
    exact h1
  | bwd i σ =>
    have h1 := Exec.act (enc inp cap σ) (fun _ => none) (moveAt (sTape i) .left)
    rw [act_move_s] at h1
    exact h1
  | setc v σ =>
    have h1 := Exec.act (enc inp cap σ) (writeAt cTape v) (fun _ => .stay)
    have e : (enc inp cap σ).act (writeAt cTape v) (fun _ => .stay) = enc inp cap (σ.setc v) := by
      apply Bank.ext'
      · intro j; rfl
      · intro j
        simp only [Bank.act, writeAt]
        by_cases hj : j = cTape
        · subst hj; simp [writeTapeBit]
        · rw [if_neg hj]
          simp only [enc, RState.setc_val, RState.setc_sh, RState.setc_cell]
          cases hr : role j with
          | stream i => rfl
          | cell => exact absurd (role_cell hr) hj
          | reg r' => rfl
    rw [e] at h1
    exact h1
  | seq _ _ ih1 ih2 => exact Exec.seq ih1 ih2
  | ifrT hv _ ih => exact Exec.iteT (by rw [bit_r]; simpa using hv) ih
  | ifrF hv _ ih => exact Exec.iteF (by rw [bit_r]; simpa using hv) ih
  | ifsT hv _ ih => exact Exec.iteT (by rw [bit_s]; exact hv) ih
  | ifsF hv _ ih => exact Exec.iteF (by rw [bit_s]; exact hv) ih
  | whrF hv => exact Exec.loopF (by rw [bit_r]; simpa using hv)
  | whrT hv _ _ ih1 ih2 => exact Exec.loopT (by rw [bit_r]; simpa using hv) ih1 ih2
  | whsF hv => exact Exec.loopF (by rw [bit_s]; exact hv)
  | whsT hv _ _ ih1 ih2 => exact Exec.loopT (by rw [bit_s]; exact hv) ih1 ih2
  | mono _ hnm ih => exact Exec.mono ih hnm

end NearCubicWires.WireExponent3_5.FinalPass.Tm
