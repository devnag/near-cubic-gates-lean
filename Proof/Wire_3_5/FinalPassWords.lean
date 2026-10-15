import Proof.Wire_3_5.FinalPassRegLib

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-- Stream heads and contents, register values and the result cell. -/
structure WState (ns nr : ℕ) where
  sh : Fin (ns + 1) → ℕ
  st : Fin (ns + 1) → List Bool
  val : Fin nr → ℕ
  cell : Bool

variable {ns nr : ℕ}

def WState.setv (σ : WState ns nr) (r : Fin nr) (x : ℕ) : WState ns nr := ⟨σ.sh, σ.st, Function.update σ.val r x, σ.cell⟩
def WState.seth (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) : WState ns nr :=
  ⟨Function.update σ.sh i x, σ.st, σ.val, σ.cell⟩
def WState.sets (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) : WState ns nr :=
  ⟨σ.sh, Function.update σ.st i l, σ.val, σ.cell⟩
def WState.setc (σ : WState ns nr) (c : Bool) : WState ns nr := ⟨σ.sh, σ.st, σ.val, c⟩

@[simp] theorem WState.setv_val (σ : WState ns nr) (r : Fin nr) (x : ℕ) :
    (σ.setv r x).val = Function.update σ.val r x := rfl
@[simp] theorem WState.setv_sh (σ : WState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).sh = σ.sh := rfl
@[simp] theorem WState.setv_st (σ : WState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).st = σ.st := rfl
@[simp] theorem WState.setv_cell (σ : WState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).cell = σ.cell := rfl
@[simp] theorem WState.seth_val (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) : (σ.seth i x).val = σ.val := rfl
@[simp] theorem WState.seth_sh (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) :
    (σ.seth i x).sh = Function.update σ.sh i x := rfl
@[simp] theorem WState.seth_st (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) : (σ.seth i x).st = σ.st := rfl
@[simp] theorem WState.seth_cell (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) : (σ.seth i x).cell = σ.cell := rfl
@[simp] theorem WState.sets_val (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) : (σ.sets i l).val = σ.val := rfl
@[simp] theorem WState.sets_sh (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) : (σ.sets i l).sh = σ.sh := rfl
@[simp] theorem WState.sets_st (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) :
    (σ.sets i l).st = Function.update σ.st i l := rfl
@[simp] theorem WState.sets_cell (σ : WState ns nr) (i : Fin (ns + 1)) (l : List Bool) : (σ.sets i l).cell = σ.cell :=
  rfl
@[simp] theorem WState.setc_val (σ : WState ns nr) (c : Bool) : (σ.setc c).val = σ.val := rfl
@[simp] theorem WState.setc_sh (σ : WState ns nr) (c : Bool) : (σ.setc c).sh = σ.sh := rfl
@[simp] theorem WState.setc_st (σ : WState ns nr) (c : Bool) : (σ.setc c).st = σ.st := rfl
@[simp] theorem WState.setc_cell (σ : WState ns nr) (c : Bool) : (σ.setc c).cell = c := rfl

theorem WState.eq {σ τ : WState ns nr} (h1 : σ.sh = τ.sh) (h2 : σ.st = τ.st) (h3 : σ.val = τ.val)
    (h4 : σ.cell = τ.cell) : σ = τ := by
  cases σ; cases τ; simp_all

/-- The encoded bank. -/
def wenc (cap : ℕ) (σ : WState ns nr) : Bank (ns + 2 + nr) where
  H := fun j => match role j with
    | .stream i => σ.sh i
    | .cell => 0
    | .reg r => σ.val r
  A := fun j => match role j with
    | .stream i => σ.st i
    | .cell => [σ.cell]
    | .reg r => regTape cap (σ.val r)

variable (cap : ℕ)

@[simp] theorem wenc_H_s (σ : WState ns nr) (i : Fin (ns + 1)) : (wenc cap σ).H (sTape i) = σ.sh i := by
  simp [wenc, role_sTape]
@[simp] theorem wenc_A_s (σ : WState ns nr) (i : Fin (ns + 1)) : (wenc cap σ).A (sTape i) = σ.st i := by
  simp [wenc, role_sTape]
@[simp] theorem wenc_H_r (σ : WState ns nr) (r : Fin nr) : (wenc cap σ).H (rTape r) = σ.val r := by
  simp [wenc, role_rTape]
@[simp] theorem wenc_A_r (σ : WState ns nr) (r : Fin nr) : (wenc cap σ).A (rTape r) = regTape cap (σ.val r) := by
  simp [wenc, role_rTape]

/-- The scanned bit of a stream. -/
def wbit (σ : WState ns nr) (i : Fin (ns + 1)) : Bool := readTapeBit (σ.st i) (σ.sh i)

/-- Register programs with writable streams. -/
inductive WM (ns nr : ℕ) where
  | skip : WM ns nr
  | inc (r : Fin nr) : WM ns nr
  | dec (r : Fin nr) : WM ns nr
  | fwd (i : Fin (ns + 1)) : WM ns nr
  | bwd (i : Fin (ns + 1)) : WM ns nr
  | wr (i : Fin (ns + 1)) (b : Bool) : WM ns nr
  | setc (v : Bool) : WM ns nr
  | seq (P Q : WM ns nr) : WM ns nr
  | ifr (r : Fin nr) (P Q : WM ns nr) : WM ns nr
  | ifs (i : Fin (ns + 1)) (P Q : WM ns nr) : WM ns nr
  | whr (r : Fin nr) (P : WM ns nr) : WM ns nr
  | whs (i : Fin (ns + 1)) (P : WM ns nr) : WM ns nr

/-- The compiled structured program. -/
def WM.toProg : WM ns nr → Prog (ns + 2 + nr)
  | .skip => .skip
  | .inc r => .seq (.act (fun _ => none) (moveAt (rTape r) .right)) (.act (writeAt (rTape r) true) (fun _ => .stay))
  | .dec r => .act (writeAt (rTape r) false) (moveAt (rTape r) .left)
  | .fwd i => .act (fun _ => none) (moveAt (sTape i) .right)
  | .bwd i => .act (fun _ => none) (moveAt (sTape i) .left)
  | .wr i b => .act (writeAt (sTape i) b) (fun _ => .stay)
  | .setc v => .act (writeAt cTape v) (fun _ => .stay)
  | .seq P Q => .seq P.toProg Q.toProg
  | .ifr r P Q => .ite (rTape r) P.toProg Q.toProg
  | .ifs i P Q => .ite (sTape i) P.toProg Q.toProg
  | .whr r P => .loop (rTape r) P.toProg
  | .whs i P => .loop (sTape i) P.toProg

/-- **Big-step semantics** with the costs of the compiled machine. -/
inductive WExec : WM ns nr → WState ns nr → WState ns nr → ℕ → Prop where
  | skip (σ : WState ns nr) : WExec .skip σ σ 0
  | inc (r : Fin nr) (σ : WState ns nr) : σ.val r < cap → WExec (.inc r) σ (σ.setv r (σ.val r + 1)) 3
  | dec (r : Fin nr) (σ : WState ns nr) : σ.val r ≤ cap → WExec (.dec r) σ (σ.setv r (σ.val r - 1)) 1
  | fwd (i : Fin (ns + 1)) (σ : WState ns nr) : WExec (.fwd i) σ (σ.seth i (σ.sh i + 1)) 1
  | bwd (i : Fin (ns + 1)) (σ : WState ns nr) : WExec (.bwd i) σ (σ.seth i (σ.sh i - 1)) 1
  | wr (i : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) :
      WExec (.wr i b) σ (σ.sets i (writeTapeBit (σ.st i) (σ.sh i) b)) 1
  | setc (v : Bool) (σ : WState ns nr) : WExec (.setc v) σ (σ.setc v) 1
  | seq {P Q : WM ns nr} {σ τ ρ : WState ns nr} {n k : ℕ} : WExec P σ τ n → WExec Q τ ρ k →
      WExec (.seq P Q) σ ρ (n + 1 + k)
  | ifrT {r : Fin nr} {P Q : WM ns nr} {σ τ : WState ns nr} {n : ℕ} : σ.val r ≠ 0 → WExec P σ τ n →
      WExec (.ifr r P Q) σ τ (n + 1)
  | ifrF {r : Fin nr} {P Q : WM ns nr} {σ τ : WState ns nr} {n : ℕ} : σ.val r = 0 → WExec Q σ τ n →
      WExec (.ifr r P Q) σ τ (n + 1)
  | ifsT {i : Fin (ns + 1)} {P Q : WM ns nr} {σ τ : WState ns nr} {n : ℕ} : wbit σ i = true → WExec P σ τ n →
      WExec (.ifs i P Q) σ τ (n + 1)
  | ifsF {i : Fin (ns + 1)} {P Q : WM ns nr} {σ τ : WState ns nr} {n : ℕ} : wbit σ i = false → WExec Q σ τ n →
      WExec (.ifs i P Q) σ τ (n + 1)
  | whrF {r : Fin nr} {P : WM ns nr} {σ : WState ns nr} : σ.val r = 0 → WExec (.whr r P) σ σ 1
  | whrT {r : Fin nr} {P : WM ns nr} {σ τ ρ : WState ns nr} {n k : ℕ} : σ.val r ≠ 0 → WExec P σ τ n →
      WExec (.whr r P) τ ρ k → WExec (.whr r P) σ ρ (n + 2 + k)
  | whsF {i : Fin (ns + 1)} {P : WM ns nr} {σ : WState ns nr} : wbit σ i = false → WExec (.whs i P) σ σ 1
  | whsT {i : Fin (ns + 1)} {P : WM ns nr} {σ τ ρ : WState ns nr} {n k : ℕ} : wbit σ i = true →
      WExec P σ τ n → WExec (.whs i P) τ ρ k → WExec (.whs i P) σ ρ (n + 2 + k)
  | mono {P : WM ns nr} {σ τ : WState ns nr} {n m : ℕ} : WExec P σ τ n → n ≤ m → WExec P σ τ m

/-! ## Soundness -/

theorem wbit_s (σ : WState ns nr) (i : Fin (ns + 1)) : (wenc cap σ).bit (sTape i) = wbit σ i := by
  simp [Bank.bit, wbit]

theorem wbit_r (σ : WState ns nr) (r : Fin nr) : (wenc cap σ).bit (rTape r) = decide (σ.val r ≠ 0) := by
  simp [Bank.bit, regTape_read]

theorem wenc_move_s (σ : WState ns nr) (i : Fin (ns + 1)) (mv : HeadMove) :
    (wenc cap σ).act (fun _ => none) (moveAt (sTape i) mv) = wenc cap (σ.seth i (mv.apply (σ.sh i))) := by
  apply Bank.ext'
  · intro j
    simp only [Bank.act, moveAt]
    by_cases hj : j = sTape i
    · subst hj; simp
    · rw [if_neg hj]
      simp only [HeadMove.apply, wenc, WState.seth_sh]
      cases hr : role j with
      | stream i' =>
        have hne : i' ≠ i := by rintro rfl; exact hj (role_stream hr)
        simp [Function.update_of_ne hne]
      | cell => rfl
      | reg r => rfl
  · intro j; rfl

theorem wenc_reg (σ τ : WState ns nr) (r : Fin nr) (hsh : τ.sh = σ.sh) (hst : τ.st = σ.st) (hc : τ.cell = σ.cell)
    (hv : ∀ r', r' ≠ r → τ.val r' = σ.val r') (j : Fin (ns + 2 + nr)) (hj : j ≠ rTape r) :
    (wenc cap τ).H j = (wenc cap σ).H j ∧ (wenc cap τ).A j = (wenc cap σ).A j := by
  simp only [wenc]
  cases hr : role j with
  | stream i => simp [hsh, hst]
  | cell => simp [hc]
  | reg r' =>
    have hne : r' ≠ r := by rintro rfl; exact hj (role_reg hr)
    simp [hv r' hne]

theorem WExec.exec {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    Exec P.toProg (wenc cap σ) (wenc cap τ) n := by
  induction h with
  | skip σ => exact Exec.skip _
  | inc r σ hv =>
    have h1 := Exec.act (wenc cap σ) (fun _ => none) (moveAt (rTape r) .right)
    have h2 := Exec.act ((wenc cap σ).act (fun _ => none) (moveAt (rTape r) .right)) (writeAt (rTape r) true)
      (fun _ => .stay)
    have e : ((wenc cap σ).act (fun _ => none) (moveAt (rTape r) .right)).act (writeAt (rTape r) true)
        (fun _ => .stay) = wenc cap (σ.setv r (σ.val r + 1)) := by
      apply Bank.ext'
      · intro j
        by_cases hj : j = rTape r
        · subst hj; simp [Bank.act, moveAt, HeadMove.apply]
        · have := (wenc_reg cap σ (σ.setv r (σ.val r + 1)) r rfl rfl rfl
            (fun r' h => by simp [Function.update_of_ne h]) j hj).1
          rw [this]; simp [Bank.act, moveAt, hj, HeadMove.apply]
      · intro j
        by_cases hj : j = rTape r
        · subst hj; simp [Bank.act, moveAt, writeAt, HeadMove.apply, regTape_inc cap _ hv]
        · have := (wenc_reg cap σ (σ.setv r (σ.val r + 1)) r rfl rfl rfl
            (fun r' h => by simp [Function.update_of_ne h]) j hj).2
          rw [this]; simp [Bank.act, writeAt, hj]
    rw [e] at h2
    exact Exec.seq h1 h2
  | dec r σ hv =>
    have h1 := Exec.act (wenc cap σ) (writeAt (rTape r) false) (moveAt (rTape r) .left)
    have e : (wenc cap σ).act (writeAt (rTape r) false) (moveAt (rTape r) .left) =
        wenc cap (σ.setv r (σ.val r - 1)) := by
      apply Bank.ext'
      · intro j
        by_cases hj : j = rTape r
        · subst hj; simp [Bank.act, moveAt, HeadMove.apply]
        · have := (wenc_reg cap σ (σ.setv r (σ.val r - 1)) r rfl rfl rfl
            (fun r' h => by simp [Function.update_of_ne h]) j hj).1
          rw [this]; simp [Bank.act, moveAt, hj, HeadMove.apply]
      · intro j
        by_cases hj : j = rTape r
        · subst hj; simp [Bank.act, writeAt, regTape_dec cap _ hv]
        · have := (wenc_reg cap σ (σ.setv r (σ.val r - 1)) r rfl rfl rfl
            (fun r' h => by simp [Function.update_of_ne h]) j hj).2
          rw [this]; simp [Bank.act, writeAt, hj]
    rw [e] at h1
    exact h1
  | fwd i σ =>
    have h1 := Exec.act (wenc cap σ) (fun _ => none) (moveAt (sTape i) .right)
    rw [wenc_move_s] at h1
    exact h1
  | bwd i σ =>
    have h1 := Exec.act (wenc cap σ) (fun _ => none) (moveAt (sTape i) .left)
    rw [wenc_move_s] at h1
    exact h1
  | wr i b σ =>
    have h1 := Exec.act (wenc cap σ) (writeAt (sTape i) b) (fun _ => .stay)
    have e : (wenc cap σ).act (writeAt (sTape i) b) (fun _ => .stay) =
        wenc cap (σ.sets i (writeTapeBit (σ.st i) (σ.sh i) b)) := by
      apply Bank.ext'
      · intro j
        simp only [Bank.act, HeadMove.apply, wenc, WState.sets_sh, WState.sets_val]
      · intro j
        by_cases hj : j = sTape i
        · subst hj; simp [Bank.act, writeAt]
        · simp only [Bank.act, writeAt, hj, if_false, wenc, WState.sets_st, WState.sets_val, WState.sets_cell]
          cases hr : role j with
          | stream i' =>
            have hne : i' ≠ i := by rintro rfl; exact hj (role_stream hr)
            simp [Function.update_of_ne hne]
          | cell => rfl
          | reg r => rfl
    rw [e] at h1
    exact h1
  | setc v σ =>
    have h1 := Exec.act (wenc cap σ) (writeAt cTape v) (fun _ => .stay)
    have e : (wenc cap σ).act (writeAt cTape v) (fun _ => .stay) = wenc cap (σ.setc v) := by
      apply Bank.ext'
      · intro j; rfl
      · intro j
        simp only [Bank.act, writeAt]
        by_cases hj : j = cTape
        · subst hj; simp [wenc, role_cTape, writeTapeBit]
        · rw [if_neg hj]
          simp only [wenc, WState.setc_val, WState.setc_sh, WState.setc_st, WState.setc_cell]
          cases hr : role j with
          | stream i => rfl
          | cell => exact absurd (role_cell hr) hj
          | reg r' => rfl
    rw [e] at h1
    exact h1
  | seq _ _ ih1 ih2 => exact Exec.seq ih1 ih2
  | ifrT hv _ ih => exact Exec.iteT (by rw [wbit_r]; simpa using hv) ih
  | ifrF hv _ ih => exact Exec.iteF (by rw [wbit_r]; simpa using hv) ih
  | ifsT hv _ ih => exact Exec.iteT (by rw [wbit_s]; exact hv) ih
  | ifsF hv _ ih => exact Exec.iteF (by rw [wbit_s]; exact hv) ih
  | whrF hv => exact Exec.loopF (by rw [wbit_r]; simpa using hv)
  | whrT hv _ _ ih1 ih2 => exact Exec.loopT (by rw [wbit_r]; simpa using hv) ih1 ih2
  | whsF hv => exact Exec.loopF (by rw [wbit_s]; exact hv)
  | whsT hv _ _ ih1 ih2 => exact Exec.loopT (by rw [wbit_s]; exact hv) ih1 ih2
  | mono _ hnm ih => exact Exec.mono ih hnm

end NearCubicWires.WireExponent3_5.FinalPass.Tm
