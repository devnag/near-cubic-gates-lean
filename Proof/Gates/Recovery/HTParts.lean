import Proof.Gates.Codec.Frame
import Proof.Gates.CheckedPCPP.LitDecode

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HTParts

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.CheckedPCPP.LitDecode (rtb_off rtb_off0)

variable {ns nr : ℕ} (cap : ℕ)

section Adv
variable (src dst : Fin (ns + 1)) (OP SC : Fin nr)

/-- `u` appended to `dst`, the head of `src` and the counter `SC` advanced by `k`. -/
def adv (σ : WState ns nr) (u : List Bool) (k : ℕ) : WState ns nr :=
  ((appendO σ dst OP u).seth src (σ.sh src + k)).setv SC (σ.val SC + k)

variable {src dst OP SC}

theorem adv_zero (σ : WState ns nr) : adv src dst OP SC σ [] 0 = σ := by
  unfold adv; rw [appendO_nil]; simp only [Nat.add_zero]; rw [wseth_same, wsetv_same]

theorem adv_adv (hsd : src ≠ dst) (hOS : OP ≠ SC) (σ : WState ns nr) (u u' : List Bool) (k k' : ℕ) :
    adv src dst OP SC (adv src dst OP SC σ u k) u' k' = adv src dst OP SC σ (u ++ u') (k + k') := by
  apply WState.eq
  · funext j; by_cases hj : j = src
    · subst hj; simp [adv, appendO, Function.update_apply, Ne.symm hsd]; ring
    · by_cases hd : j = dst
      · subst hd; simp [adv, appendO, Function.update_apply, hj]; ring
      · simp [adv, appendO, Function.update_apply, hj, hd]
  · funext j; by_cases hd : j = dst
    · subst hd; simp [adv, appendO, Function.update_apply, Ne.symm hsd]
    · simp [adv, appendO, Function.update_apply, hd]
  · funext r; by_cases hr : r = SC
    · subst hr; simp [adv, appendO, Function.update_apply, Ne.symm hOS]; ring
    · by_cases ho : r = OP
      · subst ho; simp [adv, appendO, Function.update_apply, hr]; ring
      · simp [adv, appendO, Function.update_apply, hr, ho]
  · simp [adv, appendO]

@[simp] theorem adv_st_dst (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).st dst = σ.st dst ++ u := by simp [adv, appendO]
@[simp] theorem adv_sh_dst (hsd : src ≠ dst) (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).sh dst = σ.sh dst + u.length := by
  simp [adv, appendO, Function.update_apply, Ne.symm hsd]
@[simp] theorem adv_st_src (hsd : src ≠ dst) (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).st src = σ.st src := by simp [adv, appendO, Function.update_apply, hsd]
@[simp] theorem adv_sh_src (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).sh src = σ.sh src + k := by simp [adv]
theorem adv_st_other (σ : WState ns nr) (u : List Bool) (k : ℕ) (j : Fin (ns + 1)) (hj : j ≠ dst) :
    (adv src dst OP SC σ u k).st j = σ.st j := by simp [adv, appendO, Function.update_apply, hj]
theorem adv_sh_other (σ : WState ns nr) (u : List Bool) (k : ℕ) (j : Fin (ns + 1)) (hj : j ≠ dst) (hs : j ≠ src) :
    (adv src dst OP SC σ u k).sh j = σ.sh j := by simp [adv, appendO, Function.update_apply, hj, hs]
@[simp] theorem adv_val_OP (hOS : OP ≠ SC) (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).val OP = σ.val OP + u.length := by
  simp [adv, appendO, Function.update_apply, hOS]
@[simp] theorem adv_val_SC (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).val SC = σ.val SC + k := by simp [adv]
theorem adv_val_other (σ : WState ns nr) (u : List Bool) (k : ℕ) (r : Fin nr) (h1 : r ≠ OP) (h2 : r ≠ SC) :
    (adv src dst OP SC σ u k).val r = σ.val r := by simp [adv, appendO, Function.update_apply, h1, h2]
@[simp] theorem adv_cell (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).cell = σ.cell := by simp [adv, appendO]
theorem adv_setv (σ : WState ns nr) (u : List Bool) (k : ℕ) (r : Fin nr) (x : ℕ) (h1 : r ≠ OP) (h2 : r ≠ SC) :
    adv src dst OP SC (σ.setv r x) u k = (adv src dst OP SC σ u k).setv r x := by
  apply WState.eq <;> try rfl
  funext q; simp only [adv, appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
  by_cases q1 : q = SC
  · subst q1; simp [Ne.symm h2]
  · by_cases q2 : q = OP
    · subst q2; simp [q1, Ne.symm h1]
    · simp [q1, q2]

end Adv

/-! ## One cell -/

section Cell
variable (src dst : Fin (ns + 1)) (OP SC : Fin nr)

/-- Emit `E b` for the scanned bit `b` of `src`, then step `src` (counted in `SC`). -/
def cellE (E : Bool → WM ns nr) : WM ns nr := .seq (.ifs src (E true) (E false)) (WM.fwdC src SC)

/-- An emitter: `E b` appends `e b` to `dst` in `c` steps. -/
def Emits (e : Bool → List Bool) (E : Bool → WM ns nr) (c : ℕ) : Prop :=
  ∀ (b : Bool) (τ : WState ns nr), τ.sh dst = (τ.st dst).length → τ.val OP + (e b).length ≤ cap →
    WExec cap (E b) τ (appendO τ dst OP (e b)) c

variable {src dst OP SC}

theorem emits_raw : Emits cap dst OP (fun b => [b]) (fun b => emitC dst OP b) 7 := fun b τ ho hc =>
  Codec.emitBit_spec cap dst OP b τ ho (by simpa using hc)

theorem emits_pair : Emits cap dst OP (fun b => [true, b]) (fun b => emitPair dst OP b) 15 := fun b τ ho hc =>
  emitPair_spec cap dst OP b τ ho (by simpa using hc)

theorem emits_none : Emits cap dst OP (fun _ => []) (fun _ => WM.skip) 0 := fun _ τ _ _ => by
  rw [appendO_nil]; exact WExec.skip τ

theorem cellE_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {e : Bool → List Bool} {E : Bool → WM ns nr} {c : ℕ}
    (hE : Emits cap dst OP e E c) (σ : WState ns nr) (hd : σ.sh dst = (σ.st dst).length)
    (hc : σ.val OP + (e (readTapeBit (σ.st src) (σ.sh src))).length ≤ cap) (hsc : σ.val SC < cap) :
    WExec cap (cellE src SC E) σ (adv src dst OP SC σ (e (readTapeBit (σ.st src) (σ.sh src))) 1) (c + 7) := by
  set b := readTapeBit (σ.st src) (σ.sh src) with hb
  have h1 : WExec cap (.ifs src (E true) (E false)) σ (appendO σ dst OP (e b)) (c + 1) := by
    cases hbv : b
    · rw [hbv] at hc
      exact WExec.ifsF (by unfold wbit; rw [← hb, hbv]) (hE false σ hd hc)
    · rw [hbv] at hc
      exact WExec.ifsT (by unfold wbit; rw [← hb, hbv]) (hE true σ hd hc)
  have h2 := wfwdC_spec cap src SC (appendO σ dst OP (e b)) (by simp [appendO, Function.update_apply, Ne.symm hOS]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl) (by omega)
  simp [adv, appendO, Function.update_apply, hsd, Ne.symm hsd, Ne.symm hOS]

end Cell

/-! ## Counted runs of cells -/

section Loops
variable {src dst : Fin (ns + 1)} {OP SC : Fin nr}

/-- `K` cells of `src`. -/
def cntLoop (src : Fin (ns + 1)) (SC K : Fin nr) (E : Bool → WM ns nr) : WM ns nr :=
  .whr K (.seq (.dec K) (cellE src SC E))

theorem cntLoop_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {K : Fin nr} (hKO : K ≠ OP) (hKS : K ≠ SC)
    {e : Bool → List Bool} {E : Bool → WM ns nr} {c : ℕ} (hE : Emits cap dst OP e E c) (rest : List Bool) :
    ∀ (w pre : List Bool) (σ : WState ns nr), σ.st src = pre ++ w ++ rest → σ.sh src = pre.length →
      σ.sh dst = (σ.st dst).length → σ.val K = w.length → w.length ≤ cap →
      σ.val OP + (w.flatMap e).length ≤ cap → σ.val SC + w.length < cap + 1 →
      WExec cap (cntLoop src SC K E) σ ((adv src dst OP SC σ (w.flatMap e) w.length).setv K 0)
        (w.length * (c + 11) + 1)
  | [], pre, σ, _, _, _, hK, _, _, _ => by
    simp only [List.flatMap_nil, List.length_nil, adv_zero, Nat.zero_mul, Nat.zero_add]
    have hK0 : σ.val K = 0 := by simpa using hK
    rw [show σ.setv K 0 = σ by rw [← hK0]; exact wsetv_same σ K]
    exact WExec.whrF hK0
  | b :: w, pre, σ, hst, hsh, hd, hK, hKc, hOc, hSc => by
    have e1 := WExec.dec (cap := cap) K σ (by simp at hKc; omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have hb : readTapeBit (σ1.st src) (σ1.sh src) = b := by
      simp only [hσ1, WState.setv_st, WState.setv_sh]; rw [hst, hsh, List.append_assoc, rtb_off0]; rfl
    have e2 := cellE_spec cap hsd hOS hE σ1 (by simpa [hσ1] using hd)
      (by rw [hb]; simp [hσ1, Function.update_apply, Ne.symm hKO]; simp at hOc; omega)
      (by simp [hσ1, Function.update_apply, Ne.symm hKS]; simp at hSc; omega)
    rw [hb] at e2
    set σ2 := adv src dst OP SC σ1 (e b) 1 with hσ2
    have ih := cntLoop_spec hsd hOS hKO hKS hE rest w (pre ++ [b]) σ2
      (by rw [hσ2, adv_st_src hsd]; simp [hσ1, hst])
      (by rw [hσ2, adv_sh_src]; simp [hσ1, hsh])
      (by rw [hσ2, adv_sh_dst hsd, adv_st_dst]; simp [hσ1, hd])
      (by rw [hσ2, adv_val_other _ _ _ K hKO hKS]; simp [hσ1, hK])
      (by simp at hKc; omega)
      (by rw [hσ2, adv_val_OP hOS]; simp [hσ1, Function.update_apply, Ne.symm hKO]; simp at hOc; omega)
      (by rw [hσ2, adv_val_SC]; simp [hσ1, Function.update_apply, Ne.symm hKS]; simp at hSc; omega)
    refine WExec.mono (WExec.cast cap (WExec.whrT (by rw [hK]; simp) (WExec.seq e1 e2) ih) ?_ le_rfl)
      (by simp; ring_nf; omega)
    have hfin : (adv src dst OP SC (σ.setv K (σ.val K - 1)) (e b ++ w.flatMap e) (1 + w.length)).setv K 0 =
        (adv src dst OP SC σ ((b :: w).flatMap e) (b :: w).length).setv K 0 := by
      rw [adv_setv _ _ _ K _ hKO hKS]
      simp only [List.flatMap_cons, List.length_cons, Nat.add_comm 1 w.length]
      apply WState.eq <;> try rfl
      funext q; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> rfl
    rw [hσ2, adv_adv hsd hOS, hσ1]; exact hfin

def pairLoop (src : Fin (ns + 1)) (SC : Fin nr) (E1 E2 : Bool → WM ns nr) : WM ns nr :=
  .whs src (.seq (cellE src SC E1) (cellE src SC E2))

theorem pairLoop_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {e1 e2 : Bool → List Bool} {E1 E2 : Bool → WM ns nr}
    {c1 c2 : ℕ} (hE1 : Emits cap dst OP e1 E1 c1) (hE2 : Emits cap dst OP e2 E2 c2) (rest : List Bool)
    (hrest : rest.headD false = false) :
    ∀ (w pre : List Bool) (σ : WState ns nr), σ.st src = pre ++ marks w ++ rest → σ.sh src = pre.length →
      σ.sh dst = (σ.st dst).length →
      σ.val OP + (w.flatMap fun b => e1 true ++ e2 b).length ≤ cap → σ.val SC + 2 * w.length < cap + 1 →
      WExec cap (pairLoop src SC E1 E2) σ
        (adv src dst OP SC σ (w.flatMap fun b => e1 true ++ e2 b) (2 * w.length)) (w.length * (c1 + c2 + 17) + 1)
  | [], pre, σ, hst, hsh, _, _, _ => by
    simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero, adv_zero, Nat.zero_mul, Nat.zero_add]
    refine WExec.whsF ?_
    unfold wbit; rw [hst, hsh]; simp [marks, rtb_off0]
    cases rest with
    | nil => rfl
    | cons a r => simp at hrest; subst hrest; rfl
  | b :: w, pre, σ, hst, hsh, hd, hOc, hSc => by
    rw [List.flatMap_cons, List.length_append, List.length_append] at hOc
    have hst' : σ.st src = pre ++ (true :: b :: (marks w ++ rest)) := by rw [hst]; simp [marks]
    have hw : wbit σ src = true := by unfold wbit; rw [hst', hsh, rtb_off0]; rfl
    have hm : readTapeBit (σ.st src) (σ.sh src) = true := by rw [hst', hsh, rtb_off0]; rfl
    have x1 := cellE_spec cap hsd hOS hE1 σ hd (by rw [hm]; omega) (by simp at hSc; omega)
    rw [hm] at x1
    set σ1 := adv src dst OP SC σ (e1 true) 1 with hσ1
    have hb : readTapeBit (σ1.st src) (σ1.sh src) = b := by
      rw [hσ1, adv_st_src hsd, adv_sh_src, hst', hsh, rtb_off pre _ 1]; rfl
    have x2 := cellE_spec cap hsd hOS hE2 σ1 (by rw [hσ1, adv_sh_dst hsd, adv_st_dst]; simp [hd])
      (by rw [hb, hσ1, adv_val_OP hOS]; omega) (by rw [hσ1, adv_val_SC]; simp at hSc; omega)
    rw [hb] at x2
    set σ2 := adv src dst OP SC σ1 (e2 b) 1 with hσ2
    have ih := pairLoop_spec hsd hOS hE1 hE2 rest hrest w (pre ++ [true, b]) σ2
      (by rw [hσ2, adv_st_src hsd, hσ1, adv_st_src hsd, hst]; simp [marks])
      (by rw [hσ2, adv_sh_src, hσ1, adv_sh_src, hsh]; simp)
      (by rw [hσ2, adv_sh_dst hsd, adv_st_dst, hσ1, adv_sh_dst hsd, adv_st_dst]; simp [hd]; ring)
      (by rw [hσ2, adv_val_OP hOS, hσ1, adv_val_OP hOS]; omega)
      (by rw [hσ2, adv_val_SC, hσ1, adv_val_SC]; simp at hSc; omega)
    refine WExec.mono (WExec.cast cap (WExec.whsT hw (WExec.seq x1 x2) ih) ?_ le_rfl) (by simp; ring_nf; omega)
    rw [hσ2, hσ1, adv_adv hsd hOS, adv_adv hsd hOS]
    simp only [List.flatMap_cons, List.length_cons, List.append_assoc]
    congr 1; ring

end Loops

end NearCubicGates.Close.Recovery.HTParts
