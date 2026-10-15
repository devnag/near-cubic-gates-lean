import Proof.Gates.Expand.Vals2

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)

variable {ns nr : ℕ} (cap W : ℕ) {A B C S : Fin (ns + 1)} {F R G : Fin nr} {σ : WState ns nr}

theorem fCopy (hAB : A ≠ B) (hFR : F ≠ R) {a b : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.copy A B F R) σ (41 * W + 3) (fun τ => NumOn τ A W b ∧ SameExcept σ τ [A] []) :=
  ⟨_, BinW.copy_spec cap W hAB hFR σ a b hA hB hF hR hcap, numOn_sets_self σ A W b hA.2, sameExcept_sets σ (by simp) _⟩

theorem fAdd (hAB : A ≠ B) (hFR : F ≠ R) {a b : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hab : a + b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.add A B F R) σ (41 * W + 3) (fun τ => NumOn τ A W (a + b) ∧ SameExcept σ τ [A] []) :=
  ⟨_, BinW.add_spec cap W hAB hFR σ a b hA hB hF hR hab hcap, numOn_sets_self σ A W _ hA.2, sameExcept_sets σ (by simp) _⟩

theorem fSub (hAB : A ≠ B) (hFR : F ≠ R) {a b : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hba : b ≤ a) (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.sub A B F R) σ (41 * W + 9) (fun τ => NumOn τ A W (a - b) ∧ SameExcept σ τ [A] []) :=
  ⟨_, BinW.sub_spec cap W hAB hFR σ a b hA hB hF hR hba ha hcap, numOn_sets_self σ A W _ hA.2,
    sameExcept_sets σ (by simp) _⟩

theorem fInc (hAB : A ≠ B) (hFR : F ≠ R) {a b : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (ha : a + 1 < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.inc A B F R) σ (41 * W + 7) (fun τ => NumOn τ A W (a + 1) ∧ SameExcept σ τ [A] []) :=
  ⟨_, BinW.inc_spec cap W hAB hFR σ a b hA hB hF hR ha hcap, numOn_sets_self σ A W _ hA.2,
    sameExcept_sets σ (by simp) _⟩

theorem fZero (hAB : A ≠ B) (hFR : F ≠ R) {a b : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.zero A B F R) σ (41 * W + 3) (fun τ => NumOn τ A W 0 ∧ SameExcept σ τ [A] []) :=
  ⟨_, BinW.zero_spec cap W hAB hFR σ a b hA hB hF hR hcap, numOn_sets_self σ A W _ hA.2, sameExcept_sets σ (by simp) _⟩

theorem fAnd (hAB : A ≠ B) (hFR : F ≠ R) {a b : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (andX A B F R) σ (41 * W + 3) (fun τ => NumOn τ A W (a &&& b) ∧ SameExcept σ τ [A] []) :=
  ⟨_, WXExec.wm (andW_spec cap W hAB hFR σ a b hA hB hF hR hcap), numOn_sets_self σ A W _ hA.2,
    sameExcept_sets σ (by simp) _⟩

theorem fEq (hAB : A ≠ B) (hFR : F ≠ R) {a b : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.eq A B F R) σ (41 * W + 7)
      (fun τ => τ.val F = (decide (a = b)).toNat ∧ SameExcept σ τ [] [F]) :=
  ⟨_, BinW.eq_spec cap W hAB hFR σ a b hA hB hF hR ha hb hcap, by simp, sameExcept_setv σ (by simp) _⟩

theorem fLt (hAB : A ≠ B) (hFR : F ≠ R) {a b : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hF : σ.val F = 0)
    (hR : σ.val R = 0) (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.lt A B F R) σ (41 * W + 3)
      (fun τ => τ.val F = (decide (a < b)).toNat ∧ SameExcept σ τ [] [F]) :=
  ⟨_, BinW.lt_spec cap W hAB hFR σ a b hA hB hF hR ha hb hcap, by simp, sameExcept_setv σ (by simp) _⟩

theorem fMul (hAB : A ≠ B) (hAC : A ≠ C) (hAS : A ≠ S) (hBC : B ≠ C) (hBS : B ≠ S) (hCS : C ≠ S) (hFR : F ≠ R)
    (hFG : F ≠ G) (hRG : R ≠ G) {a b c s : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hC : NumOn σ C W c)
    (hS : NumOn σ S W s) (hF : σ.val F = 0) (hR : σ.val R = 0) (hG : σ.val G = 0) (hab : a * b < 2 ^ W)
    (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.mul A B C S F R G) σ (mulCost W)
      (fun τ => NumOn τ C W (a * b) ∧ NumOn τ S W 0 ∧ SameExcept σ τ [C, S] []) :=
  ⟨_, BinW.mul_spec cap W hAB hAC hAS hBC hBS hCS hFR hFG hRG σ a b c s hA hB hC hS hF hR hG hab hb hcap,
    numOn_sets_ne (numOn_sets_self σ C W _ hC.2) hCS _, numOn_sets_self _ S W 0 (by simpa using hS.2),
    SameExcept.trans (sameExcept_sets σ (by simp) _) (sameExcept_sets _ (by simp) _)⟩

theorem fDivmod {Q M X : Fin (ns + 1)} {K T : Fin nr} (hAQ : A ≠ Q) (hAM : A ≠ M) (hAX : A ≠ X) (hBQ : B ≠ Q)
    (hBM : B ≠ M) (hBX : B ≠ X) (hQM : Q ≠ M) (hQX : Q ≠ X) (hMX : M ≠ X) (hFR : F ≠ R) (hFK : F ≠ K) (hRK : R ≠ K)
    (hKT : K ≠ T) {a b q0 m0 x0 : ℕ} (hA : NumOn σ A W a) (hB : NumOn σ B W b) (hQ : NumOn σ Q W q0)
    (hM : NumOn σ M W m0) (hX : NumOn σ X W x0) (hF : σ.val F = 0) (hR : σ.val R = 0) (hK : σ.val K = 0)
    (hT : σ.val T = 0) (ha : a < 2 ^ W) (hb : 0 < b) (h2b : 2 * b ≤ 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.divmod A B Q M X F R K T) σ (BinW.divCost W)
      (fun τ => NumOn τ Q W (a / b) ∧ NumOn τ M W (a % b) ∧ NumOn τ X W 0 ∧ SameExcept σ τ [Q, M, X] []) :=
  ⟨_, BinW.divmod_spec cap W hAQ hAM hAX hBQ hBM hBX hQM hQX hMX hFR hFK hRK hKT σ a b q0 m0 x0 hA hB hQ hM hX hF hR
    hK hT ha hb h2b hcap,
    numOn_sets_ne (numOn_sets_ne (numOn_sets_self σ Q W _ hQ.2) hQM _) hQX _,
    numOn_sets_ne (numOn_sets_self _ M W _ (by simpa using hM.2)) hMX _,
    numOn_sets_self _ X W 0 (by simpa using hX.2),
    SameExcept.trans (SameExcept.trans (sameExcept_sets σ (by simp) _) (sameExcept_sets _ (by simp) _))
      (sameExcept_sets _ (by simp) _)⟩

/-- Decrement a flag known to be `1` back to `0`. -/
theorem fDec1 {r : Fin nr} (σ : WState ns nr) (h : σ.val r = 1) (hcap : 1 ≤ cap) :
    Runs cap (WMX.dec r) σ 1 (fun τ => τ.val r = 0 ∧ SameExcept σ τ [] [r]) :=
  ⟨_, WXExec.dec cap r σ (by omega), by simp [h], sameExcept_setv σ (by simp) _⟩

end NearCubicGates.Close.Expand

/-! ## A block of number streams by values -/

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)

variable {ns nr k : ℕ}

/-- Every stream of the block holds its value (width `W`). -/
def MV (S : Fin k ↪ Fin (ns + 1)) (W : ℕ) (v : Fin k → ℕ) (σ : WState ns nr) : Prop := ∀ i, NumOn σ (S i) W (v i)

theorem MV.upd {S : Fin k ↪ Fin (ns + 1)} {W : ℕ} {v : Fin k → ℕ} {σ τ : WState ns nr} {Rg : List (Fin nr)}
    (h : MV S W v σ) (a : Fin k) (f : SameExcept σ τ [S a] Rg) (x : ℕ) (ha : NumOn τ (S a) W x) :
    MV S W (Function.update v a x) τ := by
  intro i
  by_cases e : i = a
  · subst e; simpa using ha
  · rw [Function.update_of_ne e]
    exact f.numOn (by simp only [List.mem_singleton]; exact fun h' => e (S.injective h')) (h i)

theorem MV.frame {S : Fin k ↪ Fin (ns + 1)} {W : ℕ} {v : Fin k → ℕ} {σ τ : WState ns nr} {Rg : List (Fin nr)}
    (h : MV S W v σ) (f : SameExcept σ τ [] Rg) : MV S W v τ :=
  fun i => f.numOn (by simp) (h i)

section Ops
variable (cap W : ℕ) {S : Fin k ↪ Fin (ns + 1)} {v : Fin k → ℕ} {σ : WState ns nr} {F R : Fin nr}

theorem sN {S : Fin k ↪ Fin (ns + 1)} {a b : Fin k} (h : a ≠ b) : S a ≠ S b := fun e => h (S.injective e)

theorem mCopy (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.copy (S a) (S b) F R) σ (41 * W + 3)
      (fun τ => MV S W (Function.update v a (v b)) τ ∧ SameExcept σ τ [S a] []) :=
  (fCopy cap W (sN hab) hFR (h a) (h b) hF hR hcap).post (fun _ ⟨h1, f⟩ => ⟨h.upd a f _ h1, f⟩)

theorem mAdd (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hlt : v a + v b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.add (S a) (S b) F R) σ (41 * W + 3)
      (fun τ => MV S W (Function.update v a (v a + v b)) τ ∧ SameExcept σ τ [S a] []) :=
  (fAdd cap W (sN hab) hFR (h a) (h b) hF hR hlt hcap).post (fun _ ⟨h1, f⟩ => ⟨h.upd a f _ h1, f⟩)

theorem mSub (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hba : v b ≤ v a) (hlt : v a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.sub (S a) (S b) F R) σ (41 * W + 9)
      (fun τ => MV S W (Function.update v a (v a - v b)) τ ∧ SameExcept σ τ [S a] []) :=
  (fSub cap W (sN hab) hFR (h a) (h b) hF hR hba hlt hcap).post (fun _ ⟨h1, f⟩ => ⟨h.upd a f _ h1, f⟩)

theorem mInc (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hlt : v a + 1 < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.inc (S a) (S b) F R) σ (41 * W + 7)
      (fun τ => MV S W (Function.update v a (v a + 1)) τ ∧ SameExcept σ τ [S a] []) :=
  (fInc cap W (sN hab) hFR (h a) (h b) hF hR hlt hcap).post (fun _ ⟨h1, f⟩ => ⟨h.upd a f _ h1, f⟩)

theorem mZero (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.zero (S a) (S b) F R) σ (41 * W + 3)
      (fun τ => MV S W (Function.update v a 0) τ ∧ SameExcept σ τ [S a] []) :=
  (fZero cap W (sN hab) hFR (h a) (h b) hF hR hcap).post (fun _ ⟨h1, f⟩ => ⟨h.upd a f _ h1, f⟩)

theorem mAnd (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (andX (S a) (S b) F R) σ (41 * W + 3)
      (fun τ => MV S W (Function.update v a (v a &&& v b)) τ ∧ SameExcept σ τ [S a] []) :=
  (fAnd cap W (sN hab) hFR (h a) (h b) hF hR hcap).post (fun _ ⟨h1, f⟩ => ⟨h.upd a f _ h1, f⟩)

theorem mEq (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (ha : v a < 2 ^ W) (hb : v b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.eq (S a) (S b) F R) σ (41 * W + 7)
      (fun τ => MV S W v τ ∧ τ.val F = (decide (v a = v b)).toNat ∧ SameExcept σ τ [] [F]) :=
  (fEq cap W (sN hab) hFR (h a) (h b) hF hR ha hb hcap).post (fun _ ⟨h1, f⟩ => ⟨h.frame f, h1, f⟩)

theorem mLt (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (ha : v a < 2 ^ W) (hb : v b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.lt (S a) (S b) F R) σ (41 * W + 3)
      (fun τ => MV S W v τ ∧ τ.val F = (decide (v a < v b)).toNat ∧ SameExcept σ τ [] [F]) :=
  (fLt cap W (sN hab) hFR (h a) (h b) hF hR ha hb hcap).post (fun _ ⟨h1, f⟩ => ⟨h.frame f, h1, f⟩)

theorem mMul {G : Fin nr} (a b c x : Fin k) (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x) (hbc : b ≠ c) (hbx : b ≠ x)
    (hcx : c ≠ x) (hFR : F ≠ R) (hFG : F ≠ G) (hRG : R ≠ G) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hG : σ.val G = 0) (hlt : v a * v b < 2 ^ W) (hb : v b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.mul (S a) (S b) (S c) (S x) F R G) σ (mulCost W)
      (fun τ => MV S W (Function.update (Function.update v c (v a * v b)) x 0) τ ∧ SameExcept σ τ [S c, S x] []) :=
  (fMul cap W (sN hab) (sN hac) (sN hax) (sN hbc) (sN hbx) (sN hcx) hFR hFG hRG (h a) (h b) (h c) (h x) hF hR hG hlt hb
    hcap).post (fun _ ⟨h1, h2, f⟩ => ⟨by
      intro i
      by_cases ex : i = x
      · subst ex; simpa using h2
      · rw [Function.update_of_ne ex]
        by_cases ec : i = c
        · subst ec; simpa using h1
        · rw [Function.update_of_ne ec]
          exact f.numOn (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨fun h' => ec (S.injective h'), fun h' => ex (S.injective h')⟩) (h i), f⟩)

end Ops

end NearCubicGates.Close.Expand
