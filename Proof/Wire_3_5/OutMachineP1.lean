import Proof.Wire_3_5.OutMachineHalf
import Proof.Wire_3_5.OutMachineVal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.P1
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires.WireExponent3_5.FinalPass.Out.Half
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## State helpers -/

theorem sets_sets (σ : WState ns nr) (i : Fin (ns + 1)) (a b : List Bool) : (σ.sets i a).sets i b = σ.sets i b :=
  WState.eq rfl (by simp) rfl rfl

theorem sets_comm (σ : WState ns nr) {i j : Fin (ns + 1)} (a b : List Bool) (h : i ≠ j) :
    (σ.sets i a).sets j b = (σ.sets j b).sets i a :=
  WState.eq rfl (by simp [Function.update_comm h]) rfl rfl

theorem seth_comm (σ : WState ns nr) {i j : Fin (ns + 1)} (x y : ℕ) (h : i ≠ j) :
    (σ.seth i x).seth j y = (σ.seth j y).seth i x :=
  WState.eq (by simp [Function.update_comm h]) rfl rfl rfl

theorem numOn_sets_ne (σ : WState ns nr) {X Y : Fin (ns + 1)} (w : List Bool) (W v : ℕ) (h : Y ≠ X)
    (hY : NumOn σ Y W v) : NumOn (σ.sets X w) Y W v :=
  ⟨by simp [Function.update_of_ne h, hY.1], by simp [hY.2]⟩

theorem numOn_setv (σ : WState ns nr) (Y : Fin (ns + 1)) (r : Fin nr) (x W v : ℕ) (hY : NumOn σ Y W v) :
    NumOn (σ.setv r x) Y W v := ⟨hY.1, hY.2⟩

theorem numOn_sets_self (σ : WState ns nr) (X : Fin (ns + 1)) (W v : ℕ) (h : σ.sh X = 0) :
    NumOn (σ.sets X (frame (binary W v))) X W v := ⟨by simp, by simp [h]⟩

theorem frame_split (w : List Bool) : frame w = frameP [] ++ frameP w ++ false :: [] := by
  rw [frame_eq_frameP]; simp

theorem bit0_frame (W a : ℕ) (hW : 1 ≤ W) : readTapeBit (frame (binary W a)) 1 = (a % 2 == 1) := by
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  rfl

/-! ## Counting the bits -/

/-- One marker: two cells on, `K += 1`, `R += 2`. -/
def cntStep (A : Fin (ns + 1)) (R K : Fin nr) : WM ns nr :=
  .seq (.fwd A) (.seq (.fwd A) (.seq (.inc K) (.seq (.inc R) (.inc R))))

/-- **`K := W`**: walk the markers of the framed word on `A`, then back by `R`. -/
def cntW (A : Fin (ns + 1)) (R K : Fin nr) : WM ns nr := .seq (.whs A (cntStep A R K)) (WM.rewind A R)

theorem cntLoop_spec (A : Fin (ns + 1)) (R K : Fin nr) (hRK : R ≠ K) (rest : List Bool) :
    ∀ (ws pre : List Bool) (σ : WState ns nr), σ.st A = frameP pre ++ frameP ws ++ false :: rest →
      σ.sh A = 2 * pre.length → σ.val K + ws.length ≤ cap → σ.val R + 2 * ws.length ≤ cap →
      WExec cap (.whs A (cntStep A R K)) σ
        (((σ.seth A (2 * (pre.length + ws.length))).setv K (σ.val K + ws.length)).setv R
          (σ.val R + 2 * ws.length)) (17 * ws.length + 1)
  | [], pre, σ, hA, hh, _, _ => by
    have hb : wbit σ A = false := by
      unfold wbit
      rw [hA, hh, ← frameP_length]
      simpa using readTapeBit_mid (frameP pre) rest false
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    simp only [List.length_nil, Nat.add_zero, Nat.mul_zero]
    rw [← hh, wseth_same, wsetv_same, wsetv_same]
  | w :: ws, pre, σ, hA, hh, hK, hR => by
    have hb : wbit σ A = true := by
      unfold wbit
      have e : frameP pre ++ frameP (w :: ws) ++ false :: rest =
          frameP pre ++ true :: (w :: (frameP ws ++ false :: rest)) := by simp
      rw [hA, hh, e, ← frameP_length, readTapeBit_mid]
    have e0 : σ = σ.seth A (2 * pre.length) := by rw [← hh, wseth_same]
    have s1 := fwd_to cap A σ (2 * pre.length)
    have s2 := fwd_to cap A σ (2 * pre.length + 1)
    obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr, τ = σ.seth A (2 * pre.length + 1 + 1) := ⟨_, rfl⟩
    rw [← hσ2] at s2
    have s3 := WExec.inc (cap := cap) K σ2 (by rw [hσ2]; simp at hK ⊢; omega)
    obtain ⟨σ3, hσ3⟩ : ∃ τ : WState ns nr, τ = σ2.setv K (σ2.val K + 1) := ⟨_, rfl⟩
    rw [← hσ3] at s3
    have s4 := WExec.inc (cap := cap) R σ3 (by
      rw [hσ3, hσ2]; simp [WState.setv_val, Function.update_of_ne hRK]; simp at hR; omega)
    obtain ⟨σ4, hσ4⟩ : ∃ τ : WState ns nr, τ = σ3.setv R (σ3.val R + 1) := ⟨_, rfl⟩
    rw [← hσ4] at s4
    have s5 := WExec.inc (cap := cap) R σ4 (by
      rw [hσ4, hσ3, hσ2]; simp [WState.setv_val, Function.update_of_ne hRK]; simp at hR; omega)
    obtain ⟨σ5, hσ5⟩ : ∃ τ : WState ns nr, τ = σ4.setv R (σ4.val R + 1) := ⟨_, rfl⟩
    rw [← hσ5] at s5
    have body := WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))
    rw [← e0] at body
    have h5K : σ5.val K = σ.val K + 1 := by
      rw [hσ5, hσ4, hσ3, hσ2]; simp [WState.setv_val, Function.update_of_ne hRK, Function.update_of_ne (Ne.symm hRK)]
    have h5R : σ5.val R = σ.val R + 2 := by
      rw [hσ5, hσ4, hσ3, hσ2]; simp [WState.setv_val, Function.update_of_ne hRK, Function.update_of_ne (Ne.symm hRK)]
    have h5st : σ5.st A = frameP (pre ++ [w]) ++ frameP ws ++ false :: rest := by
      rw [hσ5, hσ4, hσ3, hσ2]; simp [hA, frameP_app]
    have h5sh : σ5.sh A = 2 * (pre ++ [w]).length := by
      rw [hσ5, hσ4, hσ3, hσ2]; simp; omega
    have ih := cntLoop_spec A R K hRK rest ws (pre ++ [w]) σ5 h5st h5sh (by rw [h5K]; simp at hK; omega)
      (by rw [h5R]; simp at hR; omega)
    refine WExec.cast cap (WExec.whsT hb body ih) ?_ (by simp; omega)
    rw [h5K, h5R]
    subst hσ5 hσ4 hσ3 hσ2
    refine WState.eq ?_ rfl ?_ rfl
    · funext j
      by_cases h : j = A
      · subst h; simp; omega
      · simp [Function.update_of_ne h]
    · funext j
      by_cases h1 : j = R
      · subst h1; simp; omega
      · by_cases h2 : j = K
        · subst h2; simp [Function.update_of_ne h1]; omega
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]

/-- **`K := W`** from a framed `W`-bit word on `A` (`R`, `K` zero). -/
theorem cntW_spec (A : Fin (ns + 1)) (R K : Fin nr) (hRK : R ≠ K) (W x : ℕ) (σ : WState ns nr)
    (hA : NumOn σ A W x) (hR : σ.val R = 0) (hK : σ.val K = 0) (hc : 2 * W ≤ cap) :
    WExec cap (cntW A R K) σ (σ.setv K W) (27 * W + 3) := by
  have l := cntLoop_spec cap A R K hRK [] (binary W x) [] σ (by rw [hA.1, frame_split]) (by simp [hA.2])
    (by simp [hK]; omega) (by simp [hR]; omega)
  simp only [SignedSortKey.binary_length, List.length_nil, Nat.zero_add, hK, hR] at l
  have r := wrewind_spec cap A R (2 * W) (((σ.seth A (2 * W)).setv K W).setv R (2 * W)) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq l r) ?_ (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext j
    simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs with h
    · subst h; simp [hA.2]
    · rfl
  · funext j
    simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs with h1 h2 <;> (try subst_vars) <;> simp_all

/-! ## One round of stripping -/

/-- Both heads back from the first bits. -/
theorem back2 (N D : Fin (ns + 1)) (hND : N ≠ D) (σ : WState ns nr) (hN : σ.sh N = 0) (hD : σ.sh D = 0) :
    WExec cap (.seq (.bwd N) (.bwd D)) ((σ.seth N 1).seth D 1) σ 3 := by
  have b1 := WExec.bwd (cap := cap) N ((σ.seth N 1).seth D 1)
  have b2 := WExec.bwd (cap := cap) D (((σ.seth N 1).seth D 1).seth N (((σ.seth N 1).seth D 1).sh N - 1))
  refine WExec.cast cap (WExec.seq b1 b2) ?_ (by omega)
  refine WState.eq ?_ rfl rfl rfl
  funext j
  by_cases hj : j = D
  · subst hj; simp [Function.update_apply, hND, Ne.symm hND, hD]
  · by_cases hj' : j = N
    · subst hj'; simp [Function.update_apply, hND, Ne.symm hND, hN]
    · simp [Function.update_apply, hj, hj']

/-- **One round**: if `N` and `D` are both even, halve both; then `K -= 1`. -/
def stripBody (N D : Fin (ns + 1)) (R K : Fin nr) : WM ns nr :=
  .seq (.fwd N) (.seq (.fwd D) (.seq
    (.ifs N (.seq (.bwd N) (.bwd D))
      (.ifs D (.seq (.bwd N) (.bwd D)) (.seq (.seq (.bwd N) (.bwd D)) (.seq (halfW N R) (halfW D R)))))
    (.dec K)))

theorem stripBody_spec (N D : Fin (ns + 1)) (R K : Fin nr) (hND : N ≠ D) (W a b k : ℕ)
    (σ : WState ns nr) (hW : 1 ≤ W) (hN : NumOn σ N W a) (hD : NumOn σ D W b) (ha : a < 2 ^ W) (hb : b < 2 ^ W)
    (hR : σ.val R = 0) (hK : σ.val K = k + 1) (hk : k + 1 ≤ cap) (hc : 2 * W ≤ cap) :
    WExec cap (stripBody N D R K) σ
      (((σ.sets N (frame (binary W (stripStep (a, b)).1))).sets D (frame (binary W (stripStep (a, b)).2))).setv K k)
      (68 * W + 19) := by
  have s1 : WExec cap (.fwd N) σ (σ.seth N 1) 1 := by
    have h := WExec.fwd (cap := cap) N σ
    rwa [hN.2] at h
  have s2 : WExec cap (.fwd D) (σ.seth N 1) ((σ.seth N 1).seth D 1) 1 := by
    have h := WExec.fwd (cap := cap) D (σ.seth N 1)
    rwa [WState.seth_sh, Function.update_of_ne (Ne.symm hND), hD.2] at h
  have bN : wbit ((σ.seth N 1).seth D 1) N = (a % 2 == 1) := by
    unfold wbit
    simp only [WState.seth_st, WState.seth_sh, Function.update_of_ne hND, Function.update_self, hN.1]
    exact bit0_frame W a hW
  have bD : wbit ((σ.seth N 1).seth D 1) D = (b % 2 == 1) := by
    unfold wbit
    simp only [WState.seth_st, WState.seth_sh, Function.update_self, hD.1]
    exact bit0_frame W b hW
  have bk := back2 cap N D hND σ hN.2 hD.2
  have hself : (σ.sets N (frame (binary W a))).sets D (frame (binary W b)) = σ := by
    rw [← hN.1, ← hD.1, wsets_same, wsets_same]
  have hbr : WExec cap (.ifs N (.seq (.bwd N) (.bwd D))
      (.ifs D (.seq (.bwd N) (.bwd D)) (.seq (.seq (.bwd N) (.bwd D)) (.seq (halfW N R) (halfW D R)))))
      ((σ.seth N 1).seth D 1)
      ((σ.sets N (frame (binary W (stripStep (a, b)).1))).sets D (frame (binary W (stripStep (a, b)).2)))
      (68 * W + 13) := by
    by_cases h2 : a % 2 = 0 ∧ b % 2 = 0
    · have e : stripStep (a, b) = (a / 2, b / 2) := by simp [stripStep, h2]
      have hN' := halfW_spec cap N R W a σ hN hR ha hc
      have hD' := halfW_spec cap D R W b (σ.sets N (frame (binary W (a / 2))))
        (numOn_sets_ne σ _ W b (Ne.symm hND) hD) (by simp [hR]) hb hc
      have bN' : wbit ((σ.seth N 1).seth D 1) N = false := by rw [bN]; simp [h2.1]
      have bD' : wbit ((σ.seth N 1).seth D 1) D = false := by rw [bD]; simp [h2.2]
      rw [e]
      exact WExec.mono (WExec.ifsF bN' (WExec.ifsF bD' (WExec.seq bk (WExec.seq hN' hD')))) (by omega)
    · have e : stripStep (a, b) = (a, b) := by simp [stripStep, h2]
      rw [e, hself]
      by_cases h3 : a % 2 = 0
      · have h4 : b % 2 = 1 := by omega
        have bN' : wbit ((σ.seth N 1).seth D 1) N = false := by rw [bN]; simp [h3]
        have bD' : wbit ((σ.seth N 1).seth D 1) D = true := by rw [bD]; simp [h4]
        exact WExec.mono (WExec.ifsF bN' (WExec.ifsT bD' bk)) (by omega)
      · have h4 : a % 2 = 1 := by omega
        have bN' : wbit ((σ.seth N 1).seth D 1) N = true := by rw [bN]; simp [h4]
        exact WExec.mono (WExec.ifsT bN' bk) (by omega)
  have hdec := WExec.dec (cap := cap) K
    ((σ.sets N (frame (binary W (stripStep (a, b)).1))).sets D (frame (binary W (stripStep (a, b)).2)))
    (by simp [hK]; omega)
  simp only [WState.sets_val, hK, Nat.add_sub_cancel] at hdec
  exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq hbr hdec))) rfl (by omega)

theorem stripStep_lt (W a b : ℕ) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    (stripStep (a, b)).1 < 2 ^ W ∧ (stripStep (a, b)).2 < 2 ^ W := by
  have := Val.stripStep_le (a, b)
  simp only at this
  omega

/-- **The rounds**: `K` rounds give `stripStep^[K] (a, b)` on `N`, `D`. -/
theorem stripLoop_spec (N D : Fin (ns + 1)) (R K : Fin nr) (hND : N ≠ D) (hRK : R ≠ K) (W : ℕ) (hc : 2 * W ≤ cap)
    (hWc : W ≤ cap) :
    ∀ (k a b : ℕ) (σ : WState ns nr), k ≤ W → NumOn σ N W a → NumOn σ D W b → a < 2 ^ W → b < 2 ^ W →
      σ.val R = 0 → σ.val K = k →
      WExec cap (.whr K (stripBody N D R K)) σ
        (((σ.sets N (frame (binary W (stripStep^[k] (a, b)).1))).sets D
          (frame (binary W (stripStep^[k] (a, b)).2))).setv K 0) (k * (68 * W + 21) + 1)
  | 0, a, b, σ, _, hN, hD, _, _, _, hK => by
    refine WExec.cast cap (WExec.whrF hK) ?_ (by omega)
    have e := wsetv_same σ K
    rw [hK] at e
    simp only [Function.iterate_zero, id]
    rw [← hN.1, ← hD.1, wsets_same, wsets_same, e]
  | k + 1, a, b, σ, hkW, hN, hD, ha, hb, hR, hK => by
    have body := stripBody_spec cap N D R K hND W a b k σ (by omega) hN hD ha hb hR hK (by omega) hc
    have hlt := stripStep_lt W a b ha hb
    have hN1 : NumOn (((σ.sets N (frame (binary W (stripStep (a, b)).1))).sets D
        (frame (binary W (stripStep (a, b)).2))).setv K k) N W (stripStep (a, b)).1 :=
      numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ hND (numOn_sets_self σ N W _ hN.2))
    have hD1 : NumOn (((σ.sets N (frame (binary W (stripStep (a, b)).1))).sets D
        (frame (binary W (stripStep (a, b)).2))).setv K k) D W (stripStep (a, b)).2 :=
      numOn_setv _ _ _ _ _ _ (numOn_sets_self _ D W _ (by simp [hD.2]))
    have ih := stripLoop_spec N D R K hND hRK W hc hWc k (stripStep (a, b)).1 (stripStep (a, b)).2 _ (by omega)
      hN1 hD1 hlt.1 hlt.2 (by simp [hR, Function.update_of_ne hRK]) (by simp)
    rw [Prod.mk.eta] at ih
    refine WExec.cast cap (WExec.whrT (by omega) body ih) ?_ (by ring_nf; omega)
    rw [Function.iterate_succ_apply]
    refine WState.eq rfl ?_ ?_ rfl
    · funext j; simp only [WState.setv_st, WState.sets_st, Function.update_apply]; split_ifs <;> rfl
    · funext j; simp only [WState.setv_val, WState.sets_val, Function.update_apply]; split_ifs <;> rfl

/-! ## The room words -/

/-- X1's binary writer's registers: `Rg 0 = rg 1` (holding `0`), `Rg 1 = rW` (`W`), `Rg 2 … 7` scratch. -/
def rgB : Fin 8 → Fin nrO := ![rg 1, rW, rK, rg 0, rg 2, rg 3, rg 4, rg 5]

theorem rgB_inj : Function.Injective rgB := by decide

/-- `binW` at value `0` on each stream of `l`. -/
def mkZ : List (Fin (nsO + 1)) → WM nsO nrO
  | [] => .skip
  | s :: l => .seq (UnionMachine.BinW.binW s rgB) (mkZ l)

/-- `σ` with the streams of `l` set to `w`. -/
def setsL (σ : St) (l : List (Fin (nsO + 1))) (w : List Bool) : St :=
  ⟨σ.sh, fun i => if i ∈ l then w else σ.st i, σ.val, σ.cell⟩

theorem mkZ_spec (W : ℕ) (hc : 2 * W + 2 ≤ cap) : ∀ (l : List (Fin (nsO + 1))) (σ : St), l.Nodup →
    (∀ s ∈ l, σ.st s = [] ∧ σ.sh s = 0) → σ.val (rgB 0) = 0 → σ.val (rgB 1) = W →
    (∀ j : Fin 8, 2 ≤ j.val → σ.val (rgB j) = 0) →
    WExec cap (mkZ l) σ (setsL σ l (frame (binary W 0))) (l.length * (UnionMachine.BinW.binCost 0 W + 1))
  | [], σ, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.skip σ) ?_ (by simp)
    exact WState.eq rfl (by funext i; simp [setsL]) rfl rfl
  | s :: l, σ, hnd, hl, h0, hW, hz => by
    have hs := hl s (by simp)
    have b := UnionMachine.BinW.binW_spec cap s rgB rgB_inj σ 0 W h0 hW hz hs.1 hs.2 (by omega)
    have hnd' := List.nodup_cons.1 hnd
    have ih := mkZ_spec W hc l (σ.sets s (frame (binary W 0))) hnd'.2 (fun s' hs' => by
      have hne : s' ≠ s := fun h => hnd'.1 (h ▸ hs')
      have := hl s' (by simp [hs'])
      simp [Function.update_of_ne hne, this.1, this.2]) h0 hW hz
    refine WExec.cast cap (WExec.seq b ih) ?_ (by simp [Nat.succ_mul]; omega)
    refine WState.eq rfl ?_ rfl rfl
    funext i
    by_cases h1 : i ∈ l
    · simp [setsL, h1]
    · by_cases h2 : i = s
      · subst h2; simp [setsL, h1]
      · simp [setsL, h1, h2, Function.update_of_ne h2]

/-! ## P1 -/

/-- The streams made `0`: `U, V, T, X 0 … X 5`. -/
def zL : List (Fin (nsO + 1)) := [sU, sV, sT, sX 0, sX 1, sX 2, sX 3, sX 4, sX 5]

theorem zL_nodup : zL.Nodup := by decide

theorem zL_off : ∀ s ∈ zL, s ≠ sN ∧ s ≠ sD ∧ s ≠ sO := by decide

theorem sX_mem (j : Fin 6) : sX j ∈ zL := by fin_cases j <;> decide

/-- **P1's program**: `rW := W`, the room words, `rK := W`, `W` rounds of stripping. -/
def p1P : WM nsO nrO :=
  .seq (cntW sN rR rW) (.seq (mkZ zL) (.seq (UnionMachine.BinW.dupR rW rK (rg 0)) (.whr rK (stripBody sN sD rR rK))))

/-- P1's cost. -/
def p1Cost (W : ℕ) : ℕ :=
  27 * W + 3 + 1 + (9 * (UnionMachine.BinW.binCost 0 W + 1) + 1 + (18 * W + 3 + 1 + (W * (68 * W + 21) + 1)))

theorem p1Cost_le (W : ℕ) : p1Cost W ≤ 1300 * (W + 1) ^ 2 := by
  unfold p1Cost UnionMachine.BinW.binCost
  nlinarith [Nat.zero_le W]

theorem p1_run (W num den : ℕ) (σ : St) (h : Entry σ W num den) (hn : num < 2 ^ W) (hd : den < 2 ^ W) :
    ∃ τ, WExec (capO W) p1P σ τ (p1Cost W) ∧ Words τ W (strip W num den).1 (strip W num den).2 0 0 := by
  have hreg : ∀ r, σ.val r = 0 := fun r => by
    by_cases hr : r = rW
    · subst hr; exact h.bd.hw
    · exact h.bd.regs r hr
  have hNum : NumOn σ sN W num := ⟨h.hn, h.bd.heads _⟩
  have sA := cntW_spec (capO W) sN rR rW (by decide) W num σ hNum (hreg _) (hreg _) (by unfold capO; omega)
  have vA : ∀ r, (σ.setv rW W).val r = if r = rW then W else 0 := fun r => by
    by_cases hr : r = rW
    · subst hr; simp
    · simp [hr, Function.update_of_ne hr, hreg r]
  have hgB : ∀ j : Fin 8, 2 ≤ j.val → rgB j ≠ rW := by decide
  have sB := mkZ_spec (capO W) W (by unfold capO; omega) zL (σ.setv rW W) zL_nodup
    (fun s hs => ⟨by simp [h.blank s (zL_off s hs).1 (zL_off s hs).2.1], by simp [h.bd.heads s]⟩)
    (by rw [vA, if_neg (by decide)]) (by rw [vA, if_pos (by decide)]) (fun j hj => by rw [vA, if_neg (hgB j hj)])
  have vB : ∀ r, (setsL (σ.setv rW W) zL (frame (binary W 0))).val r = if r = rW then W else 0 := vA
  have sC := UnionMachine.BinW.dupR_spec (capO W) rW rK (rg 0) (by decide) (by decide) (by decide)
    (setsL (σ.setv rW W) zL (frame (binary W 0))) W (by rw [vB]; simp) (by rw [vB, if_neg (by decide)])
    (by rw [vB, if_neg (by decide)])
    (by unfold capO; omega)
  set σC := (setsL (σ.setv rW W) zL (frame (binary W 0))).setv rK W with hσC
  have vC : ∀ r, σC.val r = if r = rW then W else if r = rK then W else 0 := fun r => by
    by_cases hr : r = rK
    · subst hr; simp [hσC]
    · rw [hσC, WState.setv_val, Function.update_of_ne hr, vB]
      by_cases hr' : r = rW <;> simp [hr, hr']
  have stC : ∀ i, σC.st i = if i ∈ zL then frame (binary W 0) else σ.st i := fun i => rfl
  have shC : ∀ i, σC.sh i = 0 := fun i => h.bd.heads i
  have hN' : NumOn σC sN W num := ⟨by rw [stC, if_neg (by decide)]; exact h.hn, shC _⟩
  have hD' : NumOn σC sD W den := ⟨by rw [stC, if_neg (by decide)]; exact h.hd, shC _⟩
  have sLoop := stripLoop_spec (capO W) sN sD rR rK (by decide) (by decide) W (by unfold capO; omega)
    (by unfold capO; omega) W num den σC le_rfl hN' hD' hn hd (by rw [vC, if_neg (by decide), if_neg (by decide)])
    (by rw [vC]; simp)
  set τ := ((σC.sets sN (frame (binary W (strip W num den).1))).sets sD
    (frame (binary W (strip W num den).2))).setv rK 0 with hτ
  refine ⟨τ, WExec.cast (capO W) (WExec.seq sA (WExec.seq sB (WExec.seq sC sLoop))) rfl
    (by simp [p1Cost, zL]), ?_⟩
  have stT : ∀ i, i ≠ sN → i ≠ sD → τ.st i = σC.st i := fun i h1 h2 => by
    simp [hτ, Function.update_of_ne h1, Function.update_of_ne h2]
  have zOn : ∀ s ∈ zL, NumOn τ s W 0 := fun s hs =>
    ⟨by rw [stT s (zL_off s hs).1 (zL_off s hs).2.1, stC, if_pos hs], by simp [hτ, shC]⟩
  refine ⟨⟨fun i => by simp [hτ, shC], h.bd.cell,
    by rw [hτ, WState.setv_val, Function.update_of_ne (by decide), WState.sets_val, WState.sets_val, vC, if_pos rfl],
    fun r hr => ?_⟩, ?_, ?_, ?_,
    zOn sU (by decide), zOn sV (by decide), ⟨0, zOn sT (by decide)⟩, fun j => zOn (sX j) (sX_mem j)⟩
  · by_cases hk : r = rK
    · subst hk; simp [hτ]
    · simp [hτ, Function.update_of_ne hk, vC, hr, hk]
  · rw [stT sO (by decide) (by decide), stC, if_neg (by decide)]
    exact h.blank sO (by decide) (by decide)
  · exact ⟨by simp [hτ, Function.update_of_ne (show sN ≠ sD by decide)], by simp [hτ, shC]⟩
  · exact ⟨by simp [hτ], by simp [hτ, shC]⟩

/-- **P1**. -/
def ph1 : Ph1 := ⟨p1P, p1Cost, 1300, p1Cost_le, p1_run⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.P1
