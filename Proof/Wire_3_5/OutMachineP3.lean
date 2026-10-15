import Proof.Wire_3_5.OutMachineP2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.P3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires.WireExponent3_5.FinalPass.Out.Half NearCubicWires.WireExponent3_5.FinalPass.Out.P1
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (ltB copyB subB ltB_spec copyB_spec subB_spec)

/-! ## The round -/

/-- Swap `U` and `V` through `T` (the flag cleared first). -/
def swapB : WM nsO nrO := .seq (.dec rF) (.seq (copyB sT sU rF rR) (.seq (copyB sU sV rF rR) (copyB sV sT rF rR)))

/-- `v` odd: `rF := [v < u]`, swap if set, `V := V − U`. -/
def oddB : WM nsO nrO := .seq (.bwd sV) (.seq (ltB sV sU rF rR) (.seq (.ifr rF swapB .skip) (subB sV sU rF rR)))

/-- **One Stein round**: read `v`'s low bit; if odd, `oddB`; halve `V`; `rK -= 1`. -/
def steinBody : WM nsO nrO := .seq (.fwd sV) (.seq (.ifs sV oddB (.bwd sV)) (.seq (halfW sV rR) (.dec rK)))

/-- **The rounds' invariant**: `Words` with the round counter `rK = k`. -/
structure LoopSt (σ : St) (W a b u v k : ℕ) : Prop where
  heads : ∀ i, σ.sh i = 0
  cell : σ.cell = false
  hw : σ.val rW = W
  hk : σ.val rK = k
  regs : ∀ r, r ≠ rW → r ≠ rK → σ.val r = 0
  ho : σ.st sO = []
  hn : NumOn σ sN W a
  hd : NumOn σ sD W b
  hu : NumOn σ sU W u
  hv : NumOn σ sV W v
  ht : ∃ x, NumOn σ sT W x
  hx : ∀ j, NumOn σ (sX j) W 0

abbrev fb (W x : ℕ) : List Bool := frame (binary W x)

theorem sX_ne (j : Fin 6) : sX j ≠ sU ∧ sX j ≠ sV ∧ sX j ≠ sT := by fin_cases j <;> decide

theorem ls_setsU {σ : St} {W a b u v k : ℕ} (h : LoopSt σ W a b u v k) (u' : ℕ) :
    LoopSt (σ.sets sU (fb W u')) W a b u' v k :=
  ⟨h.heads, h.cell, h.hw, h.hk, h.regs, by simp [Function.update_of_ne (show sO ≠ sU by decide), h.ho],
    numOn_sets_ne _ _ _ _ (by decide) h.hn, numOn_sets_ne _ _ _ _ (by decide) h.hd,
    numOn_sets_self _ _ _ _ (h.heads _), numOn_sets_ne _ _ _ _ (by decide) h.hv,
    h.ht.imp fun _ hx => numOn_sets_ne _ _ _ _ (by decide) hx,
    fun j => numOn_sets_ne _ _ _ _ (sX_ne j).1 (h.hx j)⟩

theorem ls_setsV {σ : St} {W a b u v k : ℕ} (h : LoopSt σ W a b u v k) (v' : ℕ) :
    LoopSt (σ.sets sV (fb W v')) W a b u v' k :=
  ⟨h.heads, h.cell, h.hw, h.hk, h.regs, by simp [Function.update_of_ne (show sO ≠ sV by decide), h.ho],
    numOn_sets_ne _ _ _ _ (by decide) h.hn, numOn_sets_ne _ _ _ _ (by decide) h.hd,
    numOn_sets_ne _ _ _ _ (by decide) h.hu, numOn_sets_self _ _ _ _ (h.heads _),
    h.ht.imp fun _ hx => numOn_sets_ne _ _ _ _ (by decide) hx,
    fun j => numOn_sets_ne _ _ _ _ (sX_ne j).2.1 (h.hx j)⟩

theorem ls_setsT {σ : St} {W a b u v k : ℕ} (h : LoopSt σ W a b u v k) (x : ℕ) :
    LoopSt (σ.sets sT (fb W x)) W a b u v k :=
  ⟨h.heads, h.cell, h.hw, h.hk, h.regs, by simp [Function.update_of_ne (show sO ≠ sT by decide), h.ho],
    numOn_sets_ne _ _ _ _ (by decide) h.hn, numOn_sets_ne _ _ _ _ (by decide) h.hd,
    numOn_sets_ne _ _ _ _ (by decide) h.hu, numOn_sets_ne _ _ _ _ (by decide) h.hv,
    ⟨x, numOn_sets_self _ _ _ _ (h.heads _)⟩,
    fun j => numOn_sets_ne _ _ _ _ (sX_ne j).2.2 (h.hx j)⟩

theorem ls_setvK {σ : St} {W a b u v k : ℕ} (h : LoopSt σ W a b u v k) (k' : ℕ) :
    LoopSt (σ.setv rK k') W a b u v k' :=
  ⟨h.heads, h.cell, by simp [Function.update_of_ne (show rW ≠ rK by decide), h.hw], by simp,
    fun r h1 h2 => by simp [Function.update_of_ne h2, h.regs r h1 h2], h.ho,
    numOn_setv _ _ _ _ _ _ h.hn, numOn_setv _ _ _ _ _ _ h.hd, numOn_setv _ _ _ _ _ _ h.hu,
    numOn_setv _ _ _ _ _ _ h.hv, h.ht.imp fun _ hx => numOn_setv _ _ _ _ _ _ hx,
    fun j => numOn_setv _ _ _ _ _ _ (h.hx j)⟩

theorem ls_F {σ : St} {W a b u v k : ℕ} (h : LoopSt σ W a b u v k) : σ.val rF = 0 := h.regs rF (by decide) (by decide)
theorem ls_R {σ : St} {W a b u v k : ℕ} (h : LoopSt σ W a b u v k) : σ.val rR = 0 := h.regs rR (by decide) (by decide)

/-- The odd branch: `U, V := u', w` with `(u', w) = (v, u − v)` if `v < u`, else `(u, v − u)`. -/
theorem oddB_spec (W a b u v k : ℕ) (σ : St) (h : LoopSt σ W a b u v k) (hu : u < 2 ^ W) (hv : v < 2 ^ W) :
    ∃ ρ, WExec (capO W) oddB (σ.seth sV 1) ρ (205 * W + 31) ∧
      LoopSt ρ W a b (if v < u then v else u) (if v < u then u - v else v - u) k := by
  have hc : 2 * W + 1 ≤ capO W := by unfold capO; omega
  have bk : WExec (capO W) (.bwd sV) (σ.seth sV 1) σ 1 := by
    have e := WExec.bwd (cap := capO W) sV (σ.seth sV 1)
    rwa [wseth_sh_self, Nat.sub_self, wseth_seth, ← h.heads sV, wseth_same] at e
  have slt := ltB_spec (capO W) W (show sV ≠ sU by decide) (show rF ≠ rR by decide) σ v u h.hv h.hu (ls_F h) (ls_R h)
    hv hu hc
  by_cases hvu : v < u
  · simp only [hvu, if_true, decide_true, Bool.toNat_true] at slt ⊢
    have hdF : WExec (capO W) (.dec rF) (σ.setv rF 1) σ 1 := by
      have e := WExec.dec (cap := capO W) rF (σ.setv rF 1) (by simp; unfold capO; omega)
      have e2 : (σ.setv rF 1).setv rF ((σ.setv rF 1).val rF - 1) = σ := by
        rw [wsetv_setv]; simp only [wsetv_val_self, Nat.sub_self]; rw [← ls_F h, wsetv_same]
      rwa [e2] at e
    obtain ⟨x, hx⟩ := h.ht
    have c1 := copyB_spec (capO W) W (show sT ≠ sU by decide) (show rF ≠ rR by decide) σ x u hx h.hu (ls_F h)
      (ls_R h) hc
    have h1 := ls_setsT h u
    have c2 := copyB_spec (capO W) W (show sU ≠ sV by decide) (show rF ≠ rR by decide) _ u v h1.hu h1.hv (ls_F h1)
      (ls_R h1) hc
    have h2 := ls_setsU h1 v
    have c3 := copyB_spec (capO W) W (show sV ≠ sT by decide) (show rF ≠ rR by decide) _ v u h2.hv
      (numOn_sets_ne _ _ _ _ (by decide) (numOn_sets_self σ sT W u (h.heads _))) (ls_F h2) (ls_R h2) hc
    have h3 := ls_setsV h2 u
    have sw : WExec (capO W) swapB (σ.setv rF 1)
        (((σ.sets sT (fb W u)).sets sU (fb W v)).sets sV (fb W u)) (123 * W + 14) :=
      WExec.cast (capO W) (WExec.seq hdF (WExec.seq c1 (WExec.seq c2 c3))) rfl (by omega)
    have sif : WExec (capO W) (.ifr rF swapB .skip) (σ.setv rF 1)
        (((σ.sets sT (fb W u)).sets sU (fb W v)).sets sV (fb W u)) (123 * W + 15) :=
      WExec.ifrT (by simp) sw
    have sb := subB_spec (capO W) W (show sV ≠ sU by decide) (show rF ≠ rR by decide) _ u v h3.hv h3.hu (ls_F h3)
      (ls_R h3) hvu.le hu hc
    exact ⟨_, WExec.cast (capO W) (WExec.seq bk (WExec.seq slt (WExec.seq sif sb))) rfl (by omega),
      ls_setsV h3 (u - v)⟩
  · simp only [hvu, if_false, decide_false, Bool.toNat_false] at slt ⊢
    have e0 : σ.setv rF 0 = σ := by rw [← ls_F h, wsetv_same]
    rw [e0] at slt
    have sif : WExec (capO W) (.ifr rF swapB .skip) σ σ 1 := WExec.ifrF (ls_F h) (WExec.skip σ)
    have sb := subB_spec (capO W) W (show sV ≠ sU by decide) (show rF ≠ rR by decide) σ v u h.hv h.hu (ls_F h)
      (ls_R h) (by omega) hv hc
    exact ⟨_, WExec.cast (capO W) (WExec.seq bk (WExec.seq slt (WExec.seq sif sb))) rfl (by omega),
      ls_setsV h (v - u)⟩

/-- **One Stein round**. -/
theorem steinBody_spec (W a b u v k : ℕ) (σ : St) (hW : 1 ≤ W) (hkW : k + 1 ≤ W) (h : LoopSt σ W a b u v (k + 1))
    (hu : u < 2 ^ W) (hv : v < 2 ^ W) :
    ∃ ρ, WExec (capO W) steinBody σ ρ (239 * W + 40) ∧
      LoopSt ρ W a b (Val.steinStep (u, v)).1 (Val.steinStep (u, v)).2 k := by
  have hc : 2 * W ≤ capO W := by unfold capO; omega
  have s1 : WExec (capO W) (.fwd sV) σ (σ.seth sV 1) 1 := by
    have e := WExec.fwd (cap := capO W) sV σ
    rwa [h.hv.2] at e
  have bV : wbit (σ.seth sV 1) sV = (v % 2 == 1) := by
    unfold wbit
    simp only [WState.seth_st, WState.seth_sh, Function.update_self, h.hv.1]
    exact bit0_frame W v hW
  by_cases hodd : v % 2 = 1
  · obtain ⟨ρ, hρ, hl⟩ := oddB_spec W a b u v (k + 1) σ h hu hv
    have b' : wbit (σ.seth sV 1) sV = true := by rw [bV]; simp [hodd]
    have hw' : (if v < u then u - v else v - u) < 2 ^ W := by split_ifs <;> omega
    have sh := halfW_spec (capO W) sV rR W _ ρ hl.hv (ls_R hl) hw' hc
    have hl2 := ls_setsV hl ((if v < u then u - v else v - u) / 2)
    have sd := WExec.dec (cap := capO W) rK (ρ.sets sV (fb W ((if v < u then u - v else v - u) / 2)))
      (by rw [hl2.hk]; unfold capO; omega)
    rw [hl2.hk, Nat.add_sub_cancel] at sd
    have e : Val.steinStep (u, v) = ((if v < u then v else u), (if v < u then u - v else v - u) / 2) := by
      unfold Val.steinStep; simp only [hodd, if_true]; split_ifs <;> rfl
    rw [e]
    exact ⟨_, WExec.cast (capO W) (WExec.seq s1 (WExec.seq (WExec.ifsT b' hρ) (WExec.seq sh sd))) rfl (by omega),
      ls_setvK hl2 k⟩
  · have b' : wbit (σ.seth sV 1) sV = false := by rw [bV]; simp; omega
    have bk : WExec (capO W) (.bwd sV) (σ.seth sV 1) σ 1 := by
      have e := WExec.bwd (cap := capO W) sV (σ.seth sV 1)
      rwa [wseth_sh_self, Nat.sub_self, wseth_seth, ← h.heads sV, wseth_same] at e
    have sh := halfW_spec (capO W) sV rR W v σ h.hv (ls_R h) hv hc
    have hl2 := ls_setsV h (v / 2)
    have sd := WExec.dec (cap := capO W) rK (σ.sets sV (fb W (v / 2))) (by rw [hl2.hk]; unfold capO; omega)
    rw [hl2.hk, Nat.add_sub_cancel] at sd
    have e : Val.steinStep (u, v) = (u, v / 2) := by
      unfold Val.steinStep; simp only [hodd, if_false]
    rw [e]
    exact ⟨_, WExec.cast (capO W) (WExec.seq s1 (WExec.seq (WExec.ifsF b' bk) (WExec.seq sh sd))) rfl (by omega),
      ls_setvK hl2 k⟩

/-- **`k` Stein rounds**. -/
theorem steinLoop_spec (W a b : ℕ) :
    ∀ (k u v : ℕ) (σ : St), k ≤ W → LoopSt σ W a b u v k → u % 2 = 1 → u < 2 ^ W → v < 2 ^ W →
      ∃ ρ, WExec (capO W) (.whr rK steinBody) σ ρ (k * (239 * W + 42) + 1) ∧
        LoopSt ρ W a b (Val.steinStep^[k] (u, v)).1 (Val.steinStep^[k] (u, v)).2 0
  | 0, u, v, σ, _, h, _, _, _ => ⟨σ, WExec.cast (capO W) (WExec.whrF h.hk) rfl (by omega), h⟩
  | k + 1, u, v, σ, hkW, h, hu1, hu, hv => by
    obtain ⟨ρ, hρ, hl⟩ := steinBody_spec W a b u v k σ (by omega) hkW h hu hv
    obtain ⟨i1, i2, i3⟩ := Val.stein_inv W u v hu1 hu hv
    obtain ⟨ρ', hρ', hl'⟩ := steinLoop_spec W a b k _ _ ρ (by omega) hl i1 i2 i3
    rw [Prod.mk.eta] at hl'
    refine ⟨ρ', WExec.cast (capO W) (WExec.whrT (by rw [h.hk]; omega) hρ hρ') rfl (by ring_nf; omega), ?_⟩
    rw [Function.iterate_succ_apply]
    exact hl'

/-! ## P3 -/

/-- `rK := W`, then `W` Stein rounds. -/
def half3 : WM nsO nrO := .seq (UnionMachine.BinW.dupR rW rK (rg 0)) (.whr rK steinBody)

/-- **P3's program**: `2W` Stein rounds. -/
def p3P : WM nsO nrO := .seq half3 half3

def h3Cost (W : ℕ) : ℕ := 18 * W + 3 + 1 + (W * (239 * W + 42) + 1)

def p3Cost (W : ℕ) : ℕ := h3Cost W + 1 + h3Cost W

theorem p3Cost_le (W : ℕ) : p3Cost W ≤ 600 * (W + 1) ^ 2 := by
  unfold p3Cost h3Cost
  nlinarith [Nat.zero_le W]

theorem half3_spec (W a b u v : ℕ) (σ : St) (h : Words σ W a b u v) (hu1 : u % 2 = 1) (hu : u < 2 ^ W)
    (hv : v < 2 ^ W) :
    ∃ ρ, WExec (capO W) half3 σ ρ (h3Cost W) ∧
      Words ρ W a b (Val.steinStep^[W] (u, v)).1 (Val.steinStep^[W] (u, v)).2 := by
  have sd := UnionMachine.BinW.dupR_spec (capO W) rW rK (rg 0) (by decide) (by decide) (by decide) σ W h.bd.hw
    (h.bd.regs rK (by decide)) (h.bd.regs (rg 0) (by decide)) (by unfold capO; omega)
  have hl : LoopSt (σ.setv rK W) W a b u v W :=
    ⟨h.bd.heads, h.bd.cell, by simp [Function.update_of_ne (show rW ≠ rK by decide), h.bd.hw], by simp,
      fun r h1 h2 => by simp [Function.update_of_ne h2, h.bd.regs r h1], by simpa using h.ho,
      numOn_setv _ _ _ _ _ _ h.hn, numOn_setv _ _ _ _ _ _ h.hd, numOn_setv _ _ _ _ _ _ h.hu,
      numOn_setv _ _ _ _ _ _ h.hv, h.ht.imp fun _ hx => numOn_setv _ _ _ _ _ _ hx,
      fun j => numOn_setv _ _ _ _ _ _ (h.hx j)⟩
  obtain ⟨ρ, hρ, hl'⟩ := steinLoop_spec W a b W u v _ le_rfl hl hu1 hu hv
  refine ⟨ρ, WExec.cast (capO W) (WExec.seq sd hρ) rfl (by unfold h3Cost; omega), ?_⟩
  exact ⟨⟨hl'.heads, hl'.cell, hl'.hw, fun r hr => by
    by_cases hk : r = rK
    · subst hk; exact hl'.hk
    · exact hl'.regs r hr hk⟩, hl'.ho, hl'.hn, hl'.hd, hl'.hu, hl'.hv, hl'.ht, hl'.hx⟩

theorem p3_run (W a b u v : ℕ) (σ : St) (h : Words σ W a b u v) (hu1 : u % 2 = 1) (hu : u < 2 ^ W)
    (hv : v < 2 ^ W) :
    ∃ τ, WExec (capO W) p3P σ τ (p3Cost W) ∧ Words τ W a b (Nat.gcd u v) 0 := by
  obtain ⟨ρ, hρ, hl⟩ := half3_spec W a b u v σ h hu1 hu hv
  obtain ⟨i1, i2, i3, _⟩ := Val.stein_iter_inv W W u v hu1 hu hv
  obtain ⟨ρ', hρ', hl'⟩ := half3_spec W a b _ _ ρ hl i1 i2 i3
  rw [Prod.mk.eta, ← Function.iterate_add_apply, ← Nat.two_mul, Val.stein_spec W u v hu1 hu hv] at hl'
  exact ⟨ρ', WExec.cast (capO W) (WExec.seq hρ hρ') rfl (by unfold p3Cost; omega), hl'⟩

/-- **P3**. -/
def ph3 : Ph3 := ⟨p3P, p3Cost, 600, p3Cost_le, p3_run⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.P3
