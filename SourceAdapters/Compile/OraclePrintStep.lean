import SourceAdapters.Compile.OraclePrintRounds

/-!
# Moving a vector to the wire map; the oracle gate and its answer wire

proof of `thm:short-pcp-ours`: in each round the query address bits feed one oracle gate, whose output is the answer wire read by
the transition formulas; after a vector of formulas its outputs are the next wires. On the cell side:
* `copyW`: the first `VC` entries of store `W2` (the vector's outputs) overwrite the wire map `WM`;
* `oracleP`: append the oracle gate's record `[5, 0, 0] ++ addresses` (addresses = the first `ell` entries of `W2`)
  and write its index (the node counter) at wire-map entry `clockBits` (`PS.oracle`, `putAt`).
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Compile (OracleCompilationRequest)

set_option autoImplicit false

variable {C : Ctx} {n arity : ℕ}

@[simp] theorem DS.adv_env' (a : DS VV MM) (m : Fin MM) : (a.adv m).env = a.env := rfl
@[simp] theorem DS.adv_ram' (a : DS VV MM) (m : Fin MM) : (a.adv m).ram = a.ram := rfl
@[simp] theorem DS.put_env' (a : DS VV MM) (m : Fin MM) (v : ℕ) : (a.put m v).env = a.env := rfl
@[simp] theorem DS.rew_env' (a : DS VV MM) (m : Fin MM) : (a.rew m).env = a.env := rfl
@[simp] theorem DS.rew_ram' (a : DS VV MM) (m : Fin MM) : (a.rew m).ram = a.ram := rfl

theorem take_succ_nat (l : List ℕ) (i : ℕ) (hi : i < l.length) : l.take (i + 1) = l.take i ++ [l.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem overwrite_length (old new : List ℕ) : (overwrite old new).length = max old.length new.length := by
  simp [overwrite]; omega

/-! ## Copying the outputs to the wire map -/

/-- `WM[0..VC) := W2[0..VC)`, `WL := max WL VC`. -/
def copyW : St VV MM :=
  .seq (.op (.rwM W2)) (.seq (.op (.rwM WM)) (.seq (.op (.zero IR))
    (.seq (.loop (.lt IR VC) (.seq (.op (.rdM W2 XA)) (.seq (.op (.wrM WM XA)) (.op (.inc IR)))))
      (.ite (.lt WL VC) (.op (.copy WL VC)) skipS))))

def CwT (y : ℕ) : Prop := y = 3 ∨ y = 24 ∨ y = 103 ∨ y = 105

def CwL (y : ℕ) : Prop := y = 24 ∨ y = 105

theorem copyW_spec (w : List ℕ) (D : List Bool) (S : PS n arity) (a : DS VV MM) (h : Rep w D S a)
    (count : ℕ) (hVC : a.env VC = count) (hW2 : count ≤ (a.ram W2).length) (hW : count + 1 < 2 ^ C.Wd) :
    Hx C copyW a (fun b c => Rep (overwrite w ((a.ram W2).take count)) D S b ∧ b.rc W2 = count ∧
      Keep CwT (fun m => m = 2) (fun m => m = 2 ∨ m = 4) a b ∧ c ≤ a.rc W2 + a.rc WM + 7 * count + 12) := by
  obtain ⟨⟨hc, hcnt, hns, hnsc, hwm, hwl, hwc, hdsr, hdl, hdc⟩, hs1, hs2, hs3⟩ := h
  refine Hx.seq' (Hx.ofHs (hs_rwM C W2 a)) (fun b0 c0 ⟨hc0, hb0⟩ => ?_)
  subst hb0
  refine Hx.seq' (Hx.ofHs (hs_rwM C WM _)) (fun b1 c1 ⟨hc1, hb1⟩ => ?_)
  subst hb1
  refine Hx.seq' (Hx.ofHs (hs_zero C IR _)) (fun b2 c2 ⟨hc2, hb2⟩ => ?_)
  subst hb2
  have hrcWM : ((a.rew W2).rew WM).rc WM = 0 := by simp [DS.rew]
  have hc1' : c1 ≤ a.rc WM + 1 := by
    have : (a.rew W2).rc WM = a.rc WM := by simp only [DS.rew]; exact Function.update_of_ne (by decide) _ _
    rw [this] at hc1; exact hc1
  set a1 := ((a.rew W2).rew WM).set IR 0 with ha1
  have k1 : Keep CwL (fun m => m = 2) (fun m => m = 2 ∨ m = 4) a a1 :=
    ⟨fun y hy => DS.set_env_ne _ _ (neP hy (show CwL IR.val by unfold CwL; simp)), fun _ _ => rfl,
      fun m hm => by
        simp only [ha1, DS.set_rc, DS.rew]
        rw [Function.update_of_ne (neM (by simp at hm ⊢; omega)), Function.update_of_ne (neM (by simp at hm ⊢; omega))],
      rfl, rfl, rfl, rfl, rfl⟩
  let I : ℕ → DS VV MM → ℕ → Prop := fun i x cc => x.ram WM = overwrite w ((a.ram W2).take i) ∧ x.rc WM = i ∧
    x.rc W2 = i ∧ x.env IR = i ∧ Keep CwL (fun m => m = 2) (fun m => m = 2 ∨ m = 4) a x ∧ cc ≤ 7 * i
  have hVCx : ∀ x, Keep CwL (fun m => m = 2) (fun m => m = 2 ∨ m = 4) a x → x.env VC = count := fun x k => by
    rw [k.env VC (by unfold CwL; simp), hVC]
  have step : ∀ i < count, ∀ x cc, I i x cc → Cnd.eval x (.lt IR VC) = true ∧
      Hx C (.seq (.op (.rdM W2 XA)) (.seq (.op (.wrM WM XA)) (.op (.inc IR)))) x
        (fun y c1 => I (i + 1) y (cc + c1 + 2)) := by
    intro i hi x cc ⟨x1, x2, x3, x4, x5, x6⟩
    refine ⟨by simp [Cnd.eval, x4, hVCx x x5, hi], ?_⟩
    have hrW2 : x.ram W2 = a.ram W2 := x5.ram W2 (by simp)
    refine Hx.seq' (Hx.ofHs (hs_rdM C W2 XA x (by rw [x3, hrW2]; omega))) (fun y0 d0 ⟨hd0, hy0⟩ => ?_)
    subst hy0
    set y1 := (x.set XA ((x.ram W2).getD (x.rc W2) 0)).adv W2 with hy1
    have hy1WM : y1.rc WM = i := by
      rw [hy1]; simp only [DS.adv]; rw [Function.update_of_ne (by decide)]; exact x2
    have hy1le : y1.rc WM ≤ (y1.ram WM).length := by
      rw [hy1WM]; show i ≤ (x.ram WM).length; rw [x1]
      have := overwrite_length_ge w ((a.ram W2).take i); simp at this; omega
    refine Hx.seq' (Hx.ofHs (hs_wrM C WM XA y1 hy1le)) (fun y2 d2 ⟨hd2, hy2⟩ => ?_)
    subst hy2
    have hIR : (y1.put WM (y1.env XA)).env IR = i := by
      show y1.env IR = i
      rw [hy1, DS.adv_env', DS.set_env_ne _ _ (by decide), x4]
    refine Hx.mono' (Hx.ofHs (hs_inc C IR _ (by rw [hIR]; omega))) (fun y3 d3 ⟨hd3, hy3⟩ => ?_)
    subst hy3
    have hXA : y1.env XA = (a.ram W2).getD i 0 := by
      rw [hy1, DS.adv_env', DS.set_env_self, x3, hrW2]
    refine ⟨?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [DS.set_ram]
      simp only [DS.put, Function.update_self]
      have hyWM : y1.ram WM = overwrite w ((a.ram W2).take i) := x1
      rw [hy1WM, hyWM, hXA, take_succ_nat _ _ (by omega)]
      have hl : ((a.ram W2).take i).length = i := by simp; omega
      rw [← putAt_overwrite, hl]
    · rw [DS.set_rc]; simp only [DS.put, Function.update_self]; rw [hy1WM]
    · rw [DS.set_rc]; simp only [DS.put]; rw [Function.update_of_ne (by decide)]
      rw [hy1]; simp only [DS.adv, Function.update_self]; rw [DS.set_rc, x3]
    · rw [DS.set_env_self, hIR]
    · have kA : Keep CwL (fun m => m = 2) (fun m => m = 2 ∨ m = 4) x y1 :=
        ⟨fun z hz => by
          rw [hy1, DS.adv_env']
          exact DS.set_env_ne _ _ (neP hz (show CwL XA.val by unfold CwL; simp)), fun _ _ => rfl,
          fun m hm => by
            rw [hy1]; simp only [DS.adv]; exact Function.update_of_ne (neM (by simp at hm ⊢; omega)) _ _,
          rfl, rfl, rfl, rfl, rfl⟩
      have kB : Keep CwL (fun m => m = 2) (fun m => m = 2 ∨ m = 4) y1 (y1.put WM (y1.env XA)) :=
        (keep_put y1 WM _).mono (fun _ h => h.elim) (fun m hm => by simpa using hm)
          (fun m hm => Or.inl (by simpa using hm))
      exact x5.trans (kA.trans (kB.trans (Keep.set _ _ _ (show CwL IR.val by unfold CwL; simp))))
  have stop : ∀ x cc, I count x cc → Cnd.eval x (.lt IR VC) = false := by
    intro x cc ⟨_, _, _, x4, x5, _⟩
    simp [Cnd.eval, x4, hVCx x x5]
  have hI0 : I 0 a1 0 := by
    refine ⟨?_, ?_, ?_, DS.set_env_self _ _ _, k1, le_rfl⟩
    · rw [ha1, DS.set_ram]; show a.ram WM = _; rw [hwm]; simp [overwrite]
    · rw [ha1, DS.set_rc, hrcWM]
    · rw [ha1, DS.set_rc]; simp only [DS.rew]; rw [Function.update_of_ne (by decide), Function.update_self]
  refine Hx.seq' (Hx.loopAcc (show Cnd.wf (Cnd.lt IR VC) from (by decide : IR ≠ VC)) I count step stop a1 hI0)
    (fun b3 c3 ⟨cf, ⟨i1, i2, i3, i4, i5, i6⟩, hc3⟩ => ?_)
  have hWL3 : b3.env WL = w.length := by rw [i5.env WL (by unfold CwL; simp), hwl]
  have hVC3 : b3.env VC = count := hVCx b3 i5
  have hlen : (overwrite w ((a.ram W2).take count)).length = max w.length count := by
    rw [overwrite_length]; congr 1; simp; omega
  have fin : ∀ d, Keep CwT (fun m => m = 2) (fun m => m = 2 ∨ m = 4) b3 d → d.ram = b3.ram → d.rc = b3.rc →
      d.env WL = max w.length count →
      Rep (overwrite w ((a.ram W2).take count)) D S d ∧ d.rc W2 = count ∧
        Keep CwT (fun m => m = 2) (fun m => m = 2 ∨ m = 4) a d := by
    intro d kd hram hrc hdWL
    have k := (i5.mono (fun y hy => by unfold CwL at hy; unfold CwT; omega) (fun _ h => h) (fun _ h => h)).trans kd
    refine ⟨⟨⟨k.cst (by unfold CwT; omega) hc, by rw [k.env CNT (by unfold CwT; simp), hcnt],
      by rw [k.ram NS (by simp), hns], by rw [k.rc NS (by simp), k.ram NS (by simp), hnsc],
      by rw [hram, i1], by rw [hdWL, hlen], by rw [hrc, i2, hlen]; omega,
      by rw [k.ram DSt (by simp), hdsr], by rw [k.env DL (by unfold CwT; simp), hdl],
      by rw [k.rc DSt (by simp)]; exact hdc⟩, by rw [k.env HR (by unfold CwT; simp), hs1],
      by rw [k.rc STK (by simp), hs2], by rw [k.ram STK (by simp), hs3]⟩, by rw [hrc, i3], k⟩
  refine Hx.ite' (show Cnd.wf (Cnd.lt WL VC) from (by decide : WL ≠ VC)) (fun hlt => ?_) (fun hge => ?_)
  · refine Hx.mono' (Hx.ofHs (hs_copy C WL VC b3 (by decide))) (fun d k ⟨hk, hd⟩ => ?_)
    subst hd
    have hl : w.length < count := by simpa [Cnd.eval, hWL3, hVC3] using hlt
    obtain ⟨r1, r2, r3⟩ := fin (b3.set WL (b3.env VC)) (Keep.set _ _ _ (show CwT WL.val by unfold CwT; simp)) rfl rfl
      (by rw [DS.set_env_self, hVC3]; omega)
    exact ⟨r1, r2, r3, by omega⟩
  · refine Hx.mono' (Hx.ofHs (skip_spec (C := C) b3)) (fun d k ⟨hk, hd⟩ => ?_)
    subst hd
    have hl : count ≤ w.length := by simpa [Cnd.eval, hWL3, hVC3] using hge
    obtain ⟨r1, r2, r3⟩ := fin (b3.set vJ 0) (Keep.set _ _ _ (show CwT vJ.val from Or.inl rfl)) rfl rfl
      (by rw [DS.set_env_ne _ _ (by decide), hWL3]; omega)
    exact ⟨r1, r2, r3, by omega⟩

/-! ## The oracle gate and its answer wire -/

/-- `TT := 5`. -/
def tag5 : St VV MM := .seq (.op (.copy TT v2)) (.seq (.op (.add TT v2)) (.op (.inc TT)))

/-- The oracle gate record `[5, 0, 0] ++ W2[0..ell)`; its index (`CNT`) is written at `WM[CBR]`. -/
def oracleP : St VV MM :=
  .seq tag5 (.seq (rec3 TT vZ vZ) (.seq (.op (.rwM W2)) (.seq (.op (.zero IR))
    (.seq (.loop (.lt IR ELR) (.seq (.op (.rdM W2 XA)) (.seq (.op (.wrM NS XA)) (.op (.inc IR)))))
      (.seq (seek WM CBR) (.seq (.op (.wrM WM CNT)) (.seq (.ite (.eq WL CBR) (.op (.inc WL)) skipS)
        (.op (.inc CNT)))))))))

def OrT (y : ℕ) : Prop := y = 3 ∨ y = 24 ∨ y = 101 ∨ y = 103 ∨ (105 ≤ y ∧ y ≤ 111)

theorem ofFn_getD (A : List ℕ) (k : ℕ) (h : A.length = k) : List.ofFn (fun i : Fin k => A.getD i.val 0) = A := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD]

theorem tag5_spec (a : DS VV MM) (hc : Cst a) (h8 : 8 ≤ 2 ^ C.Wd) :
    Hx C tag5 a (fun b c => b.env TT = 5 ∧ b = (a.set TT 4).set TT 5 ∧ c ≤ 5) := by
  refine Hx.seq' (Hx.ofHs (hs_copy C TT v2 a (by decide))) (fun b0 c0 ⟨hc0, hb0⟩ => ?_)
  subst hb0
  refine Hx.seq' (Hx.ofHs (hs_add C TT v2 _ (by decide) (by
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), hc.two]; omega))) (fun b1 c1 ⟨hc1, hb1⟩ => ?_)
  subst hb1
  refine Hx.mono' (Hx.ofHs (hs_inc C TT _ (by
    rw [DS.set_env_self, DS.set_env_self, DS.set_env_ne _ _ (by decide), hc.two]; omega))) (fun b2 c2 ⟨hc2, hb2⟩ => ?_)
  subst hb2
  have e : ((a.set TT (a.env v2)).set TT ((a.set TT (a.env v2)).env TT + (a.set TT (a.env v2)).env v2)).env TT = 4 := by
    rw [DS.set_env_self, DS.set_env_self, DS.set_env_ne _ _ (by decide), hc.two]
  refine ⟨by rw [DS.set_env_self, e], ?_, by omega⟩
  rw [e]
  simp only [DS.set, Function.update_idem]

def OrL (y : ℕ) : Prop := y = 24 ∨ (105 ≤ y ∧ y ≤ 111)

theorem putAt_length_le (w : List ℕ) (cb v : ℕ) (hw : cb ≤ w.length) :
    (putAt w cb v).length = if w.length = cb then cb + 1 else w.length := by
  unfold putAt
  split_ifs with h1 h2 h2 <;> simp <;> omega

theorem oracleP_spec (w : List ℕ) (D : List Bool) (k cb : ℕ) (S : PS k k) (a : DS VV MM) (h : Rep w D S a)
    (hell : a.env ELR = k) (hcb : a.env CBR = cb) (hW2 : k ≤ (a.ram W2).length) (hw : cb ≤ w.length)
    (hW : S.cnt + w.length + k + 8 < 2 ^ C.Wd) :
    Hx C oracleP a (fun b c => Rep (putAt w cb S.cnt) D (S.oracle ((a.ram W2).take k)) b ∧
      Keep OrT (fun m => m = 0 ∨ m = 2) (fun m => m = 0 ∨ m = 2 ∨ m = 4) a b ∧ b.rc W2 = k ∧
      c ≤ a.rc W2 + a.rc WM + 7 * k + 5 * cb + 60) := by
  obtain ⟨⟨hc, hcnt, hns, hnsc, hwm, hwl, hwc, hdsr, hdl, hdc⟩, hs1, hs2, hs3⟩ := h
  set A := (a.ram W2).take k with hA
  have hAl : A.length = k := by rw [hA]; simp; omega
  refine Hx.seq' (tag5_spec a hc (by omega)) (fun b0 c0 ⟨t1, t2, t3⟩ => ?_)
  have k0 : Keep OrL (fun _ => False) (fun _ => False) a b0 := by
    rw [t2]; exact (Keep.set _ _ _ (by unfold OrL; simp)).trans (Keep.set _ _ _ (by unfold OrL; simp))
  have hc0 : Cst b0 := k0.cst (by unfold OrL; omega) hc
  refine Hx.seq' (Hx.ofHs (rec3_spec (C := C) TT vZ vZ b0 (by rw [k0.rc NS id, k0.ram NS id, hnsc])))
    (fun b1 c1 ⟨hc1, r1, r2, r3⟩ => ?_)
  refine Hx.seq' (Hx.ofHs (hs_rwM C W2 b1)) (fun b2 c2 ⟨hc2, hb2⟩ => ?_)
  subst hb2
  refine Hx.seq' (Hx.ofHs (hs_zero C IR _)) (fun b3 c3 ⟨hc3, hb3⟩ => ?_)
  subst hb3
  have hrcW2 : b1.rc W2 = a.rc W2 := by rw [r3.rc W2 (by simp), k0.rc W2 id]
  have hbase : b1.ram NS = S.nodes.flatMap nodeRec ++ [5, 0, 0] := by
    rw [r1, k0.ram NS id, hns, t1, hc0.z]
  have k1 : Keep OrL (fun _ => False) (fun m => m = 4) b1 ((b1.rew W2).set IR 0) :=
    ⟨fun y hy => DS.set_env_ne _ _ (neP hy (show OrL IR.val by unfold OrL; simp)), fun _ _ => rfl,
      fun m hm => by simp only [DS.set_rc, DS.rew]; exact Function.update_of_ne (neM (by simpa using hm)) _ _,
      rfl, rfl, rfl, rfl, rfl⟩
  have hW2b1 : b1.ram W2 = a.ram W2 := by rw [r3.ram W2 (by simp), k0.ram W2 id]
  have hELRb1 : b1.env ELR = k := by rw [r3.env ELR id, k0.env ELR (by unfold OrL; simp), hell]
  let I : ℕ → DS VV MM → ℕ → Prop := fun i x cc => x.ram NS = b1.ram NS ++ A.take i ∧
    x.rc NS = (x.ram NS).length ∧ x.rc W2 = i ∧ x.env IR = i ∧
    Keep OrL (fun m => m = 0) (fun m => m = 0 ∨ m = 4) ((b1.rew W2).set IR 0) x ∧ cc ≤ 7 * i
  have hELRx : ∀ x, Keep OrL (fun m => m = 0) (fun m => m = 0 ∨ m = 4) ((b1.rew W2).set IR 0) x → x.env ELR = k :=
    fun x kx => by rw [kx.env ELR (by unfold OrL; simp), k1.env ELR (by unfold OrL; simp), hELRb1]
  have step : ∀ i < k, ∀ x cc, I i x cc → Cnd.eval x (.lt IR ELR) = true ∧
      Hx C (.seq (.op (.rdM W2 XA)) (.seq (.op (.wrM NS XA)) (.op (.inc IR)))) x
        (fun y c1 => I (i + 1) y (cc + c1 + 2)) := by
    intro i hi x cc ⟨x1, x2, x3, x4, x5, x6⟩
    refine ⟨by simp [Cnd.eval, x4, hELRx x x5, hi], ?_⟩
    have hrW2 : x.ram W2 = a.ram W2 := by rw [x5.ram W2 (by simp), k1.ram W2 id, hW2b1]
    refine Hx.seq' (Hx.ofHs (hs_rdM C W2 XA x (by rw [x3, hrW2]; omega))) (fun y0 d0 ⟨hd0, hy0⟩ => ?_)
    subst hy0
    set y1 := (x.set XA ((x.ram W2).getD (x.rc W2) 0)).adv W2 with hy1
    have hy1NS : y1.rc NS = (y1.ram NS).length := by
      rw [hy1]; simp only [DS.adv, DS.set_rc, DS.set_ram]; rw [Function.update_of_ne (by decide)]; exact x2
    refine Hx.seq' (Hx.ofHs (hs_wrM C NS XA y1 (by omega))) (fun y2 d2 ⟨hd2, hy2⟩ => ?_)
    subst hy2
    have hIR : (y1.put NS (y1.env XA)).env IR = i := by
      rw [DS.put_env', hy1, DS.adv_env', DS.set_env_ne _ _ (by decide), x4]
    refine Hx.mono' (Hx.ofHs (hs_inc C IR _ (by rw [hIR]; omega))) (fun y3 d3 ⟨hd3, hy3⟩ => ?_)
    subst hy3
    have hXA : y1.env XA = A.getD i 0 := by
      rw [hy1, DS.adv_env', DS.set_env_self, x3, hrW2, hA]
      simp [List.getD_eq_getElem?_getD, hi]
    obtain ⟨p1, p2⟩ := put_end y1 NS (y1.env XA) hy1NS
    refine ⟨?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [DS.set_ram, p1]
      show x.ram NS ++ _ = _
      rw [x1, hXA, take_succ_nat _ _ (by omega), List.append_assoc]
    · rw [DS.set_rc, DS.set_ram]; exact p2
    · rw [DS.set_rc]; simp only [DS.put]; rw [Function.update_of_ne (by decide)]
      rw [hy1]; simp only [DS.adv, Function.update_self]; rw [DS.set_rc, x3]
    · rw [DS.set_env_self, hIR]
    · have kA : Keep OrL (fun m => m = 0) (fun m => m = 0 ∨ m = 4) x y1 :=
        ⟨fun z hz => by
          rw [hy1, DS.adv_env']
          exact DS.set_env_ne _ _ (neP hz (show OrL XA.val by unfold OrL; simp)), fun _ _ => rfl,
          fun m hm => by
            rw [hy1]; simp only [DS.adv]; exact Function.update_of_ne (neM (by simp at hm ⊢; omega)) _ _,
          rfl, rfl, rfl, rfl, rfl⟩
      have kB : Keep OrL (fun m => m = 0) (fun m => m = 0 ∨ m = 4) y1 (y1.put NS (y1.env XA)) :=
        (keep_put y1 NS _).mono (fun _ h => h.elim) (fun m hm => by simpa using hm)
          (fun m hm => Or.inl (by simpa using hm))
      exact x5.trans (kA.trans (kB.trans (Keep.set _ _ _ (show OrL IR.val by unfold OrL; simp))))
  have stop : ∀ x cc, I k x cc → Cnd.eval x (.lt IR ELR) = false := by
    intro x cc ⟨_, _, _, x4, x5, _⟩
    simp [Cnd.eval, x4, hELRx x x5]
  have hI0 : I 0 ((b1.rew W2).set IR 0) 0 := by
    refine ⟨by simp, ?_, ?_, DS.set_env_self _ _ _, Keep.refl _ _ _ _, le_rfl⟩
    · rw [DS.set_rc, DS.set_ram]; simp only [DS.rew]
      rw [Function.update_of_ne (by decide)]; exact r2
    · rw [DS.set_rc]; simp [DS.rew]
  refine Hx.seq' (Hx.loopAcc (show Cnd.wf (Cnd.lt IR ELR) from (by decide : IR ≠ ELR)) I k step stop _ hI0)
    (fun b4 c4 ⟨cf, ⟨i1, i2, i3, i4, i5, i6⟩, hc4⟩ => ?_)
  have kab4 : Keep OrL (fun m => m = 0) (fun m => m = 0 ∨ m = 4) a b4 :=
    ((k0.mono (fun _ h => h) (fun _ h => h.elim) (fun _ h => h.elim)).trans
      ((r3.mono (fun _ h => h.elim) (fun _ h => h) (fun m hm => Or.inl hm)).trans
        ((k1.mono (fun _ h => h) (fun _ h => h.elim) (fun m hm => Or.inr hm)).trans i5)))
  have hWM4 : b4.ram WM = w := by rw [kab4.ram WM (by simp), hwm]
  have hCB4 : b4.env CBR = cb := by rw [kab4.env CBR (by unfold OrL; simp), hcb]
  refine Hx.seq' (Hx.ofHs (seek_spec (C := C) WM CBR (by unfold SkT; simp) b4 (by rw [hCB4, hWM4]; exact hw)
    (by rw [hCB4]; omega))) (fun b5 c5 ⟨hc5, s1, s2⟩ => ?_)
  have kab5 : Keep OrL (fun m => m = 0) (fun m => m = 0 ∨ m = 2 ∨ m = 4) a b5 :=
    (kab4.mono (fun _ h => h) (fun _ h => h) (fun m hm => by omega)).trans
      (s2.mono (fun y hy => by unfold SkT at hy; unfold OrL; omega) (fun _ h => h.elim) (fun m hm => by simp at hm; omega))
  have hWM5 : b5.ram WM = w := by rw [kab5.ram WM (by simp), hwm]
  have hCNT5 : b5.env CNT = S.cnt := by rw [kab5.env CNT (by unfold OrL; simp), hcnt]
  have hWL5 : b5.env WL = w.length := by rw [kab5.env WL (by unfold OrL; simp), hwl]
  refine Hx.seq' (Hx.ofHs (hs_wrM C WM CNT b5 (by rw [s1, hWM5, hCB4]; exact hw))) (fun b6 c6 ⟨hc6, hb6⟩ => ?_)
  subst hb6
  set b6 := b5.put WM (b5.env CNT) with hb6
  have hWM6 : b6.ram WM = putAt w cb S.cnt := by
    rw [hb6]; simp only [DS.put, Function.update_self]; rw [s1, hWM5, hCB4, hCNT5]
  have hrcWM6 : b6.rc WM = cb + 1 := by
    rw [hb6]; simp only [DS.put, Function.update_self]; rw [s1, hCB4]
  have kb56 : Keep (fun _ => False) (· = 2) (· = 2) b5 b6 := keep_put b5 WM _
  have hlenP := putAt_length_le w cb S.cnt hw
  refine Hx.seq' (R1 := fun b7 c7 => b7.env WL = (putAt w cb S.cnt).length ∧ b7.ram = b6.ram ∧ b7.rc = b6.rc ∧
      Keep (fun y => y = 3 ∨ y = 103) (fun _ => False) (fun _ => False) b6 b7 ∧ c7 ≤ 2)
    (Hx.ite' (show Cnd.wf (Cnd.eq WL CBR) from (by decide : WL ≠ CBR)) (fun he => ?_) (fun hne => ?_))
    (fun b7 c7 ⟨w1, w2, w3, w4, w5⟩ => ?_)
  · have hl : w.length = cb := by
      have : b6.env WL = b6.env CBR := by simpa [Cnd.eval] using he
      rwa [hb6, DS.put_env', hWL5, kab5.env CBR (by unfold OrL; simp), hcb] at this
    have hWL6 : b6.env WL = w.length := by rw [hb6, DS.put_env', hWL5]
    refine Hx.mono' (Hx.ofHs (hs_inc C WL b6 (by rw [hWL6]; omega))) (fun d c ⟨hc, hd⟩ => ?_)
    subst hd
    exact ⟨by rw [DS.set_env_self, hWL6, hlenP, if_pos hl]; omega, rfl, rfl, Keep.set _ _ _ (Or.inr rfl), by omega⟩
  · have hl : w.length ≠ cb := by
      have : ¬ b6.env WL = b6.env CBR := by simpa [Cnd.eval] using hne
      rwa [hb6, DS.put_env', hWL5, kab5.env CBR (by unfold OrL; simp), hcb] at this
    refine Hx.mono' (Hx.ofHs (skip_spec (C := C) b6)) (fun d c ⟨hc, hd⟩ => ?_)
    subst hd
    exact ⟨by rw [DS.set_env_ne _ _ (by decide), hb6, DS.put_env', hWL5, hlenP, if_neg hl], rfl, rfl,
      Keep.set _ _ _ (Or.inl rfl), by omega⟩
  have hCNT7 : b7.env CNT = S.cnt := by
    rw [w4.env CNT (by simp), hb6, DS.put_env', hCNT5]
  refine Hx.mono' (Hx.ofHs (hs_inc C CNT b7 (by rw [hCNT7]; omega))) (fun b8 c8 ⟨hc8, hb8⟩ => ?_)
  subst hb8
  -- the frame
  have k57 : Keep (fun y => y = 3 ∨ y = 103) (· = 2) (· = 2) b5 b7 :=
    (kb56.mono (fun _ h => h.elim) (fun _ h => h) (fun _ h => h)).trans
      (w4.mono (fun _ h => h) (fun _ h => h.elim) (fun _ h => h.elim))
  have kall : Keep OrT (fun m => m = 0 ∨ m = 2) (fun m => m = 0 ∨ m = 2 ∨ m = 4) a (b7.set CNT (b7.env CNT + 1)) :=
    ((kab5.mono (fun y hy => by unfold OrL at hy; unfold OrT; omega) (fun m hm => Or.inl hm) (fun _ h => h)).trans
      (k57.mono (fun y hy => by unfold OrT; omega) (fun m hm => Or.inr hm) (fun m hm => Or.inr (Or.inl hm)))).trans
      (Keep.set _ _ _ (by unfold OrT; simp))
  have hA' : A.take k = A := List.take_of_length_le (by omega)
  have hstore : ∀ m : Fin MM, m ≠ WM → (b7.set CNT (b7.env CNT + 1)).ram m = b4.ram m ∧
      (m ≠ NS → m ≠ W2 → (b7.set CNT (b7.env CNT + 1)).rc m = a.rc m) := fun m hm => by
    refine ⟨?_, fun h1 h2 => ?_⟩
    · rw [DS.set_ram, w2, hb6]; simp only [DS.put]; rw [Function.update_of_ne hm, s2.ram m id]
    · rw [DS.set_rc, w3, hb6]; simp only [DS.put]; rw [Function.update_of_ne hm]
      exact kab5.rc m (fun h => by
        rcases h with h | h | h
        · exact h1 (Fin.ext h)
        · exact hm (Fin.ext h)
        · exact h2 (Fin.ext h))
  have hNS8 : (b7.set CNT (b7.env CNT + 1)).ram NS = (S.oracle A).nodes.flatMap nodeRec := by
    rw [(hstore NS (by decide)).1, i1, hA', hbase]
    simp only [PS.oracle, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, nodeRec,
      nodeTag, nodeLeft, nodeRight, nodeArgs, List.append_assoc, ofFn_getD A k hAl]
  have hrcNS8 : (b7.set CNT (b7.env CNT + 1)).rc NS = ((b7.set CNT (b7.env CNT + 1)).ram NS).length := by
    have e1 : (b7.set CNT (b7.env CNT + 1)).rc NS = b4.rc NS := by
      rw [DS.set_rc, w3, hb6]; simp only [DS.put]; rw [Function.update_of_ne (by decide), s2.rc NS (by simp)]
    rw [e1, (hstore NS (by decide)).1]; exact i2
  refine ⟨⟨⟨kall.cst (by unfold OrT; omega) hc, by rw [DS.set_env_self, hCNT7]; rfl, hNS8, hrcNS8,
      by rw [DS.set_ram, w2, hWM6], by rw [DS.set_env_ne _ _ (by decide), w1],
      by rw [DS.set_rc, w3, hrcWM6, hlenP]; split_ifs <;> omega,
      by rw [kall.ram DSt (by simp), hdsr], by rw [kall.env DL (by unfold OrT; simp), hdl],
      by rw [kall.rc DSt (by simp)]; exact hdc⟩,
    by rw [kall.env HR (by unfold OrT; simp)]; exact hs1, by rw [kall.rc STK (by simp)]; exact hs2,
    by rw [kall.ram STK (by simp)]; exact hs3⟩, kall, ?_, ?_⟩
  · rw [DS.set_rc, w3, hb6]; simp only [DS.put]; rw [Function.update_of_ne (by decide), s2.rc W2 (by simp)]; exact i3
  have hc2' : c2 ≤ a.rc W2 + 1 := by rw [hrcW2] at hc2; exact hc2
  have hc5' : c5 ≤ b4.rc WM + 5 * cb + 6 := by rw [hCB4] at hc5; exact hc5
  have hrcWM4 : b4.rc WM = a.rc WM := kab4.rc WM (by simp)
  omega

end NearCubicGates.Adapters.Compile.OraclePrint
