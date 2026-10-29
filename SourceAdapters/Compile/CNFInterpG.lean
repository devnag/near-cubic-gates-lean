import SourceAdapters.Compile.CNFInterpF

/-!
# Token interpreter, part G: one token read from the token store

`stepP` reads the token code at the cursor of `sTT`, splits it into kind (`code % 8`) and payload (`code / 8`), and
dispatches to the token programs of parts C–F: `stepP_spec : IR n k S a → Hs C stepP a … (IR n (k+1) (S.step tok) ·)`.
-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {C : Ctx}

def dispatchP : St VV MM :=
  .ite (.eq iK vZ) cstTokP (.ite (.eq iK v1) inpTokP (.ite (.eq iK v2) wirTokP (.ite (.eq iK kc3) negTokP
    (.ite (.eq iK kc4) conjTokP (.ite (.eq iK kc5) disjTokP (.ite (.eq iK kc6) saveTokP swapTokP))))))

def stepP : St VV MM := .seq (.op (.rdM sTT iTk)) (.seq (.op (.dm iTk kc8 iPl iK)) dispatchP)

/-- The kind and payload of a token code. -/
def tkind : RTok → ℕ
  | .cst _ => 0
  | .inp _ => 1
  | .wir _ => 2
  | .neg => 3
  | .conj => 4
  | .disj => 5
  | .save => 6
  | .swap => 7

def tpay : RTok → ℕ
  | .cst b => b.toNat
  | .inp j => j
  | .wir k => k
  | _ => 0

theorem tcode_mod (t : RTok) : tcode t % 8 = tkind t := by
  cases t with
  | cst b => cases b <;> rfl
  | inp j => simp [tcode, tkind]
  | wir k => simp [tcode, tkind]
  | _ => rfl

theorem tcode_div (t : RTok) : tcode t / 8 = tpay t := by
  cases t with
  | cst b => cases b <;> rfl
  | inp j => simp [tcode, tpay]; omega
  | wir k => simp [tcode, tpay]; omega
  | _ => rfl

/-- The clause codes of the node a token emits are in range. -/
def ClauseOK (C : Ctx) (n : ℕ) (S : RS) : RTok → Prop
  | .cst b => ∀ c ∈ (rcl n S.idx (.cst b)).map Encodable.encode, c < 2 ^ C.Wd
  | .inp j => ∀ c ∈ (rcl n S.idx (.inp j)).map Encodable.encode, c < 2 ^ C.Wd
  | .neg => ∀ c ∈ (rcl n S.idx (.neg (popS S.stk).1)).map Encodable.encode, c < 2 ^ C.Wd
  | .conj => ∀ c ∈ (rcl n S.idx (.conj (popS (popS S.stk).2).1 (popS S.stk).1)).map Encodable.encode, c < 2 ^ C.Wd
  | .disj => ∀ c ∈ (rcl n S.idx (.disj (popS (popS S.stk).2).1 (popS S.stk).1)).map Encodable.encode, c < 2 ^ C.Wd
  | _ => True

/-- The cost of one token. -/
def stepCost (k : ℕ) : ℕ := 30 * k + 300

/-- The common post-state of a token. -/
def StepPost (n k : ℕ) (S : RS) (tok : RTok) (a d : DS VV MM) : Prop :=
  IR n (k + 1) (S.step tok) d ∧ d.ram sTT = a.ram sTT ∧ d.rc sTT = a.rc sTT ∧ d.ip = a.ip ∧ d.out = a.out ∧
    Fr a d irT

theorem dispatchP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (tok : RTok) (hK : a.env iK = tkind tok) (hP : a.env iPl = tpay tok) (hpk : tpay tok ≤ k)
    (hok : ClauseOK C n S tok) :
    Hs C dispatchP a (stepCost k) (fun d => StepPost n k S tok a d) := by
  have hk := h.kc
  have hrsk : a.rc sSK ≤ k := le_trans h.rsk h.bsk
  have hrwm : a.rc sWM ≤ k := le_trans h.rwm h.bwm
  have kZ := hk.z; have k1 := hk.one; have k2 := hk.two; have k3 := hk.k3; have k4 := hk.k4
  have k5 := hk.k5; have k6 := hk.k6; have k7 := hk.k7
  -- evaluate the chain of tests
  have ev : ∀ (c : Fin VV) (v : ℕ), a.env c = v → (Cnd.eq iK c).eval a = decide (tkind tok = v) := by
    intro c v hc; simp [Cnd.eval, hK, hc]
  have post : ∀ d, (IR n (k + 1) (S.step tok) d ∧ (∀ m, m ≠ sSK → m ≠ sCL → d.ram m = a.ram m ∧ d.rc m = a.rc m) ∧
      d.ip = a.ip ∧ d.out = a.out ∧ Fr a d irT) → StepPost n k S tok a d := fun d ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, (h2 sTT (by decide) (by decide)).1, (h2 sTT (by decide) (by decide)).2, h3, h4, h5⟩
  have post2 : ∀ d, (IR n (k + 1) (S.step tok) d ∧ (∀ m, m ≠ sSK → m ≠ sWM → d.ram m = a.ram m ∧
      d.rc m = a.rc m) ∧ d.ram sWM = a.ram sWM ∧ d.ip = a.ip ∧ d.out = a.out ∧ Fr a d irT) →
      StepPost n k S tok a d := fun d ⟨h1, h2, _, h3, h4, h5⟩ =>
    ⟨h1, (h2 sTT (by decide) (by decide)).1, (h2 sTT (by decide) (by decide)).2, h3, h4, h5⟩
  have post3 : ∀ d, (IR n (k + 1) (S.step tok) d ∧ (∀ m, m ≠ sSK → m ≠ sNW → d.ram m = a.ram m ∧
      d.rc m = a.rc m) ∧ d.ip = a.ip ∧ d.out = a.out ∧ Fr a d irT) → StepPost n k S tok a d :=
    fun d ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, (h2 sTT (by decide) (by decide)).1, (h2 sTT (by decide) (by decide)).2,
      h3, h4, h5⟩
  have post4 : ∀ d, (IR n (k + 1) (S.step tok) d ∧ (∀ m, m ≠ sWM → m ≠ sNW → d.ram m = a.ram m ∧
      d.rc m = a.rc m) ∧ d.ip = a.ip ∧ d.out = a.out ∧ Fr a d irT) → StepPost n k S tok a d :=
    fun d ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, (h2 sTT (by decide) (by decide)).1, (h2 sTT (by decide) (by decide)).2,
      h3, h4, h5⟩
  unfold dispatchP
  have hc : ∀ c : Fin VV, c ≠ iK → (Cnd.eq iK c).wf := fun c hc => Ne.symm hc
  cases tok with
  | cst b =>
      refine Hs.mono (Hs.iteT (hc vZ (by decide)) (by rw [ev vZ 0 kZ]; rfl)
        (cstTokP_spec n k S a h hW b hP hok)) (by unfold stepCost; omega) (fun d hd => post d hd)
  | inp j =>
      refine Hs.mono (Hs.iteF (hc vZ (by decide)) (by rw [ev vZ 0 kZ]; rfl) (Hs.iteT (hc v1 (by decide))
        (by rw [ev v1 1 k1]; rfl) (inpTokP_spec n k S a h hW j hP hok))) (by unfold stepCost; omega)
        (fun d hd => post d hd)
  | wir j =>
      refine Hs.mono (Hs.iteF (hc vZ (by decide)) (by rw [ev vZ 0 kZ]; rfl) (Hs.iteF (hc v1 (by decide))
        (by rw [ev v1 1 k1]; rfl) (Hs.iteT (hc v2 (by decide)) (by rw [ev v2 2 k2]; rfl)
        (wirTokP_spec n k S a h hW j hP hpk)))) (by unfold stepCost; omega) (fun d hd => post2 d hd)
  | neg =>
      refine Hs.mono (Hs.iteF (hc vZ (by decide)) (by rw [ev vZ 0 kZ]; rfl) (Hs.iteF (hc v1 (by decide))
        (by rw [ev v1 1 k1]; rfl) (Hs.iteF (hc v2 (by decide)) (by rw [ev v2 2 k2]; rfl)
        (Hs.iteT (hc kc3 (by decide)) (by rw [ev kc3 3 k3]; rfl) (negTokP_spec n k S a h hW hok)))))
        (by unfold stepCost; omega) (fun d hd => post d hd)
  | conj =>
      refine Hs.mono (Hs.iteF (hc vZ (by decide)) (by rw [ev vZ 0 kZ]; rfl) (Hs.iteF (hc v1 (by decide))
        (by rw [ev v1 1 k1]; rfl) (Hs.iteF (hc v2 (by decide)) (by rw [ev v2 2 k2]; rfl)
        (Hs.iteF (hc kc3 (by decide)) (by rw [ev kc3 3 k3]; rfl) (Hs.iteT (hc kc4 (by decide))
        (by rw [ev kc4 4 k4]; rfl) (conjTokP_spec n k S a h hW hok))))))
        (by unfold stepCost; omega) (fun d hd => post d hd)
  | disj =>
      refine Hs.mono (Hs.iteF (hc vZ (by decide)) (by rw [ev vZ 0 kZ]; rfl) (Hs.iteF (hc v1 (by decide))
        (by rw [ev v1 1 k1]; rfl) (Hs.iteF (hc v2 (by decide)) (by rw [ev v2 2 k2]; rfl)
        (Hs.iteF (hc kc3 (by decide)) (by rw [ev kc3 3 k3]; rfl) (Hs.iteF (hc kc4 (by decide))
        (by rw [ev kc4 4 k4]; rfl) (Hs.iteT (hc kc5 (by decide)) (by rw [ev kc5 5 k5]; rfl)
        (disjTokP_spec n k S a h hW hok)))))))
        (by unfold stepCost; omega) (fun d hd => post d hd)
  | save =>
      refine Hs.mono (Hs.iteF (hc vZ (by decide)) (by rw [ev vZ 0 kZ]; rfl) (Hs.iteF (hc v1 (by decide))
        (by rw [ev v1 1 k1]; rfl) (Hs.iteF (hc v2 (by decide)) (by rw [ev v2 2 k2]; rfl)
        (Hs.iteF (hc kc3 (by decide)) (by rw [ev kc3 3 k3]; rfl) (Hs.iteF (hc kc4 (by decide))
        (by rw [ev kc4 4 k4]; rfl) (Hs.iteF (hc kc5 (by decide)) (by rw [ev kc5 5 k5]; rfl)
        (Hs.iteT (hc kc6 (by decide)) (by rw [ev kc6 6 k6]; rfl) (saveTokP_spec n k S a h hW))))))))
        (by unfold stepCost; omega) (fun d hd => post3 d hd)
  | swap =>
      refine Hs.mono (Hs.iteF (hc vZ (by decide)) (by rw [ev vZ 0 kZ]; rfl) (Hs.iteF (hc v1 (by decide))
        (by rw [ev v1 1 k1]; rfl) (Hs.iteF (hc v2 (by decide)) (by rw [ev v2 2 k2]; rfl)
        (Hs.iteF (hc kc3 (by decide)) (by rw [ev kc3 3 k3]; rfl) (Hs.iteF (hc kc4 (by decide))
        (by rw [ev kc4 4 k4]; rfl) (Hs.iteF (hc kc5 (by decide)) (by rw [ev kc5 5 k5]; rfl)
        (Hs.iteF (hc kc6 (by decide)) (by rw [ev kc6 6 k6]; rfl) (swapTokP_spec n k S a h hW))))))))
        (by unfold stepCost; omega) (fun d hd => post4 d hd)

/-- `IR` is insensitive to scratch registers and to the token cursor. -/
theorem IR.scratch {n k : ℕ} {S : RS} {a b : DS VV MM} (h : IR n k S a) (hram : b.ram = a.ram)
    (hrc : ∀ m, m ≠ sTT → b.rc m = a.rc m) (hregs : ∀ y ∈ [dN, iIdx, iSp, iWl, iNc] ++ kcRegs, b.env y = a.env y) :
    IR n k S b := by
  have e := hregs
  have hk : KC b := ⟨by rw [e vZ (by decide), h.kc.z], by rw [e v1 (by decide), h.kc.one],
    by rw [e v2 (by decide), h.kc.two], by rw [e kc3 (by decide), h.kc.k3], by rw [e kc4 (by decide), h.kc.k4],
    by rw [e kc5 (by decide), h.kc.k5], by rw [e kc6 (by decide), h.kc.k6], by rw [e kc7 (by decide), h.kc.k7],
    by rw [e kc8 (by decide), h.kc.k8]⟩
  exact ⟨hk, by rw [e dN (by decide), h.dn], by rw [e iIdx (by decide), h.idx], h.nodes,
    ⟨by rw [e iSp (by decide), h.stk.sp], by rw [hram]; exact h.stk.take, by rw [hram]; exact h.stk.len⟩,
    by rw [e iWl (by decide), h.wl], by rw [hram]; exact h.wires, by rw [hram]; exact h.wlen,
    by rw [e iNc (by decide), h.nc], by rw [hram]; exact h.next, by rw [hram]; exact h.nlen,
    by rw [hrc sNW (by decide), h.rcnw], by rw [hram]; exact h.cl, by rw [hram, hrc sCL (by decide)]; exact h.rccl,
    by rw [hram]; exact h.bsk, by rw [hram, hrc sSK (by decide)]; exact h.rsk, by rw [hram]; exact h.bwm,
    by rw [hram, hrc sWM (by decide)]; exact h.rwm, by rw [hram]; exact h.bnw, h.bidx, h.vstk, h.vwires, h.vnext⟩

theorem stepP_spec (n k : ℕ) (S : RS) (a : DS VV MM) (h : IR n k S a) (hW : 64 * (n + k) + 64 ≤ 2 ^ C.Wd)
    (tok : RTok) (p : ℕ) (hp : a.rc sTT = p) (hlen : p < (a.ram sTT).length) (htok : (a.ram sTT).getD p 0 = tcode tok)
    (hpk : tpay tok ≤ k) (hok : ClauseOK C n S tok) :
    Hs C stepP a (stepCost k + 4) (fun d => IR n (k + 1) (S.step tok) d ∧ d.ram sTT = a.ram sTT ∧
      d.rc sTT = p + 1 ∧ d.ip = a.ip ∧ d.out = a.out ∧ Fr a d (iTk :: iPl :: iK :: irT)) := by
  have hk := h.kc
  have hcode : tcode tok ≤ 8 * k + 7 := by
    cases tok <;> simp [tcode, tpay] at hpk ⊢ <;> try omega
    all_goals (rename_i b; cases b <;> simp <;> omega)
  refine Hs.seqc (t1 := 1) (t2 := stepCost k + 2) (hs_rdM C sTT iTk a (by rw [hp]; exact hlen)) (fun b1 e1 => ?_)
    (by omega)
  subst e1
  refine Hs.seqc (t1 := 1) (t2 := stepCost k) (hs_dm C iTk kc8 iPl iK _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by vsimp [DS.adv, hk.k8]) (by vsimp [DS.adv, hk.k8]; omega))
    (fun b2 e2 => ?_) (by omega)
  subst e2
  set b2 := (((a.set iTk ((a.ram sTT).getD (a.rc sTT) 0)).adv sTT).set iPl
    (((a.set iTk ((a.ram sTT).getD (a.rc sTT) 0)).adv sTT).env iTk /
      ((a.set iTk ((a.ram sTT).getD (a.rc sTT) 0)).adv sTT).env kc8)).set iK
    (((a.set iTk ((a.ram sTT).getD (a.rc sTT) 0)).adv sTT).env iTk %
      ((a.set iTk ((a.ram sTT).getD (a.rc sTT) 0)).adv sTT).env kc8) with hb2
  have hb2r : b2.ram = a.ram := by simp [hb2, DS.adv]
  have hb2c : ∀ m, m ≠ sTT → b2.rc m = a.rc m := fun m hm => by simp [hb2, DS.adv, Function.update_of_ne hm]
  have hb2e : ∀ y, y ∉ [iTk, iPl, iK] → b2.env y = a.env y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hb2, DS.adv, DS.set, Function.update_apply, hy]
  have hIR : IR n k S b2 := h.scratch hb2r hb2c (fun y hy => hb2e y (by revert hy; decide +revert))
  rw [List.getD_eq_getElem?_getD] at htok
  have hK : b2.env iK = tkind tok := by
    vsimp [hb2, DS.adv, hp, htok, hk.k8, tcode_mod]
  have hP : b2.env iPl = tpay tok := by
    vsimp [hb2, DS.adv, hp, htok, hk.k8, tcode_div]
  refine Hs.mono (dispatchP_spec n k S b2 hIR hW tok hK hP hpk hok) le_rfl ?_
  rintro d ⟨d1, d2, d3, d4, d5, d6⟩
  refine ⟨d1, by rw [d2, hb2r], by rw [d3]; simp [hb2, DS.adv, hp], by rw [d4]; simp [hb2, DS.adv],
    by rw [d5]; simp [hb2, DS.adv], ?_⟩
  intro y hy
  simp only [List.mem_cons, not_or] at hy
  rw [d6 y hy.2.2.2, hb2e y (by simp [hy.1, hy.2.1, hy.2.2.1])]

end NearCubicGates.Adapters.Compile
