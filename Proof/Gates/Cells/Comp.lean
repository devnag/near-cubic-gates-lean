import Proof.Gates.Cells.CompK
import Proof.Gates.Cells.CompSort

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces.Formats

variable {V M : ℕ}

/-- The program of one operation. -/
noncomputable def compOp (K : Callee) : Op V M → WMX (NS M (TSK K) V) (NR M)
  | .kem b => kemP K b
  | .kcall => kcallP K
  | .rdK x => rdKP K x
  | .srtM m => srtP m
  | o => compB o

/-- The loop part of a compiled `while` (entered with the test in `F`). -/
def wpart {t : ℕ} (c : Cnd V) (S : WMX (NS M t V) (NR M)) : WMX (NS M t V) (NR M) :=
  .whr rF (.seq (WMX.dec rF) (.seq S (condP c)))

/-- **The compiler.** -/
noncomputable def comp (K : Callee) : St V M → WMX (NS M (TSK K) V) (NR M)
  | .op o => compOp K o
  | .seq s t => .seq (comp K s) (comp K t)
  | .ite c s t => .seq (condP c) (.ifr rF (.seq (WMX.dec rF) (comp K s)) (comp K t))
  | .loop c s => .seq (condP c) (wpart c (comp K s))

/-! ## Growth of the output and of the stores -/

theorem OpEx.ram_len {C : Ctx} {o : Op V M} {a b : DS V M} {k : ℕ} (h : OpEx C o a b k) (m : Fin M) :
    (b.ram m).length ≤ (a.ram m).length + k := by
  cases h with
  | wrM m' x a hr =>
    simp only [DS.put]
    by_cases hm : m = m'
    · subst hm; rw [Function.update_self, putAt_length _ _ _ hr]; omega
    · rw [Function.update_of_ne hm]; omega
  | srtM m' a _ =>
    simp only [DS.srt]
    by_cases hm : m = m'
    · subst hm; rw [Function.update_self, (List.perm_insertionSort _ _).length_eq]; omega
    · rw [Function.update_of_ne hm]; omega
  | _ => simp [DS.set, DS.adv, DS.rew, DS.called]

theorem Ex.ram_len {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) (m : Fin M) :
    (b.ram m).length ≤ (a.ram m).length + n := by
  induction h with
  | op h => exact h.ram_len m
  | seq _ _ ih1 ih2 => omega
  | iteT _ _ _ ih => omega
  | iteF _ _ _ ih => omega
  | loopF _ _ => omega
  | loopT _ _ _ _ ih1 ih2 => omega
  | mono _ hnm ih => omega

/-! ## One operation -/

section Ops
variable (C : Ctx) (cap : ℕ)

/-- The capacity facts the compiled operations need, for a state `a` and `n` further cost units. -/
structure CapOK (a : DS V M) (n : ℕ) : Prop where
  W : 1 ≤ C.Wd
  wd : 2 * C.Wd + 2 ≤ cap
  inp : 2 * C.inp.length + 2 ≤ cap
  out : a.out.length + n ≤ cap
  ram : ∀ m, (2 * C.Wd + 1) * ((a.ram m).length + n + 1) + 1 ≤ cap
  k : Rk C + 2 ≤ cap

theorem compOp_ok {o : Op V M} {a b : DS V M} {k : ℕ} (h : OpEx C o a b k) (ha : Valid C a)
    {σ : WState (NS M (TS C) V) (NR M)} (he : Enc C a σ) (hc : CapOK C cap a k) :
    ∃ τ, Enc C b τ ∧ WXExec cap (compOp C.K o) σ τ (k * KC C) := by
  have hk1 := h.pos
  have hram : ∀ m, (2 * C.Wd + 1) * ((a.ram m).length + 1) + 1 ≤ cap := fun m => by
    have := hc.ram m; nlinarith
  have hRk : Rk C = 2 * C.Lk + C.Bk + 3 := rfl
  cases h with
  | rdI x a hi => exact rdI_ok C cap he hc.W (by have := hc.wd; omega) hc.inp x hi
  | bkI a hp => exact bkI_ok C cap he hp hc.inp ha.ip_le
  | emit bb a => exact emit_ok C cap he (by have := hc.out; omega) bb
  | rdM m x a hr => exact rdM_ok C cap he m x hr (hram m)
  | wrM m x a hr => exact wrM_ok C cap he m x hr (hram m)
  | rwM m a => exact rwM_ok C cap he m (ha.rc_le m) (hram m)
  | srtM m a h0 => exact srtM_ok C cap he ha hc.W m h0 (hram m)
  | kem bb a hk => exact kem_ok C cap he bb hk (by have := hc.k; omega)
  | kcall s a hs hb => exact kcall_ok C cap he ha s hs hb hc.k
  | rdK x a hk =>
    exact rdK_ok C cap he hc.W (by have := hc.wd; omega) x hk (by have := ha.kout_le; have := hc.k; omega)
  | zero x a => exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.zero x a) trivial
  | inc x a hv => exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.inc x a hv) trivial
  | add x y a hxy hv => exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.add x y a hxy hv) trivial
  | sub x y a hxy hv => exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.sub x y a hxy hv) trivial
  | copy x y a hxy => exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.copy x y a hxy) trivial
  | half x a => exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.half x a) trivial
  | shl x a hv => exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.shl x a hv) trivial
  | mul x y z a hxy hxz hyz hv =>
    exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.mul x y z a hxy hxz hyz hv) trivial
  | dm x y q r a hxy hxq hxr hyq hyr hqr hy h2y =>
    exact arith_ok C cap he ha hc.W (by have := hc.wd; omega) (.dm x y q r a hxy hxq hxr hyq hyr hqr hy h2y) trivial

end Ops

/-! ## The compiler is correct -/

section Comp
variable (C : Ctx) (cap : ℕ)

theorem CapOK.mono {a : DS V M} {n m : ℕ} (h : CapOK C cap a n) (hm : m ≤ n) : CapOK C cap a m :=
  ⟨h.W, h.wd, h.inp, by have := h.out; omega, fun r => by have := h.ram r; nlinarith, h.k⟩

theorem CapOK.after {s : St V M} {a b : DS V M} {n k : ℕ} (h : CapOK C cap a (n + k)) (hx : Ex C s a b n) :
    CapOK C cap b k := by
  have ho := hx.out_len
  refine ⟨h.W, h.wd, h.inp, by have := h.out; omega, fun r => ?_, h.k⟩
  have := h.ram r
  have := hx.ram_len r
  have : (b.ram r).length + k + 1 ≤ (a.ram r).length + (n + k) + 1 := by omega
  nlinarith

theorem setv_one_dec {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)} (he : Enc C a σ) (hcap : 1 ≤ cap) :
    WXExec cap (WMX.dec rF) (σ.setv rF (true.toNat)) σ 1 := by
  have d1 := WXExec.dec cap rF (σ.setv rF (true.toNat)) (by simp; omega)
  simp only [WState.setv_val, Function.update_self, Bool.toNat_true, Nat.sub_self] at d1
  rwa [show (σ.setv rF 1).setv rF 0 = σ from by rw [wsetv_setv]; exact he.setvF] at d1

/-- **The compiler is correct**: every derivation is a run of the compiled program, `KC C` steps per cost unit. -/
theorem comp_ok (hB : ∀ s, C.K.bud s ≤ C.Bk → (C.K.outw s).length ≤ C.Bk + 3)
    {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) (ha : Valid C a) :
    ∀ σ : WState (NS M (TS C) V) (NR M), Enc C a σ → CapOK C cap a n →
      (∃ τ, Enc C b τ ∧ WXExec cap (comp C.K s) σ τ (n * KC C)) ∧
      ∀ c t, s = .loop c t → ∃ τ, Enc C b τ ∧
        WXExec cap (wpart c (comp C.K t)) (σ.setv rF (c.eval a).toNat) τ ((n - 1) * KC C) := by
  have hK := KC_ge C
  induction h with
  | op h =>
    intro σ he hc
    exact ⟨compOp_ok C cap h ha he hc, fun c t e => by cases e⟩
  | @seq s t a b d n k h1 h2 ih1 ih2 =>
    intro σ he hc
    refine ⟨?_, fun c t e => by cases e⟩
    have hb := h1.valid hc.W hB ha
    obtain ⟨τ1, e1, r1⟩ := (ih1 ha σ he (hc.mono C cap (by omega))).1
    obtain ⟨τ2, e2, r2⟩ := (ih2 hb τ1 e1 ((hc.mono C cap (by omega)).after C cap h1)).1
    exact ⟨τ2, e2, WXExec.seq' cap r1 r2 (by nlinarith)⟩
  | @iteT c s t a b n hcw hev h1 ih =>
    intro σ he hc
    refine ⟨?_, fun c t e => by cases e⟩
    obtain ⟨τ, e1, r1⟩ := (ih ha σ he (hc.mono C cap (by omega))).1
    have t0 := condP_ok C cap he ha hcw (by have := hc.wd; omega)
    rw [hev] at t0
    have d1 := setv_one_dec C cap he (by have := hc.wd; omega)
    have hne : (σ.setv rF (true.toNat)).val rF ≠ 0 := by simp
    exact ⟨τ, e1, WXExec.seq' cap t0 (WXExec.ifrT hne (WXExec.seq' cap d1 r1 le_rfl)) (by nlinarith)⟩
  | @iteF c s t a b n hcw hev h1 ih =>
    intro σ he hc
    refine ⟨?_, fun c t e => by cases e⟩
    obtain ⟨τ, e1, r1⟩ := (ih ha σ he (hc.mono C cap (by omega))).1
    have t0 := condP_ok C cap he ha hcw (by have := hc.wd; omega)
    rw [hev, Bool.toNat_false, he.setvF] at t0
    exact ⟨τ, e1, WXExec.seq' cap t0 (WXExec.ifrF (by simp [he.zF]) r1) (by nlinarith)⟩
  | @loopF c s a hcw hev =>
    intro σ he hc
    have t0 := condP_ok C cap he ha hcw (by have := hc.wd; omega)
    rw [hev, Bool.toNat_false, he.setvF] at t0
    have w0 : WXExec cap (wpart c (comp C.K s)) σ σ 1 := WXExec.whrF (r := rF) he.zF
    refine ⟨⟨σ, he, WXExec.seq' cap t0 w0 (by omega)⟩, ?_⟩
    intro c' t' e
    cases e
    rw [hev, Bool.toNat_false, he.setvF]
    exact ⟨σ, he, WXExec.mono w0 (by simp; omega)⟩
  | @loopT c s a b d n k hcw hev h1 h2 ih1 ih2 =>
    intro σ he hc
    have hb := h1.valid hc.W hB ha
    have hk2 : 1 ≤ k := h2.pos
    obtain ⟨τ1, e1, r1⟩ := (ih1 ha σ he (hc.mono C cap (by omega))).1
    obtain ⟨τ2, e2, r2⟩ := (ih2 hb τ1 e1 ((hc.mono C cap (by omega)).after C cap h1)).2 c s rfl
    have tb := condP_ok C cap e1 hb hcw (by have := hc.wd; omega)
    have d1 := setv_one_dec C cap he (by have := hc.wd; omega)
    have hne : (σ.setv rF (true.toNat)).val rF ≠ 0 := by simp
    have w : WXExec cap (wpart c (comp C.K s)) (σ.setv rF (true.toNat)) τ2 ((n + k + 2 - 1) * KC C) := by
      refine WXExec.mono (WXExec.whrT hne (WXExec.seq' cap d1 (WXExec.seq' cap r1 tb le_rfl) le_rfl) r2) ?_
      have e1' : n + k + 2 - 1 = n + k + 1 := by omega
      rw [e1']
      have e2' : (k - 1) * KC C + KC C = k * KC C := by
        rw [← Nat.succ_mul]; congr 1; omega
      nlinarith
    refine ⟨?_, ?_⟩
    · have t0 := condP_ok C cap he ha hcw (by have := hc.wd; omega)
      rw [hev] at t0
      refine ⟨τ2, e2, WXExec.seq' cap t0 w ?_⟩
      have e1' : n + k + 2 - 1 = n + k + 1 := by omega
      rw [e1']; nlinarith
    · intro c' t' e
      cases e
      rw [hev]; exact ⟨τ2, e2, w⟩
  | @mono s a b n m h1 hnm ih =>
    intro σ he hc
    obtain ⟨⟨τ, e1, r1⟩, r2⟩ := ih ha σ he (hc.mono C cap hnm)
    refine ⟨⟨τ, e1, WXExec.mono r1 (Nat.mul_le_mul_right _ hnm)⟩, fun c t e => ?_⟩
    obtain ⟨τ', e', r'⟩ := r2 c t e
    exact ⟨τ', e', WXExec.mono r' (Nat.mul_le_mul_right _ (by omega))⟩

end Comp

end NearCubicGates.Close.Cells
