import SourceAdapters.Compile.CNFBalancedA

/-!
# The balanced encoder, part B: the cell passes

proof of `lem:multitape-refuter` (native balanced outer coding of the clause codes). `BR cl Hb S a`: the cell state `a` holds the
encoder state `S` (`CNFBalancedA.BS`): task stack in `sTK` (height `bT`), value stack in `sVS` (height `bV`), the
clause codes followed by a `0` sentinel in `sCL` with the cursor at the next leaf. `bodyB` is one pass (`bodyB_spec`:
`BR … S → BR … (bstep cl S)`).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.CanonicalBinary
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def bT : Fin VV := ⟨84, by decide⟩
def bV : Fin VV := ⟨85, by decide⟩
def bX : Fin VV := ⟨86, by decide⟩
def bL : Fin VV := ⟨87, by decide⟩
def bR : Fin VV := ⟨88, by decide⟩
def bY : Fin VV := ⟨89, by decide⟩
def bZ : Fin VV := ⟨90, by decide⟩
def bW : Fin VV := ⟨91, by decide⟩
def bH : Fin VV := ⟨92, by decide⟩
def bU : Fin VV := ⟨93, by decide⟩
def bN : Fin VV := ⟨94, by decide⟩

/-- The registers the encoder changes. -/
def balT : List (Fin VV) := [iS, iJ, bT, bV, bX, bL, bR, bY, bZ, bW, bH, bU, bN]

/-- Its scratch registers (all but the heights). -/
def balS : List (Fin VV) := [iS, iJ, bX, bL, bR, bY, bZ, bW, bH, bU, bN]

/-- The cell state holds the encoder state. -/
structure BR (cl : List ℕ) (Hb : ℕ) (S : BS) (a : DS VV MM) : Prop where
  kc : KC a
  tk : StkG sTK bT a S.tk
  vs : StkG sVS bV a S.vs
  cl : a.ram sCL = cl ++ [0]
  p : a.rc sCL = S.p
  rtk : a.rc sTK ≤ Hb + 1
  rvs : a.rc sVS ≤ Hb + 1

theorem StkG.congr {m : Fin MM} {sp : Fin VV} {a b : DS VV MM} {st : List ℕ} (h : StkG m sp a st)
    (hram : b.ram m = a.ram m) (hsp : b.env sp = a.env sp) : StkG m sp b st :=
  ⟨by rw [hsp, h.sp], by rw [hram]; exact h.take, by rw [hram]; exact h.len⟩

/-- `BR` survives register changes outside the heights and constants. -/
theorem BR.regs {cl : List ℕ} {Hb : ℕ} {S : BS} {a b : DS VV MM} (h : BR cl Hb S a) (hram : b.ram = a.ram)
    (hrc : b.rc = a.rc) (hF : Fr a b balS) : BR cl Hb S b where
  kc := h.kc.of_fr hF (by decide)
  tk := h.tk.congr (by rw [hram]) (hF bT (by decide) |>.symm ▸ rfl)
  vs := h.vs.congr (by rw [hram]) (hF bV (by decide) |>.symm ▸ rfl)
  cl := by rw [hram, h.cl]
  p := by rw [hrc, h.p]
  rtk := by rw [hrc]; exact h.rtk
  rvs := by rw [hrc]; exact h.rvs

variable {C : Ctx}

theorem vpop_spec (cl : List ℕ) (Hb : ℕ) (hW : Hb + 2 < 2 ^ C.Wd) (ts vs : List ℕ) (p : ℕ) (x : Fin VV)
    (hxT : x ∈ balT) (hx' : x ∉ [iS, iJ, bV, bT]) (a : DS VV MM) (h : BR cl Hb ⟨ts, vs, p⟩ a) (hv : vs.length ≤ Hb) :
    Hs C (popG sVS bV x) a (6 * Hb + 11) (fun b => b.env x = (popS vs).1 ∧ BR cl Hb ⟨ts, (popS vs).2, p⟩ b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [iS, iJ, bV, x]) := by
  have hx2 : x ≠ iS ∧ x ≠ iJ ∧ x ≠ bV ∧ x ≠ bT := by simpa using hx'
  refine Hs.mono (popG_spec sVS bV x (by decide) (by simp [hx2.1, hx2.2.1, hx2.2.2.1]) a vs h.vs h.kc.z h.kc.one
    (by omega)) (by have := h.rvs; omega) ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  have hsub : ∀ y ∈ [iS, iJ, bV, x], y ∈ balT := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> first | decide | exact hxT
  refine ⟨b1, ⟨h.kc.of_fr (Fr.weaken b8 hsub) (by decide), h.tk.congr (by rw [b3]) (b8 bT (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, by decide, by decide, fun e => hx2.2.2.2 e.symm⟩)), b2, by rw [b3, h.cl],
    by rw [b5 sCL (by decide), h.p], by rw [b5 sTK (by decide)]; exact h.rtk, ?_⟩, b6, b7, b8⟩
  have := h.rvs
  have := popS_len vs
  omega

theorem vpush_spec (cl : List ℕ) (Hb : ℕ) (hW : Hb + 2 < 2 ^ C.Wd) (ts vs : List ℕ) (p : ℕ) (x : Fin VV)
    (hx' : x ∉ [iS, iJ, bV]) (a : DS VV MM) (h : BR cl Hb ⟨ts, vs, p⟩ a) (hv : vs.length + 1 ≤ Hb) :
    Hs C (pushG sVS bV x) a (6 * Hb + 11) (fun b => BR cl Hb ⟨ts, a.env x :: vs, p⟩ b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [iS, iJ, bV]) := by
  refine Hs.mono (pushG_spec sVS bV x (by decide) hx' a vs h.vs (by omega)) (by have := h.rvs; omega) ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, b7⟩
  refine ⟨⟨h.kc.of_fr b7 (by decide), h.tk.congr (b4 sTK (by decide)).1 (b7 bT (by decide)), b1,
    by rw [(b4 sCL (by decide)).1, h.cl], by rw [(b4 sCL (by decide)).2, h.p],
    by rw [(b4 sTK (by decide)).2]; exact h.rtk, by rw [b3]; omega⟩, b5, b6, b7⟩

theorem tpush_spec (cl : List ℕ) (Hb : ℕ) (hW : Hb + 2 < 2 ^ C.Wd) (ts vs : List ℕ) (p : ℕ) (x : Fin VV)
    (hx' : x ∉ [iS, iJ, bT]) (a : DS VV MM) (h : BR cl Hb ⟨ts, vs, p⟩ a) (hv : ts.length + 1 ≤ Hb) :
    Hs C (pushG sTK bT x) a (6 * Hb + 11) (fun b => BR cl Hb ⟨a.env x :: ts, vs, p⟩ b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [iS, iJ, bT]) := by
  refine Hs.mono (pushG_spec sTK bT x (by decide) hx' a ts h.tk (by omega)) (by have := h.rtk; omega) ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, b7⟩
  refine ⟨⟨h.kc.of_fr b7 (by decide), b1, h.vs.congr (b4 sVS (by decide)).1 (b7 bV (by decide)),
    by rw [(b4 sCL (by decide)).1, h.cl], by rw [(b4 sCL (by decide)).2, h.p], by rw [b3]; omega,
    by rw [(b4 sVS (by decide)).2]; exact h.rvs⟩, b5, b6, b7⟩

theorem tpop_spec (cl : List ℕ) (Hb : ℕ) (hW : Hb + 2 < 2 ^ C.Wd) (ts vs : List ℕ) (p : ℕ)
    (a : DS VV MM) (h : BR cl Hb ⟨ts, vs, p⟩ a) (hv : ts.length ≤ Hb) :
    Hs C (popG sTK bT bX) a (6 * Hb + 11) (fun b => b.env bX = (popS ts).1 ∧ BR cl Hb ⟨(popS ts).2, vs, p⟩ b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [iS, iJ, bT, bX]) := by
  refine Hs.mono (popG_spec sTK bT bX (by decide) (by decide) a ts h.tk h.kc.z h.kc.one (by omega))
    (by have := h.rtk; omega) ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  refine ⟨b1, ⟨h.kc.of_fr b8 (by decide), b2, h.vs.congr (by rw [b3]) (b8 bV (by decide)), by rw [b3, h.cl],
    by rw [b5 sCL (by decide), h.p], ?_, by rw [b5 sVS (by decide)]; exact h.rvs⟩, b6, b7, b8⟩
  have := h.rtk
  omega

/-- `z := Nat.pair x y` keeps `BR`. -/
theorem bpair_spec (cl : List ℕ) (Hb : ℕ) (S : BS) (x y z : Fin VV) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ bW)
    (hyz : y ≠ z) (hyw : y ≠ bW) (hzw : z ≠ bW) (hz : z ∈ balS) (a : DS VV MM) (h : BR cl Hb S a)
    (hv : Nat.pair (a.env x) (a.env y) < 2 ^ C.Wd) :
    Hs C (pairP x y z bW) a 8 (fun b => b.env z = Nat.pair (a.env x) (a.env y) ∧ BR cl Hb S b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [z, bW]) := by
  refine Hs.mono (pairP_spec x y z bW hxy hxz hxw hyz hyw hzw a hv) le_rfl ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6⟩
  have hF : Fr a b balS := Fr.weaken b6 (by simp [balS] at hz ⊢; tauto)
  exact ⟨b1, h.regs b2 b3 hF, b4, b5, b6⟩

/-! ## The pass cases -/

def combP : St VV MM :=
  .seq (popG sVS bV bR) (.seq (popG sVS bV bL) (.seq (pairP bL bR bZ bW) (.seq (pairP v2 bZ bY bW)
    (pushG sVS bV bY))))

theorem combP_spec (cl : List ℕ) (Hb : ℕ) (hW : Hb + 2 < 2 ^ C.Wd) (ts vs : List ℕ) (p : ℕ) (a : DS VV MM)
    (h : BR cl Hb ⟨ts, vs, p⟩ a) (hv : vs.length ≤ Hb) (hv2 : (popS (popS vs).2).2.length + 1 ≤ Hb)
    (hB : Nat.pair 2 (Nat.pair (popS (popS vs).2).1 (popS vs).1) < 2 ^ C.Wd) :
    Hs C combP a (24 * Hb + 70) (fun b =>
      BR cl Hb ⟨ts, Nat.pair 2 (Nat.pair (popS (popS vs).2).1 (popS vs).1) :: (popS (popS vs).2).2, p⟩ b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b balT) := by
  have l1 := popS_len vs
  have l2 := popS_len (popS vs).2
  have hp1 := Nat.right_le_pair 2 (Nat.pair (popS (popS vs).2).1 (popS vs).1)
  refine Hs.seqc (t1 := 6 * Hb + 11) (t2 := 18 * Hb + 58) (vpop_spec cl Hb hW ts vs p bR (by decide) (by decide) a h hv)
    (fun b1 ⟨e1, h1, i1, o1, f1⟩ => ?_) (by omega)
  refine Hs.seqc (t1 := 6 * Hb + 11) (t2 := 12 * Hb + 46) (vpop_spec cl Hb hW ts _ p bL (by decide) (by decide) b1 h1
    (by omega)) (fun b2 ⟨e2, h2, i2, o2, f2⟩ => ?_) (by omega)
  have e2R : b2.env bR = (popS vs).1 := by rw [f2 bR (by decide), e1]
  refine Hs.seqc (t1 := 8) (t2 := 12 * Hb + 37) (bpair_spec cl Hb _ bL bR bZ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) b2 h2 (by rw [e2, e2R]; omega)) (fun b3 ⟨e3, h3, i3, o3, f3⟩ => ?_)
    (by omega)
  refine Hs.seqc (t1 := 8) (t2 := 6 * Hb + 11) (bpair_spec cl Hb _ v2 bZ bY (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) b3 h3 (by rw [e3, h3.kc.two, e2, e2R]; omega))
    (fun b4 ⟨e4, h4, i4, o4, f4⟩ => ?_) (by omega)
  refine Hs.mono (vpush_spec cl Hb hW ts _ p bY (by decide) b4 h4 (by omega)) le_rfl ?_
  rintro b5 ⟨h5, i5, o5, f5⟩
  refine ⟨?_, by rw [i5, i4, i3, i2, i1], by rw [o5, o4, o3, o2, o1], (Fr.weaken f1 (by simp [balT])).trans
    ((Fr.weaken f2 (by simp [balT])).trans ((Fr.weaken f3 (by simp [balT])).trans ((Fr.weaken f4 (by simp [balT])).trans
    (Fr.weaken f5 (by simp [balT])))))⟩
  rw [e4, h3.kc.two, e3, e2, e2R] at h5
  exact h5

def zeroP' : St VV MM := .seq (.op (.zero bY)) (pushG sVS bV bY)

theorem zeroP'_spec (cl : List ℕ) (Hb : ℕ) (hW : Hb + 2 < 2 ^ C.Wd) (ts vs : List ℕ) (p : ℕ) (a : DS VV MM)
    (h : BR cl Hb ⟨ts, vs, p⟩ a) (hv : vs.length + 1 ≤ Hb) :
    Hs C zeroP' a (6 * Hb + 13) (fun b => BR cl Hb ⟨ts, 0 :: vs, p⟩ b ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b balT) := by
  refine Hs.seqc (t1 := 1) (t2 := 6 * Hb + 11) (hs_zero C bY a) (fun b1 hb1 => ?_) (by omega)
  subst hb1
  have hF : Fr a (a.set bY 0) balS := Fr.set a 0 (by simp [balS])
  refine Hs.mono (vpush_spec cl Hb hW ts vs p bY (by decide) _ (h.regs rfl rfl hF) hv) le_rfl ?_
  rintro b ⟨h2, i2, o2, f2⟩
  exact ⟨by simpa using h2, i2, o2, (Fr.weaken hF (by simp [balT, balS])).trans (Fr.weaken f2 (by simp [balT]))⟩

def leafP : St VV MM := .seq (.op (.rdM sCL bU)) (.seq (pairP v1 bU bY bW) (pushG sVS bV bY))

theorem leafP_spec (cl : List ℕ) (Hb : ℕ) (hW : Hb + 2 < 2 ^ C.Wd) (ts vs : List ℕ) (p : ℕ) (a : DS VV MM)
    (h : BR cl Hb ⟨ts, vs, p⟩ a) (hv : vs.length + 1 ≤ Hb) (hp : p < cl.length)
    (hB : Nat.pair 1 (cl.getD p 0) < 2 ^ C.Wd) :
    Hs C leafP a (6 * Hb + 22) (fun b => BR cl Hb ⟨ts, Nat.pair 1 (cl.getD p 0) :: vs, p + 1⟩ b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b balT) := by
  have hcl := h.cl
  have hpc := h.p
  refine Hs.seqc (t1 := 1) (t2 := 6 * Hb + 20) (hs_rdM C sCL bU a (by rw [hpc, hcl]; simp; omega))
    (fun b1 hb1 => ?_) (by omega)
  subst hb1
  set b1 := (a.set bU ((a.ram sCL).getD (a.rc sCL) 0)).adv sCL with hb1
  have hU : b1.env bU = cl.getD p 0 := by
    rw [hb1]; simp only [DS.adv, DS.set_env_self, hpc, hcl]
    rw [List.getD_append _ _ _ _ hp]
  have hF1 : Fr a b1 balS := fun y hy => by
    rw [hb1]; simp only [DS.adv]; exact Fr.set a _ (show bU ∈ balS by simp [balS]) y hy
  have h1 : BR cl Hb ⟨ts, vs, p + 1⟩ b1 :=
    { kc := h.kc.of_fr hF1 (by decide)
      tk := h.tk.congr (by rw [hb1]; rfl) (hF1 bT (by decide))
      vs := h.vs.congr (by rw [hb1]; rfl) (hF1 bV (by decide))
      cl := by rw [hb1]; exact hcl
      p := by rw [hb1]; simp [DS.adv, hpc]
      rtk := by rw [hb1]; simp [DS.adv, Function.update_of_ne (show sTK ≠ sCL by decide)]; exact h.rtk
      rvs := by rw [hb1]; simp [DS.adv, Function.update_of_ne (show sVS ≠ sCL by decide)]; exact h.rvs }
  refine Hs.seqc (t1 := 8) (t2 := 6 * Hb + 11) (bpair_spec cl Hb _ v1 bU bY (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) b1 h1 (by rw [h1.kc.one, hU]; exact hB))
    (fun b2 ⟨e2, h2, i2, o2, f2⟩ => ?_) (by omega)
  refine Hs.mono (vpush_spec cl Hb hW ts vs (p + 1) bY (by decide) b2 h2 hv) le_rfl ?_
  rintro b3 ⟨h3, i3, o3, f3⟩
  rw [e2, h1.kc.one, hU] at h3
  exact ⟨h3, by rw [i3, i2, hb1]; rfl, by rw [o3, o2, hb1]; rfl, (Fr.weaken hF1 (by simp [balT, balS])).trans ((Fr.weaken f2 (by simp [balT])).trans
    (Fr.weaken f3 (by simp [balT])))⟩

/-- `len := bX - 1`, `h := (len + 1) / 2`; `bZ := 0`, `bR := len - h + 1`, `bH := h + 1`. -/
def splitArP : St VV MM :=
  .seq (.op (.copy bL bX)) (.seq (.op (.sub bL v1)) (.seq (.op (.copy bH bL)) (.seq (.op (.inc bH))
    (.seq (.op (.half bH)) (.seq (.op (.copy bR bL)) (.seq (.op (.sub bR bH)) (.seq (.op (.zero bZ))
    (.seq (.op (.inc bR)) (.op (.inc bH))))))))))

def splitP : St VV MM := .seq splitArP (.seq (pushG sTK bT bZ) (.seq (pushG sTK bT bR) (pushG sTK bT bH)))

theorem splitP_spec (cl : List ℕ) (Hb : ℕ) (hW : Hb + cl.length + 10 < 2 ^ C.Wd) (ts vs : List ℕ) (p c : ℕ)
    (a : DS VV MM) (h : BR cl Hb ⟨ts, vs, p⟩ a) (hX : a.env bX = c + 3) (hc : c + 3 ≤ cl.length + 1)
    (hv : ts.length + 3 ≤ Hb) :
    Hs C splitP a (18 * Hb + 60) (fun b =>
      BR cl Hb ⟨((c + 3) / 2 + 1) :: (c + 2 - (c + 3) / 2 + 1) :: 0 :: ts, vs, p⟩ b ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b balT) := by
  have hk := h.kc
  have s1 : Hs C splitArP a 19 (fun b => b.env bZ = 0 ∧ b.env bR = c + 2 - (c + 3) / 2 + 1 ∧
      b.env bH = (c + 3) / 2 + 1 ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b balS) := by
    apply hs_of_wpc
    simp only [splitArP, wpc, opwp]
    vsimp [hX, hk.one]
    and_split
    all_goals first | omega | rfl | skip
    all_goals frx [balS]
  refine Hs.seqc (t1 := 19) (t2 := 18 * Hb + 35) s1 (fun b1 ⟨z1, r1, h1', m1, c1', i1, o1, f1⟩ => ?_) (by omega)
  have h1 : BR cl Hb ⟨ts, vs, p⟩ b1 := h.regs m1 c1' f1
  refine Hs.seqc (t1 := 6 * Hb + 11) (t2 := 12 * Hb + 23) (tpush_spec cl Hb (by omega) ts vs p bZ (by decide) b1 h1
    (by omega)) (fun b2 ⟨h2, i2, o2, f2⟩ => ?_) (by omega)
  have r2 : b2.env bR = c + 2 - (c + 3) / 2 + 1 := by rw [f2 bR (by decide), r1]
  have hh2 : b2.env bH = (c + 3) / 2 + 1 := by rw [f2 bH (by decide), h1']
  refine Hs.seqc (t1 := 6 * Hb + 11) (t2 := 6 * Hb + 11) (tpush_spec cl Hb (by omega) _ vs p bR (by decide) b2 h2
    (by simp; omega)) (fun b3 ⟨h3, i3, o3, f3⟩ => ?_) (by omega)
  have hh3 : b3.env bH = (c + 3) / 2 + 1 := by rw [f3 bH (by decide), hh2]
  refine Hs.mono (tpush_spec cl Hb (by omega) _ vs p bH (by decide) b3 h3 (by simp; omega)) le_rfl ?_
  rintro b4 ⟨h4, i4, o4, f4⟩
  rw [hh3, r2, z1] at h4
  exact ⟨h4, by rw [i4, i3, i2, i1], by rw [o4, o3, o2, o1], (Fr.weaken f1 (by simp [balT, balS])).trans ((Fr.weaken f2 (by simp [balT])).trans
    ((Fr.weaken f3 (by simp [balT])).trans (Fr.weaken f4 (by simp [balT]))))⟩

end NearCubicGates.Adapters.Compile
