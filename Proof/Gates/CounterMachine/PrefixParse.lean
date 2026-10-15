import Proof.Gates.CounterMachine.PrefixVal
import Proof.Gates.CounterMachine.PrefixLoad3

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader

/-- The stores of the prefix program (`sN = 0` is the loader's). -/
def sG1 : Fin MM := ⟨1, by decide⟩
def sG2 : Fin MM := ⟨2, by decide⟩
def sPa : Fin MM := ⟨3, by decide⟩
def sIn : Fin MM := ⟨4, by decide⟩

/-- Variables of the parse. -/
def xG1 : Fin VV := ⟨40, by decide⟩
def xG2 : Fin VV := ⟨41, by decide⟩
def xm1 : Fin VV := ⟨42, by decide⟩
def xm2 : Fin VV := ⟨43, by decide⟩
def xnp : Fin VV := ⟨44, by decide⟩
def xk : Fin VV := ⟨45, by decide⟩
def xkk : Fin VV := ⟨46, by decide⟩
def xt : Fin VV := ⟨47, by decide⟩

/-! ## Store passes -/

theorem drop_next {l R : List ℕ} {i v : ℕ} (h : l.drop i = v :: R) :
    i < l.length ∧ l.getD i 0 = v ∧ l.drop (i + 1) = R := by
  have hi : i < l.length := by
    by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at h; cases h
  refine ⟨hi, ?_, ?_⟩
  · rw [List.drop_eq_getElem_cons hi] at h
    rw [List.getD_eq_getElem _ _ hi]; exact (List.cons.inj h).1
  · rw [← List.drop_drop, h]; rfl

theorem drop_skip {l L R : List ℕ} {i : ℕ} (h : l.drop i = L ++ R) : l.drop (i + L.length) = R := by
  rw [← List.drop_drop, h, List.drop_left]

theorem rdS_spec (C : Ctx) (m : Fin MM) (x : Fin VV) (b : DS VV MM) (v : ℕ) (R : List ℕ)
    (h : (b.ram m).drop (b.rc m) = v :: R) :
    Hs C (.op (.rdM m x)) b 1 (fun d => d.env x = v ∧ (d.ram m).drop (d.rc m) = R ∧ d.ram = b.ram ∧
      d.rc = Function.update b.rc m (b.rc m + 1) ∧ d.out = b.out ∧ Oth b d ∧ Fr b d [x]) := by
  obtain ⟨h1, h2, h3⟩ := drop_next h
  refine Hs.mono (hs_rdM C m x b h1) le_rfl ?_
  rintro d rfl
  refine ⟨by simp only [DS.adv, DS.set_env_self]; exact h2, by simp [DS.adv, h3], rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  intro y hy; simp only [DS.adv]; exact Fr.set b _ (by simp) y hy

/-- Skip `k` records (a constant). -/
def skipK (m : Fin MM) : ℕ → St VV MM
  | 0 => .op (.zero yJ)
  | k + 1 => .seq (.op (.rdM m yJ)) (skipK m k)

theorem skipK_spec (C : Ctx) (m : Fin MM) : ∀ (k : ℕ) (b : DS VV MM) (L R : List ℕ),
    (b.ram m).drop (b.rc m) = L ++ R → L.length = k →
    Hs C (skipK m k) b (2 * k + 1) (fun d => (d.ram m).drop (d.rc m) = R ∧ d.ram = b.ram ∧
      d.rc = Function.update b.rc m (b.rc m + k) ∧ d.out = b.out ∧ Oth b d ∧ Fr b d [yJ])
  | 0, b, L, R, h, hk => by
    have hL : L = [] := List.eq_nil_of_length_eq_zero hk
    subst hL
    refine Hs.mono (hs_zero C yJ b) le_rfl ?_
    rintro d rfl
    exact ⟨by simpa using h, rfl, by simp, rfl, ⟨rfl, rfl, rfl, rfl⟩, Fr.set b _ (by simp)⟩
  | k + 1, b, L, R, h, hk => by
    obtain ⟨v, L', rfl⟩ : ∃ v L', L = v :: L' := by
      cases L with
      | nil => simp at hk
      | cons v L' => exact ⟨v, L', rfl⟩
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 2 * k + 1) (rdS_spec C m yJ b v (L' ++ R) (by simpa using h))
      (fun d ⟨_, d2, d3, d4, d5, d6, d7⟩ => ?_)) (by omega) (fun _ h => h)
    refine Hs.mono (skipK_spec C m k d L' R d2 (by simpa using hk)) le_rfl ?_
    rintro e ⟨e1, e2, e3, e4, e5, e6⟩
    refine ⟨e1, e2.trans d3, ?_, e4.trans d5, d6.trans e5, Fr.trans d7 e6⟩
    rw [e3, d4]; simp only [Function.update_self, Function.update_idem]; congr 1; omega

/-- Skip `cnt` records. -/
def skipS (m : Fin MM) (cnt : Fin VV) : St VV MM := forS j1 cnt (.op (.rdM m yJ))

theorem skipS_spec (C : Ctx) (m : Fin MM) (cnt : Fin VV) (hcnt : 38 ≤ cnt.val) (b : DS VV MM) (L R : List ℕ)
    (h : (b.ram m).drop (b.rc m) = L ++ R) (hlen : b.env cnt = L.length) (hN : L.length < 2 ^ C.Wd) :
    Hs C (skipS m cnt) b (L.length * 5 + 4) (fun d => (d.ram m).drop (d.rc m) = R ∧ d.ram = b.ram ∧
      d.rc = Function.update b.rc m (b.rc m + L.length) ∧ d.out = b.out ∧ Oth b d ∧ Fr b d [j1, yJ]) := by
  let I : ℕ → DS VV MM → Prop := fun j d => (d.ram m).drop (d.rc m) = L.drop j ++ R ∧ d.ram = b.ram ∧
    d.rc = Function.update b.rc m (b.rc m + j) ∧ d.out = b.out ∧ Oth b d ∧ Fr b d [j1, yJ]
  have hl := forS_spec' (C := C) j1 cnt (Ne.symm (ne_lo hcnt (by decide))) (.op (.rdM m yJ)) b L.length hN I 1
    (fun k d w ⟨d1, d2, d3, d4, d5, d6⟩ => ⟨d1, d2, d3, d4, d5.trans ⟨rfl, rfl, rfl, rfl⟩,
      Fr.trans d6 (Fr.set d w (by simp))⟩)
    ⟨by simpa using h, rfl, by simp, rfl, ⟨rfl, rfl, rfl, rfl⟩, Fr.refl _ _⟩ hlen ?_
  · refine Hs.mono hl (by omega) ?_
    rintro d ⟨⟨d1, d2, d3, d4, d5, d6⟩, _, _⟩
    exact ⟨by simpa using d1, d2, d3, d4, d5, d6⟩
  · intro k hk d ⟨d1, d2, d3, d4, d5, d6⟩ hdk hdc
    have hcons : L.drop k ++ R = L[k] :: (L.drop (k + 1) ++ R) := by
      rw [List.drop_eq_getElem_cons hk]; rfl
    refine Hs.mono (rdS_spec C m yJ d L[k] _ (by rw [d1, hcons])) le_rfl ?_
    rintro e ⟨_, e2, e3, e4, e5, e6, e7⟩
    refine ⟨⟨e2, e3.trans d2, ?_, e5.trans d4, d5.trans e6, Fr.trans d6 (Fr.weaken e7 (by simp))⟩, ?_, ?_⟩
    · rw [e4, d3]; simp only [Function.update_self, Function.update_idem]; congr 1
    · rw [e7 j1 (by decide)]; exact hdk
    · rw [e7 cnt (by simp; exact ne_lo hcnt (by decide))]; exact hdc

/-- Copy `cnt` records to store `dst`. -/
def cpS (m dst : Fin MM) (cnt : Fin VV) : St VV MM := forS j1 cnt (.seq (.op (.rdM m yv)) (.op (.wrM dst yv)))

theorem cpS_spec (C : Ctx) (m dst : Fin MM) (hmd : m ≠ dst) (cnt : Fin VV) (hcnt : 38 ≤ cnt.val) (b : DS VV MM)
    (L R : List ℕ) (h : (b.ram m).drop (b.rc m) = L ++ R) (hlen : b.env cnt = L.length) (hN : L.length < 2 ^ C.Wd)
    (hd : b.rc dst = (b.ram dst).length) :
    Hs C (cpS m dst cnt) b (L.length * 7 + 4) (fun d => (d.ram m).drop (d.rc m) = R ∧
      d.ram = Function.update b.ram dst (b.ram dst ++ L) ∧
      d.rc = Function.update (Function.update b.rc m (b.rc m + L.length)) dst ((b.ram dst).length + L.length) ∧
      d.out = b.out ∧ Oth b d ∧ Fr b d [j1, yv]) := by
  let I : ℕ → DS VV MM → Prop := fun j d => (d.ram m).drop (d.rc m) = L.drop j ++ R ∧
    d.ram = Function.update b.ram dst (b.ram dst ++ L.take j) ∧
    d.rc = Function.update (Function.update b.rc m (b.rc m + j)) dst ((b.ram dst).length + j) ∧ d.out = b.out ∧
    Oth b d ∧ Fr b d [j1, yv]
  have hl := forS_spec' (C := C) j1 cnt (Ne.symm (ne_lo hcnt (by decide)))
    (.seq (.op (.rdM m yv)) (.op (.wrM dst yv))) b L.length hN I 3
    (fun k d w ⟨d1, d2, d3, d4, d5, d6⟩ => ⟨d1, d2, d3, d4, d5.trans ⟨rfl, rfl, rfl, rfl⟩,
      Fr.trans d6 (Fr.set d w (by simp))⟩)
    ⟨by simpa using h, by simp, by
      funext m'; by_cases h1 : m' = dst
      · subst h1; simp [hd]
      · by_cases h2 : m' = m
        · subst h2; simp [Function.update_of_ne h1]
        · simp [Function.update_of_ne h1], rfl, ⟨rfl, rfl, rfl, rfl⟩, Fr.refl _ _⟩ hlen ?_
  · refine Hs.mono hl (by omega) ?_
    rintro d ⟨⟨d1, d2, d3, d4, d5, d6⟩, _, _⟩
    exact ⟨by simpa using d1, by rw [d2, List.take_of_length_le le_rfl], d3, d4, d5, d6⟩
  · intro k hk d ⟨d1, d2, d3, d4, d5, d6⟩ hdk hdc
    have hcons : L.drop k ++ R = L[k] :: (L.drop (k + 1) ++ R) := by
      rw [List.drop_eq_getElem_cons hk]; rfl
    refine Hs.seq (t1 := 1) (t2 := 1) (rdS_spec C m yv d L[k] (L.drop (k + 1) ++ R) (by rw [d1, hcons]))
      (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ => ?_)
    have edst : e.rc dst = (e.ram dst).length := by
      rw [e4, e3, d2, d3, Function.update_of_ne (Ne.symm hmd), Function.update_self, Function.update_self]
      simp; omega
    refine Hs.mono (hs_wrM C dst yv e (le_of_eq edst)) le_rfl ?_
    rintro g rfl
    have htake : L.take (k + 1) = L.take k ++ [L[k]] :=
      CellTables.take_succ_getElem L k _ (List.getElem?_eq_getElem hk)
    have hput : putAt (e.ram dst) (e.rc dst) (e.env yv) = b.ram dst ++ L.take (k + 1) := by
      rw [edst]; unfold putAt
      rw [if_neg (lt_irrefl _), e1, e3, d2, Function.update_self, htake, List.append_assoc]
    have ercm : e.rc m = b.rc m + k + 1 := by
      rw [e4, Function.update_self, d3, Function.update_of_ne hmd, Function.update_self]
    have ercd : e.rc dst = (b.ram dst).length + k := by
      rw [e4, Function.update_of_ne (Ne.symm hmd), d3, Function.update_self]
    refine ⟨⟨?_, ?_, ?_, by simp [DS.put, e5, d4], d5.trans (e6.trans ⟨rfl, rfl, rfl, rfl⟩), ?_⟩, ?_, ?_⟩
    · simp only [DS.put, Function.update_of_ne hmd]; exact e2
    · simp only [DS.put]; rw [hput, e3, d2, Function.update_idem]
    · funext m'
      simp only [DS.put]
      by_cases h1 : m' = dst
      · subst h1; rw [Function.update_self, Function.update_self, ercd]; omega
      · rw [Function.update_of_ne h1, Function.update_of_ne h1]
        by_cases h2 : m' = m
        · subst h2; rw [Function.update_self, ercm]; omega
        · rw [Function.update_of_ne h2, e4, Function.update_of_ne h2, d3, Function.update_of_ne h1,
            Function.update_of_ne h2]
    · exact Fr.trans d6 (Fr.weaken e7 (by simp))
    · simp only [DS.put]; rw [e7 j1 (by decide)]; exact hdk
    · simp only [DS.put]; rw [e7 cnt (by simp; exact ne_lo hcnt (by decide))]; exact hdc

/-! ## The parse state -/

/-- Every store but `sN` has its cursor at its end. -/
def AtEnd (d : DS VV MM) : Prop := ∀ m, m ≠ sN → d.rc m = (d.ram m).length

/-- Variables written by the parse. -/
def parseT : List (Fin VV) := [j1, yv, yJ, xG1, xG2, xm1, xm2, xnp, xk, xkk, xt]

/-- The parse state: `R` remains in `sN`, the stores are `F`. -/
structure PS (b d : DS VV MM) (R : List ℕ) (F : Fin MM → List ℕ) : Prop where
  rem : (d.ram sN).drop (d.rc sN) = R
  ram : d.ram = F
  ends : AtEnd d
  out : d.out = b.out
  oth : Oth b d
  fr : Fr b d parseT

theorem PS.rdS {C : Ctx} {b d : DS VV MM} {v : ℕ} {R : List ℕ} {F : Fin MM → List ℕ} (h : PS b d (v :: R) F)
    (x : Fin VV) (hx : x ∈ parseT) :
    Hs C (.op (.rdM sN x)) d 1 (fun e => PS b e R F ∧ e.env x = v ∧ Fr d e [x]) := by
  refine Hs.mono (rdS_spec C sN x d v R h.rem) le_rfl ?_
  rintro e ⟨e1, e2, e3, e4, e5, e6, e7⟩
  refine ⟨⟨e2, e3.trans h.ram, fun m hm => ?_, e5.trans h.out, h.oth.trans e6,
    Fr.trans h.fr (Fr.weaken e7 (by simpa using hx))⟩, e1, e7⟩
  rw [e4, Function.update_of_ne hm, e3]; exact h.ends m hm

theorem PS.skipK {C : Ctx} {b d : DS VV MM} {L R : List ℕ} {F : Fin MM → List ℕ} (h : PS b d (L ++ R) F)
    (k : ℕ) (hk : L.length = k) :
    Hs C (skipK sN k) d (2 * k + 1) (fun e => PS b e R F ∧ Fr d e [yJ]) := by
  refine Hs.mono (skipK_spec C sN k d L R h.rem hk) le_rfl ?_
  rintro e ⟨e1, e2, e3, e4, e5, e6⟩
  refine ⟨⟨e1, e2.trans h.ram, fun m hm => ?_, e4.trans h.out, h.oth.trans e5,
    Fr.trans h.fr (Fr.weaken e6 (by simp [parseT]))⟩, e6⟩
  rw [e3, Function.update_of_ne hm, e2]; exact h.ends m hm

theorem PS.skipS {C : Ctx} {b d : DS VV MM} {L R : List ℕ} {F : Fin MM → List ℕ} (h : PS b d (L ++ R) F)
    (cnt : Fin VV) (hcnt : 38 ≤ cnt.val) (hlen : d.env cnt = L.length) (hN : L.length < 2 ^ C.Wd) :
    Hs C (skipS sN cnt) d (L.length * 5 + 4) (fun e => PS b e R F ∧ Fr d e [j1, yJ]) := by
  refine Hs.mono (skipS_spec C sN cnt hcnt d L R h.rem hlen hN) le_rfl ?_
  rintro e ⟨e1, e2, e3, e4, e5, e6⟩
  refine ⟨⟨e1, e2.trans h.ram, fun m hm => ?_, e4.trans h.out, h.oth.trans e5,
    Fr.trans h.fr (Fr.weaken e6 (by simp [parseT]))⟩, e6⟩
  rw [e3, Function.update_of_ne hm, e2]; exact h.ends m hm

theorem PS.cpS {C : Ctx} {b d : DS VV MM} {L R : List ℕ} {F : Fin MM → List ℕ} (h : PS b d (L ++ R) F)
    (dst : Fin MM) (hdst : dst ≠ sN) (cnt : Fin VV) (hcnt : 38 ≤ cnt.val) (hlen : d.env cnt = L.length)
    (hN : L.length < 2 ^ C.Wd) :
    Hs C (cpS sN dst cnt) d (L.length * 7 + 4) (fun e =>
      PS b e R (Function.update F dst (F dst ++ L)) ∧ Fr d e [j1, yv]) := by
  refine Hs.mono (cpS_spec C sN dst (Ne.symm hdst) cnt hcnt d L R h.rem hlen hN (h.ends dst hdst)) le_rfl ?_
  rintro e ⟨e1, e2, e3, e4, e5, e6⟩
  refine ⟨⟨e1, by rw [e2, h.ram], fun m hm => ?_, e4.trans h.out, h.oth.trans e5,
    Fr.trans h.fr (Fr.weaken e6 (by simp [parseT]))⟩, e6⟩
  rw [e3, e2]
  by_cases h1 : m = dst
  · subst h1; simp only [Function.update_self, List.length_append]
  · rw [Function.update_of_ne h1, Function.update_of_ne hm, Function.update_of_ne h1]; exact h.ends m hm

/-! ## One circuit -/

/-- Read `|C.gates|`, copy the gate block to `sG`, skip the coefficients and the table. -/
def circP (sG : Fin MM) (xG xm : Fin VV) : St VV MM :=
  .seq (.op (.rdM sN xG)) (.seq (.op (.mul xG gS xm)) (.seq (cpS sN sG xm)
    (.seq (.op (.rdM sN xt)) (.seq (.op (.shl xt)) (.seq (skipS sN xt) (.seq (.op (.rdM sN xt)) (skipS sN xt)))))))

theorem circN_eq {n : ℕ} (Cc : NCircuit n) : circN Cc = Cc.gates.length :: (Cc.gates.flatMap gateN ++
    (Cc.coeffs.length :: (Cc.coeffs.flatMap intN ++ (Cc.table.length :: Cc.table.map bitN)))) := by
  simp [circN, List.append_assoc]

theorem intN_flat_length (l : List ℤ) : (l.flatMap intN).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.length_append, ih]; simp [intN]; ring

theorem circP_spec (C : Ctx) (sG : Fin MM) (hsG : sG ≠ sN) (xG xm : Fin VV) (hxG : xG ∈ parseT)
    (hxm : xm ∈ parseT) (hGm : xG ≠ xm) (hG38 : 38 ≤ xG.val) (hm38 : 38 ≤ xm.val) (hxGt : xG ≠ xt)
    (hxmt : xm ≠ xt) {n : ℕ} (Cc : NCircuit n) (b d : DS VV MM) (R : List ℕ) (F : Fin MM → List ℕ)
    (h : PS b d (circN Cc ++ R) F) (hgS : d.env gS = 2 * n + 3) (hN : (circN Cc).length < 2 ^ C.Wd) :
    Hs C (circP sG xG xm) d (7 * (circN Cc).length + 30) (fun e =>
      PS b e R (Function.update F sG (F sG ++ Cc.gates.flatMap gateN)) ∧ e.env xG = Cc.gates.length ∧
        e.env xm = (Cc.gates.flatMap gateN).length ∧ Fr d e [j1, yv, yJ, xG, xm, xt]) := by
  have hlen : (circN Cc).length = 1 + (Cc.gates.flatMap gateN).length + 1 + (Cc.coeffs.flatMap intN).length + 1 +
      (Cc.table.map bitN).length := by
    rw [circN_eq]; simp only [List.length_cons, List.length_append]; omega
  set blk := Cc.gates.flatMap gateN with hblk
  set cf := Cc.coeffs.flatMap intN with hcf
  set tb := Cc.table.map bitN with htb
  have hblen : blk.length = Cc.gates.length * (2 * n + 3) := gates_flat_length _
  have hcflen : cf.length = 2 * Cc.coeffs.length := intN_flat_length _
  have htblen : tb.length = Cc.table.length := by simp [htb]
  have h0 : PS b d (Cc.gates.length :: (blk ++ (Cc.coeffs.length :: (cf ++ (Cc.table.length :: (tb ++ R)))))) F := by
    have := h; rw [circN_eq] at this; simpa [List.append_assoc] using this
  have hxt : xt ∈ parseT := by simp [parseT]
  have hgSn : gS ≠ xG ∧ gS ≠ xm ∧ gS ≠ xt := ⟨fun e => by rw [← e] at hG38; simp [gS] at hG38,
    fun e => by rw [← e] at hm38; simp [gS] at hm38, by decide⟩
  refine Hs.mono (t := 1 + (1 + ((blk.length * 7 + 4) + (1 + (1 + ((cf.length * 5 + 4) + (1 + (tb.length * 5 + 4)
    + 1) + 1) + 1) + 1) + 1) + 1) + 1) ?_ (by omega) (fun _ h => h)
  refine Hs.seq (t1 := 1) (h0.rdS xG hxG) (fun d1 ⟨p1, v1', f1⟩ => ?_)
  have d1gS : d1.env gS = 2 * n + 3 := by rw [f1 gS (by simp; exact hgSn.1), hgS]
  refine Hs.seq (t1 := 1) (hs_mul C xG gS xm d1 (Ne.symm hgSn.1) hGm hgSn.2.1 (by
    rw [v1', d1gS, ← hblen]; omega)) (fun d2 hd2 => ?_)
  subst hd2
  have p2 : PS b (d1.set xm (d1.env xG * d1.env gS)) (blk ++ (Cc.coeffs.length :: (cf ++
      (Cc.table.length :: (tb ++ R))))) F :=
    ⟨p1.rem, p1.ram, p1.ends, p1.out, p1.oth.trans ⟨rfl, rfl, rfl, rfl⟩, Fr.trans p1.fr (Fr.set _ _ hxm)⟩
  have m2 : (d1.set xm (d1.env xG * d1.env gS)).env xm = blk.length := by
    rw [DS.set_env_self, v1', d1gS, hblen]
  refine Hs.seq (t1 := blk.length * 7 + 4) (p2.cpS sG hsG xm hm38 m2 (by omega)) (fun d3 ⟨p3, f3⟩ => ?_)
  refine Hs.seq (t1 := 1) (p3.rdS xt hxt) (fun d4 ⟨p4, v4, f4⟩ => ?_)
  refine Hs.seq (t1 := 1) (hs_shl C xt d4 (by rw [v4, ← hcflen]; omega)) (fun d5 hd5 => ?_)
  subst hd5
  have p5 : PS b (d4.set xt (2 * d4.env xt)) (cf ++ (Cc.table.length :: (tb ++ R)))
      (Function.update F sG (F sG ++ blk)) :=
    ⟨p4.rem, p4.ram, p4.ends, p4.out, p4.oth.trans ⟨rfl, rfl, rfl, rfl⟩, Fr.trans p4.fr (Fr.set _ _ hxt)⟩
  refine Hs.seq (t1 := cf.length * 5 + 4) (p5.skipS xt (by decide) (by rw [DS.set_env_self, v4, hcflen])
    (by omega)) (fun d6 ⟨p6, f6⟩ => ?_)
  refine Hs.seq (t1 := 1) (p6.rdS xt hxt) (fun d7 ⟨p7, v7, f7⟩ => ?_)
  refine Hs.mono (p7.skipS xt (by decide) (by rw [v7, htblen]) (by omega)) le_rfl ?_
  rintro e ⟨p8, f8⟩
  have frm : ∀ y, y ≠ xt → y ≠ j1 → y ≠ yJ → y ≠ yv → e.env y = d3.env y := by
    intro y h1 h2 h3 h4
    rw [f8 y (by simp; exact ⟨h2, h3⟩), f7 y (by simp; exact h1), f6 y (by simp; exact ⟨h2, h3⟩),
      DS.set_env_ne _ _ h1, f4 y (by simp; exact h1)]
  refine ⟨p8, ?_, ?_, ?_⟩
  · rw [frm xG hxGt (fun e => by rw [e] at hG38; simp [j1] at hG38) (fun e => by rw [e] at hG38; simp [yJ] at hG38)
      (fun e => by rw [e] at hG38; simp [yv] at hG38)]
    rw [f3 xG (by simp; exact ⟨fun e => by rw [e] at hG38; simp [j1] at hG38,
      fun e => by rw [e] at hG38; simp [yv] at hG38⟩), DS.set_env_ne _ _ hGm, v1']
  · rw [frm xm hxmt (fun e => by rw [e] at hm38; simp [j1] at hm38) (fun e => by rw [e] at hm38; simp [yJ] at hm38)
      (fun e => by rw [e] at hm38; simp [yv] at hm38)]
    rw [f3 xm (by simp; exact ⟨fun e => by rw [e] at hm38; simp [j1] at hm38,
      fun e => by rw [e] at hm38; simp [yv] at hm38⟩), m2]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hy
    rw [frm y h6 h1 h3 h2, f3 y (by simp; exact ⟨h1, h2⟩), DS.set_env_ne _ _ h5, f1 y (by simp; exact h4)]

/-! ## The whole pass -/

/-- The rest of the witness after the coordinates. -/
def witRest (c : Call) (p : Params) (wt : Wit c.n) : List ℕ :=
  (srList c p).flatMap fun sr => [(wt.coef sr.1 sr.2).length] ++ (wt.coef sr.1 sr.2).flatMap intN

/-- What follows the parity list, in the shape the pass consumes it. -/
def callTail (c : Call) (p : Params) (wt : Wit c.n) : List ℕ :=
  (ratN c.radius ++ ([p.n, bitN p.pair, p.W] ++ ratN p.beta)) ++ (p.k :: ([p.T, p.m, p.Dmax, p.P, p.e] ++
      ((p.primes.sort (· ≤ ·)).length :: ((p.primes.sort (· ≤ ·)) ++
      (([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1, p.J]) ++ (p.factors.length ::
      (p.factors ++ ([p.A, p.Lambda] ++ ((coordsOf wt.I).length :: (coordsOf wt.I ++ witRest c p wt))))))))))

/-- The cell input's naturals in the shape the pass consumes them. -/
theorem cellN_split (c : Call) (p : Params) (wt : Wit c.n) :
    cellN c p wt = [c.n, kindTag c.kind] ++ (circN c.first ++ (circN c.second ++ (c.parity.length :: (c.parity ++
      callTail c p wt)))) := by
  simp [cellN, callN, paramsN, witN, witRest, callTail, List.append_assoc]

theorem ratN_length (q : ℚ) : (ratN q).length = 3 := by simp [ratN, intN]

/-- The call part of the pass: `n`, kind, the two circuits (gate blocks kept), the parity list (kept). -/
def parse1 : St VV MM :=
  .seq (skipK sN 2) (.seq (circP sG1 xG1 xm1) (.seq (circP sG2 xG2 xm2) (.seq (.op (.rdM sN xnp))
    (cpS sN sPa xnp))))

theorem parse1_spec (C : Ctx) (c : Call) (R : List ℕ) (b d : DS VV MM) (F : Fin MM → List ℕ)
    (h : PS b d ([c.n, kindTag c.kind] ++ (circN c.first ++ (circN c.second ++ (c.parity.length ::
      (c.parity ++ R))))) F) (hgS : d.env gS = 2 * c.n + 3)
    (h1 : (circN c.first).length < 2 ^ C.Wd) (h2 : (circN c.second).length < 2 ^ C.Wd)
    (h3 : c.parity.length < 2 ^ C.Wd) :
    Hs C parse1 d (7 * (circN c.first).length + 7 * (circN c.second).length + 7 * c.parity.length + 80) (fun e =>
      PS b e R (Function.update (Function.update (Function.update F sG1 (F sG1 ++ c.first.gates.flatMap gateN)) sG2
        (F sG2 ++ c.second.gates.flatMap gateN)) sPa (F sPa ++ c.parity)) ∧
      e.env xG1 = c.first.gates.length ∧ e.env xm1 = (c.first.gates.flatMap gateN).length ∧
      e.env xG2 = c.second.gates.length ∧ e.env xm2 = (c.second.gates.flatMap gateN).length ∧
      e.env xnp = c.parity.length ∧ Fr d e [j1, yv, yJ, xG1, xm1, xG2, xm2, xnp, xt]) := by
  refine Hs.mono (t := 2 * 2 + 1 + (7 * (circN c.first).length + 30 + (7 * (circN c.second).length + 30 +
    (1 + (c.parity.length * 7 + 4) + 1) + 1) + 1) + 1) ?_ (by omega) (fun _ h => h)
  refine Hs.seq (t1 := 2 * 2 + 1) (h.skipK 2 rfl) (fun d1 ⟨p1, f1⟩ => ?_)
  have g1 : d1.env gS = 2 * c.n + 3 := by rw [f1 gS (by decide), hgS]
  refine Hs.seq (t1 := 7 * (circN c.first).length + 30) (circP_spec C sG1 (by decide) xG1 xm1 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) c.first b d1 _ F p1 g1 h1)
    (fun d2 ⟨p2, a2, b2, f2⟩ => ?_)
  have g2 : d2.env gS = 2 * c.n + 3 := by rw [f2 gS (by decide), g1]
  refine Hs.seq (t1 := 7 * (circN c.second).length + 30) (circP_spec C sG2 (by decide) xG2 xm2 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) c.second b d2 _ _ p2 g2 h2)
    (fun d3 ⟨p3, a3, b3, f3⟩ => ?_)
  refine Hs.seq (t1 := 1) (p3.rdS xnp (by decide)) (fun d4 ⟨p4, v4, f4⟩ => ?_)
  refine Hs.mono (p4.cpS sPa (by decide) xnp (by decide) v4 h3) (by omega) ?_
  rintro e ⟨p5, f5⟩
  have hF : ∀ G : Fin MM → List ℕ, G = Function.update (Function.update F sG1 (F sG1 ++ c.first.gates.flatMap
      gateN)) sG2 ((Function.update F sG1 (F sG1 ++ c.first.gates.flatMap gateN)) sG2 ++
      c.second.gates.flatMap gateN) → Function.update G sPa (G sPa ++ c.parity) = Function.update (Function.update
      (Function.update F sG1 (F sG1 ++ c.first.gates.flatMap gateN)) sG2 (F sG2 ++ c.second.gates.flatMap gateN))
      sPa (F sPa ++ c.parity) := by
    rintro G rfl
    rw [Function.update_of_ne (show sG2 ≠ sG1 by decide)]
    congr 1
  refine ⟨by rw [← hF _ rfl]; exact p5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f5 xG1 (by decide), f4 xG1 (by decide), f3 xG1 (by decide), a2]
  · rw [f5 xm1 (by decide), f4 xm1 (by decide), f3 xm1 (by decide), b2]
  · rw [f5 xG2 (by decide), f4 xG2 (by decide), a3]
  · rw [f5 xm2 (by decide), f4 xm2 (by decide), b3]
  · rw [f5 xnp (by decide), v4]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hy
    rw [f5 y (by simp; exact ⟨h1, h2⟩), f4 y (by simp; exact h8), f3 y (by simp; exact ⟨h1, h2, h3, h6, h7, h9⟩),
      f2 y (by simp; exact ⟨h1, h2, h3, h4, h5, h9⟩), f1 y (by simp; exact h3)]

/-- The parameter and witness part of the pass: `k`, then the coordinates (kept). -/
def parse2 : St VV MM :=
  .seq (skipK sN 9) (.seq (.op (.rdM sN xk)) (.seq (skipK sN 5) (.seq (.op (.rdM sN xt)) (.seq (skipS sN xt)
    (.seq (skipK sN 11) (.seq (.op (.rdM sN xt)) (.seq (skipS sN xt) (.seq (skipK sN 2) (.seq (.op (.rdM sN xkk))
      (cpS sN sIn xkk))))))))))

theorem parse2_spec (C : Ctx) (A9 A5 prs A11 fs A2 crd R : List ℕ) (k : ℕ) (hA9 : A9.length = 9)
    (hA5 : A5.length = 5) (hA11 : A11.length = 11) (hA2 : A2.length = 2) (b d : DS VV MM) (F : Fin MM → List ℕ)
    (h : PS b d (A9 ++ (k :: (A5 ++ (prs.length :: (prs ++ (A11 ++ (fs.length :: (fs ++ (A2 ++ (crd.length ::
      (crd ++ R))))))))))) F)
    (h1 : prs.length < 2 ^ C.Wd) (h2 : fs.length < 2 ^ C.Wd) (h3 : crd.length < 2 ^ C.Wd) :
    Hs C parse2 d (5 * prs.length + 5 * fs.length + 7 * crd.length + 120) (fun e =>
      PS b e R (Function.update F sIn (F sIn ++ crd)) ∧ e.env xk = k ∧ e.env xkk = crd.length ∧
        Fr d e [j1, yv, yJ, xk, xt, xkk]) := by
  refine Hs.mono (t := 2 * 9 + 1 + (1 + (2 * 5 + 1 + (1 + ((prs.length * 5 + 4) + (2 * 11 + 1 + (1 + ((fs.length * 5
    + 4) + (2 * 2 + 1 + (1 + (crd.length * 7 + 4) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) ?_ (by omega)
    (fun _ h => h)
  refine Hs.seq (t1 := 2 * 9 + 1) (h.skipK 9 hA9) (fun d1 ⟨p1, f1⟩ => ?_)
  refine Hs.seq (t1 := 1) (p1.rdS xk (by decide)) (fun d2 ⟨p2, v2, f2⟩ => ?_)
  refine Hs.seq (t1 := 2 * 5 + 1) (p2.skipK 5 hA5) (fun d3 ⟨p3, f3⟩ => ?_)
  refine Hs.seq (t1 := 1) (p3.rdS xt (by decide)) (fun d4 ⟨p4, v4, f4⟩ => ?_)
  refine Hs.seq (t1 := prs.length * 5 + 4) (p4.skipS xt (by decide) v4 h1) (fun d5 ⟨p5, f5⟩ => ?_)
  refine Hs.seq (t1 := 2 * 11 + 1) (p5.skipK 11 hA11) (fun d6 ⟨p6, f6⟩ => ?_)
  refine Hs.seq (t1 := 1) (p6.rdS xt (by decide)) (fun d7 ⟨p7, v7, f7⟩ => ?_)
  refine Hs.seq (t1 := fs.length * 5 + 4) (p7.skipS xt (by decide) v7 h2) (fun d8 ⟨p8, f8⟩ => ?_)
  refine Hs.seq (t1 := 2 * 2 + 1) (p8.skipK 2 hA2) (fun d9 ⟨p9, f9⟩ => ?_)
  refine Hs.seq (t1 := 1) (p9.rdS xkk (by decide)) (fun d10 ⟨p10, v10, f10⟩ => ?_)
  refine Hs.mono (p10.cpS sIn (by decide) xkk (by decide) v10 h3) le_rfl ?_
  rintro e ⟨p11, f11⟩
  refine ⟨p11, ?_, ?_, ?_⟩
  · rw [f11 xk (by decide), f10 xk (by decide), f9 xk (by decide), f8 xk (by decide), f7 xk (by decide),
      f6 xk (by decide), f5 xk (by decide), f4 xk (by decide), f3 xk (by decide), v2]
  · rw [f11 xkk (by decide), v10]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hy
    rw [f11 y (by simp; exact ⟨h1, h2⟩), f10 y (by simp; exact h6), f9 y (by simp; exact h3),
      f8 y (by simp; exact ⟨h1, h3⟩), f7 y (by simp; exact h5), f6 y (by simp; exact h3),
      f5 y (by simp; exact ⟨h1, h3⟩), f4 y (by simp; exact h5), f3 y (by simp; exact h3), f2 y (by simp; exact h4),
      f1 y (by simp; exact h3)]

/-- **The pass.** -/
def parseP : St VV MM := .seq (.op (.rwM sN)) (.seq parse1 parse2)

/-- The stores after the pass. -/
def storesOf (F : Fin MM → List ℕ) (c : Call) (wt : Wit c.n) : Fin MM → List ℕ :=
  Function.update (Function.update (Function.update (Function.update F sG1 (F sG1 ++ c.first.gates.flatMap gateN))
    sG2 (F sG2 ++ c.second.gates.flatMap gateN)) sPa (F sPa ++ c.parity)) sIn (F sIn ++ coordsOf wt.I)

theorem parseP_spec (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (b : DS VV MM)
    (hN : b.ram sN = cellN c p wt) (hend : AtEnd b) (hrc : b.rc sN ≤ (cellN c p wt).length)
    (hgS : b.env gS = 2 * c.n + 3) (hbig : (cellN c p wt).length < 2 ^ C.Wd) :
    Hs C parseP b (16 * (cellN c p wt).length + 300) (fun e =>
      PS b e (witRest c p wt) (storesOf b.ram c wt) ∧
      e.env xG1 = c.first.gates.length ∧ e.env xm1 = (c.first.gates.flatMap gateN).length ∧
      e.env xG2 = c.second.gates.length ∧ e.env xm2 = (c.second.gates.flatMap gateN).length ∧
      e.env xnp = c.parity.length ∧ e.env xk = p.k ∧ e.env xkk = (coordsOf wt.I).length ∧ Fr b e parseT) := by
  have hsplit := cellN_split c p wt
  have hlen := congrArg List.length hsplit
  simp only [callTail, List.length_append, List.length_cons, List.length_nil] at hlen
  have p0 : PS b (b.rew sN) (cellN c p wt) b.ram :=
    ⟨by simp [DS.rew, hN], rfl, fun m hm => by simp [DS.rew, Function.update_of_ne hm]; exact hend m hm,
      rfl, ⟨rfl, rfl, rfl, rfl⟩, Fr.refl _ _⟩
  rw [hsplit] at p0
  unfold parseP
  refine Hs.mono (Hs.seq (t1 := (cellN c p wt).length + 1) (t2 := (7 * (circN c.first).length +
    7 * (circN c.second).length + 7 * c.parity.length + 80) + (5 * (p.primes.sort (· ≤ ·)).length +
    5 * p.factors.length + 7 * (coordsOf wt.I).length + 120) + 1) (Hs.mono (hs_rwM C sN b) (by omega) (fun _ h => h))
    (fun b1 hb1 => ?_)) (t' := 16 * (cellN c p wt).length + 300) ?_ (fun _ h => h)
  · subst hb1
    refine Hs.seq (parse1_spec C c (callTail c p wt) b (b.rew sN) b.ram p0
      (by simp [DS.rew]; exact hgS) (by omega) (by omega) (by omega)) (fun d1 ⟨q1, a1, a2, a3, a4, a5, f1⟩ => ?_)
    unfold callTail at q1
    refine Hs.mono (parse2_spec C _ _ _ _ _ _ _ (witRest c p wt) p.k (by simp [ratN_length]) rfl
      (by simp [ratN_length]) rfl b d1 _ q1 (by omega) (by omega) (by omega)) le_rfl ?_
    rintro e ⟨q2, v1, v2, f2⟩
    refine ⟨q2, ?_, ?_, ?_, ?_, ?_, v1, v2, ?_⟩
    · rw [f2 xG1 (by decide), a1]
    · rw [f2 xm1 (by decide), a2]
    · rw [f2 xG2 (by decide), a3]
    · rw [f2 xm2 (by decide), a4]
    · rw [f2 xnp (by decide), a5]
    · intro y hy
      simp only [parseT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hy
      rw [f2 y (by simp; exact ⟨h1, h2, h3, h9, h11, h10⟩), f1 y (by simp; exact ⟨h1, h2, h3, h4, h6, h5, h7, h8, h11⟩)]
      rfl
  · omega

end NearCubicGates.Close.CounterMachine.PrefixProg
