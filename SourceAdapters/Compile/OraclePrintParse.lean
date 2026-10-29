import SourceAdapters.Compile.OraclePrintPlan
import SourceAdapters.Compile.OraclePrintValues
import SourceAdapters.Proximity.PrefixSizes
import Proof.Gates.Cells.Arith

/-!
# The printer reads its request

proof of `thm:short-pcp-ours`; proof of `cor:short-pcp-clock`: the printer is one ordinary machine whose input is the request (data word, seed
length, clock); every number it uses is computed from that input. The entry word of the printing program is
`LengthPrefix.wrapped r.word = natWord |r.word| ++ frame data ++ frame 1^ell ++ frame 1^fuel`. `parse p` sets the
constants, skips the size header, copies the framed data word bit by bit into store `DSt`, counts the two unary
fields, and computes the template numbers `[width, clock, ell, |frame data|]` into the slots and the clock-wire count
`clockBits` into `CBR`. **`parse_spec`**: from the initial state the token machine is represented with the empty
wire map, no nodes and the request's data bits.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.RepairSource NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Compile (OracleCompilationRequest)
open NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires.RepairRepresentation (natWord)

set_option autoImplicit false

/-! ## Glue registers -/

def ELR : Fin VV := ⟨20, by decide⟩
def FUR : Fin VV := ⟨21, by decide⟩
def CBR : Fin VV := ⟨22, by decide⟩
def RDR : Fin VV := ⟨23, by decide⟩
def IR : Fin VV := ⟨24, by decide⟩
def OUTR : Fin VV := ⟨25, by decide⟩
def TGR : Fin VV := ⟨26, by decide⟩
def LFR : Fin VV := ⟨27, by decide⟩
def RTR : Fin VV := ⟨28, by decide⟩

@[simp] theorem ELR_val : ELR.val = 20 := rfl
@[simp] theorem FUR_val : FUR.val = 21 := rfl
@[simp] theorem CBR_val : CBR.val = 22 := rfl
@[simp] theorem RDR_val : RDR.val = 23 := rfl
@[simp] theorem IR_val : IR.val = 24 := rfl
@[simp] theorem OUTR_val : OUTR.val = 25 := rfl
@[simp] theorem TGR_val : TGR.val = 26 := rfl
@[simp] theorem LFR_val : LFR.val = 27 := rfl
@[simp] theorem RTR_val : RTR.val = 28 := rfl

/-- A frame for the parsing phase: registers outside `T`, all stores but `DSt`, and the output are kept. -/
structure PF (T : ℕ → Prop) (a b : DS VV MM) : Prop where
  env : ∀ y : Fin VV, ¬ T y.val → b.env y = a.env y
  ram : ∀ m : Fin MM, m ≠ DSt → b.ram m = a.ram m
  rc : ∀ m : Fin MM, m ≠ DSt → b.rc m = a.rc m
  out : b.out = a.out

theorem PF.refl (T : ℕ → Prop) (a : DS VV MM) : PF T a a := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem PF.trans {T : ℕ → Prop} {a b c : DS VV MM} (h1 : PF T a b) (h2 : PF T b c) : PF T a c :=
  ⟨fun y hy => (h2.env y hy).trans (h1.env y hy), fun m hm => (h2.ram m hm).trans (h1.ram m hm),
    fun m hm => (h2.rc m hm).trans (h1.rc m hm), h2.out.trans h1.out⟩

theorem PF.mono {T T' : ℕ → Prop} {a b : DS VV MM} (h : PF T a b) (hT : ∀ y, T y → T' y) : PF T' a b :=
  ⟨fun y hy => h.env y (fun h' => hy (hT _ h')), h.ram, h.rc, h.out⟩

theorem PF.cst {T : ℕ → Prop} {a b : DS VV MM} (h : PF T a b) (hT : ¬ T 0 ∧ ¬ T 1 ∧ ¬ T 2) (hc : Cst a) : Cst b :=
  ⟨by rw [h.env vZ hT.1, hc.z], by rw [h.env v1 hT.2.1, hc.one], by rw [h.env v2 hT.2.2, hc.two]⟩

theorem PF.set {T : ℕ → Prop} (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : T x.val) : PF T a (a.set x v) :=
  ⟨fun _ hy => DS.set_env_ne a v (neP hy hx), fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem PF.ofSame {T : ℕ → Prop} {a b : DS VV MM} (h : Same a b) (he : ∀ y : Fin VV, ¬ T y.val → b.env y = a.env y) :
    PF T a b :=
  ⟨he, fun _ _ => by rw [h.ram], fun _ _ => by rw [h.rc], h.out⟩

variable {C : Ctx}

/-! ## Reading one input bit into the data store -/

/-- Read one input bit into `x`, append it to `DSt`, count it in `DL`. -/
def rdW (x : Fin VV) : St VV MM := .seq (.op (.rdI x)) (.seq (.op (.wrM DSt x)) (.op (.inc DL)))

theorem take_succ_map (F : List Bool) (i : ℕ) (hi : i < F.length) :
    (F.take (i + 1)).map Bool.toNat = (F.take i).map Bool.toNat ++ [(F.getD i false).toNat] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem putAt_end (l : List ℕ) (v : ℕ) : putAt l l.length v = l ++ [v] := by
  unfold putAt; simp

theorem putAt_end' (l : List ℕ) (i v : ℕ) (h : l.length = i) : putAt l i v = l ++ [v] := by
  subst h; exact putAt_end l v

theorem rdW_spec (x : Fin VV) (hx : x.val = 105 ∨ x.val = 106) (F rest : List Bool) (p0 : ℕ)
    (hin : C.inp.drop p0 = F ++ rest) (s : DS VV MM) (i : ℕ) (hip : s.ip = p0 + i) (hi : i < F.length)
    (hD : s.ram DSt = (F.take i).map Bool.toNat) (hDc : s.rc DSt = i) (hDL : s.env DL = i)
    (hW : i + 1 < 2 ^ C.Wd) :
    Hs C (rdW x) s 5 (fun t => t.ram DSt = (F.take (i + 1)).map Bool.toNat ∧ t.rc DSt = i + 1 ∧ t.env DL = i + 1 ∧
      t.ip = p0 + (i + 1) ∧ t.env x = (F.getD i false).toNat ∧ PF (fun y => y = x.val ∨ y = 104) s t) := by
  have hlen : p0 + i < C.inp.length := by
    have := congrArg List.length hin
    rw [List.length_drop, List.length_append] at this
    omega
  have hxD : x ≠ DL := fun e => by rw [e] at hx; simp at hx
  have hbit : bitOf C.inp s.ip = (F.getD i false).toNat := by rw [hip]; exact bitOf_drop hin i hi
  refine Hs.mono (t := 1 + (1 + 1 + 1) + 1) (Hs.seq (hs_rdI C x s (by omega)) (fun b hb => ?_)) le_rfl
    (fun t ht => ht)
  subst hb
  have hlD : (F.take i).map Bool.toNat = ((F.take i).map Bool.toNat) := rfl
  have hle : ({ s.set x (bitOf C.inp s.ip) with ip := s.ip + 1 } : DS VV MM).rc DSt ≤
      (({ s.set x (bitOf C.inp s.ip) with ip := s.ip + 1 } : DS VV MM).ram DSt).length := by
    show s.rc DSt ≤ (s.ram DSt).length
    rw [hD, hDc]; simp; omega
  refine Hs.seq (hs_wrM C DSt x _ hle) (fun b hb => ?_)
  subst hb
  have hDL' : (({ s.set x (bitOf C.inp s.ip) with ip := s.ip + 1 } : DS VV MM).put DSt
      (({ s.set x (bitOf C.inp s.ip) with ip := s.ip + 1 } : DS VV MM).env x)).env DL = i := by
    show (s.set x _).env DL = i
    rw [DS.set_env_ne _ _ hxD.symm, hDL]
  refine Hs.mono (hs_inc C DL _ (by rw [hDL']; omega)) le_rfl ?_
  rintro t rfl
  have hiF : i ≤ F.length := hi.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [DS.set_ram, DS.put, Function.update_self]
    show putAt (s.ram DSt) (s.rc DSt) ((s.set x (bitOf C.inp s.ip)).env x) = _
    rw [hD, hDc, DS.set_env_self, hbit, take_succ_map F i hi]
    have : ((F.take i).map Bool.toNat).length = i := by simp; omega
    rw [putAt_end' _ _ _ this]
  · simp only [DS.set_rc, DS.put, Function.update_self]
    show s.rc DSt + 1 = i + 1
    rw [hDc]
  · rw [DS.set_env_self, hDL']
  · show s.ip + 1 = p0 + (i + 1)
    omega
  · rw [DS.set_env_ne _ _ hxD]
    show (s.set x (bitOf C.inp s.ip)).env x = _
    rw [DS.set_env_self, hbit]
  · refine ⟨fun y hy => ?_, fun m hm => ?_, fun m hm => ?_, rfl⟩
    · have h1 : y ≠ DL := fun e => hy (Or.inr (by rw [e]; rfl))
      have h2 : y ≠ x := fun e => hy (Or.inl (by rw [e]))
      rw [DS.set_env_ne _ _ h1]
      show (s.set x _).env y = s.env y
      rw [DS.set_env_ne _ _ h2]
    · simp only [DS.set_ram, DS.put]
      exact Function.update_of_ne hm _ _
    · simp only [DS.set_rc, DS.put]
      exact Function.update_of_ne hm _ _

/-! ## Copying a framed word -/

/-- Copy `frame l` from the input to `DSt`, bit by bit (markers included). -/
def copyFr : St VV MM := .seq (rdW XA) (.loop (.eq XA v1) (.seq (rdW XB) (rdW XA)))

def CopyT (y : ℕ) : Prop := y = 105 ∨ y = 106 ∨ y = 104

theorem copyFr_spec (a : DS VV MM) (hc : Cst a) (l rest : List Bool)
    (hin : C.inp.drop a.ip = RepairOrdinary.frame l ++ rest) (hD : a.ram DSt = []) (hDc : a.rc DSt = 0)
    (hDL : a.env DL = 0) (hW : 2 * l.length + 2 < 2 ^ C.Wd) :
    Hs C copyFr a (13 * l.length + 8) (fun b => b.ram DSt = (RepairOrdinary.frame l).map Bool.toNat ∧
      b.rc DSt = (RepairOrdinary.frame l).length ∧ b.env DL = (RepairOrdinary.frame l).length ∧
      b.ip = a.ip + (RepairOrdinary.frame l).length ∧ PF CopyT a b) := by
  set F := RepairOrdinary.frame l with hF
  have hFl : F.length = 2 * l.length + 1 := frame_length' l
  let I : ℕ → DS VV MM → Prop := fun k x => x.ram DSt = (F.take (2 * k + 1)).map Bool.toNat ∧
    x.rc DSt = 2 * k + 1 ∧ x.env DL = 2 * k + 1 ∧ x.ip = a.ip + (2 * k + 1) ∧
    x.env XA = (F.getD (2 * k) false).toNat ∧ PF CopyT a x
  have hfirst := rdW_spec (C := C) XA (Or.inl rfl) F rest a.ip hin a 0 (by omega) (by omega)
    (by rw [hD]; simp) hDc hDL (by omega)
  refine Hs.mono (t := 5 + (l.length * (11 + 2) + 2) + 1) (Hs.seq hfirst (fun b hb => ?_)) (by omega)
    (fun t ht => ht)
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have hI0 : I 0 b := ⟨b1, b2, b3, b4, b5, b6.mono (fun y hy => by unfold CopyT; simp at hy; omega)⟩
  have hstep : ∀ k < l.length, ∀ x, I k x → Cnd.eval x (.eq XA v1) = true ∧
      Hs C (.seq (rdW XB) (rdW XA)) x 11 (I (k + 1)) := by
    intro k hk x ⟨x1, x2, x3, x4, x5, x6⟩
    have hcx : Cst x := x6.cst (by unfold CopyT; omega) hc
    have hev : F.getD (2 * k) false = true := by rw [hF, frame_getD_even]; simp [hk]
    refine ⟨by show decide (x.env XA = x.env v1) = true; rw [x5, hcx.one, hev]; rfl, ?_⟩
    have s1 := rdW_spec (C := C) XB (Or.inr rfl) F rest a.ip hin x (2 * k + 1) x4 (by omega) x1 x2 x3 (by omega)
    refine Hs.mono (t := 5 + 5 + 1) (Hs.seq s1 (fun y hy => ?_)) le_rfl (fun t ht => ht)
    obtain ⟨y1, y2, y3, y4, _, y6⟩ := hy
    refine Hs.mono (rdW_spec (C := C) XA (Or.inl rfl) F rest a.ip hin y (2 * k + 1 + 1) y4 (by omega) y1 y2 y3
      (by omega)) le_rfl ?_
    rintro t ⟨t1, t2, t3, t4, t5, t6⟩
    refine ⟨by rw [t1]; ring_nf, by rw [t2]; ring, by rw [t3]; ring, by rw [t4]; ring, by rw [t5]; ring_nf, ?_⟩
    exact x6.trans ((y6.mono (fun z hz => by unfold CopyT; simp at hz; omega)).trans
      (t6.mono (fun z hz => by unfold CopyT; simp at hz; omega)))
  have hstop : ∀ x, I l.length x → Cnd.eval x (.eq XA v1) = false := by
    intro x ⟨_, _, _, _, x5, x6⟩
    have hcx : Cst x := x6.cst (by unfold CopyT; omega) hc
    have hev : F.getD (2 * l.length) false = false := by rw [hF, frame_getD_even]; simp
    show decide (x.env XA = x.env v1) = false
    rw [x5, hcx.one, hev]; rfl
  refine Hs.mono (Hs.loopN (show Cnd.wf (Cnd.eq XA v1) from (by decide : XA ≠ v1)) I l.length 11 hstep hstop b hI0) le_rfl ?_
  rintro t ⟨t1, t2, t3, t4, _, t6⟩
  have htake : F.take (2 * l.length + 1) = F := List.take_of_length_le (by omega)
  exact ⟨by rw [t1, htake], by rw [t2, hFl], by rw [t3, hFl], by rw [t4, hFl], t6⟩

/-! ## Counting a unary field -/

/-- Count the ones of a framed unary word into `x` (from `0`). -/
def cntFr (x : Fin VV) : St VV MM :=
  .seq (.op (.rdI XA)) (.loop (.eq XA v1) (.seq (.op (.rdI XB)) (.seq (.op (.inc x)) (.op (.rdI XA)))))

theorem frame_replicate_even (m k : ℕ) :
    (RepairOrdinary.frame (List.replicate m true)).getD (2 * k) false = decide (k < m) := by
  rw [frame_getD_even]; simp

/-- Reading one input bit changes only `x` and the input position. -/
theorem rdI_frame (x : Fin VV) (s : DS VV MM) (v : ℕ) (T : ℕ → Prop) (hx : T x.val) :
    PF T s ({ s.set x v with ip := s.ip + 1 } : DS VV MM) ∧
      ({ s.set x v with ip := s.ip + 1 } : DS VV MM).ram DSt = s.ram DSt ∧
      ({ s.set x v with ip := s.ip + 1 } : DS VV MM).rc DSt = s.rc DSt :=
  ⟨⟨fun _ hy => DS.set_env_ne s v (neP hy hx), fun _ _ => rfl, fun _ _ => rfl, rfl⟩, rfl, rfl⟩

def CntT (x : ℕ) (y : ℕ) : Prop := y = x ∨ y = 105 ∨ y = 106

theorem cntFr_spec (x : Fin VV) (hx : x.val = 20 ∨ x.val = 21) (a : DS VV MM) (hc : Cst a) (m : ℕ)
    (rest : List Bool) (hin : C.inp.drop a.ip = RepairOrdinary.frame (List.replicate m true) ++ rest)
    (h0 : a.env x = 0) (hW : m + 1 < 2 ^ C.Wd) :
    Hs C (cntFr x) a (7 * m + 4) (fun b => b.env x = m ∧ b.ip = a.ip + (2 * m + 1) ∧ PF (CntT x.val) a b ∧
      b.ram DSt = a.ram DSt ∧ b.rc DSt = a.rc DSt) := by
  set F := RepairOrdinary.frame (List.replicate m true) with hF
  have hFl : F.length = 2 * m + 1 := by rw [hF, frame_length']; simp
  have hlen : a.ip + F.length ≤ C.inp.length := by
    have := congrArg List.length hin
    rw [List.length_drop, List.length_append] at this
    omega
  have hbit : ∀ j < F.length, bitOf C.inp (a.ip + j) = (F.getD j false).toNat := fun j hj => bitOf_drop hin j hj
  have hTx : CntT x.val x.val := Or.inl rfl
  have hTA : CntT x.val 105 := Or.inr (Or.inl rfl)
  have hTB : CntT x.val 106 := Or.inr (Or.inr rfl)
  have hxA : x ≠ XA := fun e => by rw [e] at hx; simp at hx
  have hxB : x ≠ XB := fun e => by rw [e] at hx; simp at hx
  refine Hs.mono (t := 1 + (m * (5 + 2) + 2) + 1) (Hs.seq (hs_rdI C XA a (by omega)) (fun b hb => ?_)) (by omega)
    (fun t ht => ht)
  subst hb
  let I : ℕ → DS VV MM → Prop := fun k y => y.env x = k ∧ y.ip = a.ip + (2 * k + 1) ∧
    y.env XA = (decide (k < m)).toNat ∧ PF (CntT x.val) a y ∧ y.ram DSt = a.ram DSt ∧ y.rc DSt = a.rc DSt
  obtain ⟨f1, f2, f3⟩ := rdI_frame XA a (bitOf C.inp a.ip) (CntT x.val) hTA
  have hI0 : I 0 ({ a.set XA (bitOf C.inp a.ip) with ip := a.ip + 1 } : DS VV MM) := by
    refine ⟨?_, rfl, ?_, f1, f2, f3⟩
    · show (a.set XA _).env x = 0
      rw [DS.set_env_ne _ _ hxA, h0]
    · show (a.set XA (bitOf C.inp a.ip)).env XA = _
      rw [DS.set_env_self]
      have e1 := hbit 0 (by omega)
      have e2 := frame_replicate_even m 0
      rw [Nat.add_zero] at e1
      rw [Nat.mul_zero] at e2
      rw [e1, e2]
  have hstep : ∀ k < m, ∀ y, I k y → Cnd.eval y (.eq XA v1) = true ∧
      Hs C (.seq (.op (.rdI XB)) (.seq (.op (.inc x)) (.op (.rdI XA)))) y 5 (I (k + 1)) := by
    intro k hk y ⟨y1, y2, y3, y4, y5, y6⟩
    have hcy : Cst y := y4.cst (by unfold CntT; omega) hc
    refine ⟨by show decide (y.env XA = y.env v1) = true; rw [y3, hcy.one]; simp [hk], ?_⟩
    refine Hs.mono (t := 1 + (1 + 1 + 1) + 1) (Hs.seq (hs_rdI C XB y (by omega)) (fun b hb => ?_)) le_rfl
      (fun t ht => ht)
    subst hb
    obtain ⟨g1, g2, g3⟩ := rdI_frame XB y (bitOf C.inp y.ip) (CntT x.val) hTB
    set y' := ({ y.set XB (bitOf C.inp y.ip) with ip := y.ip + 1 } : DS VV MM) with hy'
    have hy'x : y'.env x = k := by
      show (y.set XB _).env x = k
      rw [DS.set_env_ne _ _ hxB, y1]
    refine Hs.seq (hs_inc C x y' (by rw [hy'x]; omega)) (fun b hb => ?_)
    subst hb
    have hip2 : (y'.set x (y'.env x + 1)).ip = a.ip + (2 * k + 1) + 1 := by
      show y.ip + 1 = _
      rw [y2]
    refine Hs.mono (hs_rdI C XA _ (by rw [hip2]; omega)) le_rfl ?_
    rintro t rfl
    obtain ⟨h1, h2, h3⟩ := rdI_frame XA (y'.set x (y'.env x + 1)) (bitOf C.inp (y'.set x (y'.env x + 1)).ip)
      (CntT x.val) hTA
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show ((y'.set x (y'.env x + 1)).set XA _).env x = k + 1
      rw [DS.set_env_ne _ _ hxA, DS.set_env_self, hy'x]
    · show (y'.set x (y'.env x + 1)).ip + 1 = _
      rw [hip2]; ring
    · show ((y'.set x (y'.env x + 1)).set XA _).env XA = _
      rw [DS.set_env_self, hip2, show a.ip + (2 * k + 1) + 1 = a.ip + 2 * (k + 1) by ring,
        hbit _ (by omega), frame_replicate_even, DS.set_env_self]
    · exact y4.trans (g1.trans ((PF.set y' x _ hTx).trans h1))
    · rw [h2]; exact g2.trans y5
    · rw [h3]; exact g3.trans y6
  have hstop : ∀ y, I m y → Cnd.eval y (.eq XA v1) = false := by
    intro y ⟨_, _, y3, y4, _, _⟩
    have hcy : Cst y := y4.cst (by unfold CntT; omega) hc
    show decide (y.env XA = y.env v1) = false
    rw [y3, hcy.one]; simp
  refine Hs.mono (Hs.loopN (show Cnd.wf (Cnd.eq XA v1) from (by decide : XA ≠ v1)) I m 5 hstep hstop _ hI0) le_rfl ?_
  rintro t ⟨t1, t2, _, t4, t5, t6⟩
  exact ⟨t1, t2, t4, t5, t6⟩

/-! ## The whole parse -/

/-- `v1 := 1`, `v2 := 2`. -/
def consts : St VV MM := .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.op (.inc v2)))

/-- `2·|frame data| + 4·ell + fuel + 4` over `[0, fuel, ell, |frame data|]` (`= requestWidth`). -/
def widthT : Tm := .add (.mul (.k 2) (.v 3)) (.add (.mul (.k 4) (.v 2)) (.add (.v 1) (.k 4)))

/-- The clock-wire count over the template numbers (`= clockBits`). -/
def cbT (t s : ℕ) : Tm := .add (.add (.k s) (.add (.mul (.k t) (.v 0)) (.mul (.k t) (.v 0))))
    (.add (.mul (.k t) (.add (.v 0) (.k 1))) (.add (.v 1) (.k 1)))

/-- The slots and `CBR`. -/
def setEnv (t s : ℕ) : St VV MM :=
  .seq (.op (.copy (Sl 1) FUR)) (.seq (.op (.copy (Sl 2) ELR)) (.seq (.op (.copy (Sl 3) DL))
    (.seq (compT widthT 0) (.seq (.op (.copy (Sl 0) (Rg 0))) (.seq (compT (cbT t s) 0) (.op (.copy CBR (Rg 0))))))))

/-- **Read the request.** -/
def parse (t s : ℕ) : St VV MM :=
  .seq consts (.seq rdNatI (.seq copyFr (.seq (cntFr ELR) (.seq (cntFr FUR) (setEnv t s)))))

/-- The glue facts kept through the whole printing run. -/
structure Gl (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) (a : DS VV MM) : Prop where
  slots : ∀ j < 16, a.env (Sl j) = (reqEnv r).getD j 0
  ell : a.env ELR = r.ell
  fuel : a.env FUR = r.fuel
  cb : a.env CBR = clockBits p (requestWidth r) r.fuel
  out : a.out = []

/-- The value scale of the parse. -/
def parseX (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) : ℕ :=
  8 * r.measure + 2 * p.base.tapeCount + p.base.stateCount + 8

/-- The parse cost. -/
def parseCost (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) : ℕ :=
  100 * r.measure + 30 * (p.base.tapeCount + p.base.stateCount) + 600

theorem drop_of_eq {L A B : List Bool} (h : L = A ++ B) (n : ℕ) (hn : n = A.length) : L.drop n = B := by
  subst h; subst hn; exact List.drop_left

theorem frameData_length (r : OracleCompilationRequest) :
    (RepairOrdinary.frame r.data).length = 2 * r.data.length + 1 := frame_length' _

theorem reqEnv_le (r : OracleCompilationRequest) : ∀ j, (reqEnv r).getD j 0 ≤ 6 * r.measure := by
  intro j
  have hm : 1 ≤ r.measure := by unfold OracleCompilationRequest.measure; omega
  have h0 : requestWidth r ≤ 6 * r.measure := requestWidth_bound r
  have hf : (RepairOrdinary.frame r.data).length ≤ 6 * r.measure := by
    rw [frameData_length]; unfold OracleCompilationRequest.measure; omega
  have h1 : r.fuel ≤ 6 * r.measure := by unfold OracleCompilationRequest.measure; omega
  have h2 : r.ell ≤ 6 * r.measure := by unfold OracleCompilationRequest.measure; omega
  match j with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact hf
  | n + 4 => simp [reqEnv]

theorem cbT_eval (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) :
    (cbT p.base.tapeCount p.base.stateCount).eval (reqEnv r) = clockBits p (requestWidth r) r.fuel := by
  simp [cbT, Tm.eval, reqEnv, clockBits, windowBits]

theorem consts_spec (hW : 3 < 2 ^ C.Wd) :
    Hs C consts (a0 : DS VV MM) 5 (fun b => Cst b ∧ b.ip = 0 ∧ (∀ m, b.ram m = []) ∧ (∀ m, b.rc m = 0) ∧
      b.out = [] ∧ ∀ y : Fin VV, 3 ≤ y.val → b.env y = 0) := by
  refine Hs.mono (t := 1 + (1 + 1 + 1) + 1)
    (Hs.seq (hs_inc C v1 a0 (by show (0:ℕ) + 1 < 2 ^ C.Wd; omega)) (fun b hb => ?_)) le_rfl (fun x hx => hx)
  subst hb
  refine Hs.seq (hs_inc C v2 _ (by rw [DS.set_env_ne _ _ (by decide)]; show (0:ℕ) + 1 < 2 ^ C.Wd; omega))
    (fun b hb => ?_)
  subst hb
  refine Hs.mono (hs_inc C v2 _ (by
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide)]; show (0:ℕ) + 1 + 1 < 2 ^ C.Wd; omega)) le_rfl ?_
  rintro b rfl
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ => rfl, rfl, fun y hy => ?_⟩
  rw [DS.set_env_ne _ _ (ne_of_val (by simp [v2]; omega)), DS.set_env_ne _ _ (ne_of_val (by simp [v2]; omega)),
    DS.set_env_ne _ _ (ne_of_val (by simp [v1]; omega))]
  rfl

theorem parse_spec (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (hinp : C.inp = Proximity.LengthPrefix.wrapped r.word) (B : ℕ) (hB : 2 * B + 2 ≤ 2 ^ C.Wd)
    (hX : parseX p r ^ 20 ≤ B) (hnb : natBitLength r.word.length + 2 ≤ C.Wd) :
    Hs C (parse p.base.tapeCount p.base.stateCount) a0 (parseCost p r)
      (fun b => Rep [] (reqD r) (⟨0, [], []⟩ : PS r.ell r.ell) b ∧ Gl p r b ∧ b.rc W2 = 0) := by
  set t := p.base.tapeCount
  set s := p.base.stateCount
  set m := r.measure with hmdef
  have hm : 1 ≤ m := by rw [hmdef]; unfold OracleCompilationRequest.measure; omega
  have hX1 : 1 ≤ parseX p r := by unfold parseX; omega
  have hXB : parseX p r ≤ B := by
    calc parseX p r = parseX p r ^ 1 := (pow_one _).symm
      _ ≤ parseX p r ^ 20 := Nat.pow_le_pow_right hX1 (by omega)
      _ ≤ B := hX
  have hmB : 8 * m + 8 ≤ B := by unfold parseX at hXB; omega
  have hdl : r.data.length + r.ell + r.fuel + 1 = m := rfl
  have hwl : r.word.length = 2 * m + 1 := by
    simp only [OracleCompilationRequest.word, List.length_append, frame_length', List.length_replicate]; omega
  have hnbl : natBitLength r.word.length ≤ 2 * m + 2 := by
    have := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le r.word.length; omega
  -- the input
  set nw := natWord r.word.length
  set fd := RepairOrdinary.frame r.data
  set fe := RepairOrdinary.frame (List.replicate r.ell true)
  set ff := RepairOrdinary.frame (List.replicate r.fuel true)
  have hfe : fe.length = 2 * r.ell + 1 := by rw [frame_length']; simp
  have hfd : fd.length = 2 * r.data.length + 1 := frame_length' _
  have hI : C.inp = nw ++ (fd ++ (fe ++ ff)) := by
    rw [hinp]
    show nw ++ r.word = _
    congr 1
    simp only [OracleCompilationRequest.word, List.append_assoc]
    rfl
  -- consts
  have hcost : 5 + ((30 * natBitLength r.word.length + 30) + ((13 * r.data.length + 8) +
      ((7 * r.ell + 4) + ((7 * r.fuel + 4) + (1 + (1 + (1 + (widthT.cost + (1 + ((cbT t s).cost + 1 + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤ parseCost p r := by
    simp only [widthT, cbT, Tm.cost, parseCost]
    omega
  refine Hs.mono (Hs.seq (consts_spec (by omega)) (fun b hb0 => ?_)) hcost (fun x hx => hx)
  obtain ⟨hcb, hipb, hramb, hrcb, houtb, henvb⟩ := hb0
  -- header
  have hcw : C.inp.drop b.ip = natWord r.word.length ++ r.word := by rw [hipb, List.drop_zero, hinp]; rfl
  refine Hs.seq (rdNatI_spec b hcb r.word.length r.word hcw hnb) (fun b2 ⟨_, _, hip2, hst2, hfr2⟩ => ?_)
  simp only [Prod.mk.injEq] at hst2
  obtain ⟨ho2, hr2, hc2, -, -, -⟩ := hst2
  have hcb2 : Cst b2 := cst_fr hcb hfr2
  have hnot : ∀ y : Fin VV, 9 ≤ y.val → y ∉ rdNatT := fun y hy hm => by
    simp only [rdNatT, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> (subst h; simp [t0, t1, t2, t3, t4, vJ] at hy)
  have he2 : ∀ y : Fin VV, 9 ≤ y.val → b2.env y = 0 := fun y hy => by rw [hfr2 y (hnot y hy), henvb y (by omega)]
  -- data frame
  have hin3 : C.inp.drop b2.ip = fd ++ (fe ++ ff) := by
    rw [hip2, hipb, Nat.zero_add]; exact drop_of_eq hI _ rfl
  refine Hs.seq (copyFr_spec b2 hcb2 r.data (fe ++ ff) hin3 (by rw [hr2, hramb]) (by rw [hc2, hrcb])
    (he2 DL (by simp)) (by omega)) (fun b3 ⟨d1, d2, d3, d4, d5⟩ => ?_)
  have hcb3 : Cst b3 := d5.cst (by unfold CopyT; omega) hcb2
  -- seed length
  have hin4 : C.inp.drop b3.ip = fe ++ ff := by
    have : b3.ip = (nw ++ fd).length := by rw [d4, hip2, hipb, Nat.zero_add, List.length_append]
    rw [this]
    exact drop_of_eq (by rw [hI, List.append_assoc]) _ rfl
  refine Hs.seq (cntFr_spec ELR (Or.inl rfl) b3 hcb3 r.ell ff hin4
    (by rw [d5.env ELR (by unfold CopyT; simp), he2 ELR (by simp)]) (by omega)) (fun b4 ⟨e1, e2, e3, e4, e5⟩ => ?_)
  have hcb4 : Cst b4 := e3.cst (by unfold CntT; simp) hcb3
  -- clock
  have hin5 : C.inp.drop b4.ip = ff ++ [] := by
    have : b4.ip = (nw ++ fd ++ fe).length := by
      rw [e2, d4, hip2, hipb, Nat.zero_add, List.length_append, List.length_append, hfe]
    rw [this]
    exact drop_of_eq (by rw [hI]; simp only [List.append_assoc, List.append_nil]) _ rfl
  refine Hs.seq (cntFr_spec FUR (Or.inr rfl) b4 hcb4 r.fuel [] hin5
    (by rw [e3.env FUR (by unfold CntT; simp), d5.env FUR (by unfold CopyT; simp), he2 FUR (by simp)])
    (by omega)) (fun b5 ⟨f1, f2, f3, f4, f5⟩ => ?_)
  have hcb5 : Cst b5 := f3.cst (by unfold CntT; simp) hcb4
  -- the facts after reading
  have g1 : b5.env ELR = r.ell := by rw [f3.env ELR (by unfold CntT; simp), e1]
  have g2 : b5.env FUR = r.fuel := f1
  have g3 : b5.env DL = fd.length := by
    rw [f3.env DL (by unfold CntT; simp), e3.env DL (by unfold CntT; simp), d3]
  have g4 : ∀ y : Fin VV, 9 ≤ y.val → ¬ (y.val = 20 ∨ y.val = 21 ∨ (104 ≤ y.val ∧ y.val ≤ 106)) →
      b5.env y = 0 := fun y hy hy' => by
    rw [f3.env y (by unfold CntT; simp at hy' ⊢; omega), e3.env y (by unfold CntT; simp at hy' ⊢; omega),
      d5.env y (by unfold CopyT; omega), he2 y hy]
  have g5 : ∀ m : Fin MM, m ≠ DSt → b5.ram m = [] ∧ b5.rc m = 0 := fun m hm =>
    ⟨by rw [f3.ram m hm, e3.ram m hm, d5.ram m hm, hr2, hramb],
      by rw [f3.rc m hm, e3.rc m hm, d5.rc m hm, hc2, hrcb]⟩
  have g6 : b5.ram DSt = fd.map Bool.toNat ∧ b5.rc DSt = fd.length := by
    rw [f4, e4, f5, e5]; exact ⟨d1, d2⟩
  have g7 : b5.out = [] := by rw [f3.out, e3.out, d5.out, ho2, houtb]
  -- the slots
  refine Hs.seq (hs_copy C (Sl 1) FUR b5 (by decide)) (fun b6 hb6 => ?_)
  subst hb6
  refine Hs.seq (hs_copy C (Sl 2) ELR _ (by decide)) (fun b7 hb7 => ?_)
  subst hb7
  refine Hs.seq (hs_copy C (Sl 3) DL _ (by decide)) (fun b8 hb8 => ?_)
  subst hb8
  set c8 := ((b5.set (Sl 1) (b5.env FUR)).set (Sl 2) ((b5.set (Sl 1) (b5.env FUR)).env ELR)).set (Sl 3)
    (((b5.set (Sl 1) (b5.env FUR)).set (Sl 2) ((b5.set (Sl 1) (b5.env FUR)).env ELR)).env DL) with hc8
  have hc8e : ∀ y : Fin VV, y ≠ Sl 1 → y ≠ Sl 2 → y ≠ Sl 3 → c8.env y = b5.env y := fun y h1 h2 h3 => by
    rw [hc8, DS.set_env_ne _ _ h3, DS.set_env_ne _ _ h2, DS.set_env_ne _ _ h1]
  have hS1 : c8.env (Sl 1) = r.fuel := by
    rw [hc8, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), DS.set_env_self, g2]
  have hS2 : c8.env (Sl 2) = r.ell := by
    rw [hc8, DS.set_env_ne _ _ (by decide), DS.set_env_self, DS.set_env_ne _ _ (by decide), g1]
  have hS3 : c8.env (Sl 3) = fd.length := by
    rw [hc8, DS.set_env_self, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), g3]
  have hcc8 : Cst c8 := ⟨by rw [hc8e vZ (by decide) (by decide) (by decide), hcb5.z],
    by rw [hc8e v1 (by decide) (by decide) (by decide), hcb5.one],
    by rw [hc8e v2 (by decide) (by decide) (by decide), hcb5.two]⟩
  set env0 : List ℕ := [0, r.fuel, r.ell, fd.length] with henv0
  have hsl0 : ∀ j < 16, c8.env (Sl j) = env0.getD j 0 := by
    intro j hj
    match j, hj with
    | 0, _ => rw [hc8e _ (by decide) (by decide) (by decide), g4 _ (by decide) (by decide)]; rfl
    | 1, _ => rw [hS1]; rfl
    | 2, _ => rw [hS2]; rfl
    | 3, _ => rw [hS3]; rfl
    | k + 4, hk =>
        have hv : (Sl (k + 4)).val = 64 + (k + 4) := Sl_val hk
        rw [hc8e _ (ne_of_val (by rw [hv, Sl_val (by omega : 1 < 16)]; omega))
          (ne_of_val (by rw [hv, Sl_val (by omega : 2 < 16)]; omega))
          (ne_of_val (by rw [hv, Sl_val (by omega : 3 < 16)]; omega)), g4 _ (by rw [hv]; omega) (by rw [hv]; omega)]
        simp [henv0]
  have hM0 : ∀ j, env0.getD j 0 ≤ 2 * m + 1 := by
    intro j
    match j with
    | 0 => simp [henv0]
    | 1 => simp [henv0]; omega
    | 2 => simp [henv0]; omega
    | 3 => simp [henv0, hfd]; omega
    | n + 4 => simp [henv0]
  have hok0 : widthT.okV B env0 := Tm.okV_of_le env0 (2 * m + 1) 4 hM0 widthT B (by simp [widthT, Tm.kmax])
    ((Nat.pow_le_pow_left (show 2 * m + 1 + 4 + 2 ≤ parseX p r by unfold parseX; omega) _).trans
      ((Nat.pow_le_pow_right hX1 (by simp [widthT, Tm.sz])).trans hX))
  refine Hs.seq (compT_spec B hB (by omega) env0 (by simp [henv0]) widthT 0 c8 hcc8 (by simp [widthT, Tm.need])
    hsl0 hok0) (fun b9 ⟨w1, w2⟩ => ?_)
  have hwv : widthT.eval env0 = requestWidth r := by
    simp only [widthT, Tm.eval, henv0, hfd]; simp [requestWidth]; ring
  rw [hwv] at w1
  refine Hs.seq (hs_copy C (Sl 0) (Rg 0) b9 (by decide)) (fun b10 hb10 => ?_)
  subst hb10
  have hcb9 : Cst b9 := w2.cst hcc8
  have he9 : ∀ y : Fin VV, (y.val < 40 ∨ 56 ≤ y.val) → b9.env y = c8.env y := fun y hy => w2.env y (notEv hy)
  have hsl10 : ∀ j < 16, (b9.set (Sl 0) (b9.env (Rg 0))).env (Sl j) = (reqEnv r).getD j 0 := by
    intro j hj
    match j, hj with
    | 0, _ => rw [DS.set_env_self, w1]; rfl
    | k + 1, hk =>
        have hv : (Sl (k + 1)).val = 64 + (k + 1) := Sl_val hk
        rw [DS.set_env_ne _ _ (ne_of_val (by rw [hv, Sl_val (by omega : 0 < 16)]; omega)), he9 _ (by rw [hv]; omega),
          hsl0 _ hk]
        match k with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
        | n + 3 => simp [henv0, reqEnv]
  have hcc10 : Cst (b9.set (Sl 0) (b9.env (Rg 0))) :=
    ⟨by rw [DS.set_env_ne _ _ (by decide), hcb9.z], by rw [DS.set_env_ne _ _ (by decide), hcb9.one],
      by rw [DS.set_env_ne _ _ (by decide), hcb9.two]⟩
  have hok1 : (cbT t s).okV B (reqEnv r) := Tm.okV_of_le (reqEnv r) (6 * m) (t + s + 1) (reqEnv_le r) (cbT t s)
    B (by simp [cbT, Tm.kmax]; omega)
    ((Nat.pow_le_pow_left (show 6 * m + (t + s + 1) + 2 ≤ parseX p r by unfold parseX; omega) _).trans
      ((Nat.pow_le_pow_right hX1 (by simp [cbT, Tm.sz])).trans hX))
  refine Hs.seq (compT_spec B hB (by omega) (reqEnv r) (by simp) (cbT t s) 0 _ hcc10 (by simp [cbT, Tm.need])
    hsl10 hok1) (fun b11 ⟨c1, c2⟩ => ?_)
  rw [cbT_eval] at c1
  refine Hs.mono (hs_copy C CBR (Rg 0) b11 (by decide)) le_rfl ?_
  rintro b12 rfl
  -- the final facts
  have hcb11 : Cst b11 := c2.cst hcc10
  have he11 : ∀ y : Fin VV, (y.val < 40 ∨ 56 ≤ y.val) → y ≠ Sl 0 → b11.env y = c8.env y := fun y hy h0 => by
    rw [c2.env y (notEv hy), DS.set_env_ne _ _ h0, he9 y hy]
  have hfin : ∀ y : Fin VV, (y.val < 40 ∨ 56 ≤ y.val) → y ≠ Sl 0 → y ≠ CBR →
      (b11.set CBR (b11.env (Rg 0))).env y = c8.env y := fun y hy h0 h1 => by
    rw [DS.set_env_ne _ _ h1, he11 y hy h0]
  have hsame : Same b5 b11 := by
    have s1 : Same b5 c8 := (Same.set _ _ _).trans ((Same.set _ _ _).trans (Same.set _ _ _))
    exact s1.trans (w2.same.trans ((Same.set _ _ _).trans c2.same))
  set fb := b11.set CBR (b11.env (Rg 0)) with hfb
  have hz : ∀ y : Fin VV, 9 ≤ y.val → (y.val < 40 ∨ 56 ≤ y.val) → ¬ (64 ≤ y.val ∧ y.val < 68) →
      ¬ (y.val = 20 ∨ y.val = 21 ∨ y.val = 22 ∨ (104 ≤ y.val ∧ y.val ≤ 106)) → fb.env y = 0 := fun y h9 hy hs hn => by
    rw [hfin y hy (ne_of_val (by simp [Sl_val]; omega)) (ne_of_val (by simp; omega)),
      hc8e y (ne_of_val (by simp [Sl_val]; omega)) (ne_of_val (by simp [Sl_val]; omega))
        (ne_of_val (by simp [Sl_val]; omega)), g4 y h9 (by omega)]
  have hcfb : Cst fb := ⟨by rw [hfb, DS.set_env_ne _ _ (by decide), hcb11.z],
    by rw [hfb, DS.set_env_ne _ _ (by decide), hcb11.one], by rw [hfb, DS.set_env_ne _ _ (by decide), hcb11.two]⟩
  have hfbram : ∀ m : Fin MM, fb.ram m = b5.ram m := fun m => by rw [hfb, DS.set_ram, hsame.ram]
  have hfbrc : ∀ m : Fin MM, fb.rc m = b5.rc m := fun m => by rw [hfb, DS.set_rc, hsame.rc]
  refine ⟨⟨⟨hcfb, hz CNT (by simp) (by simp) (by simp) (by simp), by rw [hfbram, (g5 NS (by decide)).1]; rfl,
      by rw [hfbrc, hfbram, (g5 NS (by decide)).1, (g5 NS (by decide)).2]; rfl,
      by rw [hfbram, (g5 WM (by decide)).1], hz WL (by simp) (by simp) (by simp) (by simp),
      by rw [hfbrc, (g5 WM (by decide)).2]; simp, by rw [hfbram, g6.1]; rfl,
      by rw [hfin DL (by simp) (by decide) (by decide), hc8e DL (by decide) (by decide) (by decide), g3]; rfl,
      by rw [hfbrc, g6.2]; rfl⟩,
    hz HR (by simp) (by simp) (by simp) (by simp), by rw [hfbrc, (g5 STK (by decide)).2]; rfl,
    by rw [hfbram, (g5 STK (by decide)).1]; rfl⟩, ⟨fun j hj => ?_, ?_, ?_, ?_, ?_⟩, by rw [hfbrc, (g5 W2 (by decide)).2]⟩
  · rw [hfb, DS.set_env_ne _ _ (ne_of_val (by rw [Sl_val hj, CBR_val]; omega)),
      c2.env _ (notEv (by rw [Sl_val hj]; omega))]
    exact hsl10 j hj
  · rw [hfin ELR (by simp) (by decide) (by decide), hc8e ELR (by decide) (by decide) (by decide), g1]
  · rw [hfin FUR (by simp) (by decide) (by decide), hc8e FUR (by decide) (by decide) (by decide), g2]
  · rw [hfb, DS.set_env_self, c1]
  · rw [hfb, DS.set_out, hsame.out, g7]

end NearCubicGates.Adapters.Compile.OraclePrint
