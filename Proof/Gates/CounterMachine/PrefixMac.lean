import Proof.Gates.CounterMachine.CellTablesLem
import Proof.Gates.Cells.OutLen

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm (frameP frame_eq_frameP)
open NearCubicGates.Close.CounterMachine.CellTables (SameO SameO.refl SameO.trans SameO.set SameO.out emitV emitV_spec
  binary_getD_bit binary_snoc take_succ_getElem)

/-- Scratch of the printer. -/
def y0 : Fin VV := ⟨30, by decide⟩
def y1 : Fin VV := ⟨31, by decide⟩
def y2 : Fin VV := ⟨32, by decide⟩
def y3 : Fin VV := ⟨33, by decide⟩
def y4 : Fin VV := ⟨34, by decide⟩
/-- Scratch of the store passes. -/
def j1 : Fin VV := ⟨35, by decide⟩
def yv : Fin VV := ⟨36, by decide⟩
def yJ : Fin VV := ⟨37, by decide⟩

def femT : List (Fin VV) := [y0, y1, y2, y3, y4]

theorem frameP_append (u v : List Bool) : frameP (u ++ v) = frameP u ++ frameP v := by
  simp [frameP, List.flatMap_append]

theorem binary_eq_ofFn (L v : ℕ) : binary L v = List.ofFn (fun i : Fin L => v.testBit i.val) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have h := binary_getD_bit L v i (by simpa using h1)
  rw [List.getD_eq_getElem _ _ h1] at h
  rw [h, List.getElem_ofFn, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ i) with e | e <;> simp [e]

theorem natWord_bin (v : ℕ) :
    natWord v = List.replicate (natBitLength v) true ++ false :: binary (natBitLength v) v := by
  rw [natWord_eq, binary_eq_ofFn]

/-! ## The framed printer -/

/-- A framed constant bit. -/
def emT (b : Bool) : St VV MM := .seq (.op (.emit true)) (.op (.emit b))

theorem emT_spec (C : Ctx) (b : Bool) (a : DS VV MM) :
    Hs C (emT b) a 3 (· = { a with out := a.out ++ [true, b] }) := by
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_emit C true a) (fun d hd => ?_)
  subst hd
  refine Hs.mono (hs_emit C b _) le_rfl ?_
  rintro e rfl; simp

/-- One data bit of `y0`: marker, the low bit, halve. -/
def bitF : St VV MM :=
  .seq (.op (.dm y0 v2 y3 y4)) (.seq (.op (.emit true)) (.seq (emitV y4) (.op (.copy y0 y3))))

/-- **The framed printer**: `frameP (natWord (x))`. -/
def femNat (x : Fin VV) : St VV MM :=
  .seq (.op (.copy y0 x)) (.seq (.op (.zero y1)) (.seq (.op (.inc y1)) (.seq (emT true)
    (.seq (.loop (.lt v1 y0) (.seq (.op (.half y0)) (.seq (.op (.inc y1)) (emT true))))
      (.seq (emT false) (.seq (.op (.copy y0 x)) (forS y2 y1 bitF)))))))

theorem bitF_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (hW : 2 ≤ C.Wd) :
    Hs C bitF b 8 (fun d => d.out = b.out ++ [true, decide (b.env y0 % 2 = 1)] ∧ d.env y0 = b.env y0 / 2 ∧
      Fr b d [y0, y3, y4] ∧ SameO b d) := by
  have h4 : 2 * 2 ≤ 2 ^ C.Wd := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  refine Hs.seq (t1 := 1) (t2 := 6) (hs_dm C y0 v2 y3 y4 b (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hc.two]; norm_num) (by rw [hc.two]; exact h4)) (fun e he => ?_)
  subst he
  rw [hc.two]
  set e := (b.set y3 (b.env y0 / 2)).set y4 (b.env y0 % 2) with he
  have ec : Cst e := ⟨by rw [he]; vsimp [hc.z], by rw [he]; vsimp [hc.one], by rw [he]; vsimp [hc.two]⟩
  refine Hs.seq (t1 := 1) (t2 := 4) (hs_emit C true e) (fun f hf => ?_)
  subst hf
  have fc : Cst ({ e with out := e.out ++ [true] } : DS VV MM) := ⟨ec.z, ec.one, ec.two⟩
  refine Hs.seq (t1 := 2) (t2 := 1) (emitV_spec C y4 (by decide) _ fc) (fun g hg => ?_)
  subst hg
  refine Hs.mono (hs_copy C y0 y3 _ (by decide)) le_rfl ?_
  rintro r rfl
  have e4 : e.env y4 = b.env y0 % 2 := by rw [he]; vsimp []
  have e3 : e.env y3 = b.env y0 / 2 := by rw [he]; vsimp []
  refine ⟨?_, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · simp only [DS.set_out]; show e.out ++ [true] ++ [decide (e.env y4 = 1)] = _
    rw [e4, he]; simp
  · vsimp [e3]
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h0, h3, h4'⟩ := hy
    simp only [DS.set, Function.update_apply, if_neg h0]
    show e.env y = b.env y
    rw [he]; simp only [DS.set, Function.update_apply, if_neg h3, if_neg h4']

theorem femNat_spec (C : Ctx) (x : Fin VV) (hx : x ∉ femT) (b : DS VV MM) (hc : Cst b) (hW : 2 ≤ C.Wd)
    (hv : b.env x < 2 ^ C.Wd) :
    Hs C (femNat x) b (25 * natBitLength (b.env x) + 25) (fun d =>
      d.out = b.out ++ frameP (natWord (b.env x)) ∧ Fr b d femT ∧ SameO b d) := by
  set v := b.env x with hvdef
  set ℓ := natBitLength v with hℓ
  have hℓ1 : ℓ = Nat.log 2 v + 1 := rfl
  have hlogW : Nat.log 2 v < C.Wd := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · rw [h0]; simp; omega
    · exact (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).2 hv
  have hℓW : ℓ < 2 ^ C.Wd := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := C.Wd))
  have hx0 : x ≠ y0 := fun h => hx (by rw [h]; decide)
  have hx1 : x ≠ y1 := fun h => hx (by rw [h]; decide)
  have hx2 : x ≠ y2 := fun h => hx (by rw [h]; decide)
  have hx3 : x ≠ y3 := fun h => hx (by rw [h]; decide)
  have hx4 : x ≠ y4 := fun h => hx (by rw [h]; decide)
  unfold femNat
  refine Hs.mono (t := 1 + (1 + (1 + (3 + ((Nat.log 2 v) * (7 + 2) + 2 + (3 + (1 + (ℓ * (8 + 4) + 4) + 1) + 1) + 1)
    + 1) + 1) + 1) + 1) ?_ (by omega) (fun _ h => h)
  refine Hs.seq (t1 := 1) (hs_copy C y0 x b (Ne.symm hx0)) (fun b1 hb1 => ?_)
  subst hb1
  refine Hs.seq (t1 := 1) (hs_zero C y1 _) (fun b2 hb2 => ?_)
  subst hb2
  refine Hs.seq (t1 := 1) (hs_inc C y1 _ (by rw [DS.set_env_self]; exact Nat.one_lt_two_pow (by omega)))
    (fun b3 hb3 => ?_)
  subst hb3
  refine Hs.seq (t1 := 3) (emT_spec C true _) (fun b4 hb4 => ?_)
  subst hb4
  set b4 : DS VV MM := { ((b.set y0 v).set y1 0).set y1 (((b.set y0 v).set y1 0).env y1 + 1) with
    out := (((b.set y0 v).set y1 0).set y1 (((b.set y0 v).set y1 0).env y1 + 1)).out ++ [true, true] } with hb4
  -- the unary part
  let I : ℕ → DS VV MM → Prop := fun t d => d.env y0 = v / 2 ^ t ∧ d.env y1 = t + 1 ∧
    d.out = b.out ++ frameP (List.replicate (t + 1) true) ∧ Fr b d femT ∧ SameO b d
  have hI0 : I 0 b4 := by
    refine ⟨by rw [hb4]; vsimp [], by rw [hb4]; vsimp [], by rw [hb4]; simp [frameP], ?_,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    intro y hy
    simp only [femT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [hb4]; vsimp [Function.update_apply, hy.1, hy.2.1]
  have hloop := Hs.loopN (C := C) (c := .lt v1 y0) (s := .seq (.op (.half y0)) (.seq (.op (.inc y1)) (emT true)))
    (show v1 ≠ y0 by decide) I (Nat.log 2 v) 7 ?_ ?_ b4 hI0
  · refine Hs.seq (t1 := Nat.log 2 v * (7 + 2) + 2) hloop (fun d ⟨d0, d1, d2, d3, d4⟩ => ?_)
    refine Hs.seq (t1 := 3) (emT_spec C false d) (fun e he => ?_)
    subst he
    refine Hs.seq (t1 := 1) (hs_copy C y0 x _ (Ne.symm hx0)) (fun f hf => ?_)
    subst hf
    set f := { d with out := d.out ++ [true, false] }.set y0 ({ d with out := d.out ++ [true, false] }.env x)
      with hfdef
    have fx : f.env y0 = v := by rw [hfdef]; vsimp [d3 x hx]; rfl
    have fy1 : f.env y1 = ℓ := by rw [hfdef]; vsimp [d1]; rfl
    have fout : f.out = b.out ++ frameP (List.replicate ℓ true) ++ [true, false] := by
      rw [hfdef]; simp [d2, hℓ1]
    have ffr : Fr b f femT := Fr.trans d3 (Fr.set _ _ (by decide))
    have fsm : SameO b f := d4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have fc : Cst f := Cst.of_fr hc ffr (by decide)
    let J : ℕ → DS VV MM → Prop := fun j g => g.out = b.out ++ frameP (List.replicate ℓ true) ++ [true, false] ++
      frameP (binary j v) ∧ g.env y0 = v / 2 ^ j ∧ Fr b g femT ∧ SameO b g
    have hl2 := forS_spec' (C := C) y2 y1 (by decide) bitF f ℓ hℓW J 8
      (fun k g w ⟨g1, g2, g3, g4⟩ => ⟨g1, by rw [DS.set_env_ne _ _ (by decide)]; exact g2,
        Fr.trans g3 (Fr.set g w (by decide)), g4.trans (SameO.set _ _ _)⟩)
      ⟨by rw [fout]; simp [binary, frameP], by rw [fx]; simp, ffr, fsm⟩ fy1 ?_
    · refine Hs.mono hl2 le_rfl ?_
      rintro g ⟨⟨g1, _, g3, g4⟩, _, _⟩
      refine ⟨?_, g3, g4⟩
      rw [g1, natWord_bin, frameP_append]
      simp [frameP, List.append_assoc]; rfl
    · intro k hk g ⟨g1, g2, g3, g4⟩ hgk hgm
      have gc : Cst g := Cst.of_fr hc g3 (by decide)
      refine Hs.mono (bitF_spec C g gc hW) le_rfl ?_
      rintro e ⟨e1, e2, e3, e4⟩
      refine ⟨⟨?_, ?_, Fr.trans g3 (Fr.weaken e3 (by decide)), g4.trans e4⟩, ?_, ?_⟩
      · rw [e1, g1, g2, binary_snoc, frameP_append, List.append_assoc]
        rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with h | h <;> simp [frameP, h]
      · rw [e2, g2, Nat.div_div_eq_div_mul, pow_succ]
      · rw [e3 y2 (by decide)]; exact hgk
      · rw [e3 y1 (by decide)]; exact hgm
  · intro t ht d ⟨d0, d1, d2, d3, d4⟩
    have dc : Cst d := Cst.of_fr hc d3 (by decide)
    refine ⟨by simp only [Cnd.eval, d0, dc.one]; exact decide_eq_true ((lt_div_iff_lt_log v t ht.le).2 ht), ?_⟩
    refine Hs.seq (t1 := 1) (t2 := 5) (hs_half C y0 d) (fun e he => ?_)
    subst he
    refine Hs.seq (t1 := 1) (t2 := 3) (hs_inc C y1 _ (by vsimp [d1]; omega)) (fun f hf => ?_)
    subst hf
    refine Hs.mono (emT_spec C true _) le_rfl ?_
    rintro g rfl
    refine ⟨?_, ?_, ?_, ?_, d4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · vsimp [d0, Nat.div_div_eq_div_mul, pow_succ]
    · vsimp [d1]
    · simp only [DS.set_out, d2, List.replicate_succ', frameP_append, List.append_assoc]; simp [frameP]
    · exact Fr.trans d3 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
  · intro d ⟨d0, _, _, d3, _⟩
    have dc : Cst d := Cst.of_fr hc d3 (by decide)
    simp only [Cnd.eval, d0, dc.one]
    exact decide_eq_false (fun h => lt_irrefl _ ((lt_div_iff_lt_log v _ le_rfl).1 h))

/-! ## Validity for free -/

theorem hB_of (C : Ctx) : ∀ s, C.K.bud s ≤ C.Bk → (C.K.outw s).length ≤ C.Bk + 3 :=
  fun s h => (wf_out_len C.K.wf s).trans (by omega)

/-- Every run of the language keeps `Valid` (`Ex.valid`). -/
theorem Hs.valid {C : Ctx} {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM → Prop} (h : Hs C s a t R)
    (ha : Valid C a) (hW : 1 ≤ C.Wd) : Hs C s a t (fun b => R b ∧ Valid C b) := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  exact ⟨b, n, he, hn, hb, he.valid hW (hB_of C) ha⟩

/-! ## The untouched components -/

/-- The input cursor and the call words are never touched by the prefix program. -/
structure Oth (a b : DS VV MM) : Prop where
  ip : b.ip = a.ip
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem Oth.refl (a : DS VV MM) : Oth a a := ⟨rfl, rfl, rfl, rfl⟩

theorem Oth.trans {a b d : DS VV MM} (h1 : Oth a b) (h2 : Oth b d) : Oth a d :=
  ⟨h2.ip.trans h1.ip, h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩

theorem Oth.of_sameO {a b : DS VV MM} (h : SameO a b) : Oth a b := ⟨h.ip, h.kin, h.kout, h.kc⟩

theorem cst_lo {a b : DS VV MM} {T : List (Fin VV)} (hc : Cst a) (hf : Fr a b T) (hT : ∀ y ∈ T, 3 ≤ y.val) :
    Cst b :=
  ⟨by rw [hf vZ (fun h => by have := hT _ h; simp [vZ] at this)]; exact hc.z,
    by rw [hf v1 (fun h => by have := hT _ h; simp [v1] at this)]; exact hc.one,
    by rw [hf v2 (fun h => by have := hT _ h; simp [v2] at this)]; exact hc.two⟩

/-! ## Printing a whole store -/

/-- Print the `cnt` records of store `m` as framed `natWord`s. -/
def emAll (m : Fin MM) (cnt : Fin VV) : St VV MM :=
  .seq (.op (.rwM m)) (forS j1 cnt (.seq (.op (.rdM m yv)) (femNat yv)))

def emAllT : List (Fin VV) := [j1, yv, y0, y1, y2, y3, y4]

theorem emAll_spec (C : Ctx) (m : Fin MM) (cnt : Fin VV) (hcnt : cnt ∉ emAllT) (b : DS VV MM) (hv : Valid C b)
    (hc : Cst b) (hW : 2 ≤ C.Wd) (Λ : ℕ) (hlen : b.env cnt = (b.ram m).length)
    (hfit : ∀ x ∈ b.ram m, natBitLength x ≤ Λ) :
    Hs C (emAll m cnt) b ((b.ram m).length * (25 * Λ + 31) + (b.ram m).length + 7) (fun d =>
      d.out = b.out ++ (b.ram m).flatMap (fun x => frameP (natWord x)) ∧ d.ram = b.ram ∧
      d.rc = Function.update b.rc m (b.ram m).length ∧ Oth b d ∧ Fr b d emAllT) := by
  set L := b.ram m with hL
  have hN : L.length < 2 ^ C.Wd := by rw [← hlen]; exact hv.env_lt cnt
  have hrc : b.rc m ≤ L.length := hv.rc_le m
  refine Hs.mono (Hs.seq (t1 := L.length + 1) (t2 := L.length * (25 * Λ + 27 + 4) + 4)
    (Hs.mono (hs_rwM C m b) (by omega) (fun _ h => h)) (fun b1 hb1 => ?_)) (by nlinarith) (fun _ h => h)
  subst hb1
  let I : ℕ → DS VV MM → Prop := fun j d => d.out = b.out ++ (L.take j).flatMap (fun x => frameP (natWord x)) ∧
    d.ram = b.ram ∧ d.rc = Function.update b.rc m j ∧ Oth b d ∧ Fr b d emAllT
  have hl := forS_spec' (C := C) j1 cnt (fun h => hcnt (by rw [← h]; decide)) (.seq (.op (.rdM m yv)) (femNat yv))
    (b.rew m) L.length hN I
    (25 * Λ + 27)
    (fun k d w ⟨d1, d2, d3, d4, d5⟩ => ⟨d1, d2, d3, d4.trans ⟨rfl, rfl, rfl, rfl⟩, Fr.trans d5 (Fr.set d w (by decide))⟩)
    ⟨by simp [DS.rew], rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, Fr.refl _ _⟩
    (by simp only [DS.rew]; exact hlen) ?_
  · refine Hs.mono hl le_rfl ?_
    rintro d ⟨⟨d1, d2, d3, d4, d5⟩, _, _⟩
    exact ⟨by rw [d1, List.take_of_length_le le_rfl], d2, d3, d4, d5⟩
  · intro k hk d ⟨d1, d2, d3, d4, d5⟩ _ _
    have hkL : k < (d.ram m).length := by rw [d2]; exact hk
    have hrck : d.rc m < (d.ram m).length := by rw [d3, Function.update_self]; exact hkL
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 25 * Λ + 25) (hs_rdM C m yv d hrck) (fun e he => ?_)) (by omega)
      (fun _ h => h)
    subst he
    have dc : Cst d := Cst.of_fr hc d5 (by decide)
    have ec : Cst ((d.set yv ((d.ram m).getD (d.rc m) 0)).adv m) :=
      ⟨by simp [DS.adv]; vsimp [dc.z], by simp [DS.adv]; vsimp [dc.one], by simp [DS.adv]; vsimp [dc.two]⟩
    have ev : ((d.set yv ((d.ram m).getD (d.rc m) 0)).adv m).env yv = L[k] := by
      simp only [DS.adv, DS.set_env_self, d2, d3, Function.update_self]
      rw [← hL, List.getD_eq_getElem _ _ hk]
    have hxL : L[k] ∈ L := List.getElem_mem _
    have hlt : L[k] < 2 ^ C.Wd := hv.ram_lt m _ hxL
    refine Hs.mono (femNat_spec C yv (by decide) _ ec hW (by rw [ev]; exact hlt)) (by
      rw [ev]; have := hfit _ hxL; omega) ?_
    rintro e ⟨e1, e2, e3⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [e1, ev]; simp only [DS.adv, DS.set_out]
      rw [d1, take_succ_getElem L k _ (List.getElem?_eq_getElem hk), List.flatMap_append]
      simp
    · rw [e3.ram]; simp [DS.adv, d2]
    · rw [e3.rc]; simp only [DS.adv, DS.set_rc, d3, Function.update_self, Function.update_idem]
    · exact d4.trans (Oth.trans (show Oth d ((d.set yv ((d.ram m).getD (d.rc m) 0)).adv m) from
        ⟨rfl, rfl, rfl, rfl⟩) (Oth.of_sameO e3))
    · refine Fr.trans d5 (Fr.trans ?_ (Fr.weaken e2 (by decide)))
      intro y hy; simp only [DS.adv]; exact Fr.set d _ (show yv ∈ emAllT by decide) y hy
    · rw [e2 j1 (by decide)]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; assumption
    · rw [e2 cnt (fun h => hcnt (by simp [femT, emAllT] at h ⊢; tauto))]; simp only [DS.adv]
      rw [DS.set_env_ne _ _ (fun h => hcnt (by rw [h]; decide))]; assumption

/-! ## Membership scan -/

/-- `fl := [x ∈ store m]` (count of the store in `cnt`). -/
def memS (m : Fin MM) (cnt x fl : Fin VV) : St VV MM :=
  .seq (.op (.rwM m)) (.seq (.op (.zero fl))
    (forS j1 cnt (.seq (.op (.rdM m yv)) (.ite (.eq yv x) (.op (.copy fl v1)) (.op (.zero yJ))))))

theorem ne_lo {y z : Fin VV} (hy : 38 ≤ y.val) (hz : z.val < 38) : y ≠ z := fun h => by rw [h] at hy; omega

theorem memS_spec (C : Ctx) (m : Fin MM) (cnt x fl : Fin VV) (hcf : cnt ≠ fl) (hxf : x ≠ fl)
    (hcl : 38 ≤ cnt.val) (hxl : 38 ≤ x.val) (hfl : 38 ≤ fl.val) (b : DS VV MM) (hv : Valid C b)
    (hc : Cst b) (hlen : b.env cnt = (b.ram m).length) :
    Hs C (memS m cnt x fl) b (9 * (b.ram m).length + 12) (fun d =>
      d.env fl = (if b.env x ∈ b.ram m then 1 else 0) ∧ d.out = b.out ∧ d.ram = b.ram ∧
      d.rc = Function.update b.rc m (b.ram m).length ∧ Oth b d ∧ Fr b d [j1, yv, yJ, fl]) := by
  set L := b.ram m with hL
  have hN : L.length < 2 ^ C.Wd := by rw [← hlen]; exact hv.env_lt cnt
  have hrc : b.rc m ≤ L.length := hv.rc_le m
  have hcj : cnt ≠ j1 := ne_lo hcl (by decide)
  have hxv : x ≠ yv := ne_lo hxl (by decide)
  have hxj : x ≠ j1 := ne_lo hxl (by decide)
  have hxJ : x ≠ yJ := ne_lo hxl (by decide)
  have hfl1 : fl ≠ v1 := ne_lo hfl (by decide)
  have hflj : fl ≠ j1 := ne_lo hfl (by decide)
  have hflv : fl ≠ yv := ne_lo hfl (by decide)
  have hcv : cnt ≠ yv := ne_lo hcl (by decide)
  have hcJ : cnt ≠ yJ := ne_lo hcl (by decide)
  refine Hs.mono (Hs.seq (t1 := L.length + 1) (t2 := 1 + (L.length * (4 + 4) + 4) + 1)
    (Hs.mono (hs_rwM C m b) (by omega) (fun _ h => h)) (fun b1 hb1 => ?_)) (by omega) (fun _ h => h)
  subst hb1
  refine Hs.seq (t1 := 1) (hs_zero C fl _) (fun b2 hb2 => ?_)
  subst hb2
  let I : ℕ → DS VV MM → Prop := fun j d => d.env fl = (if b.env x ∈ L.take j then 1 else 0) ∧ d.out = b.out ∧
    d.ram = b.ram ∧ d.rc = Function.update b.rc m j ∧ Oth b d ∧ Fr b d [j1, yv, yJ, fl]
  have hl := forS_spec' (C := C) j1 cnt (Ne.symm hcj)
    (.seq (.op (.rdM m yv)) (.ite (.eq yv x) (.op (.copy fl v1)) (.op (.zero yJ)))) ((b.rew m).set fl 0) L.length hN I 4
    (fun k d w ⟨d1, d2, d3, d4, d5, d6⟩ => ⟨by rw [DS.set_env_ne _ _ hflj]; exact d1, d2, d3, d4,
      d5.trans ⟨rfl, rfl, rfl, rfl⟩, Fr.trans d6 (Fr.set d w (by simp))⟩)
    ⟨by simp, rfl, rfl, by simp [DS.rew], ⟨rfl, rfl, rfl, rfl⟩, Fr.set _ _ (by simp)⟩
    (by rw [DS.set_env_ne _ _ hcf]; simp only [DS.rew]; exact hlen) ?_
  · refine Hs.mono hl le_rfl ?_
    rintro d ⟨⟨d1, d2, d3, d4, d5, d6⟩, _, _⟩
    exact ⟨by rw [d1, List.take_of_length_le le_rfl], d2, d3, d4, d5, d6⟩
  · intro k hk d ⟨d1, d2, d3, d4, d5, d6⟩ hdj hdc
    have hrck : d.rc m < (d.ram m).length := by rw [d4, Function.update_self, d3]; exact hk
    refine Hs.seq (t1 := 1) (t2 := 2) (hs_rdM C m yv d hrck) (fun e he => ?_)
    subst he
    have dc : Cst d := cst_lo hc d6 (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> first | decide | omega)
    set e := (d.set yv ((d.ram m).getD (d.rc m) 0)).adv m with hedef
    have ev : e.env yv = L[k] := by
      rw [hedef]; simp only [DS.adv, DS.set_env_self, d3, d4, Function.update_self]
      rw [← hL, List.getD_eq_getElem _ _ hk]
    have ex : e.env x = b.env x := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ hxv]
      exact d6 x (by simp; exact ⟨hxj, hxv, hxJ, hxf⟩)
    have efl : e.env fl = d.env fl := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ hflv]
    have ec : Cst e := ⟨by rw [hedef]; simp [DS.adv]; vsimp [dc.z], by rw [hedef]; simp [DS.adv]; vsimp [dc.one],
      by rw [hedef]; simp [DS.adv]; vsimp [dc.two]⟩
    have htake : L.take (k + 1) = L.take k ++ [L[k]] := take_succ_getElem L k _ (List.getElem?_eq_getElem hk)
    have post : ∀ g : DS VV MM, g.env fl = (if b.env x ∈ L.take (k + 1) then 1 else 0) → g.out = e.out →
        g.ram = e.ram → g.rc = e.rc → Oth e g → Fr e g [yJ, fl] →
        I (k + 1) g ∧ g.env j1 = k ∧ g.env cnt = L.length := by
      intro g g1 g2 g3 g4 g5 g6
      refine ⟨⟨g1, by rw [g2, hedef]; simp [DS.adv, d2], by rw [g3, hedef]; simp [DS.adv, d3],
        by rw [g4, hedef]; simp [DS.adv, d4], d5.trans (Oth.trans (show Oth d e from ⟨rfl, rfl, rfl, rfl⟩) g5),
        Fr.trans d6 (Fr.trans (fun y hy => ?_) (Fr.weaken g6 (by simp)))⟩, ?_, ?_⟩
      · rw [hedef]; simp only [DS.adv]; exact Fr.set d _ (show yv ∈ [j1, yv, yJ, fl] by simp) y hy
      · rw [g6 j1 (by simp; exact ⟨by decide, Ne.symm hflj⟩), hedef]; simp only [DS.adv]
        rw [DS.set_env_ne _ _ (by decide)]; exact hdj
      · rw [g6 cnt (by simp; exact ⟨hcJ, hcf⟩), hedef]; simp only [DS.adv]
        rw [DS.set_env_ne _ _ hcv]; exact hdc
    refine Hs.ite (c := .eq yv x) (Ne.symm hxv) (fun h => ?_) (fun h => ?_)
    · have hk' : L[k] = b.env x := by simpa [Cnd.eval, ev, ex] using h
      refine Hs.mono (hs_copy C fl v1 e hfl1) le_rfl ?_
      rintro g rfl
      refine post _ ?_ rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩ (Fr.set e _ (by simp))
      rw [DS.set_env_self, ec.one, htake]; simp [hk']
    · have hk' : L[k] ≠ b.env x := by simpa [Cnd.eval, ev, ex] using h
      refine Hs.mono (hs_zero C yJ e) le_rfl ?_
      rintro g rfl
      refine post _ ?_ rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩ (Fr.set e _ (by simp))
      rw [DS.set_env_ne _ _ (ne_lo hfl (by decide)), efl, d1, htake]
      simp only [List.mem_append, List.mem_singleton, Ne.symm hk', or_false]

end NearCubicGates.Close.CounterMachine.PrefixProg
