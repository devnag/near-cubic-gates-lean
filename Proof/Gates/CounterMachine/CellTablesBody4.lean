import Proof.Gates.CounterMachine.CellTablesBody3
import Proof.Gates.Cells.Format

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

/-! ## Body variables, decidably -/

def bodyVarB (y : Fin VV) : Bool :=
  (3 ≤ y.val && y.val ≤ 20) || (30 ≤ y.val && y.val ≤ 39) || (44 ≤ y.val && y.val ≤ 46) ||
    (48 ≤ y.val && y.val ≤ 63) || 100 ≤ y.val

theorem bodyVar_of {y : Fin VV} (h : bodyVarB y = true) : BodyVar y := by
  unfold bodyVarB at h; unfold BodyVar
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- Only body variables changed. -/
def BF (a e : DS VV MM) : Prop := ∀ y, ¬ BodyVar y → e.env y = a.env y

theorem BF.refl (a : DS VV MM) : BF a a := fun _ _ => rfl
theorem BF.trans {a b d : DS VV MM} (h1 : BF a b) (h2 : BF b d) : BF a d := fun y hy => (h2 y hy).trans (h1 y hy)
theorem BF.of_fr {a b : DS VV MM} {T : List (Fin VV)} (h : Fr a b T) (hT : T.all bodyVarB = true) : BF a b :=
  fun y hy => h y (fun hm => hy (bodyVar_of (List.all_eq_true.mp hT y hm)))
theorem BF.set (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : bodyVarB x = true) : BF a (a.set x v) :=
  BF.of_fr (T := [x]) (Fr.set a v (by simp)) (by simp [hx])

/-! ## Size facts -/

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem nbl_le_cellInput (r : CellReq B1 B2 cT) (v : ℕ) (hv : v ∈ cellN r.c r.p r.wt) :
    natBitLength v ≤ (cellInput r).length := by
  have h1 : (cellN r.c r.p r.wt).flatMap natWord = cellInput r := cellN_word _ _ _
  rw [← h1]
  exact (Cells.nbl_le_word v).trans (PrefixLoader.len_le_flatMap _ _ v hv)

theorem cellN_len_le (r : CellReq B1 B2 cT) : (cellN r.c r.p r.wt).length ≤ (cellInput r).length := by
  have h1 : (cellN r.c r.p r.wt).flatMap natWord = cellInput r := cellN_word _ _ _
  rw [← h1, List.length_flatMap]
  calc (cellN r.c r.p r.wt).length = ((cellN r.c r.p r.wt).map fun _ => 1).sum := by simp
    _ ≤ _ := List.sum_le_sum (by intro i _; rw [Cells.natWord_length]; omega)

/-! ## The tail -/

def tailB (kK qv rv : Fin VV) : St VV MM :=
  .seq emCell (.seq (.op .kcall) (.seq (.op (.mul bKey kK vKY)) (.seq (.op (.copy vQE qv))
    (.seq (.op (.copy vRS rv)) convP))))

/-- The cost of the tail. -/
def tailCost (Lk Bk wb : ℕ) (r : CellReq B1 B2 cT) : ℕ :=
  (cellN r.c r.p r.wt).length * (40 * (cellInput r).length + 42 + 4) + Lk + Bk +
    100 * 2 ^ (r.c.n - r.p.k) * (wb + 10) + 120

theorem tail_spec (RK : TabCallMachine B1 B2 cT PolyTab) (Wd Lk Bk wb : ℕ) (inp : List Bool) (x : TabCallReq B1 B2 cT)
    (d : DS VV MM) (kK qv rv : Fin VV) (QE : ℕ) (res : Bool) (hF : Fit RK x.r Wd Lk Bk wb)
    (hkK : kK ∉ emCellT) (hqv : qv ∉ emCellT) (hrv : rv ∉ emCellT) (hkK2 : kK ≠ bKey) (hkK3 : kK ≠ vKY)
    (hqv2 : qv ≠ vQE) (hqv3 : qv ≠ vKY) (hrv2 : rv ≠ vRS) (hrv3 : rv ≠ vKY) (hrv4 : rv ≠ vQE)
    (hv : Valid (ctxK RK Wd inp Lk Bk) d) (hc : Cst d) (hN : d.ram sN = cellN x.r.c x.r.p x.r.wt)
    (hwN : d.env wN = (cellN x.r.c x.r.p x.r.wt).length)
    (h1 : d.env vH1 = 2 ^ ((x.r.c.n - x.r.p.k + 1) / 2)) (h0 : d.env vH0 = 2 ^ ((x.r.c.n - x.r.p.k) / 2))
    (hsh : d.env vSH = 2 ^ (keyBits x.r.p * keyLen x.r.c x.r.p + valueWidth x.r.c x.r.p))
    (hkin : d.kin = (descN x.id).flatMap natWord)
    (hkey : d.env bKey * d.env kK = reqKey x.r.c x.r.p x.id * 2 ^ valueWidth x.r.c x.r.p)
    (hqe : d.env qv = QE) (hrs : d.env rv = if res then 1 else 0)
    (hres : ∀ part q κ σ, x.id = .residue part q κ σ → res = true ∧ QE = q ^ x.r.p.e)
    (hmom : (∀ part q κ σ, x.id ≠ .residue part q κ σ) → res = false) (hq0 : res = true → 0 < QE)
    (hq4 : 4 * QE ≤ 2 ^ Wd) (hrc : d.rc sREC = (d.ram sREC).length) :
    Hs (ctxK RK Wd inp Lk Bk) (tailB kK qv rv) d (d.rc sN + tailCost Lk Bk wb x.r) (fun e =>
      Post (ctxK RK Wd inp Lk Bk) x.r d e x.id) := by
  set C := ctxK RK Wd inp Lk Bk with hC
  have hWd : 4 ≤ C.Wd := by have := hF.wd; show 4 ≤ Wd; omega
  have hspec := cellReq_spec x.r
  have hLk : (tabCallInput x).length ≤ C.Lk := hF.lk x rfl
  have hcw : (cellN x.r.c x.r.p x.r.wt).flatMap natWord = cellInput x.r := cellN_word _ _ _
  unfold tailB
  apply Hx.hs
  -- the loaded naturals
  refine Hs.then (PrefixProg.Hs.valid (emCell_spec C d hc (by omega) (cellN x.r.c x.r.p x.r.wt) (cellInput x.r).length hN hwN
    (by rw [← hwN]; exact hv.env_lt wN) (fun v hm => hv.ram_lt sN v (by rw [hN]; exact hm))
    (fun v hm => nbl_le_cellInput x.r v hm)
    (by rw [hkin, hcw]; simpa [tabCallInput] using hLk)) hv (by omega))
    (fun e1 ⟨⟨k1, r1, i1, o1, m1, ko1, kc1, c1, f1⟩, w1⟩ n1 hn1 => ?_)
  have e1in : e1.kin = tabCallInput x := by rw [k1, hkin, hcw]; rfl
  -- the call
  refine Hs.then (PrefixProg.Hs.valid (Hs.op (C := C) (R := fun b => b = e1.called (tabCallOutput PolyTab x))
    (OpEx.kcall (C := C) x e1 e1in (hF.bk x rfl)) rfl) w1 (by omega)) (fun e2 ⟨he2, w2⟩ n2 hn2 => ?_)
  subst he2
  have hfr1 : ∀ y, y ∉ emCellT → (e1.called (tabCallOutput PolyTab x)).env y = d.env y := fun y hy => f1 y hy
  have hK : reqKey x.r.c x.r.p x.id < 2 ^ (keyBits x.r.p * keyLen x.r.c x.r.p) :=
    Cells.reqKey_lt x.r.c x.r.p hspec x.id x.mem
  have hKW : reqKey x.r.c x.r.p x.id * 2 ^ valueWidth x.r.c x.r.p < 2 ^ C.Wd := by
    calc _ < 2 ^ (keyBits x.r.p * keyLen x.r.c x.r.p) * 2 ^ valueWidth x.r.c x.r.p :=
          Nat.mul_lt_mul_of_pos_right hK (Nat.two_pow_pos _)
      _ = 2 ^ (keyBits x.r.p * keyLen x.r.c x.r.p + valueWidth x.r.c x.r.p) := by rw [pow_add]
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by have := hF.wd; unfold lamW at this; show _ ≤ Wd; omega)
  refine Hs.then (PrefixProg.Hs.valid (hs_mul C bKey kK vKY _ (Ne.symm hkK2) (by decide) hkK3
    (by rw [hfr1 bKey (by decide), hfr1 kK hkK, hkey]; exact hKW)) w2 (by omega)) (fun e3 ⟨he3, w3⟩ n3 hn3 => ?_)
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C vQE qv _ (Ne.symm hqv2)) w3 (by omega)) (fun e4 ⟨he4, w4⟩ n4 hn4 => ?_)
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C vRS rv _ (Ne.symm hrv2)) w4 (by omega)) (fun e5 ⟨he5, w5⟩ n5 hn5 => ?_)
  have g5 : ∀ y, y ∉ emCellT → y ≠ vKY → y ≠ vQE → y ≠ vRS → e5.env y = d.env y := by
    intro y h1' h2' h3' h4'
    rw [he5, DS.set_env_ne _ _ h4', he4, DS.set_env_ne _ _ h3', he3, DS.set_env_ne _ _ h2']
    exact hfr1 y h1'
  have c5 : Cst e5 := ⟨by rw [g5 vZ (by decide) (by decide) (by decide) (by decide)]; exact hc.z,
    by rw [g5 v1 (by decide) (by decide) (by decide) (by decide)]; exact hc.one,
    by rw [g5 v2 (by decide) (by decide) (by decide) (by decide)]; exact hc.two⟩
  refine Hs.last (PrefixProg.Hs.valid (conv_tabCall RK Wd Lk Bk wb inp x e5 QE res w5 c5 (by rw [he5, he4, he3]; rfl) (by rw [he5, he4, he3]; rfl)
    (by rw [g5 vH1 (by decide) (by decide) (by decide) (by decide)]; exact h1)
    (by rw [g5 vH0 (by decide) (by decide) (by decide) (by decide)]; exact h0)
    (by rw [g5 vSH (by decide) (by decide) (by decide) (by decide)]; exact hsh)
    (by rw [he5, DS.set_env_ne _ _ (by decide), he4, DS.set_env_ne _ _ (by decide), he3, DS.set_env_self,
      hfr1 bKey (by decide), hfr1 kK hkK, hkey])
    (by rw [he5, DS.set_env_ne _ _ (by decide), he4, DS.set_env_self, he3, DS.set_env_ne _ _ hqv3, hfr1 qv hqv, hqe])
    (by rw [he5, DS.set_env_self, he4, DS.set_env_ne _ _ hrv4, he3, DS.set_env_ne _ _ hrv3, hfr1 rv hrv, hrs])
    hres hmom hq0 (hF.wid x rfl) hF.wd hq4
    (by rw [he5, he4, he3]; show e1.rc sREC = (e1.ram sREC).length
        rw [r1, Function.update_of_ne (by decide), m1]; exact hrc)) w5
      (by omega))
    (fun e6 ⟨⟨b1, b2, b3, b4⟩, w6⟩ n6 hn6 => ?_)
  have e5ram : e5.ram = d.ram := by rw [he5, he4, he3]; exact m1
  have e5rc : e5.rc = Function.update d.rc sN (cellN x.r.c x.r.p x.r.wt).length := by rw [he5, he4, he3]; exact r1
  refine ⟨⟨by rw [b1, e5ram], b2, fun m hm1 hm2 => by rw [b4.ram m hm1 hm2, e5ram],
    by rw [b4.rc sN (by decide) (by decide), e5rc]; simp,
    fun m hm1 hm2 hm3 => by rw [b4.rc m hm1 hm2, e5rc, Function.update_of_ne hm3],
    by rw [b3, he5, he4, he3]; exact o1, by rw [b4.ip, he5, he4, he3]; exact i1, by rw [b4.kin, he5, he4, he3]; rfl,
    w6, b4.cst c5, ?_⟩, ?_⟩
  · have bf5 : BF (e1.called (tabCallOutput PolyTab x)) e5 := by
      intro y hy
      have h44 : y ≠ vKY := fun h => hy (by rw [h]; exact bodyVar_of (by decide))
      have h45 : y ≠ vQE := fun h => hy (by rw [h]; exact bodyVar_of (by decide))
      have h46 : y ≠ vRS := fun h => hy (by rw [h]; exact bodyVar_of (by decide))
      rw [he5, DS.set_env_ne _ _ h46, he4, DS.set_env_ne _ _ h45, he3, DS.set_env_ne _ _ h44]
    refine BF.trans (BF.of_fr f1 (by decide)) (BF.trans (fun y _ => rfl) (BF.trans bf5 ?_))
    exact BF.of_fr b4.fr (by decide)
  · unfold tailCost
    have hCL : C.Lk = Lk := rfl
    have hCB : C.Bk = Bk := rfl
    omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
