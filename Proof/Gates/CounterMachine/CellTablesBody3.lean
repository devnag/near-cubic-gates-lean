import Proof.Gates.CounterMachine.CellTablesBody2
import Proof.Gates.CounterMachine.CellTablesValue
import Proof.Gates.CounterMachine.CellTablesConv
import Proof.Gates.Cells.Recs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP recOf CHyp CInv
  oneP_spec u0 u1 oneP Frame)

theorem convAll (C : Ctx) (a : DS VV MM) (s w SH KY QE : ℕ) (res : Bool) (z : ℕ → ℤ)
    (hv : Valid C a) (hc : Cst a) (h1 : a.env vH1 = 2 ^ ((s + 1) / 2)) (h0 : a.env vH0 = 2 ^ (s / 2))
    (hsh : a.env vSH = SH) (hky : a.env vKY = KY) (hqe : a.env vQE = QE) (hrs : a.env vRS = (if res then 1 else 0))
    (hq0 : res = true → 0 < QE)
    (hk : a.kout = WordPrograms.recStream ((printerOrder s).map fun i =>
      RepairOrdinary.SignedSortKey.binary w (WordPrograms.SInt.encS (z i))))
    (hkc : a.kc = 0) (henc : ∀ i < 2 ^ s, WordPrograms.SInt.encS (z i) < 2 ^ w) (hwd : w + s + 2 ≤ C.Wd)
    (hq2 : 2 * QE < 2 ^ C.Wd) (hrec : ∀ i < 2 ^ s, recOf SH KY QE res i (z i) < 2 ^ C.Wd)
    (hrc : a.rc sREC = (a.ram sREC).length) :
    Hs C convP a (100 * 2 ^ s * (w + 10) + 100) (fun b =>
      b.ram sREC = a.ram sREC ++ (printerOrder s).map (fun i => recOf SH KY QE res i (z i)) ∧
      b.rc sREC = (b.ram sREC).length ∧ b.out = a.out ∧ Frame a b) := by
  have hy : CHyp C a s w SH KY QE res z := ⟨hc, h1, h0, hsh, hky, hqe, hrs, hq0, henc, hwd, hq2, hrec⟩
  set H1 := 2 ^ ((s + 1) / 2) with hH1
  set H0 := 2 ^ (s / 2) with hH0
  have hHH : H1 * H0 = 2 ^ s := CellTables.pow_split s
  have hH0p : 1 ≤ H0 := Nat.one_le_two_pow
  have hN1 : H1 < 2 ^ C.Wd := by rw [← h1]; exact hv.env_lt vH1
  have hN0 : H0 < 2 ^ C.Wd := by rw [← h0]; exact hv.env_lt vH0
  let Io : ℕ → DS VV MM → Prop := fun r e => CInv a s w SH KY QE res z (r * H0) e
  unfold convP
  have hl := forS_spec' (C := C) u0 vH1 (by decide) (forS u1 vH0 oneP) a H1 hN1 Io (H0 * (10 * w + 33 + 4) + 4)
    (fun k e v he => he.set u0 v (by decide)) ⟨by simp only [hkc, Nat.zero_mul, List.drop_zero, hk], by simp, hrc,
      rfl, CellTables.Frame.refl a⟩ h1 ?_
  · refine Hs.mono hl ?_ ?_
    · have : H1 ≤ 2 ^ s := by rw [← hHH]; exact Nat.le_mul_of_pos_right _ hH0p
      have e : H1 * (H0 * (10 * w + 33 + 4) + 4 + 4) = (H1 * H0) * (10 * w + 37) + 8 * H1 := by ring
      rw [e, hHH]; nlinarith
    · rintro b ⟨⟨b1, b2, b3, b4, b5⟩, _, _⟩
      have hlen : (printerOrder s).length ≤ H1 * H0 := by rw [CellTables.printerOrder_length, hHH]
      refine ⟨by rw [b2, List.take_of_length_le hlen], b3, b4, b5⟩
  · intro r hr e he he0 he1
    let Ii : ℕ → DS VV MM → Prop := fun j f => CInv a s w SH KY QE res z (r * H0 + j) f ∧ f.env u0 = r
    have eH0 : e.env vH0 = H0 := by rw [he.2.2.2.2.env_lo vH0 (by decide)]; exact h0
    have hl2 := forS_spec' (C := C) u1 vH0 (by decide) oneP e H0 hN0 Ii (10 * w + 33)
      (fun k f v ⟨hf, hf0⟩ => ⟨hf.set u1 v (by decide), by rw [DS.set_env_ne _ _ (by decide)]; exact hf0⟩)
      ⟨he, he0⟩ eH0 ?_
    · refine Hs.mono hl2 le_rfl ?_
      rintro f ⟨⟨hf, hf0⟩, _, _⟩
      refine ⟨?_, hf0, ?_⟩
      · show CInv a s w SH KY QE res z ((r + 1) * H0) f
        rw [show (r + 1) * H0 = r * H0 + H0 by ring]; exact hf
      · rw [hf.2.2.2.2.env_lo vH1 (by decide)]; exact h1
    · intro j hj f ⟨hf, hf0⟩ hf1 hfm
      refine Hs.mono (oneP_spec C a s w SH KY QE res z hy r j hr hj f hf hf0 hf1) le_rfl ?_
      rintro g ⟨g1, g2, g3⟩
      exact ⟨⟨g1, g2⟩, g3, by rw [g1.2.2.2.2.env_lo vH0 (by decide)]; exact h0⟩

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem conv_tabCall (RK : TabCallMachine B1 B2 cT PolyTab) (Wd Lk Bk wb : ℕ) (inp : List Bool) (x : TabCallReq B1 B2 cT)
    (d : DS VV MM) (QE : ℕ) (res : Bool) (hv : Valid (ctxK RK Wd inp Lk Bk) d) (hc : Cst d)
    (hkout : d.kout = tabCallOutput PolyTab x) (hkc : d.kc = 0)
    (h1 : d.env vH1 = 2 ^ ((x.r.c.n - x.r.p.k + 1) / 2)) (h0 : d.env vH0 = 2 ^ ((x.r.c.n - x.r.p.k) / 2))
    (hsh : d.env vSH = 2 ^ (keyBits x.r.p * keyLen x.r.c x.r.p + valueWidth x.r.c x.r.p))
    (hky : d.env vKY = reqKey x.r.c x.r.p x.id * 2 ^ valueWidth x.r.c x.r.p) (hqe : d.env vQE = QE)
    (hrs : d.env vRS = if res then 1 else 0)
    (hres : ∀ part q κ σ, x.id = .residue part q κ σ → res = true ∧ QE = q ^ x.r.p.e)
    (hmom : (∀ part q κ σ, x.id ≠ .residue part q κ σ) → res = false) (hq0 : res = true → 0 < QE)
    (hw : PolyTab.width (tabCallTab x) ≤ wb) (hwd : wb + lamW x.r.c x.r.p + 4 ≤ Wd) (hq4 : 4 * QE ≤ 2 ^ Wd)
    (hrc : d.rc sREC = (d.ram sREC).length) :
    Hs (ctxK RK Wd inp Lk Bk) convP d (100 * 2 ^ (x.r.c.n - x.r.p.k) * (wb + 10) + 100) (fun b =>
      b.ram sREC = d.ram sREC ++ recsOf x.r.c x.r.p x.r.wt x.id ∧ b.rc sREC = (b.ram sREC).length ∧
      b.out = d.out ∧ Frame d b) := by
  have hs : (tabCallTab x).s = x.r.c.n - x.r.p.k := tabCallTab_s x
  have hspec := cellReq_spec x.r
  obtain ⟨w0, hw0⟩ := x.r.hw
  have hWpos : 0 < 2 ^ Wd := Nat.two_pow_pos _
  unfold lamW at hwd
  have hrec : ∀ i < 2 ^ (tabCallTab x).s, recOf (2 ^ (keyBits x.r.p * keyLen x.r.c x.r.p + valueWidth x.r.c x.r.p))
      (reqKey x.r.c x.r.p x.id * 2 ^ valueWidth x.r.c x.r.p) QE res i
      (tabTarget (tabCallTab x) (outerOf (tabCallTab x).s i)) < 2 ^ Wd := by
    intro i hi
    rw [CellTablesValue.recOf_tabCall x QE res hres hmom i]
    have hb := (Cells.cellRec_bounds x.r.c x.r.p x.r.wt hspec w0 hw0 i x.id x.mem).2
    rw [hs] at hi
    calc _ < (i + 1) * 2 ^ (Cells.keyW x.r.c x.r.p + valueWidth x.r.c x.r.p) := hb
      _ ≤ 2 ^ (x.r.c.n - x.r.p.k) * 2 ^ (Cells.keyW x.r.c x.r.p + valueWidth x.r.c x.r.p) :=
          Nat.mul_le_mul_right _ hi
      _ = 2 ^ (x.r.c.n - x.r.p.k + (keyBits x.r.p * keyLen x.r.c x.r.p + valueWidth x.r.c x.r.p)) := by
          rw [← pow_add]
      _ ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc' := convAll (ctxK RK Wd inp Lk Bk) d (tabCallTab x).s (PolyTab.width (tabCallTab x)) _ _ QE res
    (fun i => tabTarget (tabCallTab x) (outerOf (tabCallTab x).s i)) hv hc (by rw [hs]; exact h1) (by rw [hs]; exact h0)
    hsh hky hqe hrs hq0 (by rw [hkout]; rfl) hkc (fun i _ => PolyTab.fits _ _) (by show _ ≤ Wd; omega)
    (by show 2 * QE < 2 ^ Wd; omega) hrec hrc
  refine Hs.mono hc' (by rw [hs]; have := Nat.mul_le_mul_left (100 * 2 ^ (x.r.c.n - x.r.p.k)) (show
    PolyTab.width (tabCallTab x) + 10 ≤ wb + 10 by omega); omega) ?_
  rintro b ⟨b1, b2, b3, b4⟩
  refine ⟨?_, b2, b3, b4⟩
  rw [b1, recsOf]
  congr 1
  rw [show printerOrder (x.r.c.n - x.r.p.k) = printerOrder (tabCallTab x).s by rw [hs]]
  apply List.map_congr_left
  intro i _
  exact CellTablesValue.recOf_tabCall x QE res hres hmom i

end NearCubicGates.Close.CounterMachine.CellTablesProg
