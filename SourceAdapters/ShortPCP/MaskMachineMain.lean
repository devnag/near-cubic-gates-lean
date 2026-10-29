import SourceAdapters.ShortPCP.MaskMachineRun
import Proof.Gates.Cells.Run

/-!
# The mask machine: reading `(f, n)` and the whole run

The input of the cell program is `1^s 0 ++ natWord f ++ natWord n` (`UnaryPrefix.prefixWord` of `maskWord (f, n)`,
`Field6.lean`): the prelude sets the constants, skips the unary width prefix and reads `f`, `n` with the released
reader `rdNatI` (L `Cells/Kit.lean`); phase B (`MaskMachineRun`) prints `listWord frame S` for the multiset
`S = masksOf (r0f f) f n K1 b1` of Step 3 (proof of `thm:short-pcp-ours`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5 NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP

/-! ## The prelude -/

theorem ip_env (a : Ds) (k : ℕ) : ({ a with ip := k }).env = a.env := rfl

def initM : Sc := .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.op (.inc v2)))

/-- Skip the unary prefix `1^s 0`. -/
def skipP : Sc := .seq (.op (.rdI t0)) (.loop (.eq t0 v1) (.op (.rdI t0)))

def preA : Sc :=
  .seq initM (.seq skipP (.seq rdNatI (.seq (.op (.copy vF t3)) (.seq rdNatI (.op (.copy vN t3))))))

/-- **The mask machine** (for the constants `K1`, `b1` of Step 3). -/
def maskP (K1 b1 : ℕ) : Sc := .seq preA (phaseB K1 b1)

/-- What the prelude leaves. -/
structure PreOK (b : Ds) (f n : ℕ) : Prop where
  F : b.env vF = f
  N : b.env vN = n
  cst : Cst b
  out : b.out = []
  ram : b.ram sT = []
  rc : b.rc sT = 0

def preCost (s f n : ℕ) : ℕ := 3 * s + 30 * natBitLength f + 30 * natBitLength n + 100

theorem drop_prefix (s : ℕ) (L : List Bool) : (List.replicate s true ++ false :: L).drop (s + 1) = L := by
  induction s with
  | zero => rfl
  | succ s ih => simpa [List.replicate_succ] using ih

theorem bitOf_prefix_lt (s j : ℕ) (L : List Bool) (hj : j < s) :
    bitOf (List.replicate s true ++ false :: L) j = 1 := by
  unfold bitOf
  rw [List.getD_append _ _ _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem bitOf_prefix_eq (s : ℕ) (L : List Bool) : bitOf (List.replicate s true ++ false :: L) s = 0 := by
  unfold bitOf
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem preA_spec (C : Ctx) (s f n : ℕ) (hinp : C.inp = List.replicate s true ++ false :: (natWord f ++ natWord n))
    (hWf : natBitLength f + 2 ≤ C.Wd) (hWn : natBitLength n + 2 ≤ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C preA (a0 : Ds) (preCost s f n) (fun b => PreOK b f n) := by
  have h4 : 4 ≤ 2 ^ C.Wd := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  have hlen : C.inp.length = s + 1 + (natWord f).length + (natWord n).length := by
    rw [hinp]; simp; omega
  -- the constants
  let a1 : Ds := ((a0.set v1 1).set v2 1).set v2 2
  have ex1 : Ex C initM (a0 : Ds) a1 5 := by
    have e1 := OpEx.inc (C := C) v1 (a0 : Ds) (by simp [a0]; omega)
    have e2 := OpEx.inc (C := C) v2 ((a0 : Ds).set v1 1) (by norm_env; simp [a0]; omega)
    have e3 := OpEx.inc (C := C) v2 (((a0 : Ds).set v1 1).set v2 1) (by norm_env; omega)
    simp only [show (a0 : Ds).env v1 + 1 = 1 from rfl] at e1
    norm_env at e2 e3
    exact Ex.seq (Ex.op e1) (Ex.seq (Ex.op e2) (Ex.op e3))
  have c1 : Cst a1 := ⟨by simp [a1, a0, env_set]; decide, by simp [a1, env_set]; decide, by simp [a1]⟩
  -- the prefix
  let I : ℕ → Ds → Prop := fun j b => b.ip = j + 1 ∧ b.env t0 = bitOf C.inp j ∧ Cst b ∧ b.out = [] ∧
    b.ram = (a0 : Ds).ram ∧ b.rc = (a0 : Ds).rc
  have hloop : ∀ b, I 0 b → Hs C (.loop (.eq t0 v1) (.op (.rdI t0))) b (s * (1 + 2) + 2) (I s) := by
    refine Hs.loopN (c := .eq t0 v1) (show t0 ≠ v1 by decide) I s 1 ?_ ?_
    · intro j hj b ⟨b1, b2, b3, b4, b5, b6⟩
      refine ⟨by simp only [Cnd.eval, b2, b3.one, hinp, bitOf_prefix_lt s j _ hj]; rfl, ?_⟩
      refine Hs.mono (hs_rdI C t0 b (by rw [b1, hlen]; omega)) le_rfl ?_
      rintro d rfl
      refine ⟨by simp [b1], by simp [b1], ⟨?_, ?_, ?_⟩, b4, b5, b6⟩
      · rw [ip_env]; norm_env; exact b3.z
      · rw [ip_env]; norm_env; exact b3.one
      · rw [ip_env]; norm_env; exact b3.two
    · intro b ⟨_, b2, b3, _⟩
      simp only [Cnd.eval, b2, b3.one, hinp, bitOf_prefix_eq]; rfl
  have hskip : Hs C skipP a1 (3 * s + 4) (I s) := by
    refine Hs.mono (Hs.seq (hs_rdI C t0 a1 (by simp [a1, a0, hlen])) (fun b hb => hloop b ?_)) (by omega)
      (fun _ h => h)
    subst hb
    refine ⟨by simp [a1, a0], by simp [a1, a0], ⟨?_, ?_, ?_⟩, rfl, rfl, rfl⟩
    · rw [ip_env]; norm_env; exact c1.z
    · rw [ip_env]; norm_env; exact c1.one
    · rw [ip_env]; norm_env; exact c1.two
  -- reading f and n
  unfold preA
  refine Hs.mono (Hs.seq (t2 :=
    3 * s + 4 + (30 * natBitLength f + 30 + (1 + (30 * natBitLength n + 30 + 1 + 1) + 1) + 1) + 1)
    (⟨a1, 5, ex1, le_rfl, rfl⟩ : Hs C initM (a0 : Ds) 5 (· = a1)) (fun b hb => ?_))
    (by unfold preCost; omega) (fun _ h => h)
  subst hb
  refine Hs.seq (t2 := 30 * natBitLength f + 30 + (1 + (30 * natBitLength n + 30 + 1 + 1) + 1) + 1) hskip
    (fun b ⟨b1, b2, b3, b4, b5, b6⟩ => ?_)
  have hcw : C.inp.drop b.ip = natWord f ++ natWord n := by rw [b1, hinp, drop_prefix]
  refine Hs.seq (t2 := 1 + (30 * natBitLength n + 30 + 1 + 1) + 1) (rdNatI_spec b b3 f (natWord n) hcw hWf)
    (fun c ⟨c1, _, c3, c4, c5⟩ => ?_)
  simp only [Prod.mk.injEq] at c4
  have cc : Cst c := cst_fr b3 c5
  refine Hs.seq (t2 := 30 * natBitLength n + 30 + 1 + 1) (hs_copy C vF t3 c (by decide)) (fun d hd => ?_)
  subst hd
  have hcw2 : C.inp.drop (c.set vF (c.env t3)).ip = natWord n ++ [] := by
    simp only [DS.set_ip, c3, b1]
    rw [List.append_nil, hinp, ← List.drop_drop, drop_prefix, List.drop_left]
  have cc' : Cst (c.set vF (c.env t3)) := ⟨by norm_env; exact cc.z, by norm_env; exact cc.one, by norm_env; exact cc.two⟩
  refine Hs.seq (t2 := 1) (rdNatI_spec _ cc' n [] hcw2 hWn) (fun d ⟨d1, _, _, d4, d5⟩ => ?_)
  simp only [Prod.mk.injEq] at d4
  refine Hs.mono (hs_copy C vN t3 d (by decide)) le_rfl ?_
  rintro e rfl
  have dc : Cst d := cst_fr cc' d5
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · norm_env; rw [d5 vF (by decide)]; norm_env; exact c1
  · norm_env; exact d1
  · norm_env; exact dc.z
  · norm_env; exact dc.one
  · norm_env; exact dc.two
  · simp only [DS.set_out]; rw [d4.1]; simp only [DS.set_out]; rw [c4.1, b4]
  · simp only [DS.set_ram]; rw [d4.2.1]; simp only [DS.set_ram]; rw [c4.2.1, b5]; rfl
  · simp only [DS.set_rc]; rw [d4.2.2.1]; simp only [DS.set_rc]; rw [c4.2.2.1, b6]; rfl

/-! ## The whole run -/

/-- **The printed word is `listWord frame S`**: `|S| = 2^m·2^m = 4^m` (`masksOf_length`) and the framed masks in
the order of `masksOf` (`allBits_eq`). -/
theorem listWord_eq (K1 b1 f n : ℕ) :
    listWord RepairOrdinary.frame (masksOf (r0f f) f n K1 b1) =
      natWord (4 ^ mOf K1 b1 f n) ++ allBits (Amplified.modulus (mOf K1 b1 f n)) (mOf K1 b1 f n) (rOf f) := by
  unfold listWord
  have h := allBits_eq (r0f f) f n K1 b1
  simp only at h
  rw [masksOf_length]
  unfold mOf nOf rOf
  rw [h, ← mul_pow]
  rfl

theorem maskP_run (C : Ctx) (K1 b1 s f n : ℕ)
    (hinp : C.inp = List.replicate s true ++ false :: (natWord f ++ natWord n))
    (hWf : natBitLength f + 2 ≤ C.Wd) (hWn : natBitLength n + 2 ≤ C.Wd) (hW : 2 ≤ C.Wd)
    (hbig : wBig K1 b1 f n < 2 ^ C.Wd) :
    ∃ b k, Ex C (maskP K1 b1) (a0 : Ds) b k ∧
      b.out = listWord RepairOrdinary.frame (masksOf (r0f f) f n K1 b1) ∧
      k ≤ preCost s f n + phaseBCost K1 b1 f n + 1 := by
  obtain ⟨b, k1, ex1, hk1, hb⟩ := preA_spec C s f n hinp hWf hWn hW
  obtain ⟨d, ex2, fx2, -⟩ := phaseB_spec C b K1 b1 f n hb.F hb.N hb.cst hb.ram hb.rc hW hbig
  refine ⟨d, k1 + phaseBCost K1 b1 f n + 1, Ex.seq ex1 ex2, ?_, by omega⟩
  rw [fx2.out, hb.out, List.nil_append, listWord_eq]

end NearCubicGates.Adapters.ShortPCP.MaskMachine
