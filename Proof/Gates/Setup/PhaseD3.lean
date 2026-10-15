import Proof.Gates.Setup.PhaseD2

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_nil)

noncomputable section

/-! ## Transcoding the circuit fields -/

/-- The transcoder's register file: `A 6 = R 6` (`q`), `A 13 = R 7` (`CW`'s output position), the rest `80 … 95`. -/
def aT : Fin 18 ↪ Fin nrW :=
  ⟨![80, 81, 82, 83, 84, 85, 6, 86, 87, 88, 89, 90, 91, 7, 92, 93, 94, 95], by decide⟩

/-- The transcoder's count register. -/
abbrev cA : Fin nrW := 79

/-- Transcode, then rewind `CW` (bound copied to `96`). -/
def trW {ns : ℕ} (WT CW : Fin (ns + 1)) : WMX ns nrW :=
  .wm (.seq (Codec.transcodeW WT CW aT cA) (.seq (Codec.dupR 7 96 dS) (WM.rewind CW 96)))

theorem aT_six : aT 6 = regE 6 := rfl
theorem aT_thirteen : aT 13 = (7 : Fin nrW) := rfl

theorem trW_exec {ns cap : ℕ} (WT CW : Fin (ns + 1)) (hWC : WT ≠ CW) (q m p0 : ℕ) (w : List Bool)
    (σ : WState ns nrW) (hw : σ.st WT = w) (hp : σ.sh WT = p0) (hc : σ.st CW = []) (hch : σ.sh CW = 0)
    (hq : σ.val (regE 6) = q) (hz : ∀ i : Fin 18, i ≠ 6 → σ.val (aT i) = 0) (hm : σ.val cA = m)
    (z96 : σ.val 96 = 0) (zd : σ.val dS = 0) (S : ℕ) (hmS : m ≤ S) (hqS : q ≤ S) (hwS : w.length ≤ S)
    (hcwS : (Codec.cwPrefix (Codec.circAt w q p0) m).length ≤ S) (hcap : 20 * (S + 2) ≤ cap) :
    WXExec cap (trW WT CW) σ
      ((((σ.sets CW (Codec.cwPrefix (Codec.circAt w q p0) m)).seth WT (Codec.circPos w q p0 m)).setv 7
        (Codec.cwPrefix (Codec.circAt w q p0) m).length).setv cA 0) (30000 * (S + 1) ^ 5) := by
  set cw := Codec.cwPrefix (Codec.circAt w q p0) m with hcw
  have hz7 : σ.val 7 = 0 := hz 13 (by decide)
  have hlen : ((List.range m).flatMap fun j => Interfaces.circuitWord (Codec.circAt w q p0 j)).length * 2 = cw.length := by
    rw [hcw, ← Codec.marks_emitted_cw, Codec.marks_length, Codec.emitted_cw]; ring
  have hnb : natBitLength q ≤ q + 1 := Codec.natBitLength_le_succ q
  have e1 := Codec.transcodeW_spec cap WT CW hWC aT cA (fun i h => by
      have : (aT i).val ≠ 79 := by fin_cases i <;> decide
      exact this (by rw [h]; rfl))
    q m (20000 * (S + 1) ^ 4) σ (by rw [aT_six]; exact hq) (fun i h6 _ => hz i h6) (by rw [hc, hch]; rfl) hm
    (by omega) (by rw [hw]; omega)
    (by rw [hw, hp, aT_thirteen, hz7]; omega)
    (fun j _ => by rw [hw]; exact WorkerArith.circuitWCost_field_le q w _ S hqS hwS)
  rw [hw, hp] at e1
  set σ1 := (appendO (σ.seth WT (Codec.circPos w q p0 m)) CW (aT 13) cw).setv cA 0 with hσ1
  have v1 : σ1.val 7 = cw.length ∧ σ1.val 96 = 0 ∧ σ1.val dS = 0 := by
    simp (config := { decide := true }) [hσ1, aT_thirteen, Function.update_apply, hz7, z96, zd]
  have e2 := Codec.dupR_spec cap 7 96 dS (by decide) (by decide) (by decide) σ1 v1.2.2 (by rw [v1.1, v1.2.1]; omega)
  set σ2 := σ1.setv 96 (σ1.val 96 + σ1.val 7) with hσ2
  have v2 : σ2.val 96 = cw.length := by simp [hσ2, v1.1, v1.2.1]
  have e3 := WireExponent3_5.FinalPass.Tm.wrewind_spec (cap := cap) CW 96 cw.length σ2 v2 (by omega)
  refine WXExec.cast cap (WXExec.wm (WExec.seq e1 (WExec.seq e2 e3))) ?_ ?_
  · clear e1 e2 e3
    apply WState.eq
    · funext i
      simp only [hσ2, hσ1, WState.seth_sh, WState.setv_sh, WState.sets_sh, appendO_sh, Function.update_apply]
      split_ifs <;> simp_all
    · funext i
      simp only [hσ2, hσ1, WState.seth_st, WState.setv_st, WState.sets_st, appendO_st, Function.update_apply]
      split_ifs <;> simp_all
    · funext r
      simp only [hσ2, hσ1, WState.seth_val, WState.setv_val, WState.sets_val, appendO_val, Function.update_apply,
        aT_thirteen]
      split_ifs <;> simp_all (config := { decide := true })
    · rfl
  · have h4 : (S + 1) ^ 4 ≤ (S + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : S + 1 ≤ (S + 1) ^ 5 := by
      calc S + 1 = (S + 1) ^ 1 := (pow_one _).symm
        _ ≤ (S + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h5 : m * (20000 * (S + 1) ^ 4 + 4) ≤ (S + 1) * (20000 * (S + 1) ^ 4 + 4) := Nat.mul_le_mul_right _ (by omega)
    have h6 : (S + 1) * (20000 * (S + 1) ^ 4 + 4) = 20000 * (S + 1) ^ 5 + 4 * (S + 1) := by ring
    rw [v1.1]
    omega

/-! ## The supports record's length -/

/-- `R 8 := ` the marked length of the supports record (scan with `97`, `98` the scratch output position). -/
def rowsW {ns : ℕ} (SUP : Fin (ns + 1)) : WMX ns nrW :=
  .wm (.seq (Recovery.HTParts.pairLoop SUP 97 (fun _ => WM.skip) (fun _ => WM.skip))
    (.seq (Codec.dupR 97 8 dS) (WM.rewind SUP 97)))

theorem rowsW_exec {ns cap : ℕ} (SUP SP : Fin (ns + 1)) (hSP : SUP ≠ SP) (sw : List Bool) (σ : WState ns nrW)
    (hst : σ.st SUP = RepairOrdinary.frame sw) (hsh : σ.sh SUP = 0) (hd : σ.sh SP = (σ.st SP).length)
    (z97 : σ.val 97 = 0) (z98 : σ.val 98 = 0) (z8 : σ.val 8 = 0) (zd : σ.val dS = 0) (hcap : 4 * sw.length + 4 ≤ cap) :
    WXExec cap (rowsW SUP) σ (σ.setv 8 (2 * sw.length)) (100 * (sw.length + 1)) := by
  have e1 := Recovery.HTParts.pairLoop_spec (cap := cap) (src := SUP) (dst := SP) (OP := (98 : Fin nrW))
    (SC := (97 : Fin nrW)) hSP (by decide) (Recovery.HTParts.emits_none cap) (Recovery.HTParts.emits_none cap) [false]
    rfl sw [] σ (by rw [hst, Codec.frame_eq_marks]; rfl) (by rw [hsh]; rfl) hd (by simp [z98]) (by rw [z97]; omega)
  have hfm : (sw.flatMap fun _ => ([] : List Bool) ++ []) = [] := by simp
  rw [hfm] at e1
  unfold Recovery.HTParts.adv at e1
  rw [appendO_nil, hsh, z97] at e1
  simp only [Nat.zero_add] at e1
  set σ1 := (σ.seth SUP (2 * sw.length)).setv 97 (2 * sw.length) with hσ1
  have e2 := Codec.dupR_spec cap 97 8 dS (by decide) (by decide) (by decide) σ1
    (by simp (config := { decide := true }) [hσ1, Function.update_apply, zd])
    (by simp (config := { decide := true }) [hσ1, Function.update_apply, z8]; omega)
  set σ2 := σ1.setv 8 (σ1.val 8 + σ1.val 97) with hσ2
  have v2 : σ2.val 97 = 2 * sw.length := by simp (config := { decide := true }) [hσ2, hσ1, Function.update_apply]
  have e3 := WireExponent3_5.FinalPass.Tm.wrewind_spec (cap := cap) SUP 97 (2 * sw.length) σ2 v2 (by omega)
  refine WXExec.cast cap (WXExec.wm (WExec.seq e1 (WExec.seq e2 e3))) ?_ ?_
  · clear e1 e2 e3
    apply WState.eq
    · funext i
      simp only [hσ2, hσ1, WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · funext r
      simp only [hσ2, hσ1, WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all (config := { decide := true })
    · rfl
  · have : σ1.val 97 = 2 * sw.length := by simp [hσ1]
    rw [this]
    omega

/-! ## The I-stream header -/

/-- The header file: `H 0 … H 4 = q, M, b, rb, cl` (`R 6`, `41`, `rBs = 111`, `42`, `43`), `H 5 = R 9`, scratch
`100 … 107`. The header's `N` field carries the precision base `b = ν^{lenRoot+1}` (`L_ν = b^{10}`, paper v2 §11.4: the
guard `γ/L_ν < ε_q`; the verdict machine's test `γ < ε·b^{10}`). -/
def hF : Fin 14 ↪ Fin nrW :=
  ⟨![6, 41, 111, 42, 43, 9, 100, 101, 102, 103, 104, 105, 106, 107], by decide⟩

/-- The header program. -/
def hdW {ns : ℕ} (VI : Fin (ns + 1)) : WMX ns nrW := .wm (WorkerArith.headerW VI hF)

theorem hdW_exec {ns cap : ℕ} (VI : Fin (ns + 1)) (σ : WState ns nrW) (S : ℕ) (hVI : σ.sh VI = (σ.st VI).length)
    (hz : ∀ r ∈ ([100, 101, 102, 103, 104, 105, 106, 107] : List (Fin nrW)), σ.val r = 0)
    (hq : σ.val (regE 6) ≤ S) (hN : σ.val rBs ≤ S) (hrb : σ.val rRB ≤ S) (hcl : σ.val rCL ≤ S)
    (hM : 10 * σ.val rM ≤ S) (h9 : σ.val 9 + 100 * (S + 1) ≤ cap) :
    WXExec cap (hdW VI) σ (appendO σ VI 9 (marks (WorkerArith.headerWord (σ.val (regE 6)) (σ.val rM) (σ.val rBs)
      (σ.val rRB) (σ.val rCL)))) (WorkerArith.headerCost S) := by
  have z : ∀ r ∈ ([100, 101, 102, 103, 104, 105, 106, 107] : List (Fin nrW)), σ.val r = 0 := hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at z
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7⟩ := z
  exact WXExec.wm (WorkerArith.headerW_spec cap VI hF S σ hVI (fun i hi => by
      have : i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    hq hN hrb hcl hM h9)

end

end NearCubicGates.Close.Setup
