import Proof.Gates.CounterAsm.Tail
import Proof.Gates.CounterMachine.TabCallDock
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (ratWord outputWord)
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.Expand.PolyTab (idealStart)

/-! ## Streams kept by a step -/

/-- Stream `i` has the same content and head in `σ` and `τ`. -/
def Keep {ns nr : ℕ} (σ τ : WState ns nr) (i : Fin (ns + 1)) : Prop := τ.st i = σ.st i ∧ τ.sh i = σ.sh i

theorem Keep.trans {ns nr : ℕ} {σ τ ρ : WState ns nr} {i : Fin (ns + 1)} (h1 : Keep σ τ i) (h2 : Keep τ ρ i) :
    Keep σ ρ i := ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem keep_seth {ns nr : ℕ} (σ : WState ns nr) (i j : Fin (ns + 1)) (x : ℕ) (h : i ≠ j) : Keep σ (σ.seth j x) i :=
  ⟨rfl, by simp [Function.update_apply, h]⟩

section Prog
variable (pD pK pO : Program)

/-- The stream count of the counter's layout. -/
abbrev NSc : ℕ := NS pD.tapeCount pK.tapeCount pO.tapeCount

def sDO : Fin (NSc pD pK pO + 1) := dmap pD.tapeCount pK.tapeCount pO.tapeCount pD.outputTape
def sKIN : Fin (NSc pD pK pO + 1) := kmap pD.tapeCount pK.tapeCount pO.tapeCount (tape0 pK)
def sKO : Fin (NSc pD pK pO + 1) := kmap pD.tapeCount pK.tapeCount pO.tapeCount pK.outputTape
def sOIN : Fin (NSc pD pK pO + 1) := omap pD.tapeCount pK.tapeCount pO.tapeCount (tape0 pO)
def PP : Fin 12 ↪ Fin (NSc pD pK pO + 1) := P pD.tapeCount pK.tapeCount pO.tapeCount pO.outputTape
def sOUT : Fin (NSc pD pK pO + 1) := OUT pD.tapeCount pK.tapeCount pO.tapeCount
def sLD : Fin (NSc pD pK pO + 1) := LD pD.tapeCount pK.tapeCount pO.tapeCount
def sLK : Fin (NSc pD pK pO + 1) := LK pD.tapeCount pK.tapeCount pO.tapeCount
def sLO : Fin (NSc pD pK pO + 1) := LO pD.tapeCount pK.tapeCount pO.tapeCount

theorem sDO_val : (sDO pD pK pO).val = 14 + pD.outputTape.val := by
  unfold sDO; rw [dmap_val, if_neg pD.outputFresh]
theorem sKIN_val : (sKIN pD pK pO).val = 14 + pD.tapeCount := by simp [sKIN, tape0]
theorem sKO_val : (sKO pD pK pO).val = 14 + pD.tapeCount + pK.outputTape.val := by simp [sKO]
theorem sOIN_val : (sOIN pD pK pO).val = 14 + pD.tapeCount + pK.tapeCount := by simp [sOIN, tape0]
theorem sOUT_val : (sOUT pD pK pO).val = 1 := rfl
theorem sLD_val : (sLD pD pK pO).val = 12 := rfl
theorem sLK_val : (sLK pD pK pO).val = 13 := rfl
theorem sLO_val : (sLO pD pK pO).val = 14 := rfl
theorem PP_zero : PP pD pK pO 0 = sOUT pD pK pO := P_zero _ _ _ _
theorem PP_four : PP pD pK pO 4 = omap pD.tapeCount pK.tapeCount pO.tapeCount pO.outputTape := P_four _ _ _ _
theorem PP_val (i : Fin 12) (hi : i.val ≠ 4) : (PP pD pK pO i).val = pv i := by
  unfold PP; rw [P_val, if_neg hi]

theorem dmap_zero : dmap pD.tapeCount pK.tapeCount pO.tapeCount (tape0 pD) = 0 := by
  apply Fin.ext; rw [dmap_val]; simp [tape0]

theorem notD (i : Fin (NSc pD pK pO + 1)) (h0 : i.val ≠ 0) (h : i.val ≤ 14 ∨ 14 + pD.tapeCount ≤ i.val) :
    ∀ j, dmap pD.tapeCount pK.tapeCount pO.tapeCount j ≠ i := by
  intro j hj; have h1 := congrArg Fin.val hj; have := j.isLt
  by_cases hj0 : j.val = 0
  · simp only [dmap_val, hj0, if_true] at h1; omega
  · simp only [dmap_val, hj0, if_false] at h1; omega

theorem notK (i : Fin (NSc pD pK pO + 1)) (h : i.val < 14 + pD.tapeCount ∨ 14 + pD.tapeCount + pK.tapeCount ≤ i.val) :
    ∀ j, kmap pD.tapeCount pK.tapeCount pO.tapeCount j ≠ i := by
  intro j hj; have := congrArg Fin.val hj; rw [kmap_val] at this; have := j.isLt; omega

theorem notO (i : Fin (NSc pD pK pO + 1)) (h : i.val < 14 + pD.tapeCount + pK.tapeCount) :
    ∀ j, omap pD.tapeCount pK.tapeCount pO.tapeCount j ≠ i := by
  intro j hj; have := congrArg Fin.val hj; rw [omap_val] at this; omega

/-- The final-answer branch: copy `outputWord v` to the output stream. -/
def br0 : WMX (NSc pD pK pO) 64 :=
  .seq (WMX.fwd (sDO pD pK pO)) (.wm (natLoop (sDO pD pK pO) scD kC (emitC (sOUT pD pK pO) opU)))

/-- The cell branch. -/
noncomputable def br1 (cT : ℕ) : WMX (NSc pD pK pO) 64 :=
  .seq (WMX.fwd (sDO pD pK pO)) (.seq (.wm (inK (sDO pD pK pO) (sKIN pD pK pO) (sOIN pD pK pO)))
  (.seq (WMX.machZ pK.machine (kmap pD.tapeCount pK.tapeCount pO.tapeCount) (sLK pD pK pO))
  (.seq (.wm (inO (sKO pD pK pO) (sOIN pD pK pO)))
  (.seq (WMX.machZ pO.machine (omap pD.tapeCount pK.tapeCount pO.tapeCount) (sLO pD pK pO))
  (tail cT (PP pD pK pO))))))

/-- The dispatch and two steps on its answer. -/
noncomputable def frontP : WMX (NSc pD pK pO) 64 :=
  .seq (WMX.machZ pD.machine (dmap pD.tapeCount pK.tapeCount pO.tapeCount) (sLD pD pK pO))
  (.seq (WMX.fwd (sDO pD pK pO)) (WMX.fwd (sDO pD pK pO)))

/-- **The counter program.** -/
noncomputable def ctrP (cT : ℕ) : WMX (NSc pD pK pO) 64 :=
  .seq (frontP pD pK pO) (.ifs (sDO pD pK pO) (br1 pD pK pO cT) (br0 pD pK pO))

end Prog

/-! ## The cost classes of the two paths -/

def zeroCost (bd L : ℕ) : ℕ := 2 * bd + 30 * L + 20
def cellCost (bd bk bo L F n cT : ℕ) : ℕ :=
  2 * bd + 2 * bk + 2 * bo + inKCost L n + 400 * (L + F) + tailCost cT n + 400
def cellCap (L F n cT : ℕ) : ℕ := 8 * L + 4 * F + 2 ^ (natBitLength n + 1) + 100 * (n + kOf cT n + cT + 10) ^ 2 + 20

/-! ## The dispatch and the branch test -/

section Runs
variable {RD RK RO : Type} {iD oD : RD → List Bool} {bD : RD → ℕ} {iK oK : RK → List Bool} {bK : RK → ℕ}
  {iO oO : RO → List Bool} {bO : RO → ℕ}

theorem front_run (fD : WordFunction RD iD oD bD) (pK pO : Program) (rd : RD)
    (lens : Fin (NSc fD.program pK pO + 1) → ℕ) (hLD : lens (sLD fD.program pK pO) = bD rd)
    (hlz : ∀ i, i ≠ sLD fD.program pK pO → i ≠ sLK fD.program pK pO → i ≠ sLO fD.program pK pO → lens i = 0)
    (cap : ℕ) :
    ∃ σ : WState (NSc fD.program pK pO) 64,
      WXExec cap (frontP fD.program pK pO) (idealStart _ 64 (iD rd) lens) σ (2 * bD rd + 2 + 1 + (1 + 1 + 1)) ∧
      σ.st (sDO fD.program pK pO) = oD rd ∧ σ.sh (sDO fD.program pK pO) = 2 ∧ σ.val = (fun _ => 0) ∧
      ∀ i, i.val ≠ 0 → (i.val ≤ 14 ∨ 14 + fD.program.tapeCount ≤ i.val) →
        σ.st i = List.replicate (lens i) false ∧ σ.sh i = 0 := by
  set σ0 := idealStart (NSc fD.program pK pO) 64 (iD rd) lens with hσ0
  have hdo := fD.program.outputFresh
  have hblank : ∀ j, j ≠ tape0 fD.program → σ0.st (dmap fD.program.tapeCount pK.tapeCount pO.tapeCount j) = [] := by
    intro j hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hv : (dmap fD.program.tapeCount pK.tapeCount pO.tapeCount j).val = 14 + j.val := by rw [dmap_val, if_neg hj0]
    have hz : lens (dmap fD.program.tapeCount pK.tapeCount pO.tapeCount j) = 0 := by
      apply hlz <;> intro h <;> have := congrArg Fin.val h <;> rw [hv] at this <;>
        simp [sLD_val, sLK_val, sLO_val] at this <;> omega
    simp only [hσ0, idealStart]; rw [if_neg (by rw [hv]; omega), hz]; rfl
  obtain ⟨τ, e1, hout, hsh, hoth, hval⟩ := wfDock_exact fD rd cap (dmap fD.program.tapeCount pK.tapeCount pO.tapeCount)
    (dmap_inj _ _ _) (sLD fD.program pK pO) (notD fD.program pK pO _ (by rw [sLD_val]; omega) (by rw [sLD_val]; omega)) σ0
    (by rw [dmap_zero]; simp [hσ0, idealStart]) hblank (fun _ => rfl) (bD rd)
    (by simp only [hσ0, idealStart]; rw [if_neg (by rw [sLD_val]; omega), hLD]) rfl le_rfl
  have e2 := WXExec.fwd (cap := cap) (sDO fD.program pK pO) τ
  have e3 := WXExec.fwd (cap := cap) (sDO fD.program pK pO) (τ.seth (sDO fD.program pK pO) (τ.sh (sDO fD.program pK pO) + 1))
  refine ⟨_, WXExec.seq e1 (WXExec.seq e2 e3), ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]; exact hout
  · simp; exact hsh _
  · simp only [WState.seth_val]; rw [hval]; rfl
  · intro i h0 hr
    have hD : i ≠ sDO fD.program pK pO := fun h => by
      have := congrArg Fin.val h; rw [sDO_val] at this; have := fD.program.outputTape.isLt; omega
    have k1 := hoth i (notD fD.program pK pO i h0 hr)
    simp only [WState.seth_st, WState.seth_sh, Function.update_apply, if_neg hD]
    refine ⟨?_, ?_⟩
    · rw [k1.1]; simp only [hσ0, idealStart]; rw [if_neg h0]
    · rw [k1.2]; rfl

theorem bit_one (u : List Bool) : readTapeBit (natWord 1 ++ u) 2 = true := by rw [natWord_one]; rfl
theorem bit_zero (u : List Bool) : readTapeBit (natWord 0 ++ u) 2 = false := by rw [natWord_zero]; rfl

/-- **The final-answer path.** -/
theorem zero_run (fD : WordFunction RD iD oD bD) (pK pO : Program) (rd : RD) (cT : ℕ) (vs : List ℕ)
    (hD : oD rd = natWord 0 ++ vs.flatMap natWord) (lens : Fin (NSc fD.program pK pO + 1) → ℕ)
    (hLD : lens (sLD fD.program pK pO) = bD rd)
    (hlz : ∀ i, i ≠ sLD fD.program pK pO → i ≠ sLK fD.program pK pO → i ≠ sLO fD.program pK pO → lens i = 0)
    (cap : ℕ) (hcap : 2 * (vs.flatMap natWord).length + 2 ≤ cap) :
    ∃ τ : WState (NSc fD.program pK pO) 64, WXExec cap (ctrP fD.program pK pO cT) (idealStart _ 64 (iD rd) lens) τ
      (zeroCost (bD rd) (vs.flatMap natWord).length) ∧ τ.st (sOUT fD.program pK pO) = vs.flatMap natWord := by
  obtain ⟨σ, e1, hst, hsh, hval, hrest⟩ := front_run fD pK pO rd lens hLD hlz cap
  have hOUT := hrest (sOUT fD.program pK pO) (by rw [sOUT_val]; omega) (by rw [sOUT_val]; omega)
  have hlO : lens (sOUT fD.program pK pO) = 0 := hlz _ (by intro h; have := congrArg Fin.val h; simp [sOUT_val, sLD_val] at this)
    (by intro h; have := congrArg Fin.val h; simp [sOUT_val, sLK_val] at this)
    (by intro h; have := congrArg Fin.val h; simp [sOUT_val, sLO_val] at this)
  rw [hlO] at hOUT
  have hDO : sDO fD.program pK pO ≠ sOUT fD.program pK pO := by
    intro h; have := congrArg Fin.val h; rw [sDO_val, sOUT_val] at this; omega
  have e2 := WXExec.fwd (cap := cap) (sDO fD.program pK pO) σ
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = σ.seth (sDO fD.program pK pO) (σ.sh (sDO fD.program pK pO) + 1) := ⟨_, rfl⟩
  rw [← hσ1] at e2
  have e3 := natLoop_spec cap (src := sDO fD.program pK pO) (dst := sOUT fD.program pK pO) (OP := opU) (SC := scD) hDO (by decide)
    (K := kC) (by decide) (by decide) (emits_raw cap) (d := 1) (fun _ => by simp) [] rfl vs (natWord 0) σ1
    (by rw [hσ1]; simp [hst, hD]) (by rw [hσ1]; simp [hsh]; rfl)
    (by rw [hσ1]; simp [Function.update_apply, Ne.symm hDO, hOUT.1, hOUT.2])
    (by rw [hσ1]; simp [hval]) (by rw [hσ1]; simp only [WState.seth_val, hval]; omega)
    (by rw [hσ1]; simp only [WState.seth_val, hval]; omega) (by omega)
  have hb : wbit σ (sDO fD.program pK pO) = false := by unfold wbit; rw [hst, hsh, hD]; exact bit_zero _
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.ifsF hb (WXExec.seq e2 (WXExec.wm e3)))) ?_, ?_⟩
  · unfold zeroCost; omega
  · rw [adv_st_dst, hσ1]; simp [Function.update_apply, Ne.symm hDO, hOUT.1]

end Runs

end NearCubicGates.Close.CounterAsm
