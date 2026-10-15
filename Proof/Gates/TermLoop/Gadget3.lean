import Proof.Gates.TermLoop.Gadget2

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd model1 model2)
open NearCubicGates.Close.WorkerArith (TermFit termW1 termW2 termCost bud1 bud2 entryWord)
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

/-! ## Register facts -/

section Regs
variable (i : ℕ)

theorem vC_eq_v0 (r : Fin nrW) (h : r.val < 48) : vC D x bits pad B jk i r = v0 D x bits pad B jk i r := by
  simp only [vC, vF, Function.update_apply]
  rw [if_neg (fin_ne (by show r.val ≠ 71; omega)),
    if_neg (fin_ne (by show r.val ≠ 70; omega)),
    if_neg (fin_ne (by show r.val ≠ 69; omega)),
    if_neg (fin_ne (by show r.val ≠ 68; omega)),
    if_neg (fin_ne (by show r.val ≠ 67; omega)),
    if_neg (fin_ne (by show r.val ≠ 66; omega)),
    if_neg (fin_ne (by show r.val ≠ 55; omega)),
    if_neg (fin_ne (by show r.val ≠ 54; omega)),
    if_neg (fin_ne (by show r.val ≠ 53; omega)),
    if_neg (fin_ne (by show r.val ≠ 52; omega)),
    if_neg (fin_ne (by show r.val ≠ 51; omega)),
    if_neg (fin_ne (by show r.val ≠ 50; omega)),
    if_neg (fin_ne (by show r.val ≠ 49; omega)),
    if_neg (fin_ne (by show r.val ≠ 48; omega))]

theorem vC_ops (j : Fin 40) (h : j.val < 6) : vC D x bits pad B jk i (regE j) = 0 := by
  rw [vC_eq_v0 D x bits pad B jk i _ (by rw [regE_val]; omega)]; exact v0_ops D x bits pad B jk i j h

theorem vC_LT : vC D x bits pad B jk i rLT = 0 := by
  simp only [vC, Function.update_apply]
  rw [if_neg (fin_ne (by show (74 : ℕ) ≠ 71; omega)),
    if_neg (fin_ne (by show (74 : ℕ) ≠ 70; omega)),
    if_neg (fin_ne (by show (74 : ℕ) ≠ 69; omega)),
    if_neg (fin_ne (by show (74 : ℕ) ≠ 68; omega)),
    if_neg (fin_ne (by show (74 : ℕ) ≠ 67; omega)),
    if_neg (fin_ne (by show (74 : ℕ) ≠ 66; omega))]
  exact vF_ge D x bits pad B jk i rLT (by decide)

theorem regOK_vC : RegOK (P := P) x bits pad B (vC D x bits pad B jk i) := by
  have a : ∀ j : Fin 40, vC D x bits pad B jk i (regE j) = v0 D x bits pad B jk i (regE j) :=
    fun j => vC_eq_v0 D x bits pad B jk i _ (by rw [regE_val]; have := j.isLt; omega)
  have b : ∀ j : Fin 40, v0 D x bits pad B jk i (regE j) = (LoopEntry D N x bits pad B jk).val (regE j) := fun j => by
    simp only [v0]
    rw [Function.update_of_ne (fin_ne (by rw [regE_val, rLC_val]; have := j.isLt; omega)),
      Function.update_of_ne (fin_ne (by rw [regE_val, rA_val]; have := j.isLt; omega))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a, b, loopEntry_val]; simp
  · rw [a, b, loopEntry_val]; simp
  · rw [a, b, loopEntry_val]; simp
  · intro j h; rw [a]; exact v0_small D x bits pad B jk i j h

end Regs

theorem regOK_update (v : Fin nrW → ℕ) (hR : RegOK (P := P) x bits pad B v) (j : Fin 40) (hj : j.val < 6) (a : ℕ) :
    RegOK (P := P) x bits pad B (Function.update v (regE j) a) := by
  have ne : ∀ m : Fin 40, 6 ≤ m.val → regE m ≠ regE j := fun m hm => regE_ne m j (fun e => by rw [e] at hm; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (ne 6 (by decide))]; exact hR.r6
  · rw [Function.update_of_ne (ne 7 (by decide))]; exact hR.r7
  · rw [Function.update_of_ne (ne 8 (by decide))]; exact hR.r8
  · intro m hm; rw [Function.update_of_ne (ne m (by omega))]; exact hR.z m hm

theorem zeroOps_update (v : Fin nrW → ℕ) (j : Fin 40) (hj : j.val < 6) (a : ℕ) :
    zeroOps (Function.update v (regE j) a) = zeroOps v := by
  funext r
  unfold zeroOps
  simp only [Function.update_apply]
  by_cases h : r = regE j
  · subst h
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [h]

theorem zeroOps_self (v : Fin nrW → ℕ) (h : ∀ j : Fin 40, j.val < 6 → v (regE j) = 0) : zeroOps v = v := by
  funext r
  unfold zeroOps
  simp only [Function.update_apply]
  split_ifs with h5 h4 h3 h2 h1 h0
  · subst h5; exact (h 5 (by decide)).symm
  · subst h4; exact (h 4 (by decide)).symm
  · subst h3; exact (h 3 (by decide)).symm
  · subst h2; exact (h 2 (by decide)).symm
  · subst h1; exact (h 1 (by decide)).symm
  · subst h0; exact (h 0 (by decide)).symm
  · rfl

theorem zeroOps_loadL (v : Fin nrW → ℕ) (k : Fin 3) (n : Fin 40) (hn : n.val ≤ 3) :
    zeroOps (loadL v k n hn) = zeroOps v := by
  unfold loadL
  rw [zeroOps_update _ _ (by simp; omega), zeroOps_update _ _ (by simp; omega), zeroOps_update _ _ (by omega)]

theorem zeroOps_loadH (v : Fin nrW → ℕ) (n : Fin 40) (hn : n.val < 6) : zeroOps (loadH v n) = zeroOps v := by
  unfold loadH; rw [zeroOps_update _ _ hn]

theorem regOK_loadL (v : Fin nrW → ℕ) (hR : RegOK (P := P) x bits pad B v) (k : Fin 3) (n : Fin 40) (hn : n.val ≤ 3) :
    RegOK (P := P) x bits pad B (loadL v k n hn) := by
  unfold loadL
  exact regOK_update x bits pad B _ (regOK_update x bits pad B _ (regOK_update x bits pad B v hR _ (by omega) _) _
    (by simp; omega) _) _ (by simp; omega) _

theorem regOK_loadH (v : Fin nrW → ℕ) (hR : RegOK (P := P) x bits pad B v) (n : Fin 40) (hn : n.val < 6) :
    RegOK (P := P) x bits pad B (loadH v n) := regOK_update x bits pad B v hR n hn _

end

end NearCubicGates.Close.TermLoop
