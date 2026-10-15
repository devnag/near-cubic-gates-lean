import Proof.Gates.Expand.PolyTabTailCost
import Proof.Gates.Expand.PolyTabOK3
import Proof.Gates.Expand.PolyTabFit

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Mono
variable {cap cap' : ℕ}

theorem tcap_mono {L N M K T : ℕ} {o : List Bool} (h : TCap cap L N M K T o) (hc : cap ≤ cap') :
    TCap cap' L N M K T o := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨a.trans hc, b.trans hc, c.trans hc, d.trans hc⟩

theorem stepOK_mono {W s k : ℕ} {xs : List ℕ} {p c : ℕ} {o : Occ} {tf : List (List ℤ)} {M : ℕ}
    (h : StepOK cap W s k xs p c o tf M) (hc : cap ≤ cap') : StepOK cap' W s k xs p c o tf M :=
  { h with
    cap1 := h.cap1.trans hc
    capK := h.capK.trans hc
    capE := h.capE.trans hc
    capEO := h.capEO.trans hc
    capT := tcap_mono h.capT hc
    capC := h.capC.trans hc
    capR := h.capR.trans hc }

theorem monoOK_mono {W s k Wd CS B : ℕ} {xs : List ℕ} {p c : ℕ} {os : List Occ} {out : List Bool} {g : ℕ}
    (h : MonoOK cap W s k Wd CS B xs p c os out g) (hc : cap ≤ cap') : MonoOK cap' W s k Wd CS B xs p c os out g :=
  { h with
    cap0 := h.cap0.trans hc
    step := fun i hi => stepOK_mono (h.step i hi) hc
    capL := h.capL.trans hc
    hBc := h.hBc.trans hc
    capS := h.capS.trans hc
    capO := h.capO.trans hc }

theorem pointOK_mono {W s k Wd CS B CM : ℕ} {hs : List ℕ} {ts : List (List Occ × ℤ)} {out : List Bool} {g j : ℕ}
    (h : PointOK cap W s k Wd CS B CM hs ts out g j) (hc : cap ≤ cap') : PointOK cap' W s k Wd CS B CM hs ts out g j :=
  fun hj => ⟨(h hj).1, fun i hi => monoOK_mono ((h hj).2.1 i hi) hc, (h hj).2.2⟩

end Mono

/-- The cut part of the tail's cost. -/
noncomputable def cutCost (E : ExpandMachine) (r : TabReq) : ℕ :=
  cutMCost (Wk E r) r.s (hsK E r).length (tsK E r).length (xsK E r).length (CMk E r)
    (EquationRowCuts.stream (Wdk E r) (tabT E r).exactCuts).length ((r.s + 1) / 2) (Wdk E r)
    (tabT E r).exactCuts.length

/-- **PolyTab tail (4a).** The cut machine on the head's deliverable. -/
theorem cut_run (E : ExpandMachine) (a : WilliamsAlgorithm) (r : TabReq) (cap : ℕ)
    (σ : WState (NSx E.wf.program.tapeCount (Qa a)) NRk) (h : TailPre E a r cap σ) :
    Runs cap (cutM sZ rY (sP 0)) σ (cutCost E r) (fun τ =>
      τ.st (sP 0) = frame (EquationRowRaw.source (inp E r)) ∧ τ.sh (sP 0) = 0 ∧
      SameExcept σ τ (sP 0 :: cutIdx.map sZ) [rY 74]) := by
  have hs67 := s67 r
  have hWd := Wdk_succ E r
  have hWd1 : 1 ≤ Wdk E r := by nlinarith
  have hcapk := h.capK
  have hO : ∀ i, (sP (te := E.wf.program.tapeCount) (qa := Qa a) 0) ≠ sZ i := fun i => by
    have := i.isLt; polyTabNe
  have hcapd : capk E r = ((idx2 E r).map (monoCap E r)).sum + ((idx3 E r).map (stepCap E r)).sum + BBk E r +
      ((tsK E r).length * (2 * ((r.s + 1) * (Wk E r + 1)) + 1) + 2 * ((r.s + 1) * (Wk E r + 1)) + 2) +
      (xsK E r).length + ((hsK E r).length * (2 * (Wk E r + 1) + 1) + 2 * (Wk E r + 1) + 2) + 1 := rfl
  have hrun := cutM_spec (Z := sZ) (Y := rY) (tabT E r) cap (Wk E r) (Wdk E r) (CSk E r) (BBk E r) (CMk E r)
    (by omega) hWd hWd1 (sP 0) hO [] (fits_Wd E r) hs67 (capT E r) σ h.cut h.c56 h.c56h h.c57 h.c57h h.y100 h.y101
    h.y102 h.y103 (h.pBlank 0).1 (h.pBlank 0).2 h.y104 h.y108 h.y109 h.y105 h.y106 h.y107
    (fun j => pointOK_mono (pointOK_all E r j) hcapk)
    (by unfold tsK at hcapd; omega) (by unfold xsK tsK at hcapd; omega) (by unfold hsK at hcapd; omega) h.capS
  exact hrun.post fun τ hτ => ⟨hτ.1, hτ.2.1, hτ.2.2.2.2.2⟩

end NearCubicGates.Close.Expand.PolyTab
