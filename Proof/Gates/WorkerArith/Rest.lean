import Proof.Gates.WorkerArith.SupplyDefs
import Proof.Gates.WorkerArith.RestFit
import Proof.Gates.WorkerArith.Envelope
import Proof.Gates.Setup.UniformSpec
import Proof.Gates.Setup.Growth

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.Setup NearCubicGates.Close.TermLoop
open NearCubicGates.Close.WorkerArith.WeakWorker NearCubicGates.Close.WorkerArith.WorkerBounds NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount)

/-- The padding of the guess word. -/
def padOf (Ca E0 Cq CM : ℕ) (N : ℕ) : ℕ :=
  N / 16 + 2 + Ca * (N + 1) ^ E0 * (2 + 2 * (N / 16) * (Cq * (N + 1) + 1)) + 10 * (CM * (N + 1))

theorem padOf_le (Ca E0 Cq CM N : ℕ) :
    padOf Ca E0 Cq CM N ≤ (2 + Ca * (2 + 2 * (Cq + 1)) + 10 * CM) * (N + 1) ^ (E0 + 2) := by
  unfold padOf
  have hN1 : 1 ≤ N + 1 := by omega
  have hX : 1 ≤ (N + 1) ^ E0 := Nat.one_le_pow _ _ hN1
  have h16 : N / 16 ≤ N + 1 := by omega
  have hp2 : (N + 1) ^ (E0 + 2) = (N + 1) ^ E0 * (N + 1) ^ 2 := by rw [pow_add]
  have h1 : N / 16 + 1 ≤ (N + 1) ^ (E0 + 2) := by
    rw [hp2]
    have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    calc N / 16 + 1 ≤ N + 1 := by omega
      _ ≤ (N + 1) ^ 2 := this
      _ = 1 * (N + 1) ^ 2 := by ring
      _ ≤ (N + 1) ^ E0 * (N + 1) ^ 2 := Nat.mul_le_mul_right _ hX
  have h2 : 2 + 2 * (N / 16) * (Cq * (N + 1) + 1) ≤ (2 + 2 * (Cq + 1)) * (N + 1) ^ 2 := by
    have a : (N / 16) * (Cq * (N + 1) + 1) ≤ (N + 1) * ((Cq + 1) * (N + 1)) :=
      Nat.mul_le_mul h16 (by nlinarith)
    have b : 2 ≤ 2 * (N + 1) ^ 2 := by have := Nat.one_le_pow 2 (N + 1) hN1; omega
    have e : (2 + 2 * (Cq + 1)) * (N + 1) ^ 2 = 2 * (N + 1) ^ 2 + 2 * ((N + 1) * ((Cq + 1) * (N + 1))) := by ring
    have e2 : 2 * (N / 16) * (Cq * (N + 1) + 1) = 2 * ((N / 16) * (Cq * (N + 1) + 1)) := by ring
    rw [e, e2]; omega
  have h3 : 10 * (CM * (N + 1)) ≤ 10 * CM * (N + 1) ^ (E0 + 2) := by
    rw [hp2]
    have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    calc 10 * (CM * (N + 1)) ≤ 10 * (CM * (1 * (N + 1) ^ 2)) := by
          apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
      _ ≤ 10 * (CM * ((N + 1) ^ E0 * (N + 1) ^ 2)) := by
          apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; exact Nat.mul_le_mul_right _ hX
      _ = _ := by ring
  have h4 : Ca * (N + 1) ^ E0 * (2 + 2 * (N / 16) * (Cq * (N + 1) + 1)) ≤
      Ca * (2 + 2 * (Cq + 1)) * (N + 1) ^ (E0 + 2) := by
    rw [hp2]
    calc Ca * (N + 1) ^ E0 * (2 + 2 * (N / 16) * (Cq * (N + 1) + 1))
        ≤ Ca * (N + 1) ^ E0 * ((2 + 2 * (Cq + 1)) * (N + 1) ^ 2) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have e : (2 + Ca * (2 + 2 * (Cq + 1)) + 10 * CM) * (N + 1) ^ (E0 + 2) =
      2 * (N + 1) ^ (E0 + 2) + Ca * (2 + 2 * (Cq + 1)) * (N + 1) ^ (E0 + 2) + 10 * CM * (N + 1) ^ (E0 + 2) := by ring
  rw [e]; omega

/-- **Everything `WeakWorkerOf` asks beyond the machines.** -/
theorem hrest_of (hCF : CircuitSizeFit) (hRF : RowSizeFit) (hSU : Setup.SetupSupply) :
    ∀ (s : GateSources) (P : ThreeQueryPCPP) (B1 B2 : ℕ) (ctr : Counter B1 B2) (η εT ω : ℚ)
      (hD : Counter.DenOK ctr), Counter.OutOK ctr → 0 < η → 0 < ω →
      ∃ d0 : ℕ, ∀ g : GateParams, d0 ≤ g.k + 1 →
        ∃ D : SetupData s P g, (∃ prog : WMX (nsW D) nrW, SetupSpec D prog) ∧
          ctr.program.program.tapeCount = D.tc ∧
          VmapFacts D (verdictMachine P.gamma εT) ∧
          WeakWorkerRest s P g ctr hD (Closure.budgetOf η) εT ω D (verdictMachine P.gamma εT) := by
  intro s P B1 B2 ctr η εT ω hD hO _hη _hω
  obtain ⟨E0, hU⟩ := hSU s P
  obtain ⟨onc, Kc, ec, hbud⟩ := budget_split ctr
  obtain ⟨Co, eo, hOo⟩ := hO
  obtain ⟨Cv, ev, hv⟩ := (verdictMachine P.gamma εT).cls
  refine ⟨30 * (E0 * (E0 + 2 + 1)) * (ec + ev + 1) + 2 * ev + 10, fun g hg => ?_⟩
  obtain ⟨Nc, hNc⟩ := width_unbounded s g onc
  obtain ⟨D, hprog, hDtc, hDN0, ⟨Ca, hCa⟩, hpadU⟩ := hU g ctr.program.program.tapeCount Nc
  obtain ⟨CM, hCM⟩ := gadgets_lin s g
  obtain ⟨Cq, hCq⟩ := qpoly s g 1
  obtain ⟨Ce, hCe⟩ := qpoly s g eo
  have hpad1 : ∀ N, N / 16 + 1 ≤ padOf Ca E0 Cq CM N := fun N => by unfold padOf; omega
  obtain ⟨Fs, hrejFs, haccFs, Cs, ons, hFs⟩ := hpadU (padOf Ca E0 Cq CM) (2 + Ca * (2 + 2 * (Cq + 1)) + 10 * CM)
    (E0 + 2) hpad1 (padOf_le Ca E0 Cq CM)
  obtain ⟨Bh, onh, hhot⟩ := hot_bound s g D.tc (Outer.apad s.mw (g.sv s) + 1)
  obtain ⟨A, onA, hA⟩ := fp_pe Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev
    (E0 * (E0 + 2 + 1)) ⟨Cs, ons, hFs⟩ (PE.of_all (C := CM) (fun N => by rw [pow_one]; exact hCM N))
    (PE.of_all (C := Ce) (fun N => by rw [pow_one]; exact hCe N))
  refine ⟨D, hprog, hDtc.symm, vmapFacts D _ _, padOf Ca E0 Cq CM,
    fun N => Fpf Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev N + hotOf s g D.tc N,
    hotOf s g D.tc, A + 42, Bh, _, Outer.apad s.mw (g.sv s) + 1, hpad1, ?_, ?_,
    guessEnvelope s P g ctr η, hg, le_rfl, ⟨onA, fun N hN => ?_⟩, ⟨onh, hhot⟩⟩
  · intro N x bits Bo hN hdec
    have hq : onc ≤ width s g N := hNc N (hDN0.trans hN)
    obtain ⟨hca, -⟩ : auxN s P g x Bo + gadgets s g N ≤ Ca * (N + 1) ^ E0 ∧ True :=
      ⟨hCa N x bits (padOf Ca E0 Cq CM N) Bo hN (hpad1 N) hdec, trivial⟩
    have hq1 : width s g N + 1 ≤ Cq * (N + 1) := by simpa using hCq N
    have hphys : N / 16 + 2 + auxN s P g x Bo * (2 + 2 * (N / 16) * (width s g N + 2)) + 10 * gadgets s g N ≤
        padOf Ca E0 Cq CM N := by
      unfold padOf
      have h1 : auxN s P g x Bo * (2 + 2 * (N / 16) * (width s g N + 2)) ≤
          Ca * (N + 1) ^ E0 * (2 + 2 * (N / 16) * (Cq * (N + 1) + 1)) :=
        Nat.mul_le_mul (by omega) (by
          have : 2 * (N / 16) * (width s g N + 2) ≤ 2 * (N / 16) * (Cq * (N + 1) + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega)
      have h2 := hCM N
      omega
    exact accept_fit ctr hD ω εT D (verdictMachine P.gamma εT) hCF hRF Fs onc Kc ec Co eo Cv ev hbud hOo hv x bits
      (padOf Ca E0 Cq CM N) Bo hq hdec (hpad1 N) hphys (haccFs N x bits Bo hN hdec)
  · intro N x bits
    have h := hrejFs N x bits
    show rejectCost D x bits (padOf Ca E0 Cq CM N) + 10 ≤
      Fpf Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev N + hotOf s g D.tc N
    unfold Fpf
    omega
  · have h := hA N hN
    have h1 : 1 ≤ (N + 1) ^ (30 * (E0 * (E0 + 2 + 1)) * (ec + ev + 1) + 2 * ev + 10) := Nat.one_le_pow _ _ (by omega)
    show Fpf Fs (gadgets s g) (width s g) (ratWord ω).length D.tc Kc ec Co eo Cv ev N + hotOf s g D.tc N + 40 + 2 ≤
      (A + 42) * (N + 1) ^ (30 * (E0 * (E0 + 2 + 1)) * (ec + ev + 1) + 2 * ev + 10) + hotOf s g D.tc N
    rw [Nat.add_mul]
    omega

end NearCubicGates.Close.WorkerArith
