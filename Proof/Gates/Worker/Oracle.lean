import Proof.Gates.Worker.Donors
import Proof.Gates.CheckedPCPP.Composite

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicWires.WireExponent3_5
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm.DockW
open RepairOrdinary.CloseoutWitness.Oracle RepairOrdinary.RadixSemantics ExecutableInterfaces CanonicalWitnessCodec

variable {ns nr : ℕ}

/-- The oracle phase program: copy `frame x`, frame the field at the head of `WT`, run the decoder. -/
noncomputable def oracleP (X WT L : Fin (ns + 1)) (cB : Fin (tapes + 1) → Fin (ns + 1)) (OP T D K : Fin nr) :
    WMX ns nr :=
  .seq (.wm (Codec.copyRW X (cB 0) OP T D))
  (.seq (.wm (Codec.fieldRW WT (cB 1) OP K)) (WMX.machZ machine cB L))

/-- The cost of the oracle phase. -/
def oracleCost (x bits ab : List Bool) : ℕ :=
  (22 * x.length + 1 + 1 + 7 + 1 + (18 * (2 * x.length + 1) + 3 + 1 + (5 * (2 * x.length + 1) + 1 + 1 +
    (5 * (2 * x.length + 1) + 1)))) + 1 + ((7 * bits.length + 3 + 1 + (22 * bits.length + 1 + 1 + 7) + 1 +
    (5 * (2 * bits.length + 1) + 1)) + 1 + (2 * budget x bits ab + 2))

theorem oracle_ideal (X WT NB NR L : Fin (ns + 1)) (cB : Fin (tapes + 1) → Fin (ns + 1)) (hinj : Function.Injective cB)
    (h2 : cB 2 = NB) (h3 : cB 3 = NR) (hX : ∀ j, cB j ≠ X) (hW : ∀ j, cB j ≠ WT) (hL : ∀ j, cB j ≠ L) (hLW : L ≠ WT)
    (OP T D K : Fin nr) (hr : [OP, T, D, K].Nodup)
    (x bits ab rx pre rest : List Bool) (hN : 2 ≤ x.length) (hcap16 : 16 * bits.length ≤ x.length)
    (hab : ab.length ≤ x.length + 1) {cap : ℕ} (hc : 4 * x.length + 4 + 2 * bits.length + 2 ≤ cap)
    (σ : WState ns nr) (hXs : σ.st X = frame x ++ rx) (hXh : σ.sh X = 0)
    (hWs : σ.st WT = pre ++ (Worker.Format.countWord bits.length ++ bits) ++ rest) (hWh : σ.sh WT = pre.length)
    (hNB : σ.st NB = frame ab) (hNR : σ.st NR = List.replicate (value ab) true)
    (hb : ∀ j, j.val ≠ 2 → j.val ≠ 3 → σ.st (cB j) = []) (h0 : ∀ j, σ.sh (cB j) = 0)
    (hz : ∀ r ∈ [OP, T, D, K], σ.val r = 0) (hLb : Blank (σ.st L)) (hLsh : σ.sh L = 0) :
    ∃ τ out, WXExec cap (oracleP X WT L cB OP T D K) σ τ (oracleCost x bits ab) ∧
      SimW (updS cB (σ.seth WT (pre.length + bits.length + 1 + bits.length)) (fun _ => 0) out) τ ∧
      out flagSlot = [(decodeBooleanCircuit (value ab) (value bits)).isSome] ∧
      (∀ c : BooleanCircuit (value ab), decodeBooleanCircuit (value ab) (value bits) = some c →
        out descriptorSlot = PCPPNative.descriptor c) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hr
  obtain ⟨⟨hOT, hOD, hOK⟩, ⟨hTD, hTK⟩, hDK⟩ := hr
  have hO : σ.val OP = 0 := hz OP (by simp)
  have hT : σ.val T = 0 := hz T (by simp)
  have hD : σ.val D = 0 := hz D (by simp)
  have hK : σ.val K = 0 := hz K (by simp)
  have hc0 : cB 0 ≠ cB 1 := hinj.ne (by decide)
  -- 1. `frame x` on tape 0
  have e1 := Codec.copyRW_spec cap X (cB 0) (hX 0).symm OP T D hOT hOD hTD x rx σ hXs hXh (hb 0 (by decide) (by decide))
    (h0 0) hO hT hD (by omega)
  set σ1 := σ.sets (cB 0) (frame x) with hσ1
  -- 2. the field on tape 1
  have e2 := Codec.fieldRW_spec cap WT (cB 1) (hW 1).symm OP K (Ne.symm hOK) pre bits rest σ1
    (by simp [hσ1, Function.update_of_ne (hW 0).symm, hWs]) (by simp [hσ1, hWh])
    (by simp [hσ1, Function.update_of_ne hc0.symm]; exact hb 1 (by decide) (by decide)) (by simp [hσ1, h0 1])
    (by simp [hσ1, hK]) (by simp [hσ1, hO]) (by omega)
  set σ2 := (σ1.seth WT (pre.length + bits.length + 1 + bits.length)).sets (cB 1) (frame bits) with hσ2
  -- 3. the decoder
  obtain ⟨out, hrun, hflag, hdesc⟩ := cold_ready x bits ab hN hcap16 hab
  obtain ⟨τ, e4, hs⟩ := donor_ideal machine (budget x bits ab) (coldIn x bits ab) out hrun cB hinj L hL σ2
    (fun j => by simp [hσ2, hσ1, Function.update_of_ne (hW j)]; exact h0 j)
    (fun j => by
      by_cases hj0 : j = 0
      · subst hj0; simp [hσ2, hσ1, Function.update_of_ne hc0, coldIn]; exact RdEq.refl _
      by_cases hj1 : j = 1
      · subst hj1; simp [hσ2, hσ1, coldIn]; exact RdEq.refl _
      simp only [hσ2, hσ1, WState.sets_st, WState.seth_st]
      rw [Function.update_of_ne (hinj.ne hj1), Function.update_of_ne (hinj.ne hj0)]
      by_cases hj2 : j = 2
      · subst hj2; rw [h2, hNB]; simp [coldIn]; exact RdEq.refl _
      by_cases hj3 : j = 3
      · subst hj3; rw [h3, hNR]; simp [coldIn]; exact RdEq.refl _
      have hv0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      have hv1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
      have hv2 : j.val ≠ 2 := fun h => hj2 (Fin.ext h)
      have hv3 : j.val ≠ 3 := fun h => hj3 (Fin.ext h)
      rw [hb j hv2 hv3]; simp [coldIn, hv0, hv1, hv2, hv3]; exact RdEq.refl _)
    (by simp [hσ2, hσ1, Function.update_of_ne (hL 1).symm, Function.update_of_ne (hL 0).symm]; exact hLb)
    (by simp [hσ2, hσ1, Function.update_of_ne hLW, hLsh])
  refine ⟨τ, out, WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) e4), ?_, hflag, hdesc⟩
  have hid : updS cB σ2 (fun _ => 0) out =
      updS cB (σ.seth WT (pre.length + bits.length + 1 + bits.length)) (fun _ => 0) out := by
    apply updS_eq cB σ2 (fun _ => 0) out hinj
    · intro j; exact updS_st_slot cB _ _ out hinj j
    · intro j; exact updS_sh_slot cB _ _ out hinj j
    · intro i hi
      rw [updS_st_other cB _ _ out i hi, updS_sh_other cB _ _ out i hi]
      simp [hσ2, hσ1, Function.update_of_ne (hi 0).symm, Function.update_of_ne (hi 1).symm]
    · rfl
    · rfl
  rw [hid] at hs
  exact hs

theorem portDonor_ideal {t s : ℕ} (M : Machine t s) (n : ℕ) (hIn dIn : Fin t) (hd : hIn ≠ dIn) (h d : List Bool)
    (tout : Fin t → List Bool) (hr : ClockJoin.ReadyRun M n (portBank t hIn dIn h d) tout) {cap : ℕ}
    (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (L : Fin (ns + 1)) (hL : ∀ j, tmap j ≠ L)
    (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0) (hh : σ.st (tmap hIn) = h) (hdd : σ.st (tmap dIn) = d)
    (hb : ∀ j, j ≠ hIn → j ≠ dIn → σ.st (tmap j) = []) (hLb : Blank (σ.st L)) (hLsh : σ.sh L = 0) :
    ∃ τ, WXExec cap (WMX.machZ M tmap L) σ τ (2 * n + 2) ∧ SimW (updS tmap σ (fun _ => 0) tout) τ :=
  donor_ideal M n _ tout hr tmap hinj L hL σ h0
    (fun j => by
      unfold portBank
      by_cases hj : j = hIn
      · subst hj; rw [if_pos rfl, hh]; exact RdEq.refl _
      · by_cases hj' : j = dIn
        · subst hj'; rw [if_neg hj, if_pos rfl, hdd]; exact RdEq.refl _
        · rw [if_neg hj, if_neg hj', hb j hj hj']; exact RdEq.refl _)
    hLb hLsh

end NearCubicGates.Close.Worker
