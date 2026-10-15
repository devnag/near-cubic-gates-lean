import Proof.Gates.Codec.Lists

set_option autoImplicit false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

/-- Registers `rs` all hold `0`. -/
def Zeros (σ : WState ns nr) (rs : List (Fin nr)) : Prop := ∀ r ∈ rs, σ.val r = 0

theorem Zeros.seth {σ : WState ns nr} {rs : List (Fin nr)} (h : Zeros σ rs) (i : Fin (ns + 1)) (x : ℕ) :
    Zeros (σ.seth i x) rs := fun r hr => by simpa using h r hr

theorem Zeros.setv {σ : WState ns nr} {rs : List (Fin nr)} (h : Zeros σ rs) (k : Fin nr) (hk : k ∉ rs) (x : ℕ) :
    Zeros (σ.setv k x) rs := fun r hr => by
  have : r ≠ k := fun e => hk (e ▸ hr)
  simpa [Function.update_of_ne this] using h r hr

local notation "E" => WireExponent3_5.PrimAsm.ParseNat.enc
local notation "S" => WireExponent3_5.PrimAsm.ParseNat.stp

theorem encApp (ε : Bool) (u v : List Bool) : E ε (u ++ v) = E ε u ++ E ε v :=
  NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append ε u v

/-- Move past `listWord intWord zs`. -/
def skipIntList (ε : Bool) (i : Fin (ns + 1)) (f c k p t : Fin nr) : WM ns nr :=
  skipList ε i f c k p t (skipInt ε i f c)

/-- The cost of skipping one `intWord`. -/
def intCost (z : ℤ) : ℕ := skipIntCost z

theorem skipIntList_spec (ε : Bool) (i : Fin (ns + 1)) (f c k p t : Fin nr) (hd : [f, c, k, p, t].Nodup)
    (zs : List ℤ) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st i = pre ++ E ε (listWord Interfaces.intWord zs) ++ rest) (hsh : σ.sh i = pre.length)
    (hz : Zeros σ [f, c, k, p, t]) (hcap : 2 ^ (natBitLength zs.length + 1) ≤ cap) (hlen : zs.length ≤ cap)
    (hcapz : ∀ z ∈ zs, natBitLength z.natAbs + 2 ≤ cap) :
    WExec cap (skipIntList ε i f c k p t) σ (σ.seth i (pre.length + S ε * (listWord Interfaces.intWord zs).length))
      (skipListCost zs.length (zs.map intCost)) := by
  have hfc : f ≠ c := by intro e; simp [e] at hd
  have hkf : k ∉ [f, c] := by intro hm; simp at hm; rcases hm with e | e <;> simp [e] at hd
  refine skipList_spec cap ε i f c k p t (skipInt ε i f c) hd Interfaces.intWord intCost (fun σ => Zeros σ [f, c])
    (fun σ x h => h.seth i x) (fun σ x h => h.setv k hkf x) zs ?_ pre rest σ
    (fun r hr => hz r (by simp at hr ⊢; tauto)) hst hsh (hz f (by simp)) (hz c (by simp)) (hz k (by simp))
    (hz p (by simp)) (hz t (by simp)) hcap hlen
  intro z hzm pre' rest' σ' hok hst' hsh'
  exact skipInt_spec cap ε i f c hfc z pre' rest' σ' hst' hsh' (hok f (by simp)) (hok c (by simp)) (hcapz z hzm)

/-- Move past `gateWord g = listWord intWord (ofFn g.weight) ++ intWord g.threshold`. -/
def skipGate (ε : Bool) (i : Fin (ns + 1)) (f c k p t : Fin nr) : WM ns nr :=
  .seq (skipIntList ε i f c k p t) (skipInt ε i f c)

/-- The cost of skipping one gate. -/
def gateCost {n : ℕ} (gt : NormalizedThresholdGate n) : ℕ :=
  skipListCost n ((List.ofFn gt.weight).map intCost) + 1 + intCost gt.threshold

/-- Every number in a gate fits the register capacity. -/
def GateFits {n : ℕ} (cap : ℕ) (gt : NormalizedThresholdGate n) : Prop :=
  2 ^ (natBitLength n + 1) ≤ cap ∧ n ≤ cap ∧ (∀ z ∈ List.ofFn gt.weight, natBitLength z.natAbs + 2 ≤ cap) ∧
    natBitLength gt.threshold.natAbs + 2 ≤ cap

theorem skipGate_spec {n : ℕ} (ε : Bool) (i : Fin (ns + 1)) (f c k p t : Fin nr) (hd : [f, c, k, p, t].Nodup)
    (gt : NormalizedThresholdGate n) (hfit : GateFits cap gt) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st i = pre ++ E ε (gateWord gt) ++ rest) (hsh : σ.sh i = pre.length) (hz : Zeros σ [f, c, k, p, t]) :
    WExec cap (skipGate ε i f c k p t) σ (σ.seth i (pre.length + S ε * (gateWord gt).length)) (gateCost gt) := by
  have hfc : f ≠ c := by intro e; simp [e] at hd
  obtain ⟨h2, hn, hw, hth⟩ := hfit
  have hsplit : E ε (gateWord gt) = E ε (listWord Interfaces.intWord (List.ofFn gt.weight)) ++
      E ε (Interfaces.intWord gt.threshold) := by unfold gateWord; exact encApp ε _ _
  have h1 := skipIntList_spec cap ε i f c k p t hd (List.ofFn gt.weight) pre (E ε (Interfaces.intWord gt.threshold) ++ rest)
    σ (by rw [hst, hsplit]; simp [List.append_assoc]) hsh hz (by simpa using h2) (by simpa using hn) hw
  set σ1 := σ.seth i (pre.length + S ε * (listWord Interfaces.intWord (List.ofFn gt.weight)).length) with hσ1
  have hst1 : σ1.st i = (pre ++ E ε (listWord Interfaces.intWord (List.ofFn gt.weight))) ++
      E ε (Interfaces.intWord gt.threshold) ++ rest := by
    simp only [hσ1, WState.seth_st]; rw [hst, hsplit]; simp [List.append_assoc]
  have h2' := skipInt_spec cap ε i f c hfc gt.threshold (pre ++ E ε (listWord Interfaces.intWord (List.ofFn gt.weight)))
    rest σ1 hst1 (by simp [hσ1, WireExponent3_5.PrimAsm.ParseNat.enc_length])
    (by simp [hσ1, hz f (by simp)]) (by simp [hσ1, hz c (by simp)]) hth
  refine WExec.cast cap (WExec.seq h1 h2') ?_ (by unfold gateCost intCost; rw [List.length_ofFn])
  refine WState.eq ?_ rfl rfl rfl
  funext j; by_cases hj : j = i
  · subst hj; simp [hσ1, gateWord, WireExponent3_5.PrimAsm.ParseNat.enc_length]; ring
  · simp [hσ1, Function.update_of_ne hj]

/-- Move past `listWord gateWord gates` (outer counter `K`, the gates' inner counter `k`). -/
def skipGateList (ε : Bool) (i : Fin (ns + 1)) (f c k K p t : Fin nr) : WM ns nr :=
  skipList ε i f c K p t (skipGate ε i f c k p t)

theorem skipGateList_spec {n : ℕ} (ε : Bool) (i : Fin (ns + 1)) (f c k K p t : Fin nr)
    (hd : [f, c, k, K, p, t].Nodup) (gs : List (NormalizedThresholdGate n)) (hfit : ∀ gt ∈ gs, GateFits cap gt)
    (hcap : 2 ^ (natBitLength gs.length + 1) ≤ cap) (hlen : gs.length ≤ cap) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st i = pre ++ E ε (listWord gateWord gs) ++ rest) (hsh : σ.sh i = pre.length)
    (hz : Zeros σ [f, c, k, K, p, t]) :
    WExec cap (skipGateList ε i f c k K p t) σ (σ.seth i (pre.length + S ε * (listWord gateWord gs).length))
      (skipListCost gs.length (gs.map gateCost)) := by
  have hd5 : [f, c, K, p, t].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_true] at hd ⊢; tauto
  have hdg : [f, c, k, p, t].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_true] at hd ⊢; tauto
  have hK : K ∉ [f, c, k, p, t] := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_true] at hd ⊢; tauto
  refine skipList_spec cap ε i f c K p t (skipGate ε i f c k p t) hd5 gateWord gateCost
    (fun σ => Zeros σ [f, c, k, p, t]) (fun σ x h => h.seth i x) (fun σ x h => h.setv K hK x) gs ?_ pre rest σ
    (fun r hr => hz r (by simp at hr ⊢; tauto)) hst hsh (hz f (by simp)) (hz c (by simp)) (hz K (by simp))
    (hz p (by simp)) (hz t (by simp)) hcap hlen
  intro gt hgt pre' rest' σ' hok hst' hsh'
  exact skipGate_spec cap ε i f c k p t hdg gt (hfit gt hgt) pre' rest' σ' hst' hsh' hok

/-- The cost of skipping one `bitWord`. -/
def bitCost (b : Bool) : ℕ := 20 * natBitLength (if b then 1 else 0) + 20

def skipBitList (ε : Bool) (i : Fin (ns + 1)) (f c k p t : Fin nr) : WM ns nr :=
  skipList ε i f c k p t (skipNat ε i f c)

theorem skipBitList_spec (ε : Bool) (i : Fin (ns + 1)) (f c k p t : Fin nr) (hd : [f, c, k, p, t].Nodup)
    (bs : List Bool) (hcap : 2 ^ (natBitLength bs.length + 1) ≤ cap) (hlen : bs.length ≤ cap) (hc2 : 2 ≤ cap)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st i = pre ++ E ε (listWord bitWord bs) ++ rest)
    (hsh : σ.sh i = pre.length) (hz : Zeros σ [f, c, k, p, t]) :
    WExec cap (skipBitList ε i f c k p t) σ (σ.seth i (pre.length + S ε * (listWord bitWord bs).length))
      (skipListCost bs.length (bs.map bitCost)) := by
  have hfc : f ≠ c := by intro e; simp [e] at hd
  have hkf : k ∉ [f, c] := by intro hm; simp at hm; rcases hm with e | e <;> simp [e] at hd
  refine skipList_spec cap ε i f c k p t (skipNat ε i f c) hd bitWord bitCost (fun σ => Zeros σ [f, c])
    (fun σ x h => h.seth i x) (fun σ x h => h.setv k hkf x) bs ?_ pre rest σ
    (fun r hr => hz r (by simp at hr ⊢; tauto)) hst hsh (hz f (by simp)) (hz c (by simp)) (hz k (by simp))
    (hz p (by simp)) (hz t (by simp)) hcap hlen
  intro b _ pre' rest' σ' hok hst' hsh'
  have hb : natBitLength (if b then 1 else 0) + 1 ≤ cap := by
    have : natBitLength (if b then 1 else 0) ≤ 1 := by split_ifs <;> simp [natBitLength]
    omega
  exact skipNat_spec cap ε i f c hfc (if b then 1 else 0) pre' rest' σ' (by simpa [bitWord] using hst') hsh'
    (hok f (by simp)) (hok c (by simp)) hb

/-- Every number of a circuit fits the register capacity. -/
def CircuitFits {n : ℕ} (cap : ℕ) (C : NCircuit n) : Prop :=
  (∀ gt ∈ C.gates, GateFits cap gt) ∧ 2 ^ (natBitLength C.gates.length + 1) ≤ cap ∧ C.gates.length ≤ cap ∧
    2 ^ (natBitLength C.coeffs.length + 1) ≤ cap ∧ C.coeffs.length ≤ cap ∧
    (∀ z ∈ C.coeffs, natBitLength z.natAbs + 2 ≤ cap) ∧
    2 ^ (natBitLength C.table.length + 1) ≤ cap ∧ C.table.length ≤ cap ∧ 2 ≤ cap

/-- The cost of skipping one circuit. -/
def circuitCost {n : ℕ} (C : NCircuit n) : ℕ :=
  skipListCost C.gates.length (C.gates.map gateCost) + 1 +
    (skipListCost C.coeffs.length (C.coeffs.map intCost) + 1 + skipListCost C.table.length (C.table.map bitCost))

/-- Move past `circuitWord C`. -/
def skipCircuit (ε : Bool) (i : Fin (ns + 1)) (f c k K p t : Fin nr) : WM ns nr :=
  .seq (skipGateList ε i f c k K p t) (.seq (skipIntList ε i f c k p t) (skipBitList ε i f c k p t))

theorem skipCircuit_spec {n : ℕ} (ε : Bool) (i : Fin (ns + 1)) (f c k K p t : Fin nr)
    (hd : [f, c, k, K, p, t].Nodup) (C : NCircuit n) (hfit : CircuitFits cap C) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st i = pre ++ E ε (circuitWord C) ++ rest) (hsh : σ.sh i = pre.length)
    (hz : Zeros σ [f, c, k, K, p, t]) :
    WExec cap (skipCircuit ε i f c k K p t) σ (σ.seth i (pre.length + S ε * (circuitWord C).length))
      (circuitCost C) := by
  obtain ⟨hg, hg2, hgl, hc2, hcl, hcz, ht2, htl, hcap2⟩ := hfit
  have hdg : [f, c, k, p, t].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_true] at hd ⊢; tauto
  have hz5 : Zeros σ [f, c, k, p, t] := fun r hr => hz r (by simp at hr ⊢; tauto)
  have hsplit : E ε (circuitWord C) = E ε (listWord gateWord C.gates) ++ E ε (listWord Interfaces.intWord C.coeffs) ++
      E ε (listWord bitWord C.table) := by
    unfold circuitWord; rw [encApp, encApp]
  have h1 := skipGateList_spec cap ε i f c k K p t hd C.gates hg hg2 hgl pre
    (E ε (listWord Interfaces.intWord C.coeffs) ++ E ε (listWord bitWord C.table) ++ rest) σ
    (by rw [hst, hsplit]; simp [List.append_assoc]) hsh hz
  set σ1 := σ.seth i (pre.length + S ε * (listWord gateWord C.gates).length) with hσ1
  have hz1 : Zeros σ1 [f, c, k, p, t] := hz5.seth i _
  have hst1 : σ1.st i = (pre ++ E ε (listWord gateWord C.gates)) ++ E ε (listWord Interfaces.intWord C.coeffs) ++
      (E ε (listWord bitWord C.table) ++ rest) := by
    simp only [hσ1, WState.seth_st]; rw [hst, hsplit]; simp [List.append_assoc]
  have h2 := skipIntList_spec cap ε i f c k p t hdg C.coeffs (pre ++ E ε (listWord gateWord C.gates))
    (E ε (listWord bitWord C.table) ++ rest) σ1 hst1 (by simp [hσ1, WireExponent3_5.PrimAsm.ParseNat.enc_length])
    hz1 hc2 hcl hcz
  set σ2 := σ1.seth i ((pre ++ E ε (listWord gateWord C.gates)).length +
    S ε * (listWord Interfaces.intWord C.coeffs).length) with hσ2
  have hz2 : Zeros σ2 [f, c, k, p, t] := hz1.seth i _
  have hst2 : σ2.st i = (pre ++ E ε (listWord gateWord C.gates) ++ E ε (listWord Interfaces.intWord C.coeffs)) ++
      E ε (listWord bitWord C.table) ++ rest := by
    simp only [hσ2, hσ1, WState.seth_st]; rw [hst, hsplit]; simp [List.append_assoc]
  have h3 := skipBitList_spec cap ε i f c k p t hdg C.table ht2 htl hcap2
    (pre ++ E ε (listWord gateWord C.gates) ++ E ε (listWord Interfaces.intWord C.coeffs)) rest σ2 hst2
    (by simp [hσ2, WireExponent3_5.PrimAsm.ParseNat.enc_length, Nat.add_assoc]) hz2
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (le_refl _)
  refine WState.eq ?_ rfl rfl rfl
  funext j; by_cases hj : j = i
  · subst hj; simp [hσ2, hσ1, circuitWord, WireExponent3_5.PrimAsm.ParseNat.enc_length]; ring
  · simp [hσ2, hσ1, Function.update_of_ne hj]

end NearCubicGates.Close.Codec
