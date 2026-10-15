import Proof.Wire_3_5.PrimAsmParseNat
import Proof.Wire_3_5.PrimAsmCopyNat
import Proof.Gates.Interfaces.Counter

set_option autoImplicit false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

/-- Skip one `natWord` (encoding `ε`) on stream `i`. -/
abbrev skipNat (ε : Bool) (i : Fin (ns + 1)) (f c : Fin nr) : WM ns nr := skipNatM ε i f c

theorem skipNat_spec (ε : Bool) (i : Fin (ns + 1)) (f c : Fin nr) (hfc : f ≠ c) (x : ℕ) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st i = pre ++ enc ε (natWord x) ++ rest) (hsh : σ.sh i = pre.length)
    (hf : σ.val f = 0) (hc : σ.val c = 0) (hcap : natBitLength x + 1 ≤ cap) :
    WExec cap (skipNat ε i f c) σ (σ.seth i (pre.length + stp ε * (natWord x).length)) (20 * natBitLength x + 20) :=
  skipNatM_spec cap ε i f c hfc x pre rest σ hst hsh hf hc hcap

def skipInt (ε : Bool) (i : Fin (ns + 1)) (f c : Fin nr) : WM ns nr := .seq (skipNat ε i f c) (skipNat ε i f c)

/-- The cost of skipping `Interfaces.intWord z`. -/
def skipIntCost (z : ℤ) : ℕ := 20 * natBitLength (if z < 0 then 1 else 0) + 20 + 1 + (20 * natBitLength z.natAbs + 20)

theorem skipInt_spec (ε : Bool) (i : Fin (ns + 1)) (f c : Fin nr) (hfc : f ≠ c) (z : ℤ) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st i = pre ++ enc ε (Interfaces.intWord z) ++ rest) (hsh : σ.sh i = pre.length)
    (hf : σ.val f = 0) (hc : σ.val c = 0) (hcap : natBitLength z.natAbs + 2 ≤ cap) :
    WExec cap (skipInt ε i f c) σ (σ.seth i (pre.length + stp ε * (Interfaces.intWord z).length)) (skipIntCost z) := by
  have hs1 : natBitLength (if z < 0 then 1 else 0) ≤ 1 := by split_ifs <;> simp [natBitLength]
  have hsplit : enc ε (Interfaces.intWord z) = enc ε (natWord (if z < 0 then 1 else 0)) ++ enc ε (natWord z.natAbs) := by
    unfold Interfaces.intWord; exact NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append ε _ _
  have h1 := skipNat_spec cap ε i f c hfc (if z < 0 then 1 else 0) pre (enc ε (natWord z.natAbs) ++ rest) σ
    (by rw [hst, hsplit]; simp [List.append_assoc]) hsh hf hc (by omega)
  have h2 := skipNat_spec cap ε i f c hfc z.natAbs (pre ++ enc ε (natWord (if z < 0 then 1 else 0))) rest
    (σ.seth i (pre.length + stp ε * (natWord (if z < 0 then 1 else 0)).length))
    (by simp only [WState.seth_st]; rw [hst, hsplit]; simp [List.append_assoc])
    (by simp [enc_length]) (by simp [hf]) (by simp [hc]) (by omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp [skipIntCost])
  refine WState.eq ?_ rfl rfl rfl
  funext j
  by_cases hj : j = i
  · subst hj; simp [Interfaces.intWord, List.length_append, WireExponent3_5.PrimAsm.ParseNat.enc_length]; ring
  · simp [Function.update_of_ne hj]

end NearCubicGates.Close.Codec
