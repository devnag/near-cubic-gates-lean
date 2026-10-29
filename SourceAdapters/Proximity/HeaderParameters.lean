import SourceAdapters.Proximity.CoinLoop
import SourceAdapters.Proximity.HeaderReading
import Proof.Gates.CounterMachine.CellTablesCst2

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": compute the loop's actual binary
coin count and the target random-bit header using paid arithmetic. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceHeader

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg (pow2P pow2P_spec)
open SourceCallee (randomReg coinLimitReg)

def powerCounter : Fin VV := 42
def totalRandomReg : Fin VV := 44

def parameters (q : ℕ) : Script := .seq (pow2P coinLimitReg powerCounter randomReg)
  (.seq (setK totalRandomReg (predicateBlockBits q)) (.op (.add totalRandomReg randomReg)))

def parameterScratch : List (Fin VV) := [coinLimitReg, powerCounter, totalRandomReg, vJ]

theorem parameters_run (C : Ctx) (q r : ℕ) (a : State) (hc : Cst a)
    (hr : a.env randomReg = r) (hpow : r < C.Wd) (hwidth : r + predicateBlockBits q < 2 ^ C.Wd) :
    Hs C (parameters q) a (5 * r + 2 * predicateBlockBits q + 12) (fun b =>
      b.env coinLimitReg = 2 ^ r ∧ b.env totalRandomReg = r + predicateBlockBits q ∧
      Same a b ∧ Fr a b parameterScratch) := by
  have e1 := pow2P_spec C coinLimitReg powerCounter randomReg (by decide) (by decide) (by decide)
    (by decide) a hc r hr hpow
  obtain ⟨b, cost1, he1, hc1, hbpow, hbsh, hbfr⟩ := e1
  have hbSame := Same.of_sh hbsh
  have e2 := setK_spec (C := C) totalRandomReg (by decide) (predicateBlockBits q) b (by omega)
  obtain ⟨d, cost2, he2, hc2, hdvalue, hdsh, hdfr⟩ := e2
  have hdSame := Same.of_sh hdsh
  have hdr : d.env randomReg = r := (hdfr randomReg (by decide)).trans ((hbfr randomReg (by decide)).trans hr)
  have e3 := Ex.op (OpEx.add (C := C) totalRandomReg randomReg d (by decide)
    (by rw [hdvalue, hdr]; omega))
  rw [hdvalue, hdr] at e3
  refine ⟨_, cost1 + (cost2 + 1 + 1) + 1, Ex.seq he1 (Ex.seq he2 e3), by omega, ?_, ?_, ?_, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide : coinLimitReg ≠ totalRandomReg), hdfr coinLimitReg (by decide), hbpow]
  · simp only [DS.set_env_self]
    omega
  · exact hbSame.trans (hdSame.trans (Same.set d _ _))
  · exact (hbfr.weaken (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [parameterScratch])).trans
      ((hdfr.weaken (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp [parameterScratch])).trans
        (Fr.set d _ (by simp [parameterScratch])))

end NearCubicGates.Adapters.Proximity.SourceHeader
