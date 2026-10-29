import SourceAdapters.Proximity.HonestPreparedRewind
import SourceAdapters.Proximity.SourceConfiguration
import Proof.Gates.Cells.Prelude

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": initialize the fixed query and local-assignment
bounds by actual constant-writing instructions before reading the input. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceCallee (truthLengthReg)
open QueryStep (boundReg)
open TrimHonest (localBound)

def setup (q : ℕ) : Script := .seq initP
  (.seq (SourceCallee.configure q) (setK localBound (blockVariableBound q)))

def setupScratch : List (Fin VV) := [v1, v2, boundReg, truthLengthReg, vJ, localBound]

structure Configured (q : ℕ) (b : State) : Prop where
  constants : Cst b
  bound : b.env boundReg = q
  truth : b.env truthLengthReg = 2 ^ q
  local_bound : b.env localBound = blockVariableBound q
  ram : b.ram = fun _ => []
  rc : b.rc = fun _ => 0
  ip : b.ip = 0
  out : b.out = []
  kin : b.kin = []
  vars : Fr (a0 : State) b setupScratch

theorem setup_run (C : Ctx) (q : ℕ)
    (hW : 2 < 2 ^ C.Wd) (hq : q < 2 ^ C.Wd) (ht : 2 ^ q < 2 ^ C.Wd)
    (hB : blockVariableBound q < 2 ^ C.Wd) :
    Hs C (setup q) (a0 : State) (2 * q + 2 * 2 ^ q + 2 * blockVariableBound q + 17)
      (Configured q) := by
  obtain ⟨b, nb, eb, hb, cb, bm, br, bi, bo, bk, _, _, bf⟩ :=
    initP_spec (C := C) (a0 : State) rfl rfl rfl hW
  obtain ⟨c, nc, ec, hc, cq, ct, cs, cf⟩ := SourceCallee.configure_run C q b hq ht
  obtain ⟨d, nd, ed, hd, dB, ds, df⟩ := setK_spec (C := C) localBound (by decide)
    (blockVariableBound q) c hB
  have same := cs.trans (Same.of_sh ds)
  refine ⟨d, _, Ex.seq eb (Ex.seq ec ed), by omega, ?_⟩
  refine ⟨Cst.of_fr (Cst.of_fr cb cf (by decide)) df (by decide),
    (df boundReg (by decide)).trans cq, (df truthLengthReg (by decide)).trans ct, dB,
    same.ram.trans bm, same.rc.trans br, same.ip.trans bi, same.out.trans bo, same.kin.trans bk, ?_⟩
  exact (bf.weaken (by decide)).trans ((cf.weaken (by decide)).trans (df.weaken (by decide)))

end NearCubicGates.Adapters.Proximity.HonestPrepared
