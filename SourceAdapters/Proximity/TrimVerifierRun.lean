import SourceAdapters.Proximity.TrimVerifierOutput

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": full paid trimming request to raw verifier-word program. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
variable {C : Ctx}

def verifierWord (r : TrimRequest) : List Bool := (trimVerifier r.2).word

def verifierProgram : St VV MM := .seq prepareProgram verifierOutput

theorem verifier_program {n : ℕ} (V : ThreeQueryVerifier n) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = trimRequestWord ⟨n, V⟩)
    (hq : a.ram sN = []) (hqrc : a.rc sN = 0)
    (hp : a.ram proofStore = []) (hprc : a.rc proofStore = 0)
    (hu : a.ram distinctStore = []) (hurc : a.rc distinctStore = 0)
    (hW : inputSize V + 4 ≤ C.Wd) :
    Hs C verifierProgram a (2000 * (inputSize V + 1) ^ 2)
      (fun b => b.out = a.out ++ verifierWord ⟨n, V⟩) := by
  obtain ⟨b, nb, eb, hb, bp⟩ := prepare_program (C := C) V a hc hin hq hqrc hp hprc hu hurc (by omega)
  obtain ⟨d, nd, ed, hd, dout⟩ := verifier_prepared (C := C) V a b bp hW
  refine ⟨d, nb + nd + 1, Ex.seq eb ed, by nlinarith, ?_⟩
  change d.out = a.out ++ verifierWord ⟨n, V⟩
  rw [dout, bp.output]
  rfl

end NearCubicGates.Adapters.Proximity.Trim
