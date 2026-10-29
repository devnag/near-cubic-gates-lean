import SourceAdapters.Proximity.TrimVerifierRun
import SourceAdapters.Proximity.TrimAddressCompile
import SourceAdapters.Proximity.PrefixSizes
import Proof.Gates.Cells.Prelude
import Proof.Gates.CounterMachine.PrefixFinal

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": initialized physical compilation of the verifier word.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Joins
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

def verifierCompiler : St VV MM := .seq initP (.seq rdNatI verifierProgram)

theorem verifier_compiler_runs (r : TrimRequest) :
    ∃ b cost, Ex (trimCtx r) verifierCompiler (a0 : DS VV MM) b cost ∧
      b.out = verifierWord r ∧ cost ≤ 4000 * ((trimRequestWord r).length + 1) ^ 2 := by
  rcases r with ⟨n, V⟩
  let C := trimCtx ⟨n, V⟩
  let word := trimRequestWord ⟨n, V⟩
  let L := word.length
  have hwidth := trim_width ⟨n, V⟩
  change 16 * (L + 1) ≤ C.Wd at hwidth
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le L
  obtain ⟨b, nb, eb, hb, cb, bram, brc, bip, bout, _, _, _, _⟩ :=
    initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega)
  have hbInput : C.inp.drop b.ip = natWord L ++ word := by
    rw [bip]
    rfl
  obtain ⟨e, ne, ee, he, _, _, eip, eo, ef⟩ :=
    rdNatI_spec (C := C) b cb L word hbInput (by omega)
  have ce := cst_fr cb ef
  simp only [Prod.mk.injEq] at eo
  have heInput : C.inp.drop e.ip = word := by
    rw [eip, ← List.drop_drop, hbInput, List.drop_left]
  have heRam : ∀ m, e.ram m = [] := by
    intro m
    rw [eo.2.1, bram]
    rfl
  have heRc : ∀ m, e.rc m = 0 := by
    intro m
    rw [eo.2.2.1, brc]
    rfl
  obtain ⟨z, nz, ez, hz, zout⟩ := verifier_program (C := C) V e ce heInput
    (heRam _) (heRc _) (heRam _) (heRc _) (heRam _) (heRc _)
    (by change L + 4 ≤ C.Wd; omega)
  refine ⟨z, _, Ex.seq eb (Ex.seq ee ez), ?_, ?_⟩
  · have heOut : e.out = [] := by rw [eo.1, bout]; rfl
    simpa only [heOut, List.nil_append] using zout
  · change nz ≤ 2000 * (L + 1) ^ 2 at hz
    change _ ≤ 4000 * (L + 1) ^ 2
    nlinarith

noncomputable def verifierCompilerWordFunction : WordFunction TrimRequest
    (fun r => LengthPrefix.wrapped (trimRequestWord r)) verifierWord
    (fun r => langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
      (LengthPrefix.wrapped (trimRequestWord r)) (4000 * ((trimRequestWord r).length + 1) ^ 2)) :=
  wordFunction_of_lang (Req := TrimRequest) (V := VV) (M := MM)
    (fun r => LengthPrefix.wrapped (trimRequestWord r)) verifierWord
    noCallee ⟨16, 1, 0, 0, 0, 0⟩ verifierCompiler
    (fun r => 4000 * ((trimRequestWord r).length + 1) ^ 2) verifier_compiler_runs
    (fun r => by have h := trim_width r; change 1 ≤ (trimCtx r).Wd; omega)

end NearCubicGates.Adapters.Proximity.Trim
