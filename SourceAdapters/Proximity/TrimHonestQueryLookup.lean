import SourceAdapters.Proximity.TrimHonestQueryData

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": actual guarded evaluation of one stored source query. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Adapters.Code
open NearCubicGates.Published.CW19Proximity
variable {C : Ctx}

def queryLookup : St VV MM := .ite (.eq queryTagReg v1)
  (BitLookup.script proofStore addressReg proofLength valueReg)
  (BitLookup.script inputStore addressReg inputLength valueReg)

private theorem lookup_finite {N : ℕ} (bits : BitInput N) (m : Fin MM) (len : Fin VV)
    (hm : m ∈ lookupStores) (hxl : addressReg ≠ len) (hl : len ∉ [c0, vJ, valueReg])
    (a : DS VV MM) (hc : Cst a) (hram : a.ram m = (List.ofFn bits).map Bool.toNat)
    (hlen : a.env len = N) (hrc : a.rc m ≤ N) (hW : N < 2 ^ C.Wd) :
    Hs C (BitLookup.script m addressReg len valueReg) a (6 * N + 10) (fun b =>
      b.env valueReg = (finiteProofOracle bits (a.env addressReg)).toNat ∧ b.out = a.out ∧
      b.rc m ≤ N ∧ (∀ j, j ≠ m → b.rc j = a.rc j) ∧ LookupFrame lookupTemps a b) := by
  have run := HonestLoading.finite_lookup C m addressReg len valueReg hxl
    (by decide) hl (by decide) a hc bits hram hlen hrc hW
  refine run.mono le_rfl ?_
  rintro b ⟨bv, _, _, _, bi, bo, bram, bki, bko, bkc, bc, bm, bf⟩
  refine ⟨bv, bo, bm, bc, bram, ?_, bi, bki, bko, bkc, bf.weaken (by simp [lookupTemps])⟩
  intro j hj
  exact bc j (by intro he; apply hj; simpa [he] using hm)

theorem query_lookup {n N : ℕ} (input : BitInput n) (proof : BitInput N)
    (p : Bool × ℕ) (a : DS VV MM) (hc : Cst a) (ready : OracleReady C input proof a)
    (htag : a.env queryTagReg = p.1.toNat) (haddress : a.env addressReg = p.2) :
    Hs C queryLookup a (6 * (n + N) + 11) (fun b =>
      b.env valueReg = (answerValue input proof p).toNat ∧ b.out = a.out ∧
      OracleReady C input proof b ∧
      (∀ m, m ≠ inputStore → m ≠ proofStore → b.rc m = a.rc m) ∧
      LookupFrame lookupTemps a b) := by
  cases hp : p.1 with
  | false =>
    have ht : (Cnd.eq queryTagReg v1).eval a = false := by simp [Cnd.eval, htag, hp, hc.one]
    have run := Hs.iteF (c := Cnd.eq queryTagReg v1)
      (s := BitLookup.script proofStore addressReg proofLength valueReg)
      (show queryTagReg ≠ v1 by decide) ht
      (lookup_finite (C := C) input inputStore inputLength (by decide) (by decide) (by decide)
        a hc ready.input_ram ready.input_len ready.input_cursor ready.input_width)
    refine run.mono (by omega) ?_
    rintro b ⟨bv, bo, bi, bc, bf⟩
    refine ⟨by simpa [answerValue, hp, haddress] using bv, bo,
      ready.frame bf (by decide) (by decide) bi ?_, (fun m hmi _ => bc m hmi), bf⟩
    rw [bc proofStore (by decide)]
    exact ready.proof_cursor
  | true =>
    have ht : (Cnd.eq queryTagReg v1).eval a = true := by simp [Cnd.eval, htag, hp, hc.one]
    have run := Hs.iteT (c := Cnd.eq queryTagReg v1)
      (u := BitLookup.script inputStore addressReg inputLength valueReg)
      (show queryTagReg ≠ v1 by decide) ht
      (lookup_finite (C := C) proof proofStore proofLength (by decide) (by decide) (by decide)
        a hc ready.proof_ram ready.proof_len ready.proof_cursor ready.proof_width)
    refine run.mono (by omega) ?_
    rintro b ⟨bv, bo, bp, bc, bf⟩
    refine ⟨by simpa [answerValue, hp, haddress] using bv, bo,
      ready.frame bf (by decide) (by decide) ?_ bp, (fun m _ hmp => bc m hmp), bf⟩
    rw [bc inputStore (by decide)]
    exact ready.input_cursor

end NearCubicGates.Adapters.Proximity.TrimHonest
