import SourceAdapters.Code.BitLookup

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": one paid shifted bit lookup and append. The binary offset
is added to a retained index, then tested before any source scan. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.ShiftedBits

open NearCubicGates.Close.Cells

def step (source destination : Fin MM) (len offset index address result : Fin VV) : St VV MM :=
  .seq (.op (.copy address offset)) (.seq (.op (.add address index))
    (.seq (BitLookup.script source address len result) (.op (.wrM destination result))))

theorem step_runs (C : Ctx) (source destination : Fin MM) (hsd : source ≠ destination)
    (len offset index address result : Fin VV)
    (hl : len ∉ [c0, vJ, address, result]) (ho : offset ∉ [c0, vJ, address, result])
    (hi : index ∉ [c0, vJ, address, result]) (ha : address ∉ [c0, vJ, result])
    (hcst : vZ ∉ [c0, vJ, address, result] ∧ v1 ∉ [c0, vJ, address, result] ∧
      v2 ∉ [c0, vJ, address, result])
    (a : DS VV MM) (hc : Cst a) (bits previous : List Bool)
    (hbits : a.ram source = bits.map Bool.toNat)
    (hprevious : a.ram destination = previous.map Bool.toNat)
    (hlen : a.env len = bits.length) (hsource : a.rc source ≤ bits.length)
    (hdestination : a.rc destination = previous.length)
    (hwidth : bits.length < 2 ^ C.Wd)
    (hadd : a.env offset + a.env index < 2 ^ C.Wd) :
    Hs C (step source destination len offset index address result) a
      (6 * bits.length + 16) (fun b =>
      b.ram destination = (previous ++ [bits.getD (a.env offset + a.env index) false]).map Bool.toNat ∧
      b.rc destination = previous.length + 1 ∧ b.rc source ≤ bits.length ∧
      (∀ q, q ≠ destination → b.ram q = a.ram q) ∧
      (∀ q, q ≠ source → q ≠ destination → b.rc q = a.rc q) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      Fr a b [c0, vJ, address, result]) := by
  have hla : len ≠ address := by intro h; apply hl; simp [h]
  have hoa : offset ≠ address := by intro h; apply ho; simp [h]
  have hia : index ≠ address := by intro h; apply hi; simp [h]
  have sub : [c0, vJ, result] ⊆ [c0, vJ, address, result] := by
    intro q hq
    simp only [List.mem_cons] at hq ⊢
    tauto
  let a1 := a.set address (a.env offset)
  let a2 := a1.set address (a.env offset + a.env index)
  have f1 : Fr a a1 [c0, vJ, address, result] := Fr.set a _ (by simp)
  have f2 : Fr a1 a2 [c0, vJ, address, result] := Fr.set a1 _ (by simp)
  have addRun : Hs C (.op (.add address index)) a1 1 (· = a2) := by
    have h := hs_add C address index a1 hia.symm (by simpa [a1, hia] using hadd)
    simpa only [a1, DS.set_env_self, DS.set_env_ne _ _ hia] using h
  have lookupRun := BitLookup.runs C source address len result hla.symm ha
    (fun h => hl (sub h))
    ⟨fun h => hcst.1 (sub h), fun h => hcst.2.1 (sub h), fun h => hcst.2.2 (sub h)⟩
    a2 (Cst.of_fr hc (f1.trans f2) hcst) bits hbits
    (by simpa [a2, a1, hla] using hlen) hsource hwidth
  have tailRun : Hs C (.seq (BitLookup.script source address len result)
      (.op (.wrM destination result))) a2 (6 * bits.length + 12) (fun b =>
      b.ram destination = (previous ++ [bits.getD (a.env offset + a.env index) false]).map Bool.toNat ∧
      b.rc destination = previous.length + 1 ∧ b.rc source ≤ bits.length ∧
      (∀ q, q ≠ destination → b.ram q = a.ram q) ∧
      (∀ q, q ≠ source → q ≠ destination → b.rc q = a.rc q) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      Fr a b [c0, vJ, address, result]) := by
    refine Hs.mono (Hs.seq (t2 := 1) lookupRun (fun b hb => ?_)) (by omega) (fun _ h => h)
    rcases hb with ⟨bv, _, _, _, bi, bo, bm, bki, bko, bkc, brc, bs, bf⟩
    have bd : b.rc destination = previous.length := (brc destination hsd.symm).trans hdestination
    have bp : b.ram destination = previous.map Bool.toNat := by rw [bm]; exact hprevious
    refine Hs.mono (hs_wrM C destination result b (by rw [bd, bp]; simp)) le_rfl ?_
    rintro d rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, bi, bo, bki, bko, bkc,
      (f1.trans f2).trans (bf.weaken sub)⟩
    · simp only [DS.put, Function.update_self, putAt, bd, bp, List.length_map, Nat.lt_irrefl,
        if_false, List.map_append, List.map_cons, List.map_nil]
      rw [bv]
      simp only [a2, DS.set_env_self]
    · simp [DS.put, bd]
    · simpa [DS.put, hsd] using bs
    · intro q hq
      simpa [DS.put, hq, a2, a1] using congrFun bm q
    · intro q hqs hqd
      simpa [DS.put, hqd, a2, a1] using brc q hqs
  have allRun := Hs.seq (hs_copy C address offset a hoa.symm) (fun b hb => by
    subst b
    exact Hs.seq addRun (fun d hd => by subst d; exact tailRun))
  exact Hs.mono allRun (by omega) (fun _ h => h)

end NearCubicGates.Adapters.Code.ShiftedBits
