import SourceAdapters.Compile.CNFDims
import SourceAdapters.Compile.CNFAssembly

/-!
# Reading the whole request

proof of `lem:multitape-refuter` and the join's `CNFCompilationRequest.word`: from the empty cell state on the entry word
`wrapped r.word` (`CNFAssembly.requestEntryWord`), `parseP` sets the constants, skips the paid size header and reads
the five frames (`parseP_spec`): code bits in `sCB`, input bits in `sIB` (length in `dIL`), witness length in `dN`,
fuel in `dF`, `high` in `dH`.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.RepairOrdinary
  NearCubicWires.RepairSource.VerifierEncoding NearCubicWires.CanonicalBinary NearCubicWires.RepairRepresentation
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem KC.of_keep {s : St VV MM} {a b : DS VV MM} (h : KC a)
    (hs : kcRegs.all (fun x => sAny (opWr x) s == false) = true)
    (hk : ∀ x, sAny (opWr x) s = false → b.env x = a.env x) : KC b := by
  have e : ∀ y ∈ kcRegs, b.env y = a.env y := fun y hy => hk y (by
    have := List.all_eq_true.mp hs y hy; simpa using this)
  exact ⟨by rw [e vZ (by decide), h.z], by rw [e v1 (by decide), h.one], by rw [e v2 (by decide), h.two],
    by rw [e kc3 (by decide), h.k3], by rw [e kc4 (by decide), h.k4], by rw [e kc5 (by decide), h.k5],
    by rw [e kc6 (by decide), h.k6], by rw [e kc7 (by decide), h.k7], by rw [e kc8 (by decide), h.k8]⟩

/-- The program constants. -/
def constP : St VV MM :=
  .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.seq (.op (.inc v2)) (.seq (.op (.copy kc3 v2)) (.seq (.op (.inc kc3))
  (.seq (.op (.copy kc4 kc3)) (.seq (.op (.inc kc4)) (.seq (.op (.copy kc5 kc4)) (.seq (.op (.inc kc5))
  (.seq (.op (.copy kc6 kc5)) (.seq (.op (.inc kc6)) (.seq (.op (.copy kc7 kc6)) (.seq (.op (.inc kc7))
  (.seq (.op (.copy kc8 kc7)) (.op (.inc kc8)))))))))))))))

theorem constP_spec {C : Ctx} (a : DS VV MM) (hz : ∀ x ∈ kcRegs, a.env x = 0) (hW : 16 ≤ 2 ^ C.Wd) :
    Hs C constP a 29 (fun b => KC b) := by
  apply hs_of_wpc
  simp only [constP, wpc, opwp]
  have h0 := hz vZ (by decide); have h1 := hz v1 (by decide); have h2 := hz v2 (by decide)
  have h3 := hz kc3 (by decide); have h4 := hz kc4 (by decide); have h5 := hz kc5 (by decide)
  have h6 := hz kc6 (by decide); have h7 := hz kc7 (by decide); have h8 := hz kc8 (by decide)
  have hW0 : C.Wd ≠ 0 := by intro h; rw [h] at hW; norm_num at hW
  vsimp [h0, h1, h2, h3, h4, h5, h6, h7, h8, hW0]
  and_split
  all_goals first | omega | exact hW0 | skip
  exact ⟨by vsimp [h0], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [],
    by vsimp []⟩

/-- **Reading the request.** -/
def parseP : St VV MM :=
  .seq constP (.seq rdNatI (.seq (rdStoreP sCB pX) (.seq (rdStoreP sIB dIL) (.seq (rdUnaryP dN)
    (.seq (rdUnaryP dF) (rdBinP dH))))))

def parseCost (r : CNFCompilationRequest) : ℕ := 40 * r.word.length + 200

theorem natBitLength_le_self' (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 x
  omega

theorem parseP_spec (r : CNFCompilationRequest) (C : Ctx) (hC : C.inp = requestEntryWord r)
    (hW : r.word.length + 10 ≤ C.Wd) :
    Hs C parseP a0 (parseCost r) (fun b => KC b ∧ b.ram sCB = codeBits r.verifier ∧
      b.rc sCB = (code r.verifier).length ∧ b.ram sIB = r.input.map Bool.toNat ∧ b.rc sIB = r.input.length ∧
      b.env dIL = r.input.length ∧ b.env dN = r.witnessLength ∧ b.env dF = r.fuel ∧ b.env dH = r.high ∧
      (∀ x, sAny (opWr x) parseP = false → b.env x = 0) ∧
      (∀ m, sAny (opMs m) parseP = false → b.ram m = [] ∧ b.rc m = 0) ∧ b.out = []) := by
  have hWd : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hwl : (code r.verifier).length + r.input.length + r.witnessLength + r.fuel + r.high.bits.length ≤ r.word.length := by
    simp [CNFCompilationRequest.word, frame_len]; omega
  -- split the word
  have hw : C.inp.drop (natWord r.word.length).length = frame (code r.verifier) ++ (frame r.input ++
      (frame (List.replicate r.witnessLength true) ++ (frame (List.replicate r.fuel true) ++ (frame r.high.bits ++
      [])))) := by
    rw [hC, requestEntryWord, Proximity.LengthPrefix.wrapped, List.drop_left]
    simp [CNFCompilationRequest.word, List.append_assoc]
  have hlt : ∀ x, x + 10 ≤ C.Wd → x + 1 < 2 ^ C.Wd := fun x hx => by omega
  set c2 := 30 * natBitLength r.word.length + 30 with hc2
  set c3 := (code r.verifier).length * 9 + 4 with hc3
  set c4 := r.input.length * 9 + 4 with hc4
  set c5 := (List.replicate r.witnessLength true).length * 7 + 4 with hc5
  set c6 := (List.replicate r.fuel true).length * 7 + 4 with hc6
  set c7 := r.high.bits.length * 10 + 8 with hc7
  have hnb := natBitLength_le_self' r.word.length
  have main : Hs C parseP a0 (29 + (c2 + (c3 + (c4 + (c5 + (c6 + c7 + 1) + 1) + 1) + 1) + 1) + 1)
      (fun b => KC b ∧ b.ram sCB = codeBits r.verifier ∧ b.rc sCB = (code r.verifier).length ∧
        b.ram sIB = r.input.map Bool.toNat ∧ b.rc sIB = r.input.length ∧ b.env dIL = r.input.length ∧
        b.env dN = r.witnessLength ∧ b.env dF = r.fuel ∧ b.env dH = r.high) := by
    refine Hs.seq (Hs.keep (constP_spec (C := C) a0 (fun _ _ => rfl)
      (le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega)))))
      (fun b1 ⟨k1, e1, m1, i1, o1⟩ => ?_)
    have b1ip : b1.ip = 0 := i1 (by decide)
    refine Hs.seq (rdNatI_spec b1 ⟨k1.z, k1.one, k1.two⟩ r.word.length r.word (by
      rw [b1ip, List.drop_zero, hC]; rfl) (by omega)) (fun b2 ⟨_, _, i2, s2, f2⟩ => ?_)
    simp only [Prod.mk.injEq] at s2
    obtain ⟨o2, r2, c2', -, -, -⟩ := s2
    have k2 : KC b2 := k1.of_fr f2 (by decide)
    have hin2 : C.inp.drop b2.ip = frame (code r.verifier) ++ (frame r.input ++
        (frame (List.replicate r.witnessLength true) ++ (frame (List.replicate r.fuel true) ++
        (frame r.high.bits ++ [])))) := by rw [i2, b1ip, Nat.zero_add, hw]
    refine Hs.seq (rdStoreP_spec sCB pX (by decide) (code r.verifier) _ b2 hin2 k2.one
      (by rw [r2, (m1 sCB (by decide)).1]; rfl) (by rw [c2', (m1 sCB (by decide)).2]; rfl)
      (by rw [f2 pX (by decide), e1 pX (by decide)]; rfl) (hlt _ (by omega)))
      (fun b3 ⟨r3, c3', _, o3, _, i3, f3⟩ => ?_)
    have k3 : KC b3 := k2.of_fr f3 (by decide)
    refine Hs.seq (rdStoreP_spec sIB dIL (by decide) r.input _ b3 (by rw [i3]; exact drop_frame _ _ _ _ hin2) k3.one
      (by rw [(o3 sIB (by decide)).1, r2, (m1 sIB (by decide)).1]; rfl)
      (by rw [(o3 sIB (by decide)).2, c2', (m1 sIB (by decide)).2]; rfl)
      (by rw [f3 dIL (by decide), f2 dIL (by decide), e1 dIL (by decide)]; rfl) (hlt _ (by omega)))
      (fun b4 ⟨r4, c4', d4, o4, _, i4, f4⟩ => ?_)
    have k4 : KC b4 := k3.of_fr f4 (by decide)
    have hin4 := drop_frame _ _ _ _ (show C.inp.drop b3.ip = _ from by rw [i3]; exact drop_frame _ _ _ _ hin2)
    rw [show b3.ip + (2 * r.input.length + 1) = b4.ip by omega] at hin4
    refine Hs.seq (rdUnaryP_spec dN (by decide) _ _ b4 hin4 k4.one
      (by rw [f4 dN (by decide), f3 dN (by decide), f2 dN (by decide), e1 dN (by decide)]; rfl)
      (hlt _ (by simp; omega))) (fun b5 ⟨n5, r5, c5', _, i5, f5⟩ => ?_)
    have k5 : KC b5 := k4.of_fr f5 (by decide)
    have hin5 := drop_frame _ _ _ _ hin4
    rw [show b4.ip + (2 * (List.replicate r.witnessLength true).length + 1) = b5.ip by omega] at hin5
    refine Hs.seq (rdUnaryP_spec dF (by decide) _ _ b5 hin5 k5.one
      (by rw [f5 dF (by decide), f4 dF (by decide), f3 dF (by decide), f2 dF (by decide), e1 dF (by decide)]; rfl)
      (hlt _ (by simp; omega))) (fun b6 ⟨n6, r6, c6', _, i6, f6⟩ => ?_)
    have k6 : KC b6 := k5.of_fr f6 (by decide)
    have hin6 := drop_frame _ _ _ _ hin5
    rw [show b5.ip + (2 * (List.replicate r.fuel true).length + 1) = b6.ip by omega] at hin6
    refine Hs.mono (rdBinP_spec dH (by decide) _ _ b6 hin6 k6.one (by
      exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega : r.high.bits.length + 1 < C.Wd)) le_rfl))
      le_rfl ?_
    rintro b7 ⟨n7, r7, c7', _, _, f7⟩
    refine ⟨k6.of_fr f7 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r7, r6, r5, (o4 sCB (by decide)).1, r3]; rfl
    · rw [c7', c6', c5', (o4 sCB (by decide)).2, c3']
    · rw [r7, r6, r5, r4]
    · rw [c7', c6', c5', c4']
    · rw [f7 dIL (by decide), f6 dIL (by decide), f5 dIL (by decide), d4]
    · rw [f7 dN (by decide), f6 dN (by decide), n5]; simp
    · rw [f7 dF (by decide), n6]; simp
    · rw [n7, bitsValue_natBits]
  refine Hs.mono (Hs.keep main) (by
    have hwd : r.word.length = 2 * ((code r.verifier).length + r.input.length + r.witnessLength + r.fuel +
        r.high.bits.length) + 5 := by
      simp only [CNFCompilationRequest.word, List.length_append, frame_len, List.length_replicate]; ring
    simp only [hc2, hc3, hc4, hc5, hc6, hc7, List.length_replicate]
    unfold parseCost; omega) ?_
  rintro b ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hx, hm, _, ho⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun x hx' => hx x hx', fun m hm' => hm m hm', ho (by decide)⟩

end NearCubicGates.Adapters.Compile
