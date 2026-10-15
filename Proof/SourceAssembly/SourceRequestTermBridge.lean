import Proof.SourceAssembly.SourceRequestTermCoef

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermBridge
open NearCubicWires RepairOrdinary RadixSemantics CanonicalBinary CanonicalWitnessCodec
open NearCubicWires.SourceRequest.TermSeg NearCubicWires.SourceRequest.TermReader

/-- A canonical balanced-list code's traversal atoms are its decoded list. -/
theorem atoms_of_decode (code : Nat) (cs : List Nat) (h : decodeBalancedList code = some cs) :
    (PCPPNativeCanonicalTree.tree code).atoms = cs := by
  have e1 := encodeBalancedList_of_decode h
  rw [← e1, ← CanonicalBinaryProgram.balancedTraversalTree_code, PCPPNativeCanonicalTree.tree_of_code,
    CanonicalBinaryProgram.balancedTraversalTree_atoms]

/-- `Option`-valued `mapM`, element by element. -/
theorem mapM_some {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) (h : xs.mapM f = some ys) :
    ys.length = xs.length ∧ ∀ (i : Nat) (hi : i < xs.length) (hj : i < ys.length), f xs[i] = some ys[i] := by
  induction xs generalizing ys with
  | nil =>
    simp at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : xs.mapM f with
      | none => simp [hx, hr] at h
      | some zs =>
        simp [hx, hr] at h
        subst h
        obtain ⟨hl, he⟩ := ih zs hr
        refine ⟨by simp [hl], ?_⟩
        intro i hi hj
        cases i with
        | zero => simpa using hx
        | succ k => simpa using he k (by simpa using hi) (by simpa using hj)

/-- A binary word at width `w` of a value below `2^w` reads back as that value. -/
theorem value_binary (w x : Nat) (hx : x < 2 ^ w) : value (SignedSortKey.binary w x) = x :=
  SignedSortKey.binary_value w x hx

/-- A tagged pair read by the pair parser: its two fields are the two decoded components. -/
theorem pair_fields (c : List Bool) (p q : Nat) (h : decodeTaggedList (value c) = some [p, q]) :
    value (CloseoutWitness.PairHeader.codeWord c 0) = p ∧ value (CloseoutWitness.PairHeader.codeWord c 1) = q := by
  have e := encodeTaggedList_of_decode h
  obtain ⟨_, h1, h3⟩ := CloseoutWitness.PairHeader.extracted_values c p q e.symm
  exact ⟨h1, h3⟩

/-- The pair parser's code words are binary words of their own width. -/
theorem codeWord_binary (c : List Bool) (k : Fin 2) :
    CloseoutWitness.PairHeader.codeWord c k =
      SignedSortKey.binary (CloseoutWitness.PairHeader.codeWord c k).length
        (value (CloseoutWitness.PairHeader.codeWord c k)) :=
  (BoundedCounter.binary_of_value _).symm

theorem rawSum_some (code : Nat) (ts : List (ℚ × Nat)) (h : rawSum code = some ts) :
    ∃ q tc tcs, decodeTaggedList code = some [q, tc] ∧ decodeBalancedList tc = some tcs ∧
      tcs.mapM termOf = some ts := by
  unfold rawSum at h
  split at h
  · rename_i q tc hT
    cases hB : decodeBalancedList tc with
    | none => rw [hB] at h; simp at h
    | some tcs =>
      rw [hB] at h
      simp only [Option.bind_some] at h
      exact ⟨q, tc, tcs, hT, hB, h⟩
  · simp at h

theorem termOf_some (t : Nat) (x : ℚ × Nat) (h : termOf t = some x) :
    ∃ a, decodeTaggedList t = some [a, x.2] ∧ decodeCanonicalRational a = some x.1 := by
  unfold termOf at h
  split at h
  · rename_i a b hT
    cases hC : decodeCanonicalRational a with
    | none => rw [hC] at h; simp at h
    | some coef =>
      rw [hC] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨a, hT, hC⟩
  · simp at h

theorem atom_lt (w code a : Nat) (hcode : code < 2 ^ w) (ha : a ∈ (PCPPNativeCanonicalTree.tree code).atoms) :
    a < 2 ^ w :=
  lt_of_le_of_lt (CloseoutWitness.Reencode.atom_le code a ha) hcode

/-- **The bridge.** On an admitted witness, the term the reader reaches through segments A, B, C is exactly the
`i`-th entry of `rawTerms bits j`: its circuit code (normalized at `cwid`) and its coefficient record (at `cw`). -/
theorem chain (bits : List Bool) (j i cwid cw : Nat) (ts : List (ℚ × Nat)) (h : rawTerms bits j = some ts)
    (hi : i < ts.length) :
    ∃ hj : j < (sums bits).length,
      ∃ hi' : i < (TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j])).length,
        (TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j])).length = ts.length ∧
        ClockNormalize.resize cwid (CloseoutWitness.PairHeader.codeWord
          (SignedSortKey.binary (SignedSortKey.binary bits.length (sums bits)[j]).length
            (TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j]))[i]) 1) =
          SignedSortKey.binary cwid ts[i].2 ∧
        TermCoef.recordWord (CloseoutWitness.PairHeader.codeWord
          (SignedSortKey.binary (SignedSortKey.binary bits.length (sums bits)[j]).length
            (TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j]))[i]) 0) cw =
          CloseoutRowsEstimatorCoefficients.Product.record cw ts[i].1 := by
  unfold rawTerms at h
  cases hF : decodeBalancedList (value (CloseoutWitness.BoundedFields.family bits)) with
  | none => rw [hF] at h; simp at h
  | some cs =>
    rw [hF] at h
    simp only [Option.bind_some] at h
    cases hc : cs[j]? with
    | none => rw [hc] at h; simp at h
    | some cj =>
      rw [hc] at h
      simp only [Option.bind_some] at h
      have hsums : sums bits = cs := atoms_of_decode _ _ hF
      have hjc : j < cs.length := by
        by_contra hn; rw [List.getElem?_eq_none (by omega)] at hc; simp at hc
      have hj : j < (sums bits).length := by rw [hsums]; exact hjc
      have hcj : (sums bits)[j] = cj := by
        have := List.getElem?_eq_getElem hjc; rw [hc] at this
        simp only [hsums]; exact (Option.some.inj this).symm
      refine ⟨hj, ?_⟩
      obtain ⟨q, tc, tcs, hT, hB, hM⟩ := rawSum_some cj ts h
      -- the sum word
      have hFlen := family_length bits
      have hcjlt : cj < 2 ^ bits.length := by
        have hmem : cj ∈ (PCPPNativeCanonicalTree.tree (value (CloseoutWitness.BoundedFields.family bits))).atoms := by
          rw [← hcj]; exact List.getElem_mem hj
        have := atom_lt _ _ _ (value_lt _) hmem
        rwa [hFlen] at this
      have hvc : value (SignedSortKey.binary bits.length (sums bits)[j]) = cj := by
        rw [hcj]; exact value_binary _ _ hcjlt
      obtain ⟨_, hq1⟩ := pair_fields _ q tc (by rw [hvc]; exact hT)
      have hterms : TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j]) = tcs := by
        unfold TermSegB.terms TermSegB.termsCode
        rw [hq1]
        exact atoms_of_decode _ _ hB
      obtain ⟨hlen, hel⟩ := mapM_some termOf tcs ts hM
      have hi2 : i < tcs.length := by omega
      refine ⟨by rw [hterms]; exact hi2, by rw [hterms]; exact hlen.symm, ?_⟩
      -- the term word
      have hti := hel i hi2 hi
      obtain ⟨a, hTa, hCa⟩ := termOf_some _ _ hti
      have hclen : (SignedSortKey.binary bits.length (sums bits)[j]).length = bits.length :=
        SignedSortKey.binary_length _ _
      have htclt : tc < 2 ^ bits.length := by
        rw [← hq1]
        have := value_lt (CloseoutWitness.PairHeader.codeWord (SignedSortKey.binary bits.length (sums bits)[j]) 1)
        have hl : (CloseoutWitness.PairHeader.codeWord (SignedSortKey.binary bits.length (sums bits)[j]) 1).length =
            bits.length := by
          simp [CloseoutWitness.PairHeader.codeWord, RecoveryFixedUnpair.leftWord,
            CompetitorWitnessTriple.word_length]
        rwa [hl] at this
      have hmem2 : tcs[i] ∈ (PCPPNativeCanonicalTree.tree tc).atoms := by
        rw [atoms_of_decode _ _ hB]; exact List.getElem_mem hi2
      have htlt : tcs[i] < 2 ^ bits.length := atom_lt _ _ _ htclt hmem2
      have hi3 : i < (TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j])).length := by
        rw [hterms]; exact hi2
      have hvt : value (SignedSortKey.binary (SignedSortKey.binary bits.length (sums bits)[j]).length
          (TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j]))[i]) = tcs[i] := by
        simp only [hterms, hclen]
        exact value_binary _ _ htlt
      obtain ⟨hp0, hp1⟩ := pair_fields _ a ts[i].2 (by rw [hvt]; exact hTa)
      refine ⟨?_, ?_⟩
      · rw [codeWord_binary _ 1, hp1]
        exact TermSegC.resize_binary_eq _ _ _ (by rw [← hp1]; exact value_lt _)
      · exact TermCoef.recordWord_eq _ cw _ (by rw [hp0]; exact hCa)

end NearCubicWires.SourceRequest.TermBridge

