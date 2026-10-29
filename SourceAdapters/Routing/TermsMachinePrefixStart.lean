import SourceAdapters.Routing.TermsMachinePrefixRequest

/-! The construction in `lem:generator`: begin either circuit pass with its exact coordinate prefix and zero accumulator. -/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.TermsMachine

open Joins ACSP ShortPCP.Machines.FL CoordinateMachine

def prefixStart : S :=
  .seq (.set 24 (.k 0)) (.seq Prefix.program
    (.seq (.set 25 (.v 24)) (Prefix.emitGate 1 (.k 0) (.k 0))))

def prefixStartWrites : List Var := Prefix.writes ++ [25]

theorem prefixStart_spec_generic (G : Glob) (s : FS) (f m : ℕ) (cs : List ℕ)
    (hB : Prefix.Bounds G f m 0) (hcs : ∀ c ∈ cs, c < 2^f)
    (h20 : s.env 20 = f) (h21 : s.env 21 = m) (h22 : s.env 22 = packW f cs)
    (hcount : 3*m*m+2*m+1 ≤ G.cap) :
    Appends prefixStartWrites s (evalS G prefixStart s)
      (Prefix.words (s.env 31) (Prefix.gates m 0 cs ++ [.const 0])) ∧
      (evalS G prefixStart s).env 24 = 3*m*m+2*m+1 ∧
      (evalS G prefixStart s).env 25 = 3*m*m+2*m := by
  let n := 3*m*m+2*m
  let a := s.setv 24 0
  have hprefix := Prefix.program_spec G a f m cs
    (by simpa only [a, FS.setv_env, Function.update_self] using hB) hcs
    (by simpa [a] using h20) (by simpa [a] using h21) (by simpa [a] using h22)
  generalize eb : evalS G Prefix.program a = b at hprefix
  have hb24 : b.env 24 = n := by simpa only [a, FS.setv_env, Function.update_self, Nat.zero_add] using hprefix.2.1
  have hb31 : b.env 31 = s.env 31 := by
    simpa [a] using hprefix.1.env 31 (by simp [Prefix.writes, Prefix.gateWrites])
  let c := b.setv 25 n
  have ha : Appends prefixStartWrites s a [] :=
    Appends.setv _ s 24 (by simp [prefixStartWrites, Prefix.writes, Prefix.gateWrites]) 0
  have hb : Appends prefixStartWrites a b
      (Prefix.words (s.env 31) (Prefix.gates m 0 cs)) := by
    simpa [a, prefixStartWrites] using hprefix.1.mono (fun i hi => List.mem_append_left _ hi)
  have hc : Appends prefixStartWrites b c [] :=
    Appends.setv _ b 25 (by simp [prefixStartWrites]) n
  have h1 : 1 ≤ G.cap := by omega
  have hbits (v : ℕ) (hv : v ≤ 1) : NearCubicWires.natBitLength v + 2 ≤ G.K :=
    hB.bits_tag (by omega)
  have hd := Prefix.emitGate_spec G c 1 (.k 0) (.k 0) 0 0 h1
    (by simp [evalE]) (by simp [evalE]) (hbits 1 le_rfl)
    (hbits 0 (by omega)) (hbits 0 (by omega)) hB.K_N
    (by simpa [c, hb24] using hcount)
  have he : evalS G prefixStart s = evalS G (Prefix.emitGate 1 (.k 0) (.k 0)) c := by
    simp only [prefixStart, evalS_seq, evalS_set, evalE]
    change evalS G (Prefix.emitGate 1 (.k 0) (.k 0))
      ((evalS G Prefix.program a).setv 25 ((evalS G Prefix.program a).env 24)) = _
    rw [eb, hb24]
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · have hh := ((ha.trans hb).trans hc).trans
      (hd.1.mono (fun i hi => List.mem_append_left _ (List.mem_append_left _ hi)))
    have hc31 : c.env 31 = s.env 31 := by simpa [c] using hb31
    by_cases hm : s.env 31 = 0 <;>
      simpa [hc31, Prefix.words, hm, List.flatMap_append, gateWord] using hh
  · simpa [c, hb24] using hd.2
  · exact (hd.1.env 25 (by simp [Prefix.gateWrites])).trans (by simp [c, n])

/-- All numeric premises of the pass prefix are discharged by the actual request. -/
theorem prefixStart_spec (p : TermsReq) (h : TermsOk p) (s : FS)
    (h20 : s.env 20 = p.f) (h21 : s.env 21 = p.l.m)
    (h22 : s.env 22 = NearCubicWires.CanonicalBinary.bitsValue (termsCoordWord p h)) :
    let G := globOf (preparedInput (termsInput p h))
    Appends prefixStartWrites s (evalS G prefixStart s)
      (Prefix.words (s.env 31) (Prefix.gates p.l.m 0 (coordMasks p h) ++ [.const 0])) ∧
      (evalS G prefixStart s).env 24 = 3*p.l.m*p.l.m+2*p.l.m+1 ∧
      (evalS G prefixStart s).env 25 = 3*p.l.m*p.l.m+2*p.l.m := by
  have hn := Bounds.prepared_numeric_bounds p h
  have hr := (Bounds.request_arithmetic p h).2.2.2.2.2.2.2.1
  have hc : 3*p.l.m*p.l.m+2*p.l.m+1 ≤ (globOf (preparedInput (termsInput p h))).cap := by
    have hh : 3*p.l.m*p.l.m+2*p.l.m+1 ≤ Bounds.arithmeticBound (termsInput p h).length := by nlinarith
    exact hh.trans hn.1
  exact prefixStart_spec_generic _ s p.f p.l.m (coordMasks p h)
    (prepared_prefix_bounds p h) (coordMasks_lt p h) h20 h21
    (h22.trans (packed_coordinates p h)) hc

theorem prefixStart_wf (d : ℕ) (hd : d ≤ 5) : wfS prefixStart d = true := by
  simp [prefixStart, wfS, dE, Prefix.wellFormed d hd,
    Prefix.emitGate_wf 1 (.k 0) (.k 0) d (by omega) (by decide) (by decide)]

end NearCubicGates.Adapters.Routing.TermsMachine
