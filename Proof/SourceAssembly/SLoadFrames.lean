import Proof.SourceAssembly.SLoadCore

/-! The suffix's framing pass.

`Request.input` is the concatenation of five frames. This module builds that
exact word on one ambient scratch tape out of five retained framed sources by
five paid calls of the existing three-tape frame appender
(`CompetitorFrameAppend.machine`, run by `CloseoutRowsCircuitAppend.frame_run`).
The appender's source cursor and reset log are physically restored, so the five
calls chain with no re-entry cost; only the growing output cursor advances. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Frames
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.CloseoutRowsCircuitAppend
noncomputable section

/-- Source slot, shared growing output slot, shared reset log slot. -/
def ports {U : Nat} (source out log : Fin U) : Fin 3 → Fin U := ![source, out, log]

@[simp] theorem ports_zero {U : Nat} (source out log : Fin U) : ports source out log 0 = source := rfl
@[simp] theorem ports_one {U : Nat} (source out log : Fin U) : ports source out log 1 = out := rfl
@[simp] theorem ports_two {U : Nat} (source out log : Fin U) : ports source out log 2 = log := rfl

/-- One fixed frame-append stage, a four-state local program docked at three
ambient slots. Neither the tape count nor the state count depends on a request. -/
noncomputable def stage {U : Nat} (source out log : Fin U) : Machine U 4 :=
  RecoveryFocus.machine (ports source out log) CompetitorFrameAppend.machine

/-- One paid frame append onto the ambient output tape. -/
theorem stage_step {U : Nat} (source out log : Fin U)
    (hso : source ≠ out) (hsl : source ≠ log) (hlo : out ≠ log)
    (cap : Nat) (bits acc : List Bool) (hc : 2 * bits.length + 1 ≤ cap)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHs : H source = 0) (hHo : H out = acc.length) (hHl : H log = 0)
    (hAs : A source = ZeroPadding.pad cap (frame bits)) (hAo : A out = acc)
    (hAl : A log = List.replicate cap false) :
    Step (stage source out log) (4 * bits.length + 3) H A
      (Function.update H out (acc ++ frame bits).length)
      (Function.update A out (acc ++ frame bits)) := by
  have hinj := SLoad.triple_injective source out log hso hsl hlo
  have e := CloseoutRowsCircuitAppend.frame_focus (ports source out log) hinj cap bits acc hc H A
    (by
      intro i
      fin_cases i
      · simpa [frameCfg] using hHs
      · simpa [frameCfg] using hHo
      · simpa [frameCfg] using hHl)
    (by
      intro i
      fin_cases i
      · simpa [frameCfg] using hAs
      · simpa [frameCfg] using hAo
      · simpa [frameCfg] using hAl)
  exact SLoad.step_of_exact e

/-- The five-frame concatenation the packet input is built from. -/
def bundle (w0 w1 w2 w3 w4 : List Bool) : List Bool :=
  frame w0 ++ frame w1 ++ frame w2 ++ frame w3 ++ frame w4

/-- The fixed framing program: five docked appenders, twenty states. -/
noncomputable def machine {U : Nat} (s0 s1 s2 s3 s4 out log : Fin U) : Machine U 20 :=
  Composition.machine (stage s0 out log)
    (Composition.machine (stage s1 out log)
      (Composition.machine (stage s2 out log)
        (Composition.machine (stage s3 out log) (stage s4 out log))))

/-- Fuel for the framing pass, in the five actual retained word lengths. -/
def cost (n0 n1 n2 n3 n4 : Nat) : Nat := 4 * (n0 + n1 + n2 + n3 + n4) + 19

/-- The framing pass: from five retained framed words on five ambient slots,
the ambient output slot physically holds their five-frame concatenation. Only
that one slot changes, and only its head moves. -/
theorem frames_step {U : Nat} (s0 s1 s2 s3 s4 out log : Fin U)
    (h0 : s0 ≠ out) (h1 : s1 ≠ out) (h2 : s2 ≠ out) (h3 : s3 ≠ out) (h4 : s4 ≠ out)
    (g0 : s0 ≠ log) (g1 : s1 ≠ log) (g2 : s2 ≠ log) (g3 : s3 ≠ log) (g4 : s4 ≠ log)
    (hlo : out ≠ log)
    (cap : Nat) (w0 w1 w2 w3 w4 : List Bool)
    (c0 : 2 * w0.length + 1 ≤ cap) (c1 : 2 * w1.length + 1 ≤ cap)
    (c2 : 2 * w2.length + 1 ≤ cap) (c3 : 2 * w3.length + 1 ≤ cap)
    (c4 : 2 * w4.length + 1 ≤ cap)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH0 : H s0 = 0) (hH1 : H s1 = 0) (hH2 : H s2 = 0) (hH3 : H s3 = 0) (hH4 : H s4 = 0)
    (hHo : H out = 0) (hHl : H log = 0)
    (hA0 : A s0 = ZeroPadding.pad cap (frame w0)) (hA1 : A s1 = ZeroPadding.pad cap (frame w1))
    (hA2 : A s2 = ZeroPadding.pad cap (frame w2)) (hA3 : A s3 = ZeroPadding.pad cap (frame w3))
    (hA4 : A s4 = ZeroPadding.pad cap (frame w4))
    (hAo : A out = []) (hAl : A log = List.replicate cap false) :
    Step (machine s0 s1 s2 s3 s4 out log)
      (cost w0.length w1.length w2.length w3.length w4.length) H A
      (Function.update H out (bundle w0 w1 w2 w3 w4).length)
      (Function.update A out (bundle w0 w1 w2 w3 w4)) := by
  classical
  -- the four intermediate output words, in the appender's own left-nested shape
  set a1 : List Bool := frame w0 with ha1
  set a2 : List Bool := a1 ++ frame w1 with ha2
  set a3 : List Bool := a2 ++ frame w2 with ha3
  set a4 : List Bool := a3 ++ frame w3 with ha4
  have e0 := stage_step s0 out log h0 g0 hlo cap w0 [] c0 H A hH0 (by simpa using hHo) hHl hA0 hAo hAl
  rw [List.nil_append] at e0
  have e1 := stage_step s1 out log h1 g1 hlo cap w1 a1 c1
    (Function.update H out a1.length) (Function.update A out a1)
    (by rw [Function.update_of_ne h1]; exact hH1)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hlo)]; exact hHl)
    (by rw [Function.update_of_ne h1]; exact hA1)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hlo)]; exact hAl)
  rw [Function.update_idem, Function.update_idem, ← ha2] at e1
  have e2 := stage_step s2 out log h2 g2 hlo cap w2 a2 c2
    (Function.update H out a2.length) (Function.update A out a2)
    (by rw [Function.update_of_ne h2]; exact hH2)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hlo)]; exact hHl)
    (by rw [Function.update_of_ne h2]; exact hA2)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hlo)]; exact hAl)
  rw [Function.update_idem, Function.update_idem, ← ha3] at e2
  have e3 := stage_step s3 out log h3 g3 hlo cap w3 a3 c3
    (Function.update H out a3.length) (Function.update A out a3)
    (by rw [Function.update_of_ne h3]; exact hH3)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hlo)]; exact hHl)
    (by rw [Function.update_of_ne h3]; exact hA3)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hlo)]; exact hAl)
  rw [Function.update_idem, Function.update_idem, ← ha4] at e3
  have e4 := stage_step s4 out log h4 g4 hlo cap w4 a4 c4
    (Function.update H out a4.length) (Function.update A out a4)
    (by rw [Function.update_of_ne h4]; exact hH4)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hlo)]; exact hHl)
    (by rw [Function.update_of_ne h4]; exact hA4)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hlo)]; exact hAl)
  rw [Function.update_idem, Function.update_idem] at e4
  have hfinal : a4 ++ frame w4 = bundle w0 w1 w2 w3 w4 := by
    simp [bundle, ha4, ha3, ha2, ha1, List.append_assoc]
  rw [hfinal] at e4
  have joined := e0.seq (e1.seq (e2.seq (e3.seq e4)))
  refine joined.enlarge ?_
  simp only [cost]
  omega

end
end SLoad.Frames
