import SourceAdapters.Routing.CoordinateMachineArray
import SourceAdapters.Routing.CoordinateMachineInputRunner
import SourceAdapters.Routing.CoordinateMachineInputSolverBounds

/-!
# The coordinate array as a polynomial-time ordinary word function

The construction in `lem:generator`: the fixed program parses the actual modulus request, executes the iterative triangular
solver, and emits the reduced coefficient masks in row-major order. Paid framing and the ordinary FL compiler give
a polynomial budget in the original request length. All numeric capacities follow from the valid request.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins

theorem program_of_parsed (G : Glob) (initial parsed : FS) (p : CoordReq) (h : CoordOk p)
    (hparse : evalS G coordParse initial = parsed)
    (h20 : parsed.env 20 = p.f) (h22 : parsed.env 22 = p.m)
    (hfl : parsed.fl = p.f) (hfp : parsed.fp = p.irr)
    (hout : parsed.out = []) (hbad : parsed.bad = false)
    (hN : p.m + 1 ≤ G.N) (hfN : p.f ≤ G.N) (hK : p.f * (p.m + 1) ≤ G.K)
    (hw : p.f + 2 ≤ G.K) (hpow : 2 ^ p.f ≤ G.cap) (hc : 2 ≤ G.cap) :
    (evalS G program initial).out = coordWord p h ∧ (evalS G program initial).bad = false := by
  have hs := solveArray_spec G parsed p h hfl hfp h20 h22 hN hfN hK hw hpow hc
  have he : evalS G program initial = evalS G solveArray parsed := by
    rw [program, evalS_seq, hparse]
  exact ⟨(congrArg FS.out he).trans (hs.out.trans (by rw [hout]; rfl)),
    (congrArg FS.bad he).trans (hs.bad.trans hbad)⟩

theorem program_spec (p : CoordReq) (h : CoordOk p) :
    let inp := preparedInput (coordInput p)
    let t := evalS (globOf inp) program (s0 inp)
    t.out = coordWord p h ∧ t.bad = false := by
  obtain ⟨h20, _, h22, hfl, hfp, hout, hbad, _⟩ := prepared_coordParse p h
  obtain ⟨hN, hfN, hK, hw, hpow, hc⟩ := prepared_solver_bounds p h
  exact program_of_parsed (globOf (preparedInput (coordInput p))) (s0 (preparedInput (coordInput p)))
    _ p h rfl h20 h22 hfl hfp hout hbad hN hfN hK hw hpow hc

/-- The exact coordinate-array interface, with a fixed ordinary program and polynomial request-length budget. -/
theorem coordinateArrayWF : CoordArrayWF := by
  refine ⟨ordinaryCoefficient program, ordinaryDegree program, ⟨?_⟩⟩
  exact polynomialProgram (fun p : {p : CoordReq // CoordOk p} => coordInput p.1)
    (fun p => coordWord p.1 p.2) program program_wf
    (fun p => (program_spec p.1 p.2).2) (fun p => (program_spec p.1 p.2).1)

end NearCubicGates.Adapters.Routing.CoordinateMachine
