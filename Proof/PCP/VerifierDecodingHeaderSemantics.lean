import Proof.PCP.VerifierDecodingHeaderTotal

/-! Public source reconstruction for the successful physical header parser. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.HeaderMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem parts_decomposition {bits fields : List Bool} {t s : ℕ}
    (hp : parts bits=some (t,s,fields)) : bits=word t s fields := by
  unfold parts at hp
  cases hfirst : unary bits with
  | none => simp [hfirst] at hp
  | some first =>
    rcases first with ⟨a,tail⟩
    cases hsecond : unary tail with
    | none => simp [hfirst,hsecond] at hp
    | some second =>
      rcases second with ⟨b,rest⟩
      simp only [hfirst,Option.bind_some,hsecond,Option.map_some,
        Option.some.injEq,Prod.mk.injEq] at hp
      rcases hp with ⟨rfl,rfl,rfl⟩
      rw [UnaryMachine.unary_decomposition hfirst,UnaryMachine.unary_decomposition hsecond]
      rfl

end NearCubicWires.RepairSource.VerifierDecoding.HeaderMachine
