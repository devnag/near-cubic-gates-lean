import SourceAdapters.Compile.OracleWindowRun

/-!
proof of `thm:short-pcp-ours`, Step 4: the actual X5(a) request, including its outer source frame,
runs in a length-aware finite window. The window width is at most six times
the charged request measure. The verdict is negated exactly as in the proof of `thm:short-pcp-ours`, Step 4.
This proves finite execution semantics, not a polynomial circuit generator.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
  NearCubicWires.LocalBitMultitape
set_option autoImplicit false

def requestWidth (r : OracleCompilationRequest) : ℕ :=
  4*(r.data.length+r.ell)+r.fuel+6

theorem requestWidth_bound (r : OracleCompilationRequest) : requestWidth r ≤ 6*r.measure := by
  simp only [requestWidth,OracleCompilationRequest.measure]
  omega

def requestInitial (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) : p.Config :=
  initialConfiguration p.base.machine (p.base.inputTapes (r.runInput z))

theorem requestInitial_fits (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) : Fits (requestWidth r) (requestInitial p r z) := by
  constructor
  · intro tape; simp [requestInitial,initialConfiguration,requestWidth]
  · intro tape
    simp only [requestInitial,initialConfiguration,Program.inputTapes]
    split
    · simp [OracleCompilationRequest.runInput,frame_length,requestWidth]; omega
    · simp

def requestWindow (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) : Window p.base.tapeCount p.base.stateCount (requestWidth r) :=
  Window.pack (requestInitial p r z) (requestInitial_fits p r z)

theorem requestWindow_unpack (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) : (requestWindow p r z).unpack=requestInitial p r z :=
  Window.unpack_pack _ _

theorem requestWindow_room (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (z : BitInput r.ell) :
    ∀ tape, (requestWindow p r z).unpack.heads tape+r.fuel < requestWidth r := by
  rw [requestWindow_unpack]
  intro tape
  simp [requestInitial,initialConfiguration,requestWidth]
  omega

noncomputable def requestRun (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (O : BitInput r.ell → Bool) (z : BitInput r.ell) :=
  windowRounds (fixedArityOracle O) p (requestWidth r) r.fuel r.fuel (requestWindow p r z)

theorem requestRun_iff (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (O : BitInput r.ell → Bool) (z : BitInput r.ell) :
    OrdinaryOracleRuns (fixedArityOracle O) p (r.runInput z) [true] r.fuel ↔
      ∃ final, requestRun p r O z=some final ∧
        final.unpack.tapes p.base.outputTape=RepairOrdinary.frame [true] := by
  constructor
  · rintro ⟨cost,b,hc,ht,hh,ho⟩
    have htrace : OrdinaryOracleTrace (fixedArityOracle O) p cost
        (requestWindow p r z).unpack b := by rw [requestWindow_unpack]; exact ht
    obtain ⟨final,hr,he⟩ := (windowRun_iff _ _ _ _ _ b (requestWindow_room p r z)).2
      ⟨cost,hc,htrace,hh⟩
    exact ⟨final,hr,by rw [he]; exact ho⟩
  · rintro ⟨final,hr,ho⟩
    obtain ⟨cost,hc,ht,hh⟩ := (windowRun_iff _ _ _ _ _ final.unpack
      (requestWindow_room p r z)).1 ⟨final,hr,rfl⟩
    rw [requestWindow_unpack] at ht
    exact ⟨cost,final.unpack,hc,ht,hh,ho⟩

/-- True denotes the negated bounded verdict, as in the fixed circuit join. -/
noncomputable def requestVerdict (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (O : BitInput r.ell → Bool) (z : BitInput r.ell) : Bool := by
  classical
  exact match requestRun p r O z with
    | none => true
    | some final => !(decide (final.unpack.tapes p.base.outputTape=RepairOrdinary.frame [true]))

theorem requestVerdict_false_iff (p : OrdinaryOracleProgram) (r : OracleCompilationRequest)
    (O : BitInput r.ell → Bool) (z : BitInput r.ell) :
    requestVerdict p r O z=false ↔
      OrdinaryOracleRuns (fixedArityOracle O) p (r.runInput z) [true] r.fuel := by
  rw [requestRun_iff]
  unfold requestVerdict
  cases hr : requestRun p r O z <;> simp

end NearCubicGates.Adapters.Compile.OracleExecution
