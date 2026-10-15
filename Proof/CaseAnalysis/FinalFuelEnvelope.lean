import Proof.CaseAnalysis.FinalFuelRepin

namespace NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The defect: the POLYNOMIAL bucket can never hold one `2^q` call -/

/-- **THE DEFECT, machine-checked.**  For every coefficient `C` and every degree `d` the
polynomial bucket admits -- `d <= k+1`, i.e. `Runtime.ha`
(`Proof/CaseAnalysis/FinalResidualLeaves.lean`) and `runtime_of_polyFuel`'s `hd`
(`Proof/CaseAnalysis/FinalFuelRepin.lean`) -- the re-pinned budget `polyFuel C d N`
is EVENTUALLY STRICTLY BELOW `2 ^ q(N)`.

Since `paper.tex:3555-3557` charges ONE AND-four CAPP call at `2^q/q^sigma`, and `q^sigma` is
polylogarithmic in `N` while the gap here is a whole factor of `N`, this says that no admissible
`polyFuel` pays for even one analysis call.  The onset is `C` itself: once `C <= N`, the
coefficient is swallowed by one extra factor of `N+1`, and `pow_widthAt_ge` supplies the
`(N+1)^(k+2)` on the other side with `2^23` to spare. -/
theorem envelope_defect (sources : EightSources) (k C d : ℕ) (hd : d ≤ k + 1) :
    ∃ onset : ℕ, ∀ N, onset ≤ N → polyFuel C d N < 2 ^ widthAt sources k N := by
  refine ⟨C, ?_⟩
  intro N hN
  have hone : 1 ≤ N + 1 := by omega
  have hpos : 0 < (N + 1) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have hdeg : (N + 1) ^ d ≤ (N + 1) ^ (k + 1) := Nat.pow_le_pow_right hone hd
  have hstep : C * (N + 1) ^ d < (N + 1) * (N + 1) ^ (k + 1) := by
    have h1 : C * (N + 1) ^ d ≤ C * (N + 1) ^ (k + 1) := Nat.mul_le_mul_left _ hdeg
    have h2 : C * (N + 1) ^ (k + 1) < (N + 1) * (N + 1) ^ (k + 1) :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) hpos
    omega
  have hgrow : (N + 1) * (N + 1) ^ (k + 1) ≤ 2 ^ 23 * (N + 1) ^ (k + 2) := by
    have he : (N + 1) * (N + 1) ^ (k + 1) = (N + 1) ^ (k + 2) := by ring
    rw [he]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  calc polyFuel C d N = C * (N + 1) ^ d := rfl
    _ < (N + 1) * (N + 1) ^ (k + 1) := hstep
    _ ≤ 2 ^ 23 * (N + 1) ^ (k + 2) := hgrow
    _ ≤ 2 ^ widthAt sources k N := pow_widthAt_ge sources k N

/-! ## Section 2  The repair: the HOT bucket already holds it, and that is where it lands -/

/-- **The companion, machine-checked.**  The very same `polyFuel C d N` -- at every degree
`d + 1 <= k + 2` the re-pin admits -- fits inside ONE residual table factor
`2 ^ (q - kappa * L_q)`, the `hot`-bucket cell that `ledger_of_parts`' `hrow` binder
(`Proof/CaseAnalysis/FinalLedgerAssembly.lean`) allows.  That cell IS the paper's
`2^q/q^sigma` (`paper.tex:3555-3557`), by `kappa >= h_D + sigma + c_1`
(`paper.tex:2303-2307`).

So the envelope was never too small: `2 ^ (q - kappa*L_q)` holds what `A*(N+1)^a` cannot, and
`preFuel`/`cost` ALREADY reach it -- `ledger_of_parts` routes the whole `stageFuel` through
`stageFuel_core` (`Proof/CaseAnalysis/FinalSupplierFuel.lean`) into `hot`, while `hpoly`'s
`A*(N+1)^a` carries only `hrest`'s docked emit and tail budget.  This is REFUEL's own
`rowFuel_le_table` (`Proof/CaseAnalysis/FinalFuelRepin.lean`) with the `rowFuel` wrapper
removed, so that the quantity named is the budget itself. -/
theorem polyFuel_le_table (sources : EightSources) (k r degree C d N : ℕ)
    (hd : d + 1 ≤ k + 2)
    (hN : repinOnset sources k r degree C ≤ N) :
    polyFuel C d N
      ≤ 2 ^ (widthAt sources k N
          - ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1)) := by
  refine le_trans ?_ (rowFuel_le_table sources k r degree C d N hd hN)
  show polyFuel C d N ≤ 2 * polyFuel C d N + 2 * polyFuel C d N + 18
  omega

/-- **The two sections side by side**, at one instance: the same budget is below the residual
table factor and above nothing in the polynomial bucket reaches `2^q`.  Stated as one
conjunction so that a consumer cannot take half of it. -/
theorem envelope_split (sources : EightSources) (k r degree C d : ℕ) (hd : d + 1 ≤ k + 2) :
    (∃ onset : ℕ, ∀ N, onset ≤ N → polyFuel C d N < 2 ^ widthAt sources k N) ∧
    (∀ N, repinOnset sources k r degree C ≤ N →
      polyFuel C d N
        ≤ 2 ^ (widthAt sources k N
            - ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1))) :=
  ⟨envelope_defect sources k C d (by omega),
    fun N hN => polyFuel_le_table sources k r degree C d N hd hN⟩

end
end NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope
