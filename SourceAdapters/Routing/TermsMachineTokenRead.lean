import SourceAdapters.Routing.TermsMachineTokens
import SourceAdapters.Routing.CoordinateMachineInput
import SourceAdapters.Routing.CoordinateMachineOutput

/-! The construction in `lem:generator`: exact parsing of each postfix tag and payload. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open Joins CoordinateMachine

def tokenTag : TermTok → ℕ
  | .const _ => 0
  | .read _ => 1
  | .add => 2
  | .mul => 3
  | .square => 4

def tokenValue : TermTok → ℕ
  | .const c => c
  | .read v => varCode v
  | _ => 0

theorem tokenWord_eq (t : TermTok) :
    termTokWord t = natWord (tokenTag t) ++ natWord (tokenValue t) := by
  cases t <;> rfl

theorem tokenTag_lt (t : TermTok) : tokenTag t < 5 := by
  cases t <;> simp [tokenTag]

def readToken : S := .seq (storeNat 38) (storeNat 39)

def tokenReadWrites : List Var := [5, 6, 8, 9, 14, 38, 39]

theorem readToken_spec (G : Glob) (s : FS) (tag value pos Bd : ℕ)
    (hat : At (s.env 10) pos (natWord tag ++ natWord value))
    (h14 : s.env 14 = pos)
    (hend : pos + (natWord tag ++ natWord value).length ≤ Bd) (hB : BdOk G Bd) :
    let t := evalS G readToken s
    t.env 38 = tag ∧ t.env 39 = value ∧
      t.env 14 = pos + (natWord tag ++ natWord value).length ∧
      Appends tokenReadWrites s t [] := by
  obtain ⟨ha, hb⟩ := At.append hat
  have hlen : (natWord tag ++ natWord value).length =
      (natWord tag).length + (natWord value).length := List.length_append
  obtain ⟨a38, a14, aW⟩ := storeNat_spec G s 38 tag pos Bd ha h14 (by omega) hB (by decide)
  generalize ea : evalS G (storeNat 38) s = a at a38 a14 aW
  have a10 : a.env 10 = s.env 10 := aW.env 10 (by decide)
  obtain ⟨b39, b14, bW⟩ := storeNat_spec G a 39 value (pos + (natWord tag).length) Bd
    (by simpa only [a10] using hb) a14 (by omega) hB (by decide)
  generalize eb : evalS G (storeNat 39) a = b at b39 b14 bW
  have he : evalS G readToken s = b := by simp only [readToken, evalS_seq, ea, eb]
  have hip : b.ip = s.ip := by
    rw [← he]
    exact ip_rdFree G readToken s (by decide)
  have hw : Wr tokenReadWrites s b :=
    (aW.mono (by decide)).trans (bW.mono (by decide))
  dsimp only
  rw [he]
  exact ⟨(bW.env 38 (by decide)).trans a38, b39, by omega,
    ⟨hw.env, by simpa using hw.out, hw.fl, hw.fp, hip, hw.bad⟩⟩

theorem readToken_wf (d : ℕ) (hd : d ≤ 7) : wfS readToken d = true := by
  simp [readToken, storeNat, pNat, pNatOnes, pNatBits, bitE, wfS, dE]
  omega

end NearCubicGates.Adapters.Routing.TermsMachine
