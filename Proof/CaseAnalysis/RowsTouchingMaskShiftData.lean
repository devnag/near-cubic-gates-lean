import Proof.CaseAnalysis.RowsTouchingGateFoldLayout

/-! Shift the current-coordinate marker and update the one common I mask
in a single pass. The preceding marker bit is a physical carry field. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Cell:=Bool×Bool×Bool
def live (x : Cell):Bool:=x.1
def current (x : Cell):Bool:=x.2.1
def remaining (x : Cell):Bool:=x.2.2
def update (picked prior : Bool) (x : Cell):Cell:=(live x||(current x&&picked),prior,remaining x&& !prior)
def carry (xs : List Cell) (j : ℕ):Bool:=if j=0 then false else current (xs.getD (j-1) (false,false,false))
def transformed (picked : Bool) (xs : List Cell):List Cell:=
  List.ofFn (fun i : Fin xs.length=>update picked (carry xs i.val) (xs.getD i.val (false,false,false)))
def mixed (f : Cell→Bool) (xs ys : List Cell) (j : ℕ):List Bool:=
  (ys.take j).map f++(xs.drop j).map f

theorem carry_succ (xs : List Cell) (j : ℕ):carry xs (j+1)=current (xs.getD j (false,false,false)):=by
  simp [carry]

theorem transformed_length (picked : Bool) (xs : List Cell):(transformed picked xs).length=xs.length:=List.length_ofFn

theorem transformed_get (picked : Bool) (xs : List Cell) (j : ℕ) (hj:j<xs.length):
    (transformed picked xs)[j]'(by rw [transformed_length];exact hj)=
      update picked (carry xs j) (xs.getD j (false,false,false)):=by
  simp only [transformed,List.getElem_ofFn]

theorem mixed_read (f : Cell→Bool) (xs ys : List Cell) (j : ℕ) (hx:j<xs.length) (hy:j≤ys.length):
    readTapeBit (mixed f xs ys j) j=f xs[j]:=by
  have hp:((ys.take j).map f).length=j:=by simp [List.length_take,hy]
  unfold mixed
  rw [List.drop_eq_getElem_cons hx,List.map_cons]
  have actual:=Streaming.read_append ((ys.take j).map f) ((xs.drop (j+1)).map f) (f xs[j])
  simpa only [hp] using actual

theorem mixed_write (f : Cell→Bool) (xs ys : List Cell) (j : ℕ) (hx:j<xs.length) (hy:j<ys.length):
    writeTapeBit (mixed f xs ys j) j (f ys[j])=mixed f xs ys (j+1):=by
  have hp:((ys.take j).map f).length=j:=by simp [List.length_take,hy.le]
  unfold mixed
  rw [List.drop_eq_getElem_cons hx,List.map_cons,List.take_succ_eq_append_getElem hy]
  have actual:=BinaryIncrement.write_prefix ((ys.take j).map f) ((xs.drop (j+1)).map f) (f xs[j]) (f ys[j])
  simpa only [hp,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using actual

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
