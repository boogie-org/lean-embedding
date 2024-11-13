import LeanBoogie.BoogieDsl

#check 1

open Boogie


theorem unit_seq : ITree.seq (Pure.pure ()) b = b := by rw [ITree.seq]; simp_all only [pure_bind]

abbrev adaptBool (f : BitVec 32 -> BitVec 32 -> Bool) (x y : Int) : Int := if f x y then 1 else 0

def trunc    (i : Int) : Int := @BitVec.truncate 32 8 i |>.toInt
-- def sext     (i : Int) : Int := @BitVec.signExtend 32 i
def bv.slt      (x : Int) (y : Int) : Int := if @BitVec.slt 32 x y then 1 else 0
def bv.add      (x : Int) (y : Int) : Int := x + y
def bv.shl      (x : Int) (y : Int) : Int := @BitVec.shiftLeft 32 x y.toNat |>.toInt
def bv.and      (x : Int) (y : Int) : Int := @BitVec.and 32 x y |>.toInt
def bv.lshr     (x : Int) (y : Int) : Int := @BitVec.ushiftRight 32 x y.toNat |>.toInt
def bv.ne (x y : Int) : Int := if x ≠ y then 1 else 0

procedure ffs_ref(i0: bv32) returns (r: bv32) {
  var i1: bv1;
  var i3: bv32;
  var i4: bv32;
  var i5: bv1;
  var i6: bv32;
  var i7: bv32;
  var i8: bv32;
  var i9: bv1;
  var i10: bv32;
  var i2: bv32;
bb0:
  i1 := bv.ne(i0, 0);
  goto bb1, bb2;
bb1:
  assume (i1 == 1);
  i3 := 0;
  i4 := 0;
  goto bb4;
bb2:
  assume !i1 == 1;
  i2 := 0;
  goto bb3;
bb3:
  r := i2;
  goto;
bb4:
  i5 := bv.slt(i4, 32);
  goto bb5, bb6;
bb5:
  assume i5 == 1;
  i6 := bv.add(i3, 1);
  i7 := bv.shl(1, i3);
  i8 := bv.and(i7, i0);
  i9 := bv.ne(i8, 0);
  goto bb7, bb8;
bb6:
  assume !i5 == 1;
  i2 := 0;
  goto bb3;
bb7:
  assume (i9 == 1);
  i2 := i6;
  goto bb3;
bb8:
  assume !i9 == 1;
  goto bb9;
bb9:
  i10 := bv.add(i4, 1);
  i3 := i6;
  i4 := i10;
  goto bb4;
}

-- procedure ffs_imp(i0: bv32) returns (r: bv32) {
--   var i1: bv32;
--   var i2: bv1;
--   var i5: bv32;
--   var i6: bv32;
--   var i7: bv8;
--   var i8: bv32;
--   var i3: bv8;
--   var i4: bv32;
--   var i9: bv32;
--   var i10: bv1;
--   var i13: bv32;
--   var i14: bv32;
--   var i15: bv8;
--   var i16: bv32;
--   var i11: bv8;
--   var i12: bv32;
--   var i17: bv32;
--   var i18: bv1;
--   var i21: bv32;
--   var i22: bv32;
--   var i23: bv8;
--   var i24: bv32;
--   var i19: bv8;
--   var i20: bv32;
--   var i25: bv32;
--   var i26: bv1;
--   var i29: bv32;
--   var i30: bv32;
--   var i31: bv8;
--   var i32: bv32;
--   var i27: bv8;
--   var i28: bv32;
--   var i33: bv1;
--   var i34: bv32;
--   var i35: bv32;
--   var i36: bv32;
--   var i37: bv32;
--   var i38: bv32;
-- bb0:
--   i1 := and(i0, 65535);
--   i2 := ne(i1, 0);
--   i3, i4 := 1, i0;
--   goto bb1, bb3;
-- bb1:
--   assume (i2 == 1);
--   goto bb2;
-- bb2:
--   i9 := and(i4, 255);
--   i10 := ne(i9, 0);
--   i11, i12 := i3, i4;
--   goto bb4, bb6;
-- bb3:
--   assume !((i2 == 1));
--   i5 := sext(1);
--   i6 := add(i5, 16);
--   i7 := trunc(i6);
--   i8 := lshr(i0, 16);
--   i3, i4 := i7, i8;
--   goto bb2;
-- bb4:
--   assume (i10 == 1);
--   goto bb5;
-- bb5:
--   i17 := and(i12, 15);
--   i18 := ne(i17, 0);
--   i19, i20 := i11, i12;
--   goto bb7, bb9;
-- bb6:
--   assume !((i10 == 1));
--   i13 := sext(i3);
--   i14 := add(i13, 8);
--   i15 := trunc(i14);
--   i16 := lshr(i4, 8);
--   i11, i12 := i15, i16;
--   goto bb5;
-- bb7:
--   assume (i18 == 1);
--   goto bb8;
-- bb8:
--   i25 := and(i20, 3);
--   i26 := ne(i25, 0);
--   i27, i28 := i19, i20;
--   goto bb10, bb12;
-- bb9:
--   assume !((i18 == 1));
--   i21 := sext(i11);
--   i22 := add(i21, 4);
--   i23 := trunc(i22);
--   i24 := lshr(i12, 4);
--   i19, i20 := i23, i24;
--   goto bb8;
-- bb10:
--   assume (i26 == 1);
--   goto bb11;
-- bb11:
--   i33 := ne(i28, 0);
--   goto bb13, bb14;
-- bb12:
--   assume !((i26 == 1));
--   i29 := sext(i19);
--   i30 := add(i29, 2);
--   i31 := trunc(i30);
--   i32 := lshr(i20, 2);
--   i27, i28 := i31, i32;
--   goto bb11;
-- bb13:
--   assume (i33 == 1);
--   i34 := sext(i27);
--   i35 := add(i28, 1);
--   i36 := and(i35, 1);
--   i37 := add(i34, i36);
--   i38 := i37;
--   goto bb15;
-- bb14:
--   assume !((i33 == 1));
--   i38 := 0;
--   goto bb15;
-- bb15:
--   r := i38;
--   return;
-- }
-- procedure check(x: bv32) {
--   var r_ref: bv32;
--   var r_imp: bv32;
--   call r_ref := ffs_ref(x);
--   call r_imp := ffs_imp(x);
--   assert r_ref == r_imp;
-- }
