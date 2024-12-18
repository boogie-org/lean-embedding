import LeanBoogie.Dsl

open LeanBoogie

abbrev adaptBool (f : BitVec 32 -> BitVec 32 -> Bool) (x y : Int) : Int := if f x y then 1 else 0

def bv.trunc_32_8 (x : BitVec 32) : BitVec 8 := BitVec.truncate _ x
def bv.sext_8_32 (x : BitVec 8) : BitVec 32 := BitVec.signExtend _ x
def bv.slt   (x y : BitVec n) : BitVec 1 := if BitVec.slt x y then 1 else 0
def bv.add   (x y : BitVec n) : BitVec n := BitVec.add x y
def bv.shl   (x y : BitVec n) : BitVec n := BitVec.shiftLeft x y.toNat
def bv.and   (x y : BitVec n) : BitVec n := BitVec.and x y
def bv.lshr  (x y : BitVec n) : BitVec n := BitVec.ushiftRight x y.toNat
def bv.ne    (x y : BitVec n) : BitVec 1 := if x ≠ y then 1 else 0

-- set_option pp.explicit true
-- set_option trace.Meta.isDefEq true

procedure ffs_ref(i0: bv32) returns (r: bv32) {
  var i1: bv1; var i3: bv32; var i4: bv32; var i5: bv1; var i6: bv32; var i7: bv32; var i8: bv32;
  var i9: bv1; var i10: bv32; var i2: bv32;
  goto bb0;
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

#print ffs_ref

-- set_option trace.LeanBoogie.dsl true
-- set_option trace.Meta.isDefEq true

procedure ffs_imp(i0: bv32) returns (r: bv32) {
  var i1: bv32; var i2: bv1; var i5: bv32; var i6: bv32; var i7: bv8; var i8: bv32; var i3: bv8;
  var i4: bv32; var i9: bv32; var i10: bv1; var i13: bv32; var i14: bv32; var i15: bv8;
  var i16: bv32; var i11: bv8; var i12: bv32; var i17: bv32; var i18: bv1; var i21: bv32;
  var i22: bv32; var i23: bv8; var i24: bv32; var i19: bv8; var i20: bv32; var i25: bv32;
  var i26: bv1; var i29: bv32; var i30: bv32; var i31: bv8; var i32: bv32; var i27: bv8;
  var i28: bv32; var i33: bv1; var i34: bv32; var i35: bv32; var i36: bv32; var i37: bv32;
  var i38: bv32;
  goto bb0;
bb0:
  i1 := bv.and(i0, 65535);
  i2 := bv.ne(i1, 0);
  i3 := 1;
  i4 := i0;
  goto bb1, bb3;
bb1:
  assume (i2 == 1);
  goto bb2;
bb2:
  i9 := bv.and(i4, 255);
  i10 := bv.ne(i9, 0);
  i11 := i3;
  i12 := i4;
  goto bb4, bb6;
bb3:
  assume !((i2 == 1));
  i5 := bv.sext_8_32(1);
  i6 := bv.add(i5, 16);
  i7 := bv.trunc_32_8(i6);
  i8 := bv.lshr(i0, 16);
  i3 := i7;
  i4 := i8;
  goto bb2;
bb4:
  assume (i10 == 1);
  goto bb5;
bb5:
  i17 := bv.and(i12, 15);
  i18 := bv.ne(i17, 0);
  i19 := i11;
  i20 := i12;
  goto bb7, bb9;
bb6:
  assume !((i10 == 1));
  i13 := bv.sext_8_32(i3);
  i14 := bv.add(i13, 8);
  i15 := bv.trunc_32_8(i14);
  i16 := bv.lshr(i4, 8);
  i11 := i15;
  i12 := i16;
  goto bb5;
bb7:
  assume (i18 == 1);
  goto bb8;
bb8:
  i25 := bv.and(i20, 3);
  i26 := bv.ne(i25, 0);
  i27 := i19;
  i28 := i20;
  goto bb10, bb12;
bb9:
  assume !((i18 == 1));
  i21 := bv.sext_8_32(i11);
  i22 := bv.add(i21, 4);
  i23 := bv.trunc_32_8(i22);
  i24 := bv.lshr(i12, 4);
  i19 := i23;
  i20 := i24;
  goto bb8;
bb10:
  assume (i26 == 1);
  goto bb11;
bb11:
  i33 := bv.ne(i28, 0);
  goto bb13, bb14;
bb12:
  assume !((i26 == 1));
  i29 := bv.sext_8_32(i19);
  i30 := bv.add(i29, 2);
  i31 := bv.trunc_32_8(i30);
  i32 := bv.lshr(i20, 2);
  i27 := i31;
  i28 := i32;
  goto bb11;
bb13:
  assume (i33 == 1);
  i34 := bv.sext_8_32(i27);
  i35 := bv.add(i28, 1);
  i36 := bv.and(i35, 1);
  i37 := bv.add(i34, i36);
  i38 := i37;
  goto bb15;
bb14:
  assume !((i33 == 1));
  i38 := 0;
  goto bb15;
bb15:
  r := i38;
  return;
}

#check 10

-- todo1: Hide internal state
-- todo2: Lift each block into its own def to make terms smaller

/-
  Stuff in play:
  - Global state: `G : Con`
  - Return value: `R : Ty`
  - Parameters: `P : Con`
  - Local variables: `L : Con`

  From the outside perspective, `procedure f(x: bv16, y: bv16) returns (r:bv32) { ... }` should have
  the signature `[bv16, bv16]ᴬ -> ITree (Mem G) bv32ᴬ`, so a complete absence of local vars `L`.
  Internally, we will have the context `Γ := L ++ P ++ [R] ++ G`.


-/

example : ffs_imp (i0, ()) = ffs_ref (i0, ()) := by
  unfold ffs_imp
  simp
  rw [runProc, runRes]
  dsimp [Functor.map]
  simp

  -- rw [ffs_imp]

  sorry
  done
