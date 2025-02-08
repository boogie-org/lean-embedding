import Lean
import LeanBoogie.ConTy

open LeanBoogie
namespace LeanBoogie

inductive Literal : Ty -> Type
| intL : Int -> Literal .int
| boolL : Bool -> Literal .bool
| bvL : BitVec n -> Literal (.bv n)
| realL : Real -> Literal .real

inductive UnaryOp : Ty -> Type
| notB : UnaryOp .bool
| negI : UnaryOp .int

inductive BinaryOp : Ty -> Type
| addI : BinaryOp .int
| subI : BinaryOp .int
| mulI : BinaryOp .int
| divI : BinaryOp .int
| modI : BinaryOp .int
--| addR : BinaryOp .real
--| subR : BinaryOp .real
--| mulR : BinaryOp .real
--| divR : BinaryOp .real
| imp : BinaryOp .bool
| and : BinaryOp .bool
| or : BinaryOp .bool
| equiv : BinaryOp .bool -- TODO: have this in addition to .eq .bool?

inductive RelationOp : Ty -> Type
| eq : RelationOp A
| neq : RelationOp A
| lessI : RelationOp .int

inductive Appliable : Ty -> Ty -> Type
| unop : UnaryOp A -> Appliable A A
| binop : BinaryOp A -> Appliable A (.map A A)
| relop : BEq (TyA A) -> RelationOp A -> Appliable A (.map A .bool)
| mapSelect : Appliable (.map A B) (.map A B)

inductive Expr : Con -> Ty -> Type
| lit : Literal A -> Expr Γ A
| var : Var Γ A -> Expr Γ A
| apply : Appliable A B -> Expr Γ A -> Expr Γ B
| applyExpr : Expr Γ (.map A B) -> Expr Γ A -> Expr Γ B
| lambda : Expr (A :: Γ) B -> Expr Γ (.map A B)

inductive Formula : Con -> Type
| forallF : Formula (ty :: Γ) -> Formula Γ
| existsF : Formula (ty :: Γ) -> Formula Γ
| boolF : Expr Γ .bool -> Formula Γ
-- Grr. I don't like needing separate boolean and formula operators, but
-- this works out most cleanly.
| andF : Formula Γ -> Formula Γ -> Formula Γ
| orF : Formula Γ -> Formula Γ -> Formula Γ
| impF : Formula Γ -> Formula Γ -> Formula Γ
| eqF : Formula Γ -> Formula Γ -> Formula Γ
| eqE : Expr Γ A -> Expr Γ A -> Formula Γ
| litF : Bool -> Formula Γ

abbrev mkUn (op : UnaryOp A) (l : Expr Γ A) : Expr Γ A :=
  .apply (.unop op) l
abbrev mkBin (op : BinaryOp A) (l : Expr Γ A) (r : Expr Γ A) : Expr Γ A :=
  .applyExpr (.apply (.binop op) l) r
abbrev mkRel (beq: BEq (TyA A)) (op : RelationOp A) (l : Expr Γ A) (r : Expr Γ A) : Expr Γ .bool :=
  .applyExpr (.apply (.relop beq op) l) r

inductive PassiveCommand : Con -> Type
| assert : Formula Γ -> PassiveCommand Γ
| assume : Formula Γ -> PassiveCommand Γ

inductive Command : Con -> Type
| assign : (v : Var Γ A) -> Expr Γ A -> Command Γ
| passive : PassiveCommand Γ -> Command Γ

inductive TransferCommand (b : Nat) : Con -> Type
-- For now, if the list is empty, it means the same thing as ret. We
-- could choose to simply not have ret.
| goto : List (Fin b) -> TransferCommand b Γ
| ret : TransferCommand b Γ

structure Block (C: Type) (S: Type) (b : Nat) (Γ : Con) where
  -- These are executed in the given sequence
  label : Fin b
  simpleCmds : List C
  -- This is a BigBlock, in the Boogie implementation, if structuredCmd
  -- is present
  structuredCmd : S
  transferCmd : TransferCommand b Γ

abbrev PassiveBlock Γ b := Block (PassiveCommand Γ) Unit b Γ
abbrev SimpleBlock Γ b := Block (Command Γ) Unit b Γ

inductive StructuredCommand (b: Nat) : Con -> Type
| ite : Expr Γ .bool ->
        List (StructuredCommand b Γ) ->
        List (StructuredCommand b Γ) ->
        StructuredCommand b Γ
| while : Expr Γ .bool ->
          List (StructuredCommand b Γ) ->
          StructuredCommand b Γ
| cmd : Command Γ -> StructuredCommand b Γ
-- break is translated to goto by the front end
| transfer : TransferCommand b Γ -> StructuredCommand b Γ

abbrev BigBlock (b : Nat) (Γ : Con) := Block (Command Γ) (StructuredCommand b Γ) b Γ

abbrev Command.assert (p : Formula Γ) : Command Γ := .passive (.assert p)
abbrev Command.assume (p : Formula Γ) : Command Γ := .passive (.assume p)
-- abbrev Command.goto (ns : List (Fin b)) : Command b Γ := .passive (.goto ns)
abbrev Command.skip : Command Γ := .assume (.boolF (.lit (.boolL True)))

structure Axiom (Γ : Con) where
  name : Option Lean.Name
  body : Expr Γ .bool

structure Function (Γ : Con) where
  name : Lean.Name
  -- TODO: type parameters
  args : Con
  resTy : Ty
  body : Expr (Γ ++ args) resTy

structure Constant where
  name : Lean.Name
  ty : Ty
  isUnique : Bool

structure Variable where
  name : Lean.Name
  ty : Ty

structure Procedure (C: Type) (S: Type) (Γ : Con) where
  -- Γ describes globals
  name : Lean.Name
  b : Nat
  binhabited : b > 0
  effects : Type -> Type
  inParams : Con
  locals : Con
  outParams : Con
  -- TODO: contracts
  body : Fin b -> Block C S b (Γ /- ++ inParams ++ locals ++ outParams-/)

inductive Declaration (Γ : Con) : Type 1
| axiomDecl : Axiom Γ -> Declaration Γ
| functionDecl : Function Γ -> Declaration Γ
| constantDecl : Constant -> Declaration Γ
| procedureDecl : Procedure C S Γ -> Declaration Γ
| globalVarDecl : Variable -> Declaration Γ

structure Program where
  Γ : Con
  declarations : Declaration Γ
