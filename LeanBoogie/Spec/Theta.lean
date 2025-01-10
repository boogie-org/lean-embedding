import Aesop

/-- Monad morphism from a computation monad `M` to a specification monad `W`. -/
class Theta (M : Type u -> Type v) (W : outParam (Type u -> Type v)) where
  θ : M A -> W A
export Theta (θ)

attribute [aesop unfold unsafe 10%] Theta.θ

class LawfulTheta (M : (Type u -> Type v)) [m : Monad M] (W : outParam (Type u -> Type v)) [w : Monad W] [Theta M W] : Prop where
  θ_pure {a : A} : θ (return a : M A) = return a
  θ_bind {a : M A} {b : A -> M B} : θ (a >>= b) = θ a >>= (fun a => θ (b a))

attribute [aesop unsafe 50%] LawfulTheta.θ_pure
attribute [aesop unsafe 10%] LawfulTheta.θ_bind

export LawfulTheta (θ_pure θ_bind)
